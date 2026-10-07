package com.pedro.arbitrar;

import android.app.Notification;
import android.app.NotificationChannel;
import android.app.NotificationManager;
import android.app.PendingIntent;
import android.app.Service;
import android.content.Intent;
import android.graphics.Color;
import android.media.AudioAttributes;
import android.media.RingtoneManager;
import android.net.Uri;
import android.os.Build;
import android.os.IBinder;
import android.os.PowerManager;
import android.util.Log;
import androidx.core.app.NotificationCompat;
import org.json.JSONArray;
import org.json.JSONObject;
import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.math.BigDecimal;
import java.math.MathContext;
import java.math.RoundingMode;
import java.net.HttpURLConnection;
import java.net.URL;
import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.Executors;
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.TimeUnit;

/**
 * Monitor en segundo plano. Aplica las mismas reglas que arbitraje.html (motor v6):
 *
 *  1. Vigencia: cada cotización de CriptoYa trae su propio `time`. Una cotización que no se
 *     actualiza queda fuera del cálculo, aunque la API la siga devolviendo.
 *  2. Precio por unidad: CriptoYa cotiza siempre por 1 unidad. El número de la URL es el
 *     volumen a operar (define el precio en exchanges con libro de órdenes).
 *  3. Transferencia real: el retiro se descuenta con la comisión que informa CriptoYa por
 *     exchange y por red; sin red en común no hay ruta.
 *  4. Confirmación: la alerta exige que la ganancia siga ahí después de que los dos
 *     exchanges de la ruta volvieron a cotizar.
 *
 * El capital y el umbral de alerta son los de la app: MainActivity los reenvía en el Intent de
 * inicio (EXTRA_CONFIG) cada vez que se abre o que el usuario los cambia, y quedan guardados.
 */
public class BotService extends Service {

    private static final String TAG = "ArbitrARBot";
    private static final String CH_FOREGROUND = "arbitrar_fg";
    private static final String CH_ALERT      = "arbitrar_alert";
    private static final int    NOTIF_FG_ID   = 1;
    private static final int    NOTIF_ALERT_BASE = 100;

    // ─── Parámetros del motor: los mismos que CFG en arbitraje.html ───
    static final long   STALE_SEC         = 180;      // antigüedad máxima de una cotización contra la más nueva de la respuesta
    static final long   FEED_LAG_SEC      = 180;      // atraso máximo de toda la respuesta contra el reloj
    static final double MAX_PLAUSIBLE_PCT = 5.0;      // ganancia neta superior = dato sospechoso, no alerta
    static final long   ALERT_COOLDOWN_MS = 300_000L; // no repetir la alerta de una ruta antes de 5 minutos…
    static final double REALERT_STEP_PCT  = 0.5;      // …salvo que mejore al menos este margen
    static final long   FEES_TTL_MS       = 600_000L; // refresco de comisiones de retiro
    static final long   CYCLE_SEC         = 15;

    // ─── Configuración que fija la app (Capital y Alerta % de la pantalla principal) ───
    // MainActivity la reenvía en el Intent de inicio como JSON: {"capital":1000,"alertPct":0.5}
    static final String EXTRA_CONFIG    = "arbitrar.config";
    private static final String PREFS       = "arbitrar_bot";
    private static final String PREF_CONFIG = "config";
    static final double CAPITAL_DEFAULT = 1000, CAPITAL_MIN = 10,  CAPITAL_MAX = 999999;   // mismos límites que el campo de la app
    static final double ALERT_DEFAULT   = 0.5,  ALERT_MIN   = 0.1, ALERT_MAX   = 20;

    // ─── Monedas ───
    static final String[] COIN_IDS     = {"usdt", "usdc", "dai", "btc", "eth"};
    static final double[] COIN_USD_REF = {1, 1, 1, 90000, 3000};   // solo para el volumen de la primera consulta

    // ─── Exchanges: { id, nombre, claves posibles en CriptoYa en orden de preferencia } ───
    // Qué monedas opera cada uno no se declara acá: sale de la respuesta de la API.
    static final String[][] EXCHANGES = {
        {"nexo",           "Nexo",            "nexo"},
        {"letsbit",        "LetsBit",         "letsbit"},
        {"ripio",          "Ripio",           "ripio"},
        {"satoshitango",   "SatoshiTango",    "satoshitango"},
        {"lemon",          "Lemon Cash",      "lemoncash"},
        {"fiwind",         "Fiwind",          "fiwind"},
        {"astropay",       "AstroPay",        "astropay"},
        {"belo",           "Belo",            "belo"},
        {"tiendacrypto",   "TiendaCrypto",    "tiendacrypto"},
        {"cryptomkt",      "CryptoMKT",       "cryptomktpro", "cryptomkt"},
        {"decrypto",       "Decrypto",        "decrypto"},
        {"cocoscrypto",    "Cocos Crypto",    "cocoscrypto"},
        {"bybit",          "Bybit",           "bybit"},
        {"binance",        "Binance",         "binance"},
        {"universalcoins", "Universal Coins", "universalcoins"},
        {"vitawallet",     "Vita Wallet",     "vitawallet"},
        {"saldo",          "Saldo.com.ar",    "saldo"},
        {"eluter",         "Eluter",          "eluter"},
    };

    // URLs para los botones de la alerta
    private static final Map<String, String> EX_URLS = new HashMap<>();
    static {
        EX_URLS.put("nexo",           "https://nexo.com");
        EX_URLS.put("letsbit",        "https://letsbit.io");
        EX_URLS.put("ripio",          "https://exchange.ripio.com");
        EX_URLS.put("satoshitango",   "https://satoshitango.com");
        EX_URLS.put("lemon",          "https://lemon.me");
        EX_URLS.put("fiwind",         "https://fiwind.io");
        EX_URLS.put("astropay",       "https://astropay.com/wallet/exchange");
        EX_URLS.put("belo",           "https://belo.app");
        EX_URLS.put("tiendacrypto",   "https://tiendacrypto.com");
        EX_URLS.put("cryptomkt",      "https://cryptomkt.com");
        EX_URLS.put("decrypto",       "https://decrypto.com");
        EX_URLS.put("cocoscrypto",    "https://cocos.ar");
        EX_URLS.put("bybit",          "https://bybit.com");
        EX_URLS.put("binance",        "https://www.binance.com/es/trade/USDT_ARS?type=spot");
        EX_URLS.put("universalcoins", "https://universalcoins.net");
        EX_URLS.put("vitawallet",     "https://vitawallet.io");
        EX_URLS.put("saldo",          "https://saldo.com.ar");
        EX_URLS.put("eluter",         "https://eluter.com");
    }

    private static final Map<String, String> NET_LABELS = new HashMap<>();
    static {
        NET_LABELS.put("TRON", "TRC-20 (Tron)");
        NET_LABELS.put("BSC", "BEP-20 (BSC)");
        NET_LABELS.put("ETHEREUM", "ERC-20 (Ethereum)");
        NET_LABELS.put("POLYGON", "Polygon");
        NET_LABELS.put("ARBITRUM", "Arbitrum");
        NET_LABELS.put("OPTIMISM", "Optimism");
        NET_LABELS.put("BASE", "Base");
        NET_LABELS.put("SOLANA", "Solana");
        NET_LABELS.put("AVALANCHE", "Avalanche");
        NET_LABELS.put("ZKSYNC", "zkSync");
        NET_LABELS.put("BITCOIN", "Bitcoin");
        NET_LABELS.put("LN", "Lightning");
    }

    // ══════════════════════════════════════════════════════════════
    //  MOTOR (estático y sin Android: se puede probar fuera del teléfono)
    // ══════════════════════════════════════════════════════════════

    static final int ST_OK = 0, ST_SUSPECT = 1, ST_NOFEE = 2;

    static final class Quote {
        final double bid, ask;
        final long t;
        Quote(double bid, double ask, long t) { this.bid = bid; this.ask = ask; this.t = t; }
    }

    static final class Net {
        final String name;
        final double fee;
        Net(String name, double fee) { this.name = name; this.fee = fee; }
    }

    static final class Opp {
        String coinId, coinLabel, buyId, buyName, sellId, sellName;
        String net;            // red de retiro elegida (null si no hay datos de comisiones)
        double fee;            // comisión de retiro en unidades de la moneda
        double pPct, pARS, askARS, bidARS;
        long tBuy, tSell;      // hora de cada cotización (segundos unix)
        int status;
        String key() { return coinId + "|" + buyId + "|" + sellId; }
    }

    static final class CoinResult {
        final List<Opp> opps = new ArrayList<>();
        long refT;             // cotización más nueva de la respuesta
        boolean down;          // la respuesta entera está atrasada o no trae `time`
        int stale, bad, noNet;
        double refAsk;         // mediana de precios de compra vigentes
    }

    static final class AlertState {
        long tb, ts;           // cotizaciones que originaron la ruta (0 = todavía no cumple)
        long lastAt;
        double lastPct = Double.NEGATIVE_INFINITY;
    }

    private static final Comparator<Opp> BY_RANK = new Comparator<Opp>() {
        @Override public int compare(Opp a, Opp b) {
            int ra = a.status == ST_SUSPECT ? 1 : 0, rb = b.status == ST_SUSPECT ? 1 : 0;
            if (ra != rb) return ra - rb;
            return Double.compare(b.pPct, a.pPct);
        }
    };

    private static final Comparator<Opp> BY_PROFIT = new Comparator<Opp>() {
        @Override public int compare(Opp a, Opp b) { return Double.compare(b.pPct, a.pPct); }
    };

    private static double pos(double v) {
        return (Double.isNaN(v) || Double.isInfinite(v) || v <= 0) ? 0 : v;
    }

    static double median(List<Double> values) {
        if (values.isEmpty()) return 0;
        List<Double> s = new ArrayList<>(values);
        Collections.sort(s);
        int m = s.size() / 2;
        return s.size() % 2 == 1 ? s.get(m) : (s.get(m - 1) + s.get(m)) / 2;
    }

    /** Comisiones de retiro de un exchange para una moneda: { RED: { withdraw, time } }. */
    static JSONObject feeMap(JSONObject fees, String[] ex, String sym) {
        if (fees == null) return null;
        for (int i = 2; i < ex.length; i++) {
            JSONObject e = fees.optJSONObject(ex[i]);
            if (e == null) continue;
            JSONObject m = e.optJSONObject(sym);
            if (m != null && m.length() > 0) return m;
        }
        return null;
    }

    private static double feeOf(JSONObject m, String net) {
        JSONObject o = m.optJSONObject(net);
        double f = o != null ? o.optDouble("withdraw", Double.NaN) : m.optDouble(net, Double.NaN);
        return (Double.isNaN(f) || Double.isInfinite(f) || f < 0) ? -1 : f;
    }

    /** Red más barata por la que `buy` retira y que `sell` también opera; null si no comparten ninguna. */
    static Net cheapestNetwork(JSONObject fees, String[] buy, String[] sell, String sym) {
        JSONObject a = feeMap(fees, buy, sym), b = feeMap(fees, sell, sym);
        if (a == null || b == null) return null;
        String best = null;
        double bestFee = 0;
        Iterator<String> it = a.keys();
        while (it.hasNext()) {
            String n = it.next();
            if (!b.has(n)) continue;
            double f = feeOf(a, n);
            if (f < 0) continue;
            if (best == null || f < bestFee || (f == bestFee && n.compareTo(best) < 0)) {
                best = n;
                bestFee = f;
            }
        }
        return best == null ? null : new Net(best, bestFee);
    }

    /**
     * Rutas operables de una moneda a partir de la respuesta cruda de CriptoYa.
     * @param fees   respuesta de /api/fees, o null si todavía no se pudo obtener
     * @param capArs capital en pesos
     * @param nowSec reloj del teléfono en segundos unix
     */
    static CoinResult computeCoin(String coinId, JSONObject data, JSONObject fees, double capArs, long nowSec) {
        CoinResult res = new CoinResult();
        String sym = coinId.toUpperCase(Locale.US);

        // "Ahora" según CriptoYa: la cotización más nueva de toda la respuesta
        long refT = 0;
        Iterator<String> it = data.keys();
        while (it.hasNext()) {
            JSONObject e = data.optJSONObject(it.next());
            if (e == null) continue;
            long t = e.optLong("time", 0);
            if (t > refT) refT = t;
        }
        res.refT = refT;
        if (refT == 0 || nowSec - refT > FEED_LAG_SEC) {
            res.down = true;
            return res;
        }

        List<String[]> exs = new ArrayList<>();
        List<Quote> quotes = new ArrayList<>();
        List<Double> asks = new ArrayList<>();
        for (String[] ex : EXCHANGES) {
            JSONObject e = null;
            for (int i = 2; i < ex.length && e == null; i++) e = data.optJSONObject(ex[i]);
            if (e == null) continue;                               // ese exchange no cotiza esta moneda
            double ask = pos(e.optDouble("totalAsk", 0));          // totalAsk/totalBid ya incluyen la comisión de trading
            if (ask == 0) ask = pos(e.optDouble("ask", 0));
            double bid = pos(e.optDouble("totalBid", 0));
            if (bid == 0) bid = pos(e.optDouble("bid", 0));
            if (ask == 0 && bid == 0) continue;
            long t = e.optLong("time", 0);
            if (ask == 0 || bid == 0 || bid > ask) { res.bad++; continue; }       // incompleta o cruzada
            if (t == 0 || refT - t > STALE_SEC) { res.stale++; continue; }        // el exchange dejó de actualizar
            exs.add(ex);
            quotes.add(new Quote(bid, ask, t));
            asks.add(ask);
        }
        res.refAsk = median(asks);

        for (int b = 0; b < exs.size(); b++) {
            for (int s = 0; s < exs.size(); s++) {
                if (b == s) continue;
                String[] buy = exs.get(b), sell = exs.get(s);
                Quote qb = quotes.get(b), qs = quotes.get(s);

                int status = ST_OK;
                Net net = null;
                if (fees == null) {
                    status = ST_NOFEE;                             // sin comisiones no se puede costear el retiro
                } else {
                    net = cheapestNetwork(fees, buy, sell, sym);
                    if (net == null) { res.noNet++; continue; }    // no hay cómo llevar la moneda de un exchange al otro
                }

                double fee = net != null ? net.fee : 0;
                double unitsNet = capArs / qb.ask - fee;
                if (unitsNet <= 0) continue;
                double pARS = unitsNet * qs.bid - capArs;
                double pPct = (pARS / capArs) * 100;
                if (status == ST_OK && pPct > MAX_PLAUSIBLE_PCT) status = ST_SUSPECT;

                Opp o = new Opp();
                o.coinId = coinId;  o.coinLabel = sym;
                o.buyId = buy[0];   o.buyName = buy[1];
                o.sellId = sell[0]; o.sellName = sell[1];
                o.net = net != null ? net.name : null;
                o.fee = fee;
                o.pPct = pPct;      o.pARS = pARS;
                o.askARS = qb.ask;  o.bidARS = qs.bid;
                o.tBuy = qb.t;      o.tSell = qs.t;
                o.status = status;
                res.opps.add(o);
            }
        }
        Collections.sort(res.opps, BY_RANK);
        return res;
    }

    /**
     * Rutas que corresponde alertar en este ciclo, de mayor a menor ganancia. Solo rutas operables
     * cuya ganancia sigue ahí después de que los dos exchanges volvieron a cotizar (un dato suelto
     * no alcanza), y respetando la pausa entre repeticiones.
     */
    static List<Opp> selectAlerts(List<CoinResult> results, Map<String, AlertState> states,
                                  double alertPct, long nowMs) {
        List<Opp> batch = new ArrayList<>();
        Set<String> seen = new HashSet<>();
        for (CoinResult r : results) {
            for (Opp o : r.opps) {
                if (o.status != ST_OK || o.pPct < alertPct) continue;
                String k = o.key();
                seen.add(k);
                AlertState st = states.get(k);
                if (st == null) { st = new AlertState(); states.put(k, st); }
                if (st.tb == 0) { st.tb = o.tBuy; st.ts = o.tSell; }   // primera vez que cumple
                if (!(o.tBuy > st.tb && o.tSell > st.ts)) continue;    // todavía no volvieron a cotizar los dos
                boolean cooled = nowMs - st.lastAt >= ALERT_COOLDOWN_MS;
                boolean improved = o.pPct >= st.lastPct + REALERT_STEP_PCT;
                if (cooled || improved) batch.add(o);
            }
        }
        // Una ruta que deja de cumplir pierde la confirmación acumulada
        for (Map.Entry<String, AlertState> e : states.entrySet()) {
            if (!seen.contains(e.getKey())) { e.getValue().tb = 0; e.getValue().ts = 0; }
        }
        Collections.sort(batch, BY_PROFIT);
        for (Opp o : batch) {
            AlertState st = states.get(o.key());
            st.lastAt = nowMs;
            st.lastPct = o.pPct;
        }
        return batch;
    }

    /**
     * Mejor ruta operable de cada moneda en una línea, para la notificación:
     * "USDT -0,50% · USDC -0,95% · DAI -0,86% · BTC -0,71% · ETH -1,21%".
     * "s/d" = sin cotizaciones vigentes de esa moneda; "—" = sin rutas operables.
     */
    static String coinsLine(CoinResult[] byCoin) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < COIN_IDS.length; i++) {
            if (i > 0) sb.append(" · ");
            sb.append(COIN_IDS[i].toUpperCase(Locale.US)).append(' ');
            CoinResult r = i < byCoin.length ? byCoin[i] : null;
            if (r == null || r.down) { sb.append("s/d"); continue; }
            Opp best = null;
            for (Opp o : r.opps) {                 // ya vienen ordenadas de mejor a peor
                if (o.status != ST_SUSPECT) { best = o; break; }
            }
            sb.append(best == null ? "—" : String.format("%+.2f%%", best.pPct));
        }
        return sb.toString();
    }

    // ─── Formato ───

    /** Volumen para la URL de CriptoYa: 2 cifras significativas, con punto decimal y sin exponente. */
    static String fmtVol(double v) {
        if (Double.isNaN(v) || Double.isInfinite(v) || v <= 0) v = 1;
        return new BigDecimal(v).round(new MathContext(2, RoundingMode.HALF_UP)).stripTrailingZeros().toPlainString();
    }

    static String fmtUnits(double v) {
        if (v == 0) return "0";
        return new BigDecimal(v).setScale(8, RoundingMode.HALF_UP).stripTrailingZeros().toPlainString();
    }

    static String fmtPrice(double v) {
        if (v >= 100_000_000) return String.format("$%.3fM", v / 1_000_000);
        if (v >= 1_000_000)   return String.format("$%.4fM", v / 1_000_000);
        return String.format("$%,.2f", v);
    }

    static String fmtAge(long sec) {
        if (sec < 0) sec = 0;
        if (sec < 90) return sec + " s";
        if (sec < 5400) return Math.round(sec / 60.0) + " min";
        if (sec < 172800) return Math.round(sec / 3600.0) + " h";
        return Math.round(sec / 86400.0) + " d";
    }

    static String netLabel(String net) {
        String l = NET_LABELS.get(net);
        return l != null ? l : net;
    }

    // ══════════════════════════════════════════════════════════════
    //  SERVICIO
    // ══════════════════════════════════════════════════════════════

    private PowerManager.WakeLock wakeLock;
    private ScheduledExecutorService scheduler;
    private NotificationManager notifManager;

    private double usdArs = 1550.0;

    // Capital y umbral de alerta: los fija la app. Hasta recibirlos valen los que la app trae de fábrica.
    // Los escribe el hilo principal (onStartCommand) y los lee el hilo del ciclo.
    private volatile double capital  = CAPITAL_DEFAULT;   // USD
    private volatile double alertPct = ALERT_DEFAULT;     // % neto
    private volatile String lastStatus = "Monitoreando arbitraje...";
    private volatile String lastCoins;                    // mejor ruta de cada moneda en el último ciclo

    private JSONObject fees;             // comisiones de retiro (CriptoYa /api/fees)
    private long feesAt;
    private final double[] refAsk = new double[COIN_IDS.length];   // referencia de precio por moneda para el volumen
    private final Map<String, AlertState> alertStates = new HashMap<>();

    @Override
    public void onCreate() {
        super.onCreate();
        notifManager = (NotificationManager) getSystemService(NOTIFICATION_SERVICE);
        createChannels();
        acquireWakeLock();
        // Última configuración recibida de la app: vale también si Android reinicia el servicio solo
        try {
            applyConfig(getSharedPreferences(PREFS, MODE_PRIVATE).getString(PREF_CONFIG, null), false);
        } catch (Exception e) {
            Log.w(TAG, "config guardada: " + e.getMessage());
        }
    }

    @Override
    public int onStartCommand(Intent intent, int flags, int startId) {
        // La app reenvía Capital y Alerta % cada vez que se abre o que se cambian
        if (intent != null) applyConfig(intent.getStringExtra(EXTRA_CONFIG), true);
        startForeground(NOTIF_FG_ID, buildForegroundNotif(lastStatus));
        startMonitorLoop();
        return START_STICKY; // Reinicia si Android lo mata
    }

    // ─── Configuración ───────────────────────────────────────────
    /**
     * Lee {"capital":…, "alertPct":…}. Devuelve { capital, alertPct } con NaN en el campo que falte
     * o esté fuera de los límites de la app: ese campo conserva su valor anterior.
     */
    static double[] parseConfig(String json) {
        double cap = Double.NaN, pct = Double.NaN;
        if (json != null) {
            try {
                JSONObject o = new JSONObject(json);
                double c = o.optDouble("capital", Double.NaN);
                double p = o.optDouble("alertPct", Double.NaN);
                if (c >= CAPITAL_MIN && c <= CAPITAL_MAX) cap = c;
                if (p >= ALERT_MIN && p <= ALERT_MAX) pct = p;
            } catch (Exception ignored) {
                // texto que no es JSON: no cambia nada
            }
        }
        return new double[]{cap, pct};
    }

    private void applyConfig(String json, boolean persist) {
        if (json == null) return;
        double[] c = parseConfig(json);
        if (Double.isNaN(c[0]) && Double.isNaN(c[1])) return;
        if (!Double.isNaN(c[0])) capital = c[0];
        if (!Double.isNaN(c[1])) alertPct = c[1];
        Log.d(TAG, "Configuración: " + configLine());
        if (!persist) return;
        try {
            getSharedPreferences(PREFS, MODE_PRIVATE).edit()
                .putString(PREF_CONFIG, "{\"capital\":" + capital + ",\"alertPct\":" + alertPct + "}")
                .apply();
        } catch (Exception e) {
            Log.w(TAG, "guardar config: " + e.getMessage());
        }
    }

    /** Parámetros con los que está trabajando el monitor, tal como se ven en la notificación. */
    private String configLine() {
        return "Capital U$D " + String.format("%,d", Math.round(capital))
            + " · alerta " + new DecimalFormat("0.##").format(alertPct) + "%";
    }

    @Override
    public IBinder onBind(Intent intent) { return null; }

    @Override
    public void onDestroy() {
        if (scheduler != null) scheduler.shutdown();
        if (wakeLock != null && wakeLock.isHeld()) wakeLock.release();
        super.onDestroy();
    }

    // ─── WakeLock ────────────────────────────────────────────────
    private void acquireWakeLock() {
        PowerManager pm = (PowerManager) getSystemService(POWER_SERVICE);
        wakeLock = pm.newWakeLock(PowerManager.PARTIAL_WAKE_LOCK, "ArbitrAR:BotWakeLock");
        wakeLock.acquire(); // Sin timeout — el servicio lo libera al destruirse
    }

    // ─── Canales de notificación ─────────────────────────────────
    private void createChannels() {
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
            // Canal foreground (silencioso)
            NotificationChannel fg = new NotificationChannel(
                CH_FOREGROUND, "ArbitrAR Monitor", NotificationManager.IMPORTANCE_MIN);
            fg.setSound(null, null);
            notifManager.createNotificationChannel(fg);

            // Canal alertas (sonido máximo + vibración)
            Uri alarmSound = RingtoneManager.getDefaultUri(RingtoneManager.TYPE_ALARM);
            AudioAttributes aa = new AudioAttributes.Builder()
                .setContentType(AudioAttributes.CONTENT_TYPE_SONIFICATION)
                .setUsage(AudioAttributes.USAGE_ALARM)
                .build();
            NotificationChannel alert = new NotificationChannel(
                CH_ALERT, "Alertas de Arbitraje", NotificationManager.IMPORTANCE_HIGH);
            alert.setSound(alarmSound, aa);
            alert.enableVibration(true);
            alert.setVibrationPattern(new long[]{0, 300, 100, 300, 100, 600});
            alert.enableLights(true);
            alert.setLightColor(Color.GREEN);
            alert.setLockscreenVisibility(Notification.VISIBILITY_PUBLIC);
            notifManager.createNotificationChannel(alert);
        }
    }

    private Notification buildForegroundNotif(String text) {
        Intent openApp = new Intent(this, MainActivity.class);
        PendingIntent pi = PendingIntent.getActivity(this, 0, openApp,
            PendingIntent.FLAG_IMMUTABLE | PendingIntent.FLAG_UPDATE_CURRENT);
        return new NotificationCompat.Builder(this, CH_FOREGROUND)
            .setContentTitle("ArbitrAR")
            .setContentText(text)
            // Al desplegarla: la mejor ruta de cada moneda y los parámetros con que trabaja el monitor
            .setStyle(new NotificationCompat.BigTextStyle().bigText(
                text + (lastCoins != null ? "\n" + lastCoins : "") + "\n" + configLine()))
            .setSmallIcon(android.R.drawable.ic_menu_compass)
            .setContentIntent(pi)
            .setOngoing(true)
            .build();
    }

    private void updateForegroundNotif(String text) {
        lastStatus = text;
        notifManager.notify(NOTIF_FG_ID, buildForegroundNotif(text));
    }

    // ─── Loop de monitoreo ───────────────────────────────────────
    private void startMonitorLoop() {
        if (scheduler != null && !scheduler.isShutdown()) return;
        scheduler = Executors.newSingleThreadScheduledExecutor();
        scheduler.scheduleAtFixedRate(this::runCycle, 0, CYCLE_SEC, TimeUnit.SECONDS);
        Log.d(TAG, "Loop iniciado — cada " + CYCLE_SEC + " segundos");
    }

    private void runCycle() {
        try {
            // 1. Dólar blue (convierte el capital a pesos)
            String dolarJson = httpGet("https://dolarapi.com/v1/dolares");
            if (dolarJson != null) {
                try {
                    JSONArray arr = new JSONArray(dolarJson);
                    for (int i = 0; i < arr.length(); i++) {
                        JSONObject d = arr.getJSONObject(i);
                        if ("blue".equals(d.optString("casa"))) {
                            double c = d.optDouble("compra", 0), v = d.optDouble("venta", 0);
                            if (c > 0 && v > 0) usdArs = (c + v) / 2;
                            break;
                        }
                    }
                } catch (Exception e) { Log.w(TAG, "parseDolar: " + e.getMessage()); }
            }

            // 2. Comisiones de retiro: cambian poco, se refrescan cada 10 minutos.
            //    Si el refresco falla se sigue con las últimas conocidas.
            long nowMs = System.currentTimeMillis();
            if (fees == null || nowMs - feesAt > FEES_TTL_MS) {
                String f = httpGet("https://criptoya.com/api/fees");
                if (f != null) {
                    try {
                        JSONObject o = new JSONObject(f);
                        if (o.length() > 0) { fees = o; feesAt = nowMs; }
                    } catch (Exception e) { Log.w(TAG, "parseFees: " + e.getMessage()); }
                }
            }

            // 3. Cotizaciones y rutas por moneda, con el capital y el umbral que fijó la app.
            //    Se toman una sola vez por ciclo: si la app los cambia en el medio, rigen desde el próximo.
            final double cap = capital, thr = alertPct;
            double capArs = cap * usdArs;
            long nowSec = nowMs / 1000L;
            List<CoinResult> results = new ArrayList<>();
            CoinResult[] byCoin = new CoinResult[COIN_IDS.length];
            String[] raw = new String[COIN_IDS.length];
            int feedsOk = 0;
            for (int i = 0; i < COIN_IDS.length; i++) {
                // Se pide el precio para las unidades que mueve realmente el capital
                double vol = refAsk[i] > 0 ? capArs / refAsk[i] : cap / COIN_USD_REF[i];
                raw[i] = httpGet("https://criptoya.com/api/" + COIN_IDS[i] + "/ars/" + fmtVol(vol));
                if (raw[i] == null) continue;
                JSONObject data;
                try { data = new JSONObject(raw[i]); } catch (Exception e) { continue; }
                CoinResult r = computeCoin(COIN_IDS[i], data, fees, capArs, nowSec);
                if (r.refAsk > 0) refAsk[i] = r.refAsk;
                if (!r.down) feedsOk++;
                results.add(r);
                byCoin[i] = r;
            }

            // 4. Mejor ruta operable entre todas las monedas (los datos sospechosos no cuentan)
            Opp best = null;
            int profitable = 0;
            for (CoinResult r : results) {
                for (Opp o : r.opps) {
                    if (o.status == ST_SUSPECT) continue;
                    if (best == null || o.pPct > best.pPct) best = o;
                    if (o.status == ST_OK && o.pPct >= thr) profitable++;
                }
            }
            String status;
            if (best == null) {
                status = feedsOk == 0 ? "Sin cotizaciones vigentes — reintentando..." : "Sin rutas operables por ahora";
            } else {
                String tail = String.format("%+.2f%%", best.pPct)
                    + " [" + best.coinLabel + ": " + best.buyName + "→" + best.sellName + "]";
                status = profitable > 0
                    ? "🟢 " + profitable + " oportunidad(es) — mejor: " + tail
                    : "Monitoreando — mejor: " + tail;
                if (fees == null) status += " (sin costo de red)";
            }
            lastCoins = coinsLine(byCoin);
            updateForegroundNotif(status);
            Log.d(TAG, "Ciclo OK — " + status + " | " + lastCoins);

            // 5. Alertas: una notificación por ciclo, con la mejor ruta confirmada
            List<Opp> batch = selectAlerts(results, alertStates, thr, nowMs);
            if (!batch.isEmpty()) fireAlert(batch.get(0), batch.size() - 1, nowSec, cap);

            // 6. Compatibilidad con MainActivity.injectData (dólar, USDT, DAI, BTC)
            if (MainActivity.instance != null) {
                MainActivity.instance.injectData(dolarJson, raw[0], raw[2], raw[3]);
            }

        } catch (Exception e) {
            Log.e(TAG, "Error en ciclo: " + e.getMessage());
        }
    }

    // ─── HTTP ────────────────────────────────────────────────────
    private String httpGet(String urlStr) {
        HttpURLConnection conn = null;
        try {
            URL url = new URL(urlStr);
            conn = (HttpURLConnection) url.openConnection();
            conn.setRequestMethod("GET");
            conn.setConnectTimeout(8000);
            conn.setReadTimeout(8000);
            conn.setUseCaches(false);
            conn.setRequestProperty("User-Agent", "ArbitrAR-Android/1.0");
            int code = conn.getResponseCode();
            if (code != 200) return null;
            BufferedReader br = new BufferedReader(new InputStreamReader(conn.getInputStream(), "UTF-8"));
            StringBuilder sb = new StringBuilder();
            String line;
            while ((line = br.readLine()) != null) sb.append(line);
            br.close();
            return sb.toString();
        } catch (Exception e) {
            Log.w(TAG, "httpGet(" + urlStr + "): " + e.getMessage());
            return null;
        } finally {
            if (conn != null) conn.disconnect();
        }
    }

    // ─── Alertas ─────────────────────────────────────────────────
    private void fireAlert(Opp o, int more, long nowSec, double cap) {
        String title = "🚨 ARBITRAJE — " + o.coinLabel + " " + String.format("%+.2f%%", o.pPct);
        StringBuilder sb = new StringBuilder();
        sb.append(o.coinLabel).append(": ").append(o.buyName).append(" → ").append(o.sellName).append('\n');
        sb.append("Comprar @ ").append(fmtPrice(o.askARS)).append(" · Vender @ ").append(fmtPrice(o.bidARS)).append('\n');
        sb.append("Retiro por ").append(netLabel(o.net)).append(": ").append(fmtUnits(o.fee)).append(' ').append(o.coinLabel).append('\n');
        sb.append("Ganancia: $").append(String.format("%,d", Math.round(o.pARS)))
          .append(" ARS (capital U$D ").append(String.format("%,d", Math.round(cap))).append(")\n");
        sb.append("Cotizaciones de hace ").append(fmtAge(nowSec - o.tBuy)).append(" y ").append(fmtAge(nowSec - o.tSell));
        if (more > 0) sb.append('\n').append('+').append(more).append(more > 1 ? " rutas más" : " ruta más");
        String body = sb.toString();

        // Intent para abrir la app al tocar la notificación
        Intent openApp = new Intent(this, MainActivity.class);
        openApp.setFlags(Intent.FLAG_ACTIVITY_NEW_TASK | Intent.FLAG_ACTIVITY_CLEAR_TOP);
        PendingIntent pi = PendingIntent.getActivity(this, (int) System.currentTimeMillis(),
            openApp, PendingIntent.FLAG_IMMUTABLE | PendingIntent.FLAG_UPDATE_CURRENT);

        // Intent para abrir el exchange de compra
        Intent buyIntent = new Intent(Intent.ACTION_VIEW, Uri.parse(urlOf(o.buyId)));
        PendingIntent buyPi = PendingIntent.getActivity(this, (int) System.currentTimeMillis() + 1,
            buyIntent, PendingIntent.FLAG_IMMUTABLE);

        // Intent para abrir el exchange de venta
        Intent sellIntent = new Intent(Intent.ACTION_VIEW, Uri.parse(urlOf(o.sellId)));
        PendingIntent sellPi = PendingIntent.getActivity(this, (int) System.currentTimeMillis() + 2,
            sellIntent, PendingIntent.FLAG_IMMUTABLE);

        Uri alarmSound = RingtoneManager.getDefaultUri(RingtoneManager.TYPE_ALARM);

        NotificationCompat.Builder nb = new NotificationCompat.Builder(this, CH_ALERT)
            .setContentTitle(title)
            .setContentText(body)
            .setStyle(new NotificationCompat.BigTextStyle().bigText(body))
            .setSmallIcon(android.R.drawable.ic_dialog_alert)
            .setContentIntent(pi)
            .setAutoCancel(false)
            .setPriority(NotificationCompat.PRIORITY_MAX)
            .setCategory(NotificationCompat.CATEGORY_ALARM)
            .setVisibility(NotificationCompat.VISIBILITY_PUBLIC)
            .setSound(alarmSound)
            .setVibrate(new long[]{0, 300, 100, 300, 100, 600})
            .setLights(Color.GREEN, 500, 500)
            .addAction(android.R.drawable.ic_media_play, "🟢 Comprar", buyPi)
            .addAction(android.R.drawable.ic_media_pause, "🔴 Vender", sellPi);

        int notifId = NOTIF_ALERT_BASE + Math.abs(o.key().hashCode() % 50);
        notifManager.notify(notifId, nb.build());
        Log.d(TAG, "ALERTA: " + title + " — " + o.buyName + " → " + o.sellName);
    }

    private static String urlOf(String exId) {
        String u = EX_URLS.get(exId);
        return u != null ? u : "https://criptoya.com";
    }
}
