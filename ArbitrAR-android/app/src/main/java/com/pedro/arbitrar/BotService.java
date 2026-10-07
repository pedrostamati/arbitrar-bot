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
import java.io.File;
import java.io.FileOutputStream;
import java.io.InputStreamReader;
import java.math.BigDecimal;
import java.math.MathContext;
import java.math.RoundingMode;
import java.net.HttpURLConnection;
import java.net.URL;
import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.Executors;
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.TimeUnit;

/**
 * Monitor en segundo plano. Aplica las mismas reglas que arbitraje.html (motor v7):
 *
 *  1. Vigencia: cada cotización de CriptoYa trae su propio `time`. Una cotización que no se
 *     actualiza queda fuera del cálculo, aunque la API la siga devolviendo.
 *  2. Precio por unidad: CriptoYa cotiza siempre por 1 unidad. El número de la URL es el
 *     volumen a operar (define el precio en exchanges con libro de órdenes).
 *  3. Transferencia real: el retiro se descuenta con la comisión que informa CriptoYa por
 *     exchange y por red; sin red en común no hay ruta. Entre dos plazas de la misma
 *     plataforma el paso es interno y sin costo.
 *  4. Confirmación: la alerta exige que la ganancia siga ahí después de que los dos
 *     exchanges de la ruta volvieron a cotizar.
 *  5. Mis exchanges: solo cuentan las rutas entre los exchanges que el usuario dejó activos.
 *
 * La configuración es la de la app: MainActivity la reenvía en el Intent de inicio (EXTRA_CONFIG)
 * cada vez que se abre o que el usuario cambia algo, y queda guardada.
 *
 * Además graba el historial: una muestra por minuto de la mejor ruta neta de cada moneda, en
 * archivos diarios dentro de la carpeta privada de la app. La interfaz los lee por el puente.
 */
public class BotService extends Service {

    private static final String TAG = "ArbitrARBot";
    private static final String CH_FOREGROUND = "arbitrar_fg";
    private static final String CH_ALERT      = "arbitrar_alert";
    private static final int    NOTIF_FG_ID   = 1;
    private static final int    NOTIF_ALERT_BASE = 100;

    // ─── Parámetros del motor: los mismos que CFG en arbitraje.html ───
    static final long   STALE_SEC             = 180;      // antigüedad máxima de una cotización contra la más nueva de la respuesta
    static final long   FEED_LAG_SEC          = 180;      // atraso máximo de toda la respuesta contra el reloj
    static final double MAX_PLAUSIBLE_PCT     = 5.0;      // ganancia neta superior = dato sospechoso, no alerta
    static final double MAX_PLAUSIBLE_P2P_PCT = 2.0;      // el mismo tope, más estricto, si alguna punta es un anuncio P2P
    static final int    MKT_MIN_VENUES        = 3;        // exchanges vigentes necesarios para hablar de "precio de mercado"
    static final long   ALERT_COOLDOWN_MS     = 300_000L; // no repetir la alerta de una ruta antes de 5 minutos…
    static final double REALERT_STEP_PCT      = 0.5;      // …salvo que mejore al menos este margen
    static final long   FEES_TTL_MS           = 600_000L; // refresco de comisiones de retiro
    static final long   CYCLE_SEC             = 15;
    static final String HUB                   = "binance"; // dónde se convierte una stablecoin en otra en las rutas cruzadas
    static final double SWAP_FEE_PCT          = 0.1;      // comisión supuesta por cada conversión en el hub
    static final long   HUB_TTL_MS            = 60_000L;  // vigencia del precio de conversión si falla una consulta
    static final long   HUB_RETRY_MS          = 60_000L;  // espera antes de volver a pedir un par que no respondió
    static final int    CROSS_KEEP            = 60;       // rutas cruzadas que se conservan (las mejores)

    // ─── Configuración que fija la app ───
    // MainActivity la reenvía como JSON: {"capital":1000,"alertPct":0.5,"mode":"transfer","p2p":false,"cross":true,"off":["belo"]}
    static final String EXTRA_CONFIG    = "arbitrar.config";
    private static final String PREFS       = "arbitrar_bot";
    private static final String PREF_CONFIG = "config";
    static final double CAPITAL_DEFAULT = 1000, CAPITAL_MIN = 10,  CAPITAL_MAX = 999999;   // mismos límites que el campo de la app
    static final double ALERT_DEFAULT   = 0.5,  ALERT_MIN   = 0.1, ALERT_MAX   = 20;

    // ─── Monedas ───
    static final String[] COIN_IDS     = {"usdt", "usdc", "dai", "btc", "eth"};
    static final double[] COIN_USD_REF = {1, 1, 1, 90000, 3000};   // solo para el volumen de la primera consulta
    static final int[]    STABLES      = {0, 1, 2};                // índices de COIN_IDS que entran en las rutas cruzadas
    static final String   XID          = "x";                      // "moneda" de las rutas cruzadas
    static final String[] TAB_LABELS   = {"USDT", "USDC", "DAI", "BTC", "ETH", "CRUZ"};

    // ─── Exchanges ───
    // Mismo orden y mismos datos que la tabla EX de arbitraje.html.
    //   keys:    claves posibles en CriptoYa para los precios, en orden de preferencia
    //   feeKeys: claves para las comisiones de retiro
    //   grp:     plataforma; dos plazas de la misma plataforma se pasan la moneda sin red y sin costo
    //   p2p:     la cotización es un anuncio entre personas, no un precio del exchange
    static final class Venue {
        final String id, name, grp, url;
        final boolean p2p;
        final String[] keys, feeKeys;
        Venue(String id, String name, String grp, boolean p2p, String url, String[] keys, String[] feeKeys) {
            this.id = id; this.name = name; this.grp = grp; this.p2p = p2p; this.url = url;
            this.keys = keys; this.feeKeys = feeKeys != null ? feeKeys : keys;
        }
    }

    private static Venue ex(String id, String name, String url, String... keys) {
        return new Venue(id, name, id, false, url, keys, null);
    }

    private static Venue p2p(String id, String name, String grp, String url, String key, String... feeKeys) {
        return new Venue(id, name, grp != null ? grp : id, true, url, new String[]{key}, feeKeys.length > 0 ? feeKeys : null);
    }

    static final Venue[] VENUES = {
        ex("nexo",           "Nexo",            "https://nexo.com",                 "nexo"),
        ex("letsbit",        "LetsBit",         "https://letsbit.io",               "letsbit"),
        ex("ripio",          "Ripio",           "https://exchange.ripio.com",       "ripio"),
        ex("ripiotrade",     "Ripio Trade",     "https://www.ripio.com",            "ripioexchange"),
        ex("satoshitango",   "SatoshiTango",    "https://satoshitango.com",         "satoshitango"),
        ex("lemon",          "Lemon Cash",      "https://lemon.me",                 "lemoncash"),
        ex("fiwind",         "Fiwind",          "https://fiwind.io",                "fiwind"),
        ex("astropay",       "AstroPay",        "https://astropay.com/wallet/exchange", "astropay"),
        ex("belo",           "Belo",            "https://belo.app",                 "belo"),
        ex("tiendacrypto",   "TiendaCrypto",    "https://tiendacrypto.com",         "tiendacrypto"),
        ex("cryptomkt",      "CryptoMKT",       "https://cryptomkt.com",            "cryptomktpro", "cryptomkt"),
        ex("decrypto",       "Decrypto",        "https://decrypto.com",             "decrypto"),
        ex("cocoscrypto",    "Cocos Crypto",    "https://cocos.ar",                 "cocoscrypto"),
        ex("bybit",          "Bybit",           "https://www.bybit.com",            "bybit"),
        ex("binance",        "Binance",         "https://www.binance.com/es/trade/USDT_ARS?type=spot", "binance"),
        ex("universalcoins", "Universal Coins", "https://universalcoins.net",       "universalcoins"),
        ex("vitawallet",     "Vita Wallet",     "https://vitawallet.io",            "vitawallet"),
        ex("saldo",          "Saldo.com.ar",    "https://saldo.com.ar",             "saldo"),
        ex("eluter",         "Eluter",          "https://eluter.com",               "eluter"),
        ex("bitso",          "Bitso",           "https://bitso.com",                "bitsoalpha", "bitso"),
        ex("mexc",           "MEXC",            "https://www.mexc.com",             "mexc"),
        ex("takenos",        "Takenos",         "https://takenos.com",              "takenos"),
        ex("wallbit",        "Wallbit",         "https://wallbit.io",               "wallbit"),
        ex("peanut",         "Peanut",          "https://peanut.me",                "peanut"),
        ex("dolarapp",       "DolarApp",        "https://www.dolarapp.com",         "dolarapp"),
        ex("vibrant",        "Vesseo (ex Vibrant)", "https://www.vesseoapp.com",    "vibrant"),
        ex("airtm",          "Airtm",           "https://www.airtm.com",            "airtm"),
        // Anuncios entre personas (P2P): entran solo si el usuario los activa
        p2p("binancep2p",    "Binance P2P",     "binance", "https://p2p.binance.com", "binancep2p", "binancep2p", "binance"),
        p2p("bybitp2p",      "Bybit P2P",       "bybit",   "https://www.bybit.com",   "bybitp2p",   "bybitp2p", "bybit"),
        p2p("okxp2p",        "OKX P2P",         null,      "https://www.okx.com",     "okexp2p"),
        p2p("bitgetp2p",     "Bitget P2P",      null,      "https://www.bitget.com",  "bitgetp2p",  "bitgetp2p", "bitget"),
        p2p("kucoinp2p",     "KuCoin P2P",      null,      "https://www.kucoin.com",  "kucoinp2p",  "kucoinp2p", "kucoin"),
        p2p("htxp2p",        "HTX P2P",         null,      "https://www.htx.com",     "huobip2p"),
        p2p("bingxp2p",      "BingX P2P",       null,      "https://bingx.com",       "bingxp2p"),
        p2p("mexcp2p",       "MEXC P2P",        "mexc",    "https://www.mexc.com",    "mexcp2p",    "mexcp2p", "mexc"),
        p2p("weexp2p",       "WEEX P2P",        null,      "https://www.weex.com",    "weexp2p"),
        p2p("eldorado",      "El Dorado",       null,      "https://eldorado.io",     "eldoradop2p"),
        p2p("lemonp2p",      "Lemon P2P",       "lemon",   "https://lemon.me",        "lemoncashp2p", "lemoncashp2p", "lemoncash"),
        p2p("p2pme",         "P2P.me",          null,      "https://p2p.me",          "p2pme"),
    };

    private static final Map<String, Venue> VENUE_BY_ID = new HashMap<>();
    static {
        for (Venue v : VENUES) VENUE_BY_ID.put(v.id, v);
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
        NET_LABELS.put("TON", "TON");
        NET_LABELS.put("APTOS", "Aptos");
        NET_LABELS.put("PLASMA", "Plasma");
        NET_LABELS.put("STELLAR", "Stellar");
        NET_LABELS.put("ALGORAND", "Algorand");
        NET_LABELS.put("SUI", "Sui");
        NET_LABELS.put("SONIC", "Sonic");
        NET_LABELS.put("LACHAIN", "LaChain");
    }

    // ══════════════════════════════════════════════════════════════
    //  CONFIGURACIÓN (inmutable: cada cambio crea una nueva)
    // ══════════════════════════════════════════════════════════════

    static final class Config {
        final double capital, alertPct;
        final boolean both;        // dos puntas: mismas cuentas, cambia el texto de la alerta
        final boolean p2p, cross;
        final Set<String> off;     // exchanges desactivados en "Mis exchanges"

        Config(double capital, double alertPct, boolean both, boolean p2p, boolean cross, Set<String> off) {
            this.capital = capital; this.alertPct = alertPct; this.both = both; this.p2p = p2p; this.cross = cross;
            this.off = Collections.unmodifiableSet(new TreeSet<>(off));
        }

        static Config defaults() {
            return new Config(CAPITAL_DEFAULT, ALERT_DEFAULT, false, false, true, new HashSet<String>());
        }

        boolean venueOn(Venue v) { return p2p || !v.p2p; }
        boolean active(Venue v)  { return !off.contains(v.id); }

        String toJson() {
            StringBuilder sb = new StringBuilder();
            sb.append("{\"capital\":").append(fmtNum(capital)).append(",\"alertPct\":").append(fmtNum(alertPct))
              .append(",\"mode\":\"").append(both ? "both" : "transfer").append("\",\"p2p\":").append(p2p)
              .append(",\"cross\":").append(cross).append(",\"off\":[");
            boolean first = true;
            for (String id : off) {
                if (!first) sb.append(',');
                sb.append('"').append(id).append('"');
                first = false;
            }
            return sb.append("]}").toString();
        }

        /** Firma de lo que cambia los valores del historial. El umbral de alerta no entra: no altera la serie. */
        String signature() {
            int h = 5381;
            String joined = join(off);
            for (int i = 0; i < joined.length(); i++) h = ((h << 5) + h + joined.charAt(i)) & 0xffff;
            return fmtNum(capital) + "," + (both ? "b" : "t") + "," + (p2p ? 1 : 0) + "," + (cross ? 1 : 0) + ","
                + off.size() + "," + Integer.toHexString(h);
        }

        private static String join(Set<String> ids) {
            StringBuilder sb = new StringBuilder();
            for (String id : ids) {
                if (sb.length() > 0) sb.append(',');
                sb.append(id);
            }
            return sb.toString();
        }
    }

    /**
     * Aplica sobre `base` lo que traiga el JSON. Cada campo ausente o fuera de los límites de la app
     * conserva su valor anterior. Devuelve null si el texto no es un JSON de configuración.
     */
    static Config parseConfig(String json, Config base) {
        if (json == null) return null;
        try {
            JSONObject o = new JSONObject(json);
            double cap = base.capital, pct = base.alertPct;
            boolean both = base.both, p2p = base.p2p, cross = base.cross;
            Set<String> off = new HashSet<>(base.off);
            boolean any = false;
            double c = o.optDouble("capital", Double.NaN);
            if (c >= CAPITAL_MIN && c <= CAPITAL_MAX) { cap = c; any = true; }
            double p = o.optDouble("alertPct", Double.NaN);
            if (p >= ALERT_MIN && p <= ALERT_MAX) { pct = p; any = true; }
            String mode = o.optString("mode", "");
            if ("both".equals(mode)) { both = true; any = true; }
            else if ("transfer".equals(mode)) { both = false; any = true; }
            if (o.has("p2p"))   { p2p = o.optBoolean("p2p", p2p); any = true; }
            if (o.has("cross")) { cross = o.optBoolean("cross", cross); any = true; }
            JSONArray arr = o.optJSONArray("off");
            if (arr != null) {
                off.clear();
                for (int i = 0; i < arr.length(); i++) {
                    String id = arr.optString(i, "");
                    if (VENUE_BY_ID.containsKey(id)) off.add(id);      // solo exchanges que el motor conoce
                }
                any = true;
            }
            return any ? new Config(cap, pct, both, p2p, cross, off) : null;
        } catch (Exception ignored) {
            return null;   // texto que no es JSON: no cambia nada
        }
    }

    // ══════════════════════════════════════════════════════════════
    //  MOTOR (estático y sin Android: se prueba fuera del teléfono)
    // ══════════════════════════════════════════════════════════════

    static final int ST_OK = 0, ST_SUSPECT = 1, ST_NOFEE = 2;

    static final class Quote {
        final double bid, ask;     // 0 = esa punta no está publicada (solo pasa en P2P)
        final long t;
        Quote(double bid, double ask, long t) { this.bid = bid; this.ask = ask; this.t = t; }
    }

    static final class Net {
        final String name;
        final double fee;
        final boolean internal, nofee;
        Net(String name, double fee, boolean internal, boolean nofee) {
            this.name = name; this.fee = fee; this.internal = internal; this.nofee = nofee;
        }
    }

    private static final Net NET_INTERNAL = new Net("INTERNAL", 0, true, false);
    private static final Net NET_NOFEE    = new Net(null, 0, false, true);

    static final class Opp {
        String coinId;             // moneda, o XID en una ruta cruzada
        String xb, xs;             // ruta cruzada: stablecoin que se compra y stablecoin que se vende
        Venue buy, sell;
        Net net, net2;             // retiro (y segundo retiro de la ruta cruzada); null = sin datos de comisiones
        double convRaw;            // ruta cruzada: precio de conversión en el hub, antes de comisión
        double pPct, pARS, grossPct, askARS, bidARS;
        long tBuy, tSell;          // hora de cada cotización (segundos unix)
        int status;
        boolean p2p;

        String key() {
            return XID.equals(coinId) ? "x|" + xb + "@" + buy.id + ">" + xs + "@" + sell.id
                                      : coinId + "|" + buy.id + "|" + sell.id;
        }
        String label() { return XID.equals(coinId) ? "CRUZ" : coinId.toUpperCase(Locale.US); }
    }

    /** Cotizaciones vigentes de una moneda, ya filtradas, en el orden de VENUES. */
    static final class CoinData {
        final String coinId, sym;
        final LinkedHashMap<String, Quote> quotes = new LinkedHashMap<>();
        long refT;                 // cotización más nueva de la respuesta
        boolean down = true;       // la respuesta entera está atrasada o no trae `time`
        int stale, bad;
        double refAsk;             // mediana de precios de compra vigentes (para pedir el volumen)
        double mktAsk, mktBid;     // medianas del mercado; 0 si no hay suficientes exchanges
        CoinData(String coinId) { this.coinId = coinId; this.sym = coinId.toUpperCase(Locale.US); }
    }

    static final class CoinResult {
        final List<Opp> opps = new ArrayList<>();
        boolean down;
        int noNet;
        Opp bestOk() {             // la mejor con retiro costeado: es la que va al historial
            for (Opp o : opps) if (o.status == ST_OK) return o;
            return null;
        }
        Opp best() {               // la mejor operable (los datos sospechosos no cuentan)
            for (Opp o : opps) if (o.status != ST_SUSPECT) return o;
            return null;
        }
    }

    static final class HubBook {
        double usdcBid, usdcAsk;   // USDCUSDT
        double daiBid, daiAsk;     // USDTDAI
        long usdcAt, daiAt;        // cuándo se leyó cada uno (ms); 0 = nunca
    }

    static final class AlertState {
        long tb, ts;               // cotizaciones que originaron la ruta (0 = todavía no cumple)
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

    private static double fin(double v) {
        return (Double.isNaN(v) || Double.isInfinite(v)) ? 0 : v;
    }

    static double median(List<Double> values) {
        if (values.isEmpty()) return 0;
        List<Double> s = new ArrayList<>(values);
        Collections.sort(s);
        int m = s.size() / 2;
        return s.size() % 2 == 1 ? s.get(m) : (s.get(m - 1) + s.get(m)) / 2;
    }

    /** Lee la respuesta de CriptoYa de una moneda y deja solo las cotizaciones que entran al cálculo. */
    static CoinData parseCoin(String coinId, JSONObject data, long nowSec) {
        CoinData cd = new CoinData(coinId);

        // "Ahora" según CriptoYa: la cotización más nueva de toda la respuesta
        long refT = 0;
        Iterator<String> it = data.keys();
        while (it.hasNext()) {
            JSONObject e = data.optJSONObject(it.next());
            if (e == null) continue;
            long t = e.optLong("time", 0);
            if (t > refT) refT = t;
        }
        cd.refT = refT;
        if (refT == 0 || nowSec - refT > FEED_LAG_SEC) return cd;
        cd.down = false;

        List<Double> asks = new ArrayList<>(), bids = new ArrayList<>();
        for (Venue v : VENUES) {
            JSONObject e = null;
            for (int i = 0; i < v.keys.length && e == null; i++) e = data.optJSONObject(v.keys[i]);
            if (e == null) continue;                               // ese exchange no cotiza esta moneda
            double ask = fin(e.optDouble("totalAsk", 0));          // totalAsk/totalBid ya incluyen la comisión de trading
            if (ask == 0) ask = fin(e.optDouble("ask", 0));
            double bid = fin(e.optDouble("totalBid", 0));
            if (bid == 0) bid = fin(e.optDouble("bid", 0));
            boolean hasAsk = ask > 0, hasBid = bid > 0;
            if (!hasAsk && !hasBid) continue;
            long t = e.optLong("time", 0);
            // Un exchange publica las dos puntas y la venta nunca supera a la compra. En P2P cada punta es un
            // anuncio distinto: puede faltar una o venir cruzadas, y la plaza sirve igual para la que tenga.
            if (!v.p2p && (!hasAsk || !hasBid || bid > ask)) { cd.bad++; continue; }
            if (t == 0 || refT - t > STALE_SEC) { cd.stale++; continue; }          // dejó de actualizar
            cd.quotes.put(v.id, new Quote(hasBid ? bid : 0, hasAsk ? ask : 0, t));
            if (!v.p2p) { asks.add(ask); bids.add(bid); }          // la referencia de mercado no mira anuncios P2P
        }
        cd.refAsk = median(asks);
        if (asks.size() >= MKT_MIN_VENUES) { cd.mktAsk = cd.refAsk; cd.mktBid = median(bids); }
        return cd;
    }

    /** Comisiones de retiro de un exchange para una moneda: { RED: { withdraw, time } }. */
    static JSONObject feeMap(JSONObject fees, Venue v, String sym) {
        if (fees == null) return null;
        for (String k : v.feeKeys) {
            JSONObject e = fees.optJSONObject(k);
            if (e == null) continue;
            JSONObject m = e.optJSONObject(sym);
            if (m != null && m.length() > 0) return m;
        }
        return null;
    }

    private static double feeOf(JSONObject m, String net) {
        if (m.isNull(net)) return -1;                              // sin dato no es lo mismo que gratis
        JSONObject o = m.optJSONObject(net);
        double f = o != null ? (o.isNull("withdraw") ? Double.NaN : o.optDouble("withdraw", Double.NaN))
                             : m.optDouble(net, Double.NaN);
        return (Double.isNaN(f) || Double.isInfinite(f) || f < 0) ? -1 : f;
    }

    /**
     * Cómo pasa la moneda de una plaza a otra: interno si son de la misma plataforma; si no, la red más
     * barata en común. null = no comparten red; NET_NOFEE = todavía no hay datos de comisiones.
     */
    static Net hop(JSONObject fees, Venue from, Venue to, String sym) {
        if (from.grp.equals(to.grp)) return NET_INTERNAL;
        if (fees == null) return NET_NOFEE;
        JSONObject a = feeMap(fees, from, sym), b = feeMap(fees, to, sym);
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
        return best == null ? null : new Net(best, bestFee, false, false);
    }

    private static double plausibleCap(Venue a, Venue b) {
        return (a.p2p || b.p2p) ? MAX_PLAUSIBLE_P2P_PCT : MAX_PLAUSIBLE_PCT;
    }

    /**
     * Una cotización es sospechosa por sí sola cuando operar contra el precio típico del mercado ya daría
     * más que el tope: comprar ahí y vender a la mediana, o comprar a la mediana y vender ahí.
     */
    private static boolean quoteSuspect(CoinData cd, Venue v, Quote q, boolean buy) {
        if (!(cd.mktAsk > 0) || !(cd.mktBid > 0)) return false;
        double cap = v.p2p ? MAX_PLAUSIBLE_P2P_PCT : MAX_PLAUSIBLE_PCT;
        return buy ? (cd.mktBid / q.ask - 1) * 100 > cap : (q.bid / cd.mktAsk - 1) * 100 > cap;
    }

    /** Plazas de una moneda con cotización vigente que entran al cálculo, en el orden de VENUES. */
    private static List<Venue> liveVenues(CoinData cd, Config cfg) {
        List<Venue> out = new ArrayList<>();
        for (Venue v : VENUES) if (cd.quotes.containsKey(v.id) && cfg.venueOn(v)) out.add(v);
        return out;
    }

    /**
     * Rutas de una moneda entre los exchanges activos: comprar en uno, pasar la moneda al otro y venderla.
     * En dos puntas la cuenta es la misma: el retiro pasa a ser el costo de reequilibrar los saldos.
     * @param fees   respuesta de /api/fees, o null si todavía no se pudo obtener
     * @param capArs capital en pesos
     */
    static CoinResult computeCoin(CoinData cd, JSONObject fees, double capArs, Config cfg) {
        CoinResult res = new CoinResult();
        res.down = cd.down;
        if (cd.down) return res;
        List<Venue> ids = liveVenues(cd, cfg);
        for (Venue buy : ids) {
            Quote qb = cd.quotes.get(buy.id);
            if (!(qb.ask > 0) || !cfg.active(buy)) continue;
            for (Venue sell : ids) {
                if (buy == sell) continue;
                Quote qs = cd.quotes.get(sell.id);
                if (!(qs.bid > 0) || !cfg.active(sell)) continue;

                Net h = hop(fees, buy, sell, cd.sym);
                if (h == null) { res.noNet++; continue; }          // no hay cómo llevar la moneda de un exchange al otro
                int status = h.nofee ? ST_NOFEE : ST_OK;           // sin comisiones no se puede costear el retiro

                double unitsBought = capArs / qb.ask;
                double unitsNet = unitsBought - h.fee;
                if (unitsNet <= 0) continue;
                double pARS = unitsNet * qs.bid - capArs;
                double pPct = (pARS / capArs) * 100;
                if (status == ST_OK && (pPct > plausibleCap(buy, sell)
                        || quoteSuspect(cd, buy, qb, true) || quoteSuspect(cd, sell, qs, false))) status = ST_SUSPECT;

                Opp o = new Opp();
                o.coinId = cd.coinId;
                o.buy = buy;        o.sell = sell;
                o.net = h.nofee ? null : h;
                o.pPct = pPct;      o.pARS = pARS;
                o.grossPct = (qs.bid / qb.ask - 1) * 100;
                o.askARS = qb.ask;  o.bidARS = qs.bid;
                o.tBuy = qb.t;      o.tSell = qs.t;
                o.status = status;
                o.p2p = buy.p2p || sell.p2p;
                res.opps.add(o);
            }
        }
        Collections.sort(res.opps, BY_RANK);
        return res;
    }

    private static boolean fresh(long at, long nowMs) {
        return at > 0 && nowMs - at <= HUB_TTL_MS;
    }

    /**
     * Cuánto de `to` queda por cada unidad de `from` convertida en el hub: { con comisión, sin comisión }.
     * null si no hay precio vigente para esa conversión.
     */
    static double[] convRate(String from, String to, HubBook hub, long nowMs) {
        boolean cu = hub != null && fresh(hub.usdcAt, nowMs), ud = hub != null && fresh(hub.daiAt, nowMs);
        double k = 1 - SWAP_FEE_PCT / 100;
        double direct = leg(from, to, hub, cu, ud);
        if (direct > 0) return new double[]{direct * k, direct};
        if (!"usdt".equals(from) && !"usdt".equals(to)) {          // USDC ↔ DAI pasa por USDT
            double a = leg(from, "usdt", hub, cu, ud), b = leg("usdt", to, hub, cu, ud);
            if (a > 0 && b > 0) return new double[]{a * k * b * k, a * b};
        }
        return null;
    }

    private static double leg(String a, String b, HubBook hub, boolean cu, boolean ud) {
        if ("usdc".equals(a) && "usdt".equals(b)) return cu ? hub.usdcBid : 0;        // vender USDC por USDT
        if ("usdt".equals(a) && "usdc".equals(b)) return cu ? 1 / hub.usdcAsk : 0;    // comprar USDC con USDT
        if ("usdt".equals(a) && "dai".equals(b))  return ud ? hub.daiBid : 0;         // vender USDT por DAI
        if ("dai".equals(a)  && "usdt".equals(b)) return ud ? 1 / hub.daiAsk : 0;     // comprar USDT con DAI
        return 0;
    }

    /**
     * Rutas cruzadas entre stablecoins: comprar una donde está barata, convertirla en el hub y vender la
     * otra donde se paga más. Dos retiros como máximo: hacia el hub y desde el hub.
     * @param coins datos de las monedas en el orden de COIN_IDS (null = sin respuesta en este ciclo)
     */
    static CoinResult computeCross(CoinData[] coins, JSONObject fees, double capArs, Config cfg, HubBook hub, long nowMs) {
        CoinResult res = new CoinResult();
        Venue hubV = VENUE_BY_ID.get(HUB);
        if (!cfg.cross || !cfg.active(hubV)) return res;           // sin el hub entre mis exchanges no hay rutas propias
        for (int ib : STABLES) for (int is : STABLES) {
            if (ib == is) continue;
            CoinData cb = coins[ib], cs = coins[is];
            if (cb == null || cs == null || cb.down || cs.down) continue;
            double[] conv = convRate(cb.coinId, cs.coinId, hub, nowMs);
            if (conv == null) continue;
            List<Venue> sells = liveVenues(cs, cfg);
            for (Venue buy : liveVenues(cb, cfg)) {
                Quote qb = cb.quotes.get(buy.id);
                if (!(qb.ask > 0) || !cfg.active(buy)) continue;
                for (Venue sell : sells) {
                    Quote qs = cs.quotes.get(sell.id);
                    if (!(qs.bid > 0) || !cfg.active(sell)) continue;
                    if (buy == hubV && sell == hubV) continue;     // todo en el libro del hub: es un triángulo, no una ruta
                    Net h1 = hop(fees, buy, hubV, cb.sym), h2 = hop(fees, hubV, sell, cs.sym);
                    if (h1 == null || h2 == null) { res.noNet++; continue; }
                    int status = (h1.nofee || h2.nofee) ? ST_NOFEE : ST_OK;

                    double unitsBought = capArs / qb.ask;
                    double unitsHub = unitsBought - h1.fee;
                    if (unitsHub <= 0) continue;
                    double unitsConv = unitsHub * conv[0];
                    double unitsNet = unitsConv - h2.fee;
                    if (unitsNet <= 0) continue;
                    double pARS = unitsNet * qs.bid - capArs;
                    double pPct = (pARS / capArs) * 100;
                    if (status == ST_OK && (pPct > plausibleCap(buy, sell)
                            || quoteSuspect(cb, buy, qb, true) || quoteSuspect(cs, sell, qs, false))) status = ST_SUSPECT;

                    Opp o = new Opp();
                    o.coinId = XID;
                    o.xb = cb.coinId;   o.xs = cs.coinId;
                    o.buy = buy;        o.sell = sell;
                    o.net = h1.nofee ? null : h1;
                    o.net2 = h2.nofee ? null : h2;
                    o.convRaw = conv[1];
                    o.pPct = pPct;      o.pARS = pARS;
                    o.grossPct = (qs.bid * conv[1] / qb.ask - 1) * 100;
                    o.askARS = qb.ask;  o.bidARS = qs.bid;
                    o.tBuy = qb.t;      o.tSell = qs.t;
                    o.status = status;
                    o.p2p = buy.p2p || sell.p2p;
                    res.opps.add(o);
                }
            }
        }
        Collections.sort(res.opps, BY_RANK);
        if (res.opps.size() > CROSS_KEEP) {                        // las combinaciones son miles: se conservan las mejores
            List<Opp> top = new ArrayList<>(res.opps.subList(0, CROSS_KEEP));
            res.opps.clear();
            res.opps.addAll(top);
        }
        return res;
    }

    /**
     * Rutas que corresponde alertar en este ciclo, de mayor a menor ganancia. Solo rutas operables
     * cuya ganancia sigue ahí después de que los dos exchanges volvieron a cotizar (un dato suelto
     * no alcanza), y respetando la pausa entre repeticiones.
     * @param results resultados por pestaña, en orden: las cinco monedas y las rutas cruzadas
     */
    static List<Opp> selectAlerts(List<CoinResult> results, Map<String, AlertState> states,
                                  double alertPct, long nowMs) {
        List<Opp> batch = new ArrayList<>();
        Set<String> seen = new HashSet<>();
        for (CoinResult r : results) {
            if (r == null) continue;
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
     * "USDT -0,30% · USDC -0,91% · DAI -0,86% · BTC -0,71% · ETH -1,21% · CRUZ -0,54%".
     * "s/d" = sin cotizaciones vigentes de esa moneda; "—" = sin rutas operables.
     * @param byTab las cinco monedas y, al final, las rutas cruzadas (null = no se calcularon)
     */
    static String coinsLine(CoinResult[] byTab) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < TAB_LABELS.length; i++) {
            CoinResult r = i < byTab.length ? byTab[i] : null;
            if (i >= COIN_IDS.length && r == null) continue;       // rutas cruzadas apagadas: no se nombran
            if (sb.length() > 0) sb.append(" · ");
            sb.append(TAB_LABELS[i]).append(' ');
            if (r == null || r.down) { sb.append("s/d"); continue; }
            Opp best = r.best();
            sb.append(best == null ? "—" : fmtPct(best.pPct));
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

    /** Número sin ceros de más y siempre con punto: para JSON y para la firma del historial. */
    static String fmtNum(double v) {
        if (Double.isNaN(v) || Double.isInfinite(v)) return "0";
        return new BigDecimal(v).setScale(6, RoundingMode.HALF_UP).stripTrailingZeros().toPlainString();
    }

    /** Porcentaje con signo; lo que redondea a cero va sin signo. */
    static String fmtPct(double v) {
        return Math.abs(v) < 0.005 ? String.format("%.2f%%", 0.0) : String.format("%+.2f%%", v);
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

    /** Texto de la alerta: qué hacer, con qué precios y cuánto deja. */
    static String alertBody(Opp o, Config cfg, int more, long nowSec) {
        boolean cross = XID.equals(o.coinId);
        String cb = cross ? o.xb.toUpperCase(Locale.US) : o.label();
        String cs = cross ? o.xs.toUpperCase(Locale.US) : o.label();
        StringBuilder sb = new StringBuilder();
        if (cross) {
            sb.append("CRUZ: ").append(cb).append(" en ").append(o.buy.name).append(" → ").append(cs).append(" en ").append(o.sell.name).append('\n');
            sb.append("Comprar ").append(cb).append(" @ ").append(fmtPrice(o.askARS)).append(" · convertir en ")
              .append(VENUE_BY_ID.get(HUB).name).append(" a ").append(String.format("%.4f", o.convRaw))
              .append(" · vender ").append(cs).append(" @ ").append(fmtPrice(o.bidARS)).append('\n');
            sb.append(moveLine("Retiro 1", o.net, cb)).append(" · ").append(moveLine("retiro 2", o.net2, cs)).append('\n');
        } else {
            sb.append(o.label()).append(": ").append(o.buy.name).append(" → ").append(o.sell.name).append('\n');
            if (cfg.both) {
                sb.append("A la vez: comprar @ ").append(fmtPrice(o.askARS)).append(" y vender @ ").append(fmtPrice(o.bidARS)).append('\n');
                sb.append(o.net != null && o.net.internal ? "Misma plataforma: el saldo se reacomoda sin costo"
                                                          : moveLine("Reequilibrar después", o.net, cb)).append('\n');
            } else {
                sb.append("Comprar @ ").append(fmtPrice(o.askARS)).append(" · Vender @ ").append(fmtPrice(o.bidARS)).append('\n');
                sb.append(moveLine("Retiro", o.net, cb)).append('\n');
            }
        }
        sb.append("Ganancia: $").append(String.format("%,d", Math.round(o.pARS)))
          .append(" ARS (capital U$D ").append(String.format("%,d", Math.round(cfg.capital))).append(")\n");
        sb.append("Cotizaciones de hace ").append(fmtAge(nowSec - o.tBuy)).append(" y ").append(fmtAge(nowSec - o.tSell));
        if (o.p2p) sb.append("\nAnuncio P2P: verificá límites y medio de pago");
        if (more > 0) sb.append('\n').append('+').append(more).append(more > 1 ? " rutas más" : " ruta más");
        return sb.toString();
    }

    private static String moveLine(String what, Net net, String unit) {
        if (net == null) return what + " sin costear";
        if (net.internal) return what + ": paso interno, sin costo";
        return what + " por " + netLabel(net.name) + ": " + fmtUnits(net.fee) + " " + unit;
    }

    // ══════════════════════════════════════════════════════════════
    //  HISTORIAL
    //  Una muestra por minuto (la última del minuto) de la mejor ruta neta de cada moneda.
    //  Archivos diarios en <carpeta privada>/hist/h<día>.csv, con día = minuto / 1440 (UTC):
    //    minuto,usdt,usdc,dai,btc,eth,cruz[,rutas]     valores en centésimas de %; vacío = sin dato
    //    #c,minuto,firma                                configuración vigente desde ese minuto
    //  MainActivity.getHistory lee estos mismos archivos: no cambiar nombres ni formato sin tocar los dos.
    // ══════════════════════════════════════════════════════════════

    static final class History {
        static final String DIR = "hist", PREFIX = "h", SUFFIX = ".csv";
        static final int KEEP_DAYS = 90;

        private final File dir;
        private long curMinute = -1;
        private String curLine;
        private String sig;            // configuración vigente
        private long lastPruneDay = -1;

        History(File base) { this.dir = new File(base, DIR); }

        /** Línea de un minuto a partir de los resultados por pestaña (cinco monedas y rutas cruzadas). */
        static String line(long minute, CoinResult[] byTab) {
            StringBuilder sb = new StringBuilder().append(minute);
            StringBuilder routes = new StringBuilder();
            for (int i = 0; i < TAB_LABELS.length; i++) {
                sb.append(',');
                CoinResult r = i < byTab.length ? byTab[i] : null;
                Opp o = r == null ? null : r.bestOk();
                if (o == null) continue;
                sb.append(Math.round(o.pPct * 100));
                if (o.pPct >= 0) {                                  // con ganancia: se anota qué ruta era
                    if (routes.length() > 0) routes.append('|');
                    String k = o.key();
                    int a = k.indexOf('|'), b = k.indexOf('|', a + 1);
                    routes.append(k, 0, a).append(':');
                    if (b < 0) routes.append(k.substring(a + 1));
                    else routes.append(k, a + 1, b).append('>').append(k.substring(b + 1));
                }
            }
            if (routes.length() > 0) sb.append(',').append(routes);
            return sb.toString();
        }

        /** Muestra de este ciclo. Al cambiar el minuto se guarda la última del minuto anterior. */
        synchronized void sample(long minute, String line) {
            if (curMinute >= 0 && minute != curMinute && curLine != null) append(curMinute, curLine);
            curMinute = minute;
            curLine = line;
            long day = minute / 1440;
            if (day != lastPruneDay) { lastPruneDay = day; prune(day); }
        }

        /** Anota la configuración vigente si cambió (o si es la primera vez desde que arrancó el servicio). */
        synchronized void noteConfig(long minute, String signature) {
            if (signature.equals(sig)) return;
            // Lo que estaba pendiente de un minuto anterior se midió con la configuración vieja: va antes de la marca
            if (curMinute >= 0 && curMinute < minute && curLine != null) { append(curMinute, curLine); curLine = null; }
            sig = signature;
            append(minute, "#c," + minute + "," + signature);
        }

        /** Guarda la muestra en curso (el servicio se detiene). */
        synchronized void flush() {
            if (curMinute >= 0 && curLine != null) append(curMinute, curLine);
            curMinute = -1;
            curLine = null;
        }

        private void append(long minute, String line) {
            try {
                if (!dir.isDirectory() && !dir.mkdirs()) return;
                File f = new File(dir, PREFIX + (minute / 1440) + SUFFIX);
                StringBuilder sb = new StringBuilder();
                // Cada archivo empieza con la configuración vigente: se puede leer un día sin mirar los anteriores
                if (!f.exists() && sig != null && line.charAt(0) != '#') sb.append("#c,").append(minute).append(',').append(sig).append('\n');
                sb.append(line).append('\n');
                FileOutputStream out = new FileOutputStream(f, true);
                try { out.write(sb.toString().getBytes("UTF-8")); } finally { out.close(); }
            } catch (Exception e) {
                Log.w(TAG, "historial: " + e.getMessage());
            }
        }

        private void prune(long today) {
            File[] files = dir.listFiles();
            if (files == null) return;
            for (File f : files) {
                String n = f.getName();
                if (!n.startsWith(PREFIX) || !n.endsWith(SUFFIX)) continue;
                try {
                    long day = Long.parseLong(n.substring(PREFIX.length(), n.length() - SUFFIX.length()));
                    if (day < today - KEEP_DAYS && !f.delete()) Log.w(TAG, "historial: no se pudo borrar " + n);
                } catch (NumberFormatException ignored) {
                    // archivo ajeno: no se toca
                }
            }
        }
    }

    // ══════════════════════════════════════════════════════════════
    //  SERVICIO
    // ══════════════════════════════════════════════════════════════

    private PowerManager.WakeLock wakeLock;
    private ScheduledExecutorService scheduler;
    private NotificationManager notifManager;
    private History history;

    private double usdArs = 1550.0;

    // La configuración la fija la app. Hasta recibirla vale la que la app trae de fábrica.
    // La escribe el hilo principal (onStartCommand) y la lee el hilo del ciclo: se reemplaza entera.
    private volatile Config config = Config.defaults();
    private volatile String lastStatus = "Monitoreando arbitraje...";
    private volatile String lastCoins;                    // mejor ruta de cada moneda en el último ciclo

    private JSONObject fees;             // comisiones de retiro (CriptoYa /api/fees)
    private long feesAt;
    private final HubBook hub = new HubBook();
    private final long[] hubRetryAt = new long[2];       // por par: no insistir en cada ciclo si no responde
    private final double[] refAsk = new double[COIN_IDS.length];   // referencia de precio por moneda para el volumen
    private final Map<String, AlertState> alertStates = new HashMap<>();

    @Override
    public void onCreate() {
        super.onCreate();
        notifManager = (NotificationManager) getSystemService(NOTIFICATION_SERVICE);
        createChannels();
        acquireWakeLock();
        history = new History(getFilesDir());
        // Última configuración recibida de la app: vale también si Android reinicia el servicio solo
        try {
            applyConfig(getSharedPreferences(PREFS, MODE_PRIVATE).getString(PREF_CONFIG, null), false);
        } catch (Exception e) {
            Log.w(TAG, "config guardada: " + e.getMessage());
        }
    }

    @Override
    public int onStartCommand(Intent intent, int flags, int startId) {
        // La app reenvía la configuración cada vez que se abre o que se cambia algo
        if (intent != null) applyConfig(intent.getStringExtra(EXTRA_CONFIG), true);
        startForeground(NOTIF_FG_ID, buildForegroundNotif(lastStatus));
        startMonitorLoop();
        return START_STICKY; // Reinicia si Android lo mata
    }

    // ─── Configuración ───────────────────────────────────────────
    private void applyConfig(String json, boolean persist) {
        Config c = parseConfig(json, config);
        if (c == null) return;
        config = c;
        Log.d(TAG, "Configuración: " + configLine(c));
        if (!persist) return;
        try {
            getSharedPreferences(PREFS, MODE_PRIVATE).edit().putString(PREF_CONFIG, c.toJson()).apply();
        } catch (Exception e) {
            Log.w(TAG, "guardar config: " + e.getMessage());
        }
    }

    /** Parámetros con los que está trabajando el monitor, tal como se ven en la notificación. */
    static String configLine(Config c) {
        int active = 0;
        for (Venue v : VENUES) if (c.venueOn(v) && c.active(v)) active++;
        return "Capital U$D " + String.format("%,d", Math.round(c.capital))
            + " · alerta " + new DecimalFormat("0.##").format(c.alertPct) + "%"
            + " · " + (c.both ? "dos puntas" : "con transferencia")
            + " · " + active + " exchanges" + (c.p2p ? " con P2P" : "");
    }

    @Override
    public IBinder onBind(Intent intent) { return null; }

    @Override
    public void onDestroy() {
        if (scheduler != null) scheduler.shutdown();
        if (history != null) history.flush();
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
                text + (lastCoins != null ? "\n" + lastCoins : "") + "\n" + configLine(config)))
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
            // La configuración se toma una sola vez por ciclo: si la app la cambia en el medio, rige desde el próximo
            final Config cfg = config;

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

            // 3. Precio de conversión entre stablecoins en el hub (libro de Binance), para las rutas cruzadas
            if (cfg.cross) fetchHub(nowMs);

            // 4. Cotizaciones y rutas por moneda
            double capArs = cfg.capital * usdArs;
            long nowSec = nowMs / 1000L;
            CoinData[] coins = new CoinData[COIN_IDS.length];
            CoinResult[] byTab = new CoinResult[TAB_LABELS.length];
            String[] raw = new String[COIN_IDS.length];
            int feedsOk = 0;
            for (int i = 0; i < COIN_IDS.length; i++) {
                // Se pide el precio para las unidades que mueve realmente el capital
                double vol = refAsk[i] > 0 ? capArs / refAsk[i] : cfg.capital / COIN_USD_REF[i];
                raw[i] = httpGet("https://criptoya.com/api/" + COIN_IDS[i] + "/ars/" + fmtVol(vol));
                if (raw[i] == null) continue;
                JSONObject data;
                try { data = new JSONObject(raw[i]); } catch (Exception e) { continue; }
                CoinData cd = parseCoin(COIN_IDS[i], data, nowSec);
                if (cd.refAsk > 0) refAsk[i] = cd.refAsk;
                if (!cd.down) feedsOk++;
                coins[i] = cd;
                byTab[i] = computeCoin(cd, fees, capArs, cfg);
            }
            if (cfg.cross) byTab[COIN_IDS.length] = computeCross(coins, fees, capArs, cfg, hub, nowMs);
            List<CoinResult> results = Arrays.asList(byTab);

            // 5. Mejor ruta operable entre todas las monedas (los datos sospechosos no cuentan)
            Opp best = null;
            int profitable = 0;
            for (CoinResult r : results) {
                if (r == null) continue;
                for (Opp o : r.opps) {
                    if (o.status == ST_SUSPECT) continue;
                    if (best == null || o.pPct > best.pPct) best = o;
                    if (o.status == ST_OK && o.pPct >= cfg.alertPct) profitable++;
                }
            }
            String status;
            if (best == null) {
                status = feedsOk == 0 ? "Sin cotizaciones vigentes — reintentando..." : "Sin rutas operables por ahora";
            } else {
                String tail = fmtPct(best.pPct)
                    + " [" + best.label() + ": " + best.buy.name + "→" + best.sell.name + "]";
                status = profitable > 0
                    ? "🟢 " + profitable + " oportunidad(es) — mejor: " + tail
                    : "Monitoreando — mejor: " + tail;
                if (fees == null) status += " (sin costo de red)";
            }
            lastCoins = coinsLine(byTab);
            updateForegroundNotif(status);
            Log.d(TAG, "Ciclo OK — " + status + " | " + lastCoins);

            // 6. Alertas: una notificación por ciclo, con la mejor ruta confirmada
            List<Opp> batch = selectAlerts(results, alertStates, cfg.alertPct, nowMs);
            if (!batch.isEmpty()) fireAlert(batch.get(0), batch.size() - 1, nowSec, cfg);

            // 7. Historial: una muestra por minuto, también con la app cerrada
            long minute = nowSec / 60;
            history.noteConfig(minute, cfg.signature());
            if (feedsOk > 0) history.sample(minute, History.line(minute, byTab));

            // 8. Compatibilidad con MainActivity.injectData (dólar, USDT, DAI, BTC)
            if (MainActivity.instance != null) {
                MainActivity.instance.injectData(dolarJson, raw[0], raw[2], raw[3]);
            }

        } catch (Exception e) {
            Log.e(TAG, "Error en ciclo: " + e.getMessage());
        }
    }

    /** Lee USDC/USDT y USDT/DAI de Binance. Si una lectura falla, la anterior vale hasta HUB_TTL_MS. */
    private void fetchHub(long nowMs) {
        for (int i = 0; i < 2; i++) {
            if (nowMs < hubRetryAt[i]) continue;
            String sym = i == 0 ? "USDCUSDT" : "USDTDAI";
            String body = httpGet("https://data-api.binance.vision/api/v3/ticker/bookTicker?symbol=" + sym);
            if (body == null) body = httpGet("https://api.binance.com/api/v3/ticker/bookTicker?symbol=" + sym);
            boolean ok = false;
            if (body != null) {
                try {
                    ok = applyHubBook(hub, sym, new JSONObject(body), nowMs);
                } catch (Exception e) { Log.w(TAG, "hub " + sym + ": " + e.getMessage()); }
            }
            if (!ok) hubRetryAt[i] = nowMs + HUB_RETRY_MS;
        }
    }

    /** Guarda en `hub` la mejor compra y la mejor venta de un par, si la respuesta es válida. */
    static boolean applyHubBook(HubBook hub, String sym, JSONObject o, long nowMs) {
        if (!sym.equals(o.optString("symbol"))) return false;
        double bid = fin(o.optDouble("bidPrice", 0)), ask = fin(o.optDouble("askPrice", 0));
        if (!(bid > 0) || !(ask > 0) || bid > ask) return false;
        if ("USDCUSDT".equals(sym)) { hub.usdcBid = bid; hub.usdcAsk = ask; hub.usdcAt = nowMs; }
        else if ("USDTDAI".equals(sym)) { hub.daiBid = bid; hub.daiAsk = ask; hub.daiAt = nowMs; }
        else return false;
        return true;
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
    private void fireAlert(Opp o, int more, long nowSec, Config cfg) {
        String title = "🚨 ARBITRAJE — " + o.label() + " " + fmtPct(o.pPct);
        String body = alertBody(o, cfg, more, nowSec);

        // Intent para abrir la app al tocar la notificación
        Intent openApp = new Intent(this, MainActivity.class);
        openApp.setFlags(Intent.FLAG_ACTIVITY_NEW_TASK | Intent.FLAG_ACTIVITY_CLEAR_TOP);
        PendingIntent pi = PendingIntent.getActivity(this, (int) System.currentTimeMillis(),
            openApp, PendingIntent.FLAG_IMMUTABLE | PendingIntent.FLAG_UPDATE_CURRENT);

        // Intent para abrir el exchange de compra
        Intent buyIntent = new Intent(Intent.ACTION_VIEW, Uri.parse(o.buy.url));
        PendingIntent buyPi = PendingIntent.getActivity(this, (int) System.currentTimeMillis() + 1,
            buyIntent, PendingIntent.FLAG_IMMUTABLE);

        // Intent para abrir el exchange de venta
        Intent sellIntent = new Intent(Intent.ACTION_VIEW, Uri.parse(o.sell.url));
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
        Log.d(TAG, "ALERTA: " + title + " — " + o.buy.name + " → " + o.sell.name);
    }
}
