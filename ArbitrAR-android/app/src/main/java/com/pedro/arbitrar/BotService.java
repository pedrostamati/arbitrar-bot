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
import org.json.JSONObject;
import org.json.JSONArray;
import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.net.HttpURLConnection;
import java.net.URL;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.Executors;
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.TimeUnit;

public class BotService extends Service {

    private static final String TAG = "ArbitrARBot";
    private static final String CH_FOREGROUND = "arbitrar_fg";
    private static final String CH_ALERT      = "arbitrar_alert";
    private static final int    NOTIF_FG_ID   = 1;
    private static final int    NOTIF_ALERT_BASE = 100;

    private PowerManager.WakeLock wakeLock;
    private ScheduledExecutorService scheduler;
    private NotificationManager notifManager;

    // Estado del motor
    private double usdArs    = 1550.0;
    private double alertPct  = 0.3;
    private double capital   = 1000.0;   // en USD
    private double networkFee = 0.5;     // USDT / stablecoin units
    private final Map<String, Long> alertedKeys = new HashMap<>();
    private static final long ALERT_COOLDOWN_MS = 120_000;

    // ─── Definición de monedas ───────────────────────────────────
    // { coinId, cyPath, isCrypto, minPrice, maxPrice }
    // NOTA: CriptoYa devuelve siempre el precio por 1 unidad de la moneda,
    // independientemente del parámetro de cantidad en la URL (ej: /btc/ars/0.001).
    // Ese parámetro solo afecta el cálculo interno de fees de la API.
    // NO dividir por escala; los precios vienen normalizados por 1 unidad.
    private static final Object[][] COINS = {
        // coinId   cyPath               isCrypto  minPrice    maxPrice
        { "usdt",  "usdt/ars/1",        false,    100.0,      100_000.0   },
        { "usdc",  "usdc/ars/1",        false,    100.0,      100_000.0   },
        { "dai",   "dai/ars/1",         false,    100.0,      100_000.0   },
        { "btc",   "btc/ars/0.001",     true,     1_000_000.0, 1e12       },
        { "eth",   "eth/ars/0.01",      true,     100_000.0,   1e11       },
    };

    // ─── Exchanges ──────────────────────────────────────────────
    // { internalId, displayName, cyKey }
    private static final String[][] EXCHANGES = {
        { "binancep2p",   "Binance P2P",   "binancep2p"   },
        { "buenbit",      "Nexo",          "buenbit"      },  // Nexo (ex-BuenBit); CriptoYa aún usa 'buenbit'
        { "letsbit",      "LetsBit",       "letsbit"      },
        { "ripio",        "Ripio",         "ripio"        },
        { "satoshitango", "SatoshiTango",  "satoshitango" },
        { "lemoncash",    "Lemon Cash",    "lemoncash"    },
        { "fiwind",       "Fiwind",        "fiwind"       },
        { "astropay",     "AstroPay",      "astropay"     },
        { "belo",         "Belo",          "belo"         },
        { "tiendacrypto", "TiendaCrypto",  "tiendacrypto" },
        { "cryptomkt",    "CryptoMKT",     "cryptomkt"    },
        { "decrypto",     "Decrypto",      "decrypto"     },
        { "bybit",        "Bybit",         "bybit"        },
    };

    // URLs para botones de acción en alertas
    private static final Map<String, String> EX_URLS = new HashMap<String, String>() {{
        put("binancep2p",   "https://p2p.binance.com/trade/buy/USDT?fiat=ARS");
        put("buenbit",      "https://nexo.com");
        put("letsbit",      "https://letsbit.io");
        put("ripio",        "https://exchange.ripio.com");
        put("satoshitango", "https://satoshitango.com");
        put("lemoncash",    "https://lemon.me");
        put("fiwind",       "https://fiwind.io");
        put("astropay",     "https://astropay.com/wallet/exchange");
        put("belo",         "https://belo.app");
        put("tiendacrypto", "https://tiendacrypto.com");
        put("cryptomkt",    "https://www.cryptomkt.com");
        put("decrypto",     "https://decrypto.la");
        put("bybit",        "https://www.bybit.com");
    }};

    // ─── Resultado de oportunidad ────────────────────────────────
    private static class Opp {
        String coinId, coinLabel, buyId, buyName, sellId, sellName;
        double pPct, pARS, askARS, bidARS;
        Opp(String coinId, String coinLabel,
            String buyId, String buyName, String sellId, String sellName,
            double pPct, double pARS, double askARS, double bidARS) {
            this.coinId    = coinId;    this.coinLabel = coinLabel;
            this.buyId     = buyId;    this.buyName   = buyName;
            this.sellId    = sellId;   this.sellName  = sellName;
            this.pPct      = pPct;     this.pARS      = pARS;
            this.askARS    = askARS;   this.bidARS    = bidARS;
        }
    }

    // ─── Lifecycle ───────────────────────────────────────────────
    @Override
    public void onCreate() {
        super.onCreate();
        notifManager = (NotificationManager) getSystemService(NOTIFICATION_SERVICE);
        createChannels();
        acquireWakeLock();
    }

    @Override
    public int onStartCommand(Intent intent, int flags, int startId) {
        startForeground(NOTIF_FG_ID, buildForegroundNotif("Monitoreando arbitraje..."));
        startMonitorLoop();
        return START_STICKY;
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
        wakeLock.acquire();
    }

    // ─── Canales de notificación ─────────────────────────────────
    private void createChannels() {
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
            NotificationChannel fg = new NotificationChannel(
                CH_FOREGROUND, "ArbitrAR Monitor", NotificationManager.IMPORTANCE_MIN);
            fg.setSound(null, null);
            notifManager.createNotificationChannel(fg);

            Uri alarmSound = RingtoneManager.getDefaultUri(RingtoneManager.TYPE_ALARM);
            AudioAttributes aa = new AudioAttributes.Builder()
                .setContentType(AudioAttributes.CONTENT_TYPE_SONIFICATION)
                .setUsage(AudioAttributes.USAGE_ALARM).build();
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
            .setSmallIcon(android.R.drawable.ic_menu_compass)
            .setContentIntent(pi)
            .setOngoing(true)
            .build();
    }

    private void updateForegroundNotif(String text) {
        notifManager.notify(NOTIF_FG_ID, buildForegroundNotif(text));
    }

    // ─── Loop de monitoreo ───────────────────────────────────────
    private void startMonitorLoop() {
        if (scheduler != null && !scheduler.isShutdown()) return;
        scheduler = Executors.newSingleThreadScheduledExecutor();
        scheduler.scheduleAtFixedRate(this::runCycle, 0, 15, TimeUnit.SECONDS);
        Log.d(TAG, "Loop iniciado — cada 15 segundos");
    }

    private void runCycle() {
        try {
            // 1. Dólar blue
            String dolarJson = httpGet("https://dolarapi.com/v1/dolares");
            if (dolarJson != null) {
                try {
                    JSONArray arr = new JSONArray(dolarJson);
                    for (int i = 0; i < arr.length(); i++) {
                        JSONObject d = arr.getJSONObject(i);
                        if ("blue".equals(d.optString("casa"))) {
                            usdArs = (d.optDouble("compra", 1550) + d.optDouble("venta", 1550)) / 2;
                            break;
                        }
                    }
                } catch (Exception e) { Log.w(TAG, "parseDolar: " + e.getMessage()); }
            }

            // 2. Fetch de cada moneda y cálculo de oportunidades
            List<Opp> allOpps = new ArrayList<>();
            JSONObject[] coinData = new JSONObject[COINS.length]; // cache por índice de moneda

            for (int ci = 0; ci < COINS.length; ci++) {
                String coinId    = (String)  COINS[ci][0];
                String cyPath    = (String)  COINS[ci][1];
                boolean isCrypto = (boolean) COINS[ci][2];
                double minPrice  = (double)  COINS[ci][3];
                double maxPrice  = (double)  COINS[ci][4];
                String coinLabel = coinId.toUpperCase();

                String json = httpGet("https://criptoya.com/api/" + cyPath);
                if (json == null) continue;
                JSONObject data;
                try { data = new JSONObject(json); } catch (Exception e) { continue; }
                coinData[ci] = data;

                // Precios por exchange — CriptoYa ya devuelve precio por 1 unidad
                Map<String, double[]> prices = new HashMap<>();
                for (String[] ex : EXCHANGES) {
                    double[] p = getPrice(data, ex[2], minPrice, maxPrice);
                    if (p != null) prices.put(ex[0], p);
                }

                // Rutas entre exchanges para esta moneda
                for (String[] buy : EXCHANGES) {
                    for (String[] sell : EXCHANGES) {
                        if (buy[0].equals(sell[0])) continue;
                        double[] pb = prices.get(buy[0]);
                        double[] ps = prices.get(sell[0]);
                        if (pb == null || ps == null) continue;

                        double capARS   = capital * usdArs;
                        double units    = capARS / pb[1]; // pb[1] = ask
                        double unitsNet = isCrypto ? units : units - networkFee;
                        if (unitsNet <= 0) continue;
                        double pARS = unitsNet * ps[0] - capARS; // ps[0] = bid
                        double pPct = (pARS / capARS) * 100;

                        allOpps.add(new Opp(coinId, coinLabel,
                            buy[0], buy[1], sell[0], sell[1],
                            pPct, pARS, pb[1], ps[0]));

                        if (pPct >= alertPct && pPct < 50) {
                            String desc = coinLabel + ": " + buy[1] + " → " + sell[1];
                            checkAndAlert(buy[0], sell[0], coinLabel,
                                pPct, pARS, pb[1], ps[0], desc);
                        }
                    }
                }
            }

            // 3. Mejor ruta global (entre TODAS las monedas)
            Opp globalBest = null;
            int profitable = 0;
            for (Opp o : allOpps) {
                if (o.pPct > (globalBest != null ? globalBest.pPct : Double.NEGATIVE_INFINITY)) {
                    globalBest = o;
                }
                if (o.pPct >= alertPct && o.pPct < 50) profitable++;
            }

            // 4. Actualizar notificación foreground
            String status;
            if (globalBest != null) {
                String bestStr = String.format("%.2f%%", globalBest.pPct);
                String sign    = globalBest.pPct >= 0 ? "+" : "";
                if (profitable > 0) {
                    status = "🟢 " + profitable + " opor. — mejor: " + sign + bestStr
                           + " [" + globalBest.coinLabel + ": "
                           + globalBest.buyName + "→" + globalBest.sellName + "]";
                } else {
                    status = "Monitoreando — mejor: " + sign + bestStr
                           + " [" + globalBest.coinLabel + ": "
                           + globalBest.buyName + "→" + globalBest.sellName + "]";
                }
            } else {
                status = "Sin datos — reintentando...";
            }
            updateForegroundNotif(status);
            Log.d(TAG, "Ciclo OK — " + status);

            // 5. Inyectar datos al WebView si la Activity está activa
            // Pasamos los JSON de USDT, DAI y BTC para compatibilidad con versiones anteriores
            if (MainActivity.instance != null) {
                String fDolar = dolarJson;
                String fUsdt  = coinData[0] != null ? coinData[0].toString() : null;
                String fDai   = coinData[2] != null ? coinData[2].toString() : null;
                String fBtc   = coinData[3] != null ? coinData[3].toString() : null;
                MainActivity.instance.injectData(fDolar, fUsdt, fDai, fBtc);
            }

        } catch (Exception e) {
            Log.e(TAG, "Error en ciclo: " + e.getMessage());
        }
    }

    // ─── Helpers de precio ───────────────────────────────────────
    /**
     * Extrae bid/ask de un JSONObject de CriptoYa para un exchange dado.
     * CriptoYa devuelve siempre precio por 1 unidad de la moneda;
     * el parámetro de cantidad en la URL solo afecta el cálculo de fees internos.
     * Valida que los precios estén en el rango [minPrice, maxPrice].
     * Retorna double[]{bid, ask} o null si datos inválidos.
     */
    private double[] getPrice(JSONObject data, String key, double minPrice, double maxPrice) {
        try {
            JSONObject ex = data.getJSONObject(key);
            double bid = ex.optDouble("totalBid", 0);
            if (bid == 0) bid = ex.optDouble("bid", 0);
            double ask = ex.optDouble("totalAsk", 0);
            if (ask == 0) ask = ex.optDouble("ask", 0);

            if (bid > minPrice && bid < maxPrice
                    && ask > minPrice && ask < maxPrice
                    && ask >= bid) {
                return new double[]{bid, ask};
            }
        } catch (Exception ignored) {}
        return null;
    }

    // ─── HTTP ────────────────────────────────────────────────────
    private String httpGet(String urlStr) {
        try {
            URL url = new URL(urlStr);
            HttpURLConnection conn = (HttpURLConnection) url.openConnection();
            conn.setRequestMethod("GET");
            conn.setConnectTimeout(8000);
            conn.setReadTimeout(8000);
            conn.setRequestProperty("User-Agent", "ArbitrAR-Android/1.0");
            if (conn.getResponseCode() != 200) return null;
            BufferedReader br = new BufferedReader(new InputStreamReader(conn.getInputStream()));
            StringBuilder sb = new StringBuilder();
            String line;
            while ((line = br.readLine()) != null) sb.append(line);
            return sb.toString();
        } catch (Exception e) {
            Log.w(TAG, "httpGet(" + urlStr + "): " + e.getMessage());
            return null;
        }
    }

    // ─── Alertas ─────────────────────────────────────────────────
    private void checkAndAlert(String bId, String sId, String coinLabel,
                                double pPct, double pARS,
                                double askARS, double bidARS, String desc) {
        String key = coinLabel + "-" + bId + "-" + sId + "-" + (int)(pPct * 10);
        long now = System.currentTimeMillis();
        Long last = alertedKeys.get(key);
        if (last != null && now - last < ALERT_COOLDOWN_MS) return;
        alertedKeys.put(key, now);
        fireAlert(bId, sId, coinLabel, pPct, pARS, askARS, bidARS, desc);
    }

    private void fireAlert(String bId, String sId, String coinLabel,
                            double pPct, double pARS,
                            double askARS, double bidARS, String desc) {
        String sign  = pPct >= 0 ? "+" : "−";
        String title = "🚨 ARBITRAJE — " + coinLabel + " " + sign
                     + String.format("%.2f%%", Math.abs(pPct));
        String priceAsk = askARS >= 1_000_000
            ? String.format("$%.2fM", askARS / 1_000_000)
            : "$" + Math.round(askARS);
        String priceBid = bidARS >= 1_000_000
            ? String.format("$%.2fM", bidARS / 1_000_000)
            : "$" + Math.round(bidARS);
        String body = desc + "\n"
            + "Comprar @ " + priceAsk + " · Vender @ " + priceBid + "\n"
            + "Ganancia: $" + Math.round(Math.abs(pARS)) + " ARS (U$D " + capital + " capital)";

        Intent openApp = new Intent(this, MainActivity.class);
        openApp.setFlags(Intent.FLAG_ACTIVITY_NEW_TASK | Intent.FLAG_ACTIVITY_CLEAR_TOP);
        PendingIntent pi = PendingIntent.getActivity(this, (int)System.currentTimeMillis(),
            openApp, PendingIntent.FLAG_IMMUTABLE | PendingIntent.FLAG_UPDATE_CURRENT);

        String buyUrl = EX_URLS.getOrDefault(bId, "https://google.com");
        PendingIntent buyPi = PendingIntent.getActivity(this, (int)System.currentTimeMillis() + 1,
            new Intent(Intent.ACTION_VIEW, Uri.parse(buyUrl)),
            PendingIntent.FLAG_IMMUTABLE);

        String sellUrl = EX_URLS.getOrDefault(sId, "https://google.com");
        PendingIntent sellPi = PendingIntent.getActivity(this, (int)System.currentTimeMillis() + 2,
            new Intent(Intent.ACTION_VIEW, Uri.parse(sellUrl)),
            PendingIntent.FLAG_IMMUTABLE);

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
            .addAction(android.R.drawable.ic_media_play,  "🟢 Comprar", buyPi)
            .addAction(android.R.drawable.ic_media_pause, "🔴 Vender",  sellPi);

        int notifId = NOTIF_ALERT_BASE + Math.abs((bId + sId + coinLabel).hashCode() % 50);
        notifManager.notify(notifId, nb.build());
        Log.d(TAG, "ALERTA: " + title);
    }
}
