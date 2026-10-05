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
import java.util.HashMap;
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
    private double usdArs = 1550.0;
    private double alertPct = 0.3;
    private double capital = 1000.0;
    private double networkFee = 0.5;
    private final Map<String, Long> alertedKeys = new HashMap<>();
    private static final long ALERT_COOLDOWN_MS = 120_000;

    // Últimos JSON recibidos para inyectar al WebView
    private String lastDolarJson = null;
    private String lastUsdtJson  = null;
    private String lastDaiJson   = null;
    private String lastBtcJson   = null;

    // Exchanges (clave CriptoYa)
    private static final String[][] EXCHANGES = {
        {"binance_p2p",  "Binance P2P",  "binance"},
        {"buenbit",      "BuenBit",      "buenbit"},
        {"letsbit",      "LetsBit",      "letsbit"},
        {"ripio",        "Ripio",        "ripio"},
        {"satoshitango", "SatoshiTango", "satoshitango"},
        {"lemon",        "Lemon Cash",   "lemoncash"},
        {"fiwind",       "Fiwind",       "fiwind"},
        {"astropay",     "AstroPay",     "astropay"},
    };

    // URLs de exchanges para la notificación
    private static final Map<String, String> EX_URLS = new HashMap<String, String>() {{
        put("binance_p2p",  "https://p2p.binance.com/trade/buy/USDT?fiat=ARS");
        put("buenbit",      "https://buenbit.com");
        put("letsbit",      "https://letsbit.io");
        put("ripio",        "https://exchange.ripio.com");
        put("satoshitango", "https://satoshitango.com");
        put("lemon",        "https://lemon.me");
        put("fiwind",       "https://fiwind.io");
        put("astropay",     "https://astropay.com/wallet/exchange");
    }};

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
        return START_STICKY; // Reinicia si Android lo mata
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

    // ─── Notificación Foreground ─────────────────────────────────
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
            lastDolarJson = httpGet("https://dolarapi.com/v1/dolares");
            if (lastDolarJson != null) {
                try {
                    JSONArray arr = new JSONArray(lastDolarJson);
                    for (int i = 0; i < arr.length(); i++) {
                        JSONObject d = arr.getJSONObject(i);
                        if ("blue".equals(d.optString("casa"))) {
                            usdArs = (d.optDouble("compra", 1550) + d.optDouble("venta", 1550)) / 2;
                            break;
                        }
                    }
                } catch (Exception e) { Log.w(TAG, "parseDolar: " + e.getMessage()); }
            }
            // 2. Precios USDT/DAI/BTC
            lastUsdtJson = httpGet("https://criptoya.com/api/usdt/ars/1");
            lastDaiJson  = httpGet("https://criptoya.com/api/dai/ars/1");
            lastBtcJson  = httpGet("https://criptoya.com/api/btc/ars/1");
            JSONObject usdt = lastUsdtJson != null ? new JSONObject(lastUsdtJson) : null;
            JSONObject dai  = lastDaiJson  != null ? new JSONObject(lastDaiJson)  : null;
            JSONObject btc  = lastBtcJson  != null ? new JSONObject(lastBtcJson)  : null;

            if (usdt == null) {
                updateForegroundNotif("Sin datos — reintentando...");
                return;
            }

            // Calcular oportunidades
            int profitable = 0;
            double bestPct = -99;
            String bestDesc = "";

            // Tipo 1: USDT entre exchanges
            for (String[] buy : EXCHANGES) {
                for (String[] sell : EXCHANGES) {
                    if (buy[0].equals(sell[0])) continue;
                    double[] pb = getPrice(usdt, buy[2]);
                    double[] ps = getPrice(usdt, sell[2]);
                    if (pb == null || ps == null) continue;

                    double capARS = capital * usdArs;
                    double units = capARS / pb[1]; // pb[1] = ask
                    double unitsNet = units - networkFee;
                    if (unitsNet <= 0) continue;
                    double pARS = unitsNet * ps[0] - capARS; // ps[0] = bid
                    double pPct = (pARS / capARS) * 100;

                    if (pPct >= alertPct) {
                        profitable++;
                        String desc = "USDT: " + buy[1] + " → " + sell[1];
                        checkAndAlert(buy[0], sell[0], "USDT", pPct, pARS, pb[1], ps[0], desc);
                    }
                    if (pPct > bestPct) { bestPct = pPct; bestDesc = buy[1] + "→" + sell[1]; }
                }
            }

            // Tipo 2: USDT vs DAI mismo exchange
            if (dai != null) {
                for (String[] ex : EXCHANGES) {
                    double[] pu = getPrice(usdt, ex[2]);
                    double[] pd = getPrice(dai,  ex[2]);
                    if (pu == null || pd == null) continue;
                    double capARS = capital * usdArs;
                    double unA = capARS / pu[1];
                    double pA = unA * pd[0] - capARS;
                    double pPctA = (pA / capARS) * 100;
                    if (pPctA >= alertPct) {
                        profitable++;
                        String desc = "USDT→DAI en " + ex[1];
                        checkAndAlert(ex[0], ex[0], "USDT/DAI", pPctA, pA, pu[1], pd[0], desc);
                    }
                    if (pPctA > bestPct) { bestPct = pPctA; bestDesc = "USDT/DAI " + ex[1]; }
                }
            }

            // Tipo 3: BTC entre exchanges
            if (btc != null) {
                for (String[] buy : EXCHANGES) {
                    for (String[] sell : EXCHANGES) {
                        if (buy[0].equals(sell[0])) continue;
                        double[] pb = getPrice(btc, buy[2]);
                        double[] ps = getPrice(btc, sell[2]);
                        if (pb == null || ps == null) continue;
                        double capARS = capital * usdArs;
                        double btcAmt = capARS / pb[1];
                        double pARS = btcAmt * ps[0] - capARS;
                        double pPct = (pARS / capARS) * 100;
                        if (pPct >= alertPct) {
                            profitable++;
                            String desc = "BTC: " + buy[1] + " → " + sell[1];
                            checkAndAlert(buy[0], sell[0], "BTC", pPct, pARS, pb[1], ps[0], desc);
                        }
                        if (pPct > bestPct) { bestPct = pPct; bestDesc = "BTC " + buy[1] + "→" + sell[1]; }
                    }
                }
            }

            String status = profitable > 0
                ? "🟢 " + profitable + " oportunidad(es) — mejor: " + String.format("+%.2f%%", bestPct)
                : "Monitoreando — mejor: " + String.format("%.2f%%", bestPct);
            updateForegroundNotif(status);
            Log.d(TAG, "Ciclo OK — " + status);

            // Inyectar datos en el WebView si la Activity está activa
            if (MainActivity.instance != null) {
                final String fDolar = lastDolarJson;
                final String fUsdt  = lastUsdtJson;
                final String fDai   = lastDaiJson;
                final String fBtc   = lastBtcJson;
                MainActivity.instance.injectData(fDolar, fUsdt, fDai, fBtc);
            }

        } catch (Exception e) {
            Log.e(TAG, "Error en ciclo: " + e.getMessage());
        }
    }

    // ─── Fetch helpers ───────────────────────────────────────────
    private void fetchDolar() {
        try {
            String json = httpGet("https://dolarapi.com/v1/dolares");
            if (json == null) return;
            JSONArray arr = new JSONArray(json);
            for (int i = 0; i < arr.length(); i++) {
                JSONObject d = arr.getJSONObject(i);
                if ("blue".equals(d.optString("casa"))) {
                    usdArs = (d.optDouble("compra", 1550) + d.optDouble("venta", 1550)) / 2;
                    break;
                }
            }
        } catch (Exception e) { Log.w(TAG, "fetchDolar: " + e.getMessage()); }
    }

    private JSONObject fetchCriptoYa(String coin) {
        try {
            String json = httpGet("https://criptoya.com/api/" + coin + "/ars/1");
            if (json == null) return null;
            return new JSONObject(json);
        } catch (Exception e) {
            Log.w(TAG, "fetchCriptoYa(" + coin + "): " + e.getMessage());
            return null;
        }
    }

    private double[] getPrice(JSONObject data, String key) {
        try {
            JSONObject ex = data.getJSONObject(key);
            double bid = ex.optDouble("totalBid", ex.optDouble("bid", 0));
            double ask = ex.optDouble("totalAsk", ex.optDouble("ask", 0));
            if (bid > 0 && ask > 0) return new double[]{bid, ask};
        } catch (Exception ignored) {}
        return null;
    }

    private String httpGet(String urlStr) {
        try {
            URL url = new URL(urlStr);
            HttpURLConnection conn = (HttpURLConnection) url.openConnection();
            conn.setRequestMethod("GET");
            conn.setConnectTimeout(8000);
            conn.setReadTimeout(8000);
            conn.setRequestProperty("User-Agent", "ArbitrAR-Android/1.0");
            int code = conn.getResponseCode();
            if (code != 200) return null;
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
    private void checkAndAlert(String bId, String sId, String type,
                                double pPct, double pARS,
                                double askARS, double bidARS, String desc) {
        String key = type + "-" + bId + "-" + sId + "-" + (int)(pPct * 10);
        long now = System.currentTimeMillis();
        Long last = alertedKeys.get(key);
        if (last != null && now - last < ALERT_COOLDOWN_MS) return;
        alertedKeys.put(key, now);
        fireAlert(bId, sId, type, pPct, pARS, askARS, bidARS, desc);
    }

    private void fireAlert(String bId, String sId, String type,
                            double pPct, double pARS,
                            double askARS, double bidARS, String desc) {
        String sign = pPct >= 0 ? "+" : "−";
        String title = "🚨 ARBITRAJE — " + type + " " + sign + String.format("%.2f%%", Math.abs(pPct));
        String body  = desc + "\n"
            + "Comprar @ $" + Math.round(askARS) + " · Vender @ $" + Math.round(bidARS) + "\n"
            + "Ganancia: $" + Math.round(Math.abs(pARS)) + " ARS (U$D " + capital + " capital)";

        // Intent para abrir la app al tocar la notificación
        Intent openApp = new Intent(this, MainActivity.class);
        openApp.setFlags(Intent.FLAG_ACTIVITY_NEW_TASK | Intent.FLAG_ACTIVITY_CLEAR_TOP);
        PendingIntent pi = PendingIntent.getActivity(this, (int)System.currentTimeMillis(),
            openApp, PendingIntent.FLAG_IMMUTABLE | PendingIntent.FLAG_UPDATE_CURRENT);

        // Intent para abrir el exchange de compra
        String buyUrl = EX_URLS.getOrDefault(bId, "https://google.com");
        Intent buyIntent = new Intent(Intent.ACTION_VIEW, Uri.parse(buyUrl));
        PendingIntent buyPi = PendingIntent.getActivity(this, (int)System.currentTimeMillis() + 1,
            buyIntent, PendingIntent.FLAG_IMMUTABLE);

        // Intent para abrir el exchange de venta
        String sellUrl = EX_URLS.getOrDefault(sId, "https://google.com");
        Intent sellIntent = new Intent(Intent.ACTION_VIEW, Uri.parse(sellUrl));
        PendingIntent sellPi = PendingIntent.getActivity(this, (int)System.currentTimeMillis() + 2,
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

        int notifId = NOTIF_ALERT_BASE + Math.abs((bId + sId + type).hashCode() % 50);
        notifManager.notify(notifId, nb.build());
        Log.d(TAG, "ALERTA: " + title);
    }
}
