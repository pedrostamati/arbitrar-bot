package com.pedro.arbitrar;

import android.content.Context;
import android.webkit.JavascriptInterface;
import org.json.JSONObject;
import org.json.JSONArray;
import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.net.HttpURLConnection;
import java.net.URL;

/**
 * Bridge JS → Java
 * El WebView llama a estos métodos para obtener datos de las APIs
 * sin hacer fetches directos (que fallan por restricciones de seguridad)
 */
public class ArbitrARBridge {
    private final Context context;

    public ArbitrARBridge(Context context) {
        this.context = context;
    }

    @JavascriptInterface
    public String getPlatform() {
        return "android";
    }

    @JavascriptInterface
    public void log(String msg) {
        android.util.Log.d("ArbitrAR-JS", msg);
    }

    /**
     * Fetch desde Java (sin restricciones CORS/file://)
     * El WebView lo llama así:
     *   AndroidApp.fetchUrl("https://criptoya.com/api/usdt/ars/1")
     * y recibe el JSON como string
     */
    @JavascriptInterface
    public String fetchUrl(String urlStr) {
        try {
            URL url = new URL(urlStr);
            HttpURLConnection conn = (HttpURLConnection) url.openConnection();
            conn.setRequestMethod("GET");
            conn.setConnectTimeout(8000);
            conn.setReadTimeout(8000);
            conn.setRequestProperty("User-Agent", "ArbitrAR-Android/1.0");
            int code = conn.getResponseCode();
            if (code != 200) return null;
            BufferedReader br = new BufferedReader(
                new InputStreamReader(conn.getInputStream()));
            StringBuilder sb = new StringBuilder();
            String line;
            while ((line = br.readLine()) != null) sb.append(line);
            br.close();
            return sb.toString();
        } catch (Exception e) {
            android.util.Log.w("ArbitrAR-Bridge", "fetchUrl error: " + e.getMessage());
            return null;
        }
    }
}
