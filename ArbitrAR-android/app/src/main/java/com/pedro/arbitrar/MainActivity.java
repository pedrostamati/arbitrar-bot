package com.pedro.arbitrar;

import android.Manifest;
import android.content.Intent;
import android.content.pm.PackageManager;
import android.net.Uri;
import android.os.Build;
import android.os.Bundle;
import android.webkit.WebChromeClient;
import android.webkit.WebResourceRequest;
import android.webkit.WebSettings;
import android.webkit.WebView;
import android.webkit.WebViewClient;
import androidx.appcompat.app.AppCompatActivity;
import androidx.core.app.ActivityCompat;
import androidx.core.content.ContextCompat;

public class MainActivity extends AppCompatActivity {

    private WebView webView;
    private static final int NOTIF_PERMISSION_CODE = 101;

    // Referencia estática para que BotService pueda inyectar datos
    public static MainActivity instance;

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        instance = this;
        setContentView(R.layout.activity_main);

        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.TIRAMISU) {
            if (ContextCompat.checkSelfPermission(this, Manifest.permission.POST_NOTIFICATIONS)
                    != PackageManager.PERMISSION_GRANTED) {
                ActivityCompat.requestPermissions(this,
                        new String[]{Manifest.permission.POST_NOTIFICATIONS},
                        NOTIF_PERMISSION_CODE);
            }
        }

        Intent serviceIntent = new Intent(this, BotService.class);
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
            startForegroundService(serviceIntent);
        } else {
            startService(serviceIntent);
        }

        webView = findViewById(R.id.webView);
        WebSettings settings = webView.getSettings();
        settings.setJavaScriptEnabled(true);
        settings.setDomStorageEnabled(true);
        settings.setAllowFileAccess(true);
        settings.setMixedContentMode(WebSettings.MIXED_CONTENT_ALWAYS_ALLOW);
        settings.setMediaPlaybackRequiresUserGesture(false);

        webView.addJavascriptInterface(new ArbitrARBridge(this), "AndroidApp");
        webView.setWebChromeClient(new WebChromeClient());
        webView.setWebViewClient(new WebViewClient() {
            @Override
            public boolean shouldOverrideUrlLoading(WebView view, WebResourceRequest request) {
                String url = request.getUrl().toString();
                if (!url.startsWith("file://") && !url.startsWith("about:")) {
                    startActivity(new Intent(Intent.ACTION_VIEW, Uri.parse(url)));
                    return true;
                }
                return false;
            }
        });

        webView.loadUrl("file:///android_asset/arbitraje.html");
    }

    /**
     * Inyecta datos JSON en el WebView desde BotService
     * BotService llama: MainActivity.instance.injectData(dolar, usdt, dai, btc)
     */
    public void injectData(String dolarJson, String usdtJson, String daiJson, String btcJson) {
        if (webView == null) return;
        final String d = dolarJson != null ? dolarJson.replace("'", "\'") : "null";
        final String u = usdtJson  != null ? usdtJson.replace("'", "\'")  : "null";
        final String da= daiJson   != null ? daiJson.replace("'", "\'")   : "null";
        final String b = btcJson   != null ? btcJson.replace("'", "\'")   : "null";
        final String js =
            "(function(){" +
            "try{" +
            "var dolar=" + (dolarJson!=null?dolarJson:"null") + ";" +
            "var usdt="  + (usdtJson!=null?usdtJson:"null")   + ";" +
            "var dai="   + (daiJson!=null?daiJson:"null")      + ";" +
            "var btc="   + (btcJson!=null?btcJson:"null")      + ";" +
            "if(window.receiveAndroidData){" +
            "  window.receiveAndroidData(dolar,usdt,dai,btc);" +
            "}" +
            "}catch(e){console.error('inject error:'+e);}" +
            "})()";
        runOnUiThread(() -> webView.evaluateJavascript(js, null));
    }

    @Override
    public void onBackPressed() {
        if (webView != null && webView.canGoBack()) {
            webView.goBack();
        } else {
            moveTaskToBack(true);
        }
    }

    @Override
    protected void onDestroy() {
        instance = null;
        super.onDestroy();
    }
}
