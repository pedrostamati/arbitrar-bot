package com.pedro.arbitrar;

import android.content.Context;
import android.webkit.JavascriptInterface;

/**
 * Bridge JS → Java para comunicación entre el WebView y el BotService
 */
public class ArbitrARBridge {
    private final Context context;

    public ArbitrARBridge(Context context) {
        this.context = context;
    }

    @JavascriptInterface
    public void log(String msg) {
        android.util.Log.d("ArbitrAR-JS", msg);
    }

    @JavascriptInterface
    public String getPlatform() {
        return "android";
    }
}
