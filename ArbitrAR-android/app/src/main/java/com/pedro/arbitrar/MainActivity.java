package com.pedro.arbitrar;

import android.Manifest;
import android.annotation.SuppressLint;
import android.content.ActivityNotFoundException;
import android.content.ClipData;
import android.content.ClipboardManager;
import android.content.Context;
import android.content.Intent;
import android.content.pm.PackageInfo;
import android.content.pm.PackageManager;
import android.content.res.ColorStateList;
import android.graphics.Bitmap;
import android.graphics.Typeface;
import android.graphics.drawable.GradientDrawable;
import android.graphics.drawable.RippleDrawable;
import android.net.Uri;
import android.net.http.SslCertificate;
import android.net.http.SslError;
import android.os.Build;
import android.os.Bundle;
import android.os.Handler;
import android.os.Looper;
import android.os.SystemClock;
import android.text.TextUtils;
import android.util.Log;
import android.view.Gravity;
import android.view.MotionEvent;
import android.view.View;
import android.view.ViewGroup;
import android.webkit.ConsoleMessage;
import android.webkit.CookieManager;
import android.webkit.JavascriptInterface;
import android.webkit.RenderProcessGoneDetail;
import android.webkit.ServiceWorkerClient;
import android.webkit.ServiceWorkerController;
import android.webkit.SslErrorHandler;
import android.webkit.WebChromeClient;
import android.webkit.WebResourceError;
import android.webkit.WebResourceRequest;
import android.webkit.WebResourceResponse;
import android.webkit.WebSettings;
import android.webkit.WebView;
import android.webkit.WebViewClient;
import android.widget.FrameLayout;
import android.widget.LinearLayout;
import android.widget.ProgressBar;
import android.widget.ScrollView;
import android.widget.TextView;
import android.widget.Toast;

import androidx.appcompat.app.AppCompatActivity;
import androidx.core.app.ActivityCompat;
import androidx.core.content.ContextCompat;

import org.json.JSONObject;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.lang.reflect.Constructor;
import java.net.HttpURLConnection;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.text.SimpleDateFormat;
import java.util.ArrayDeque;
import java.util.Date;
import java.util.HashMap;
import java.util.Locale;
import java.util.Map;

/**
 * ArbitrAR — MainActivity, interfaz 5.3
 *
 * 5.3: window.ArbitrARNative.setBotConfig(json) reenvía a BotService el Capital y la Alerta %
 * elegidos en la interfaz. El resto es idéntico a 5.2.
 *
 * Compila solo, sin depender de otros archivos del proyecto: ArbitrARBridge y BotService se
 * cargan por nombre en tiempo de ejecución. Si falta alguno, la app arranca igual y lo informa
 * en el registro del panel.
 *
 * Por defecto funciona 100 % sin servidor (USE_HOSTING = false): la interfaz sale del APK y los
 * datos van directo de la app a CriptoYa, DolarAPI y Binance. El hosting queda como opción.
 *
 * Causa del WebView negro en v2–v4: shouldOverrideUrlLoading enviaba al navegador externo
 * toda URL que no fuera file://. InfinityFree responde primero con un desafío anti-bot
 * (testcookie-nginx-module / aes.js) que guarda una cookie y redirige con location.href.
 * Esa redirección salía de la app y el WebView quedaba clavado en la página del desafío, vacía.
 *
 * Esta versión:
 *  1. Deja navegar dentro del WebView todo fanatics.com.ar (incluida la redirección del anti-bot).
 *  2. Resuelve en Java las llamadas a proxy.php, CriptoYa, DolarAPI y Binance: sin CORS,
 *     sin anti-bot y sin gastar cuota del hosting. Si la vía nativa falla, la página sigue
 *     por su camino normal.
 *  3. Si el hosting no dibuja la interfaz, carga la copia de assets bajo un origen HTTPS
 *     virtual (nunca file://), con datos en vivo igual.
 *  4. Muestra un panel nativo de estado y registro: nunca más pantalla negra sin explicación.
 *     Tocar la pantalla con 3 dedos abre el panel en cualquier momento.
 *  5. Conserva la API que usa BotService: MainActivity.instance e injectData(...).
 *
 * No usa R.layout ni R.id: la interfaz se arma por código.
 */
public class MainActivity extends AppCompatActivity {

    private static final String TAG = "ArbitrAR-UI";
    private static final String UI_VERSION = "5.3";

    /**
     * false = 100 % sin servidor: la interfaz sale del APK y los datos van directo a las APIs.
     * true  = primero intenta la interfaz del hosting y, si falla, usa la del APK.
     */
    private static final boolean USE_HOSTING = false;

    // Página online: la misma que se ve en la PC
    private static final String OWN_DOMAIN = "fanatics.com.ar";
    private static final String REMOTE_URL = "https://fanatics.com.ar/ar/arbitraje.html";

    // Copia local servida bajo un origen HTTPS virtual (dominio reservado por Android para esto)
    private static final String LOCAL_HOST  = "appassets.androidplatform.net";
    private static final String LOCAL_ASSET = "arbitraje.html";
    private static final String LOCAL_URL   = "https://" + LOCAL_HOST + "/assets/" + LOCAL_ASSET;

    // Dominios cuyas llamadas GET resuelve la app en Java (incluye subdominios)
    private static final String[] API_DOMAINS = {
            "criptoya.com", "dolarapi.com", "binance.com", "binance.vision",
            "coingecko.com", "coinbase.com", "bluelytics.com.ar", "argentinadatos.com"
    };

    private static final long REMOTE_BUDGET_MS    = 15000;
    private static final long LOCAL_BUDGET_MS     = 10000;
    private static final long CHALLENGE_BUDGET_MS = 10000;
    private static final int  MAX_MAIN_NAVS       = 12;
    private static final int  MAX_RENDER_RESTARTS = 3;
    private static final int  LOG_MAX_LINES       = 400;
    private static final int  NOTIF_PERMISSION_CODE = 101;

    private static final int MODE_REMOTE = 0;
    private static final int MODE_LOCAL  = 1;

    private static final int MATCH = ViewGroup.LayoutParams.MATCH_PARENT;
    private static final int WRAP  = ViewGroup.LayoutParams.WRAP_CONTENT;

    // Paleta del panel nativo: tinta azulada, sin flash blanco antes de la UI oscura
    private static final int C_BG      = 0xFF0E1621;
    private static final int C_SURFACE = 0xFF172131;
    private static final int C_BORDER  = 0xFF26324A;
    private static final int C_TEXT    = 0xFFE8EDF3;
    private static final int C_MUTED   = 0xFF8D99AB;
    private static final int C_ACCENT  = 0xFF5B9CFF;
    private static final int C_ERROR   = 0xFFFF7A6E;

    // Sonda que distingue: desafío anti-bot, página vacía (error JS) o interfaz dibujada
    private static final String PROBE_JS =
            "(function(){try{"
            + "var b=document.body;"
            + "var t=b?String(b.innerText||'').replace(/\\s+/g,' ').trim():'';"
            + "var ch=!!document.querySelector('script[src*=\"aes.js\"],script[src*=\"aes.min.js\"]')"
            + "||typeof window.slowAES!=='undefined';"
            + "var ls=false;try{localStorage.setItem('__arb_probe','1');localStorage.removeItem('__arb_probe');ls=true;}catch(e){}"
            + "return {href:location.href,ready:document.readyState,text:t.length,"
            + "nodes:document.getElementsByTagName('*').length,challenge:ch,ls:ls,"
            + "bg:b?getComputedStyle(b).backgroundColor:''};"
            + "}catch(e){return {error:String(e)};}})()";

    private static final String PKG = MainActivity.class.getName()
            .substring(0, MainActivity.class.getName().lastIndexOf('.'));

    /** Extra del Intent con que se reenvía a BotService la configuración de la interfaz (mismo nombre allá). */
    private static final String BOT_CONFIG_EXTRA = "arbitrar.config";

    /** Usado por BotService para inyectar datos. No cambiar nombre ni firma. */
    public static MainActivity instance;

    private final Handler ui = new Handler(Looper.getMainLooper());
    private final long bootAt = SystemClock.elapsedRealtime();
    private final ArrayDeque<String> logLines = new ArrayDeque<>();
    private final Map<String, Integer> apiLastCode = new HashMap<>();
    private final Map<String, long[]> apiBreaker = new HashMap<>(); // host -> {fallos seguidos, pausado hasta}

    private FrameLayout root;
    private FrameLayout overlay;
    private WebView webView;
    private ProgressBar spinner;
    private TextView statusView;
    private TextView infoView;
    private TextView logView;
    private ScrollView logScroll;
    private LinearLayout actionsView;

    private volatile int mode = MODE_REMOTE;
    private volatile String userAgent;
    private int loadSeq = 0;
    private int navSeq = 0;
    private int probesNav = -1;
    private int mainNavs = 0;
    private int renderRestarts = 0;
    private long challengeSince = 0;
    private boolean pageReady = false;
    private boolean overlayShown = true;
    private boolean errorPanel = false;
    private boolean started = false;
    private boolean localAvailable = false;
    private boolean remoteFailed = false;
    private boolean logRefreshQueued = false;
    private String lastFailure = "ninguno";
    private String infoLine = "";

    // ───────────────────────────── Ciclo de vida ─────────────────────────────

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        instance = this;
        buildUi();
        logEnvironment();
        requestNotificationPermission();
        startBotService();
        localAvailable = assetExists(LOCAL_ASSET);
        log("Copia local en assets: " + (localAvailable ? "sí" : "no"));
        installServiceWorkerInterceptor();
        if (createWebView()) {
            loadMode(USE_HOSTING ? MODE_REMOTE : MODE_LOCAL, "inicio");
        }
    }

    @Override
    protected void onStart() {
        super.onStart();
        started = true;
        if (webView != null) webView.resumeTimers();
    }

    @Override
    protected void onResume() {
        super.onResume();
        instance = this;
        if (webView != null) webView.onResume();
    }

    @Override
    protected void onPause() {
        if (webView != null) webView.onPause();
        if (Build.VERSION.SDK_INT >= 21) CookieManager.getInstance().flush();
        super.onPause();
    }

    @Override
    protected void onStop() {
        started = false;
        // El monitoreo en segundo plano lo hace BotService; la interfaz no necesita correr oculta.
        if (webView != null) webView.pauseTimers();
        super.onStop();
    }

    @Override
    protected void onDestroy() {
        if (instance == this) instance = null;
        ui.removeCallbacksAndMessages(null);
        if (webView != null) {
            webView.stopLoading();
            root.removeView(webView);
            webView.destroy();
            webView = null;
        }
        super.onDestroy();
    }

    @Override
    public void onBackPressed() {
        if (overlayShown && pageReady) {
            hideOverlay();
            return;
        }
        if (webView != null && webView.canGoBack()) {
            webView.goBack();
            return;
        }
        moveTaskToBack(true);
    }

    // ───────────────────────────── Interfaz nativa ─────────────────────────────

    private void buildUi() {
        styleSystemBars();
        root = new FrameLayout(this);
        root.setBackgroundColor(C_BG);
        root.setFitsSystemWindows(true);
        setContentView(root);
        overlay = buildOverlay();
        root.addView(overlay, new FrameLayout.LayoutParams(MATCH, MATCH));
    }

    @SuppressWarnings("deprecation")
    private void styleSystemBars() {
        try {
            if (Build.VERSION.SDK_INT >= 21) {
                getWindow().setStatusBarColor(C_BG);
                getWindow().setNavigationBarColor(C_BG);
            }
            if (Build.VERSION.SDK_INT >= 23) {
                View decor = getWindow().getDecorView();
                int flags = decor.getSystemUiVisibility();
                flags &= ~View.SYSTEM_UI_FLAG_LIGHT_STATUS_BAR;
                if (Build.VERSION.SDK_INT >= 26) flags &= ~View.SYSTEM_UI_FLAG_LIGHT_NAVIGATION_BAR;
                decor.setSystemUiVisibility(flags);
            }
        } catch (Throwable ignored) {
            // Solo estética: nunca debe impedir que la app arranque
        }
    }

    private FrameLayout buildOverlay() {
        FrameLayout frame = new FrameLayout(this);
        frame.setBackgroundColor(C_BG);
        frame.setClickable(true); // mientras está visible, los toques no llegan al WebView

        LinearLayout col = new LinearLayout(this);
        col.setOrientation(LinearLayout.VERTICAL);
        col.setPadding(dp(22), dp(30), dp(22), dp(16));

        TextView title = label("ArbitrAR", 26, C_TEXT, Typeface.DEFAULT_BOLD);
        infoView = label("", 12, C_MUTED, Typeface.DEFAULT);
        infoView.setPadding(0, dp(4), 0, 0);

        LinearLayout statusRow = new LinearLayout(this);
        statusRow.setOrientation(LinearLayout.HORIZONTAL);
        statusRow.setGravity(Gravity.CENTER_VERTICAL);
        statusRow.setPadding(0, dp(22), 0, dp(14));
        spinner = new ProgressBar(this);
        spinner.setIndeterminate(true);
        if (Build.VERSION.SDK_INT >= 21) spinner.setIndeterminateTintList(ColorStateList.valueOf(C_ACCENT));
        LinearLayout.LayoutParams spinnerLp = new LinearLayout.LayoutParams(dp(20), dp(20));
        spinnerLp.rightMargin = dp(12);
        statusRow.addView(spinner, spinnerLp);
        statusView = label("Iniciando", 15, C_TEXT, Typeface.DEFAULT);
        statusRow.addView(statusView, new LinearLayout.LayoutParams(0, WRAP, 1f));

        actionsView = new LinearLayout(this);
        actionsView.setOrientation(LinearLayout.VERTICAL);
        actionsView.setVisibility(View.GONE);
        actionsView.addView(row(
                button("Probar el hosting", v -> {
                    remoteFailed = false;
                    loadMode(MODE_REMOTE, "manual");
                }),
                button("Usar sin servidor", v -> loadMode(MODE_LOCAL, "manual"))));
        actionsView.addView(row(
                button("Copiar diagnóstico", v -> copyDiagnostics()),
                button("Abrir en el navegador", v -> openExternal(Uri.parse(REMOTE_URL)))));
        actionsView.addView(row(
                button("Borrar caché y cookies", v -> resetWebData()),
                button("Ocultar panel", v -> hideOverlay())));

        TextView logTitle = label("Registro", 13, C_MUTED, Typeface.DEFAULT_BOLD);
        logTitle.setPadding(0, dp(10), 0, dp(6));

        logScroll = new ScrollView(this);
        logView = label("", 11, C_MUTED, Typeface.MONOSPACE);
        logView.setTextIsSelectable(true);
        logScroll.addView(logView);

        col.addView(title);
        col.addView(infoView);
        col.addView(statusRow);
        col.addView(actionsView);
        col.addView(logTitle);
        col.addView(logScroll, new LinearLayout.LayoutParams(MATCH, 0, 1f));
        frame.addView(col, new FrameLayout.LayoutParams(MATCH, MATCH));
        return frame;
    }

    private TextView label(String text, float sizeSp, int color, Typeface typeface) {
        TextView t = new TextView(this);
        t.setText(text);
        t.setTextSize(sizeSp);
        t.setTextColor(color);
        t.setTypeface(typeface);
        t.setLineSpacing(0f, 1.15f);
        return t;
    }

    private TextView button(String text, View.OnClickListener onClick) {
        TextView b = label(text, 13, C_TEXT, Typeface.DEFAULT_BOLD);
        b.setGravity(Gravity.CENTER);
        b.setPadding(dp(8), dp(12), dp(8), dp(12));
        GradientDrawable shape = new GradientDrawable();
        shape.setColor(C_SURFACE);
        shape.setCornerRadius(dp(10));
        shape.setStroke(dp(1), C_BORDER);
        if (Build.VERSION.SDK_INT >= 21) {
            b.setBackground(new RippleDrawable(ColorStateList.valueOf(0x33FFFFFF), shape, null));
        } else {
            b.setBackground(shape);
        }
        b.setClickable(true);
        b.setFocusable(true);
        b.setOnClickListener(onClick);
        return b;
    }

    private LinearLayout row(View left, View right) {
        LinearLayout r = new LinearLayout(this);
        r.setOrientation(LinearLayout.HORIZONTAL);
        r.setPadding(0, 0, 0, dp(10));
        LinearLayout.LayoutParams lp = new LinearLayout.LayoutParams(0, WRAP, 1f);
        lp.rightMargin = dp(5);
        LinearLayout.LayoutParams rp = new LinearLayout.LayoutParams(0, WRAP, 1f);
        rp.leftMargin = dp(5);
        r.addView(left, lp);
        r.addView(right, rp);
        return r;
    }

    private void showOverlay(boolean withActions) {
        overlayShown = true;
        errorPanel = withActions;
        overlay.animate().cancel();
        overlay.setAlpha(1f);
        overlay.setVisibility(View.VISIBLE);
        overlay.bringToFront();
        spinner.setVisibility(withActions ? View.GONE : View.VISIBLE);
        actionsView.setVisibility(withActions ? View.VISIBLE : View.GONE);
        refreshLog();
    }

    private void hideOverlay() {
        overlayShown = false;
        errorPanel = false;
        overlay.animate().alpha(0f).setDuration(200).withEndAction(() -> {
            if (!overlayShown) overlay.setVisibility(View.GONE);
        }).start();
    }

    private void showDiagnostics() {
        showOverlay(true);
        setStatus(pageReady
                ? "La interfaz está funcionando (" + modeName() + ")."
                : "Último fallo: " + lastFailure, false);
    }

    private void setStatus(final String text, final boolean isError) {
        ui.post(() -> {
            if (statusView == null) return;
            statusView.setText(text);
            statusView.setTextColor(isError ? C_ERROR : C_TEXT);
        });
    }

    private void setLoadingStatus(String text) {
        if (!pageReady && !errorPanel) setStatus(text, false);
    }

    private void toast(final String message) {
        ui.post(() -> Toast.makeText(this, message, Toast.LENGTH_LONG).show());
    }

    private int dp(float v) {
        return Math.round(v * getResources().getDisplayMetrics().density);
    }

    // ───────────────────────────── WebView ─────────────────────────────

    @SuppressLint({"SetJavaScriptEnabled", "AddJavascriptInterface", "ClickableViewAccessibility"})
    private boolean createWebView() {
        try {
            if (Build.VERSION.SDK_INT >= 19) WebView.setWebContentsDebuggingEnabled(true);
            WebView wv = new WebView(this);
            wv.setBackgroundColor(C_BG);
            wv.resumeTimers(); // por si quedó activo un pauseTimers() global de una instancia anterior

            WebSettings s = wv.getSettings();
            s.setJavaScriptEnabled(true);
            s.setDomStorageEnabled(true);
            s.setCacheMode(WebSettings.LOAD_DEFAULT);
            s.setLoadWithOverviewMode(true);
            s.setUseWideViewPort(true);
            s.setSupportZoom(false);
            s.setBuiltInZoomControls(false);
            s.setDisplayZoomControls(false);
            s.setTextZoom(100);
            s.setMediaPlaybackRequiresUserGesture(false);
            s.setSupportMultipleWindows(false);
            s.setJavaScriptCanOpenWindowsAutomatically(false);
            s.setAllowFileAccess(false);
            s.setAllowContentAccess(false);
            if (Build.VERSION.SDK_INT >= 21) {
                s.setMixedContentMode(WebSettings.MIXED_CONTENT_COMPATIBILITY_MODE);
            }
            userAgent = s.getUserAgentString();

            CookieManager cookies = CookieManager.getInstance();
            cookies.setAcceptCookie(true); // imprescindible para la cookie del anti-bot
            if (Build.VERSION.SDK_INT >= 21) cookies.setAcceptThirdPartyCookies(wv, true);

            wv.addJavascriptInterface(createLegacyBridge(), "AndroidApp"); // bridge histórico
            wv.addJavascriptInterface(new NativeBridge(), "ArbitrARNative");
            wv.setWebViewClient(new Client());
            wv.setWebChromeClient(new Chrome());
            wv.setOnTouchListener((v, ev) -> {
                if (ev.getActionMasked() == MotionEvent.ACTION_POINTER_DOWN && ev.getPointerCount() >= 3) {
                    ui.post(this::showDiagnostics);
                }
                return false; // el WebView sigue recibiendo todos los toques
            });

            root.addView(wv, 0, new FrameLayout.LayoutParams(MATCH, MATCH));
            webView = wv;
            log("WebView creado");
            return true;
        } catch (Throwable t) {
            log("No se pudo crear el WebView: " + t);
            lastFailure = "WebView no disponible: " + t.getClass().getSimpleName();
            showOverlay(true);
            setStatus("Android no pudo crear el WebView. Actualizá «Android System WebView» y "
                    + "«Chrome» desde Play Store y volvé a abrir la app.", true);
            return false;
        }
    }

    private void loadMode(int newMode, String reason) {
        if (webView == null && !createWebView()) return;
        mode = newMode;
        loadSeq++;
        navSeq++;
        mainNavs = 0;
        challengeSince = 0;
        pageReady = false;
        final int seq = loadSeq;
        // El parámetro evita que el WebView muestre una versión vieja cacheada del HTML
        String url = newMode == MODE_LOCAL ? LOCAL_URL : REMOTE_URL + "?app=" + System.currentTimeMillis();
        log("Cargando " + modeName() + " (" + reason + "): " + shortUrl(url));
        showOverlay(false);
        setStatus(newMode == MODE_LOCAL ? "Cargando la interfaz" : "Conectando con " + OWN_DOMAIN, false);
        webView.stopLoading();
        webView.loadUrl(url);
        armWatchdog(seq, newMode == MODE_LOCAL ? LOCAL_BUDGET_MS : REMOTE_BUDGET_MS);
    }

    /** Plazo para que la interfaz se dibuje. Solo descuenta tiempo con la app en pantalla. */
    private void armWatchdog(final int seq, final long budgetMs) {
        ui.postDelayed(new Runnable() {
            private long left = budgetMs;

            @Override
            public void run() {
                if (seq != loadSeq || pageReady) return;
                if (started) left -= 1000;
                if (left <= 0) {
                    failLoad(seq, (mode == MODE_LOCAL ? "La interfaz del APK" : "El hosting")
                            + " no dibujó la interfaz en " + (budgetMs / 1000) + " s.", false);
                    return;
                }
                ui.postDelayed(this, 1000);
            }
        }, 1000);
    }

    private void startProbes(final int seq, final int nav) {
        if (pageReady || probesNav == nav) return;
        probesNav = nav;
        final long[] waits = {500, 1000, 1500, 2500, 4000};
        ui.postDelayed(new Runnable() {
            private int i = 0;

            @Override
            public void run() {
                if (seq != loadSeq || nav != navSeq || pageReady || webView == null) return;
                if (!started) {
                    ui.postDelayed(this, 1000);
                    return;
                }
                final boolean last = (i == waits.length - 1);
                webView.evaluateJavascript(PROBE_JS, value -> onProbe(seq, nav, last, value));
                if (!last) {
                    i++;
                    ui.postDelayed(this, waits[i]);
                }
            }
        }, waits[0]);
    }

    private void onProbe(int seq, int nav, boolean last, String value) {
        if (seq != loadSeq || nav != navSeq || pageReady) return;
        JSONObject o;
        try {
            o = new JSONObject(value);
        } catch (Exception e) {
            log("Sonda sin resultado: " + value);
            if (last) failLoad(seq, "La página no respondió a la verificación interna.", false);
            return;
        }
        if (o.has("error")) {
            log("Sonda con error: " + o.optString("error"));
            return;
        }
        boolean challenge = o.optBoolean("challenge");
        int text = o.optInt("text");
        int nodes = o.optInt("nodes");
        log("Sonda: texto=" + text + " nodos=" + nodes + " antibot=" + (challenge ? "sí" : "no")
                + " storage=" + (o.optBoolean("ls") ? "ok" : "NO") + " estado=" + o.optString("ready")
                + " fondo=" + o.optString("bg") + " url=" + shortUrl(o.optString("href")));
        if (challenge) {
            long now = SystemClock.elapsedRealtime();
            if (challengeSince == 0) challengeSince = now;
            setLoadingStatus("Pasando la verificación anti-bot del hosting");
            if (now - challengeSince > CHALLENGE_BUDGET_MS) {
                failLoad(seq, "La verificación anti-bot del hosting no terminó.", false);
            }
            return;
        }
        if (text >= 20 || nodes >= 40) {
            markReady();
            return;
        }
        if (last) {
            failLoad(seq, "La página cargó pero no dibujó nada (" + nodes + " nodos). Hay un error de "
                    + "JavaScript: el detalle está en las líneas «JS ERROR» del registro.", false);
        }
    }

    private void markReady() {
        if (pageReady) return;
        pageReady = true;
        lastFailure = "ninguno";
        log("Interfaz lista (" + modeName() + ")");
        setStatus("Interfaz lista", false);
        if (webView != null) webView.clearHistory(); // que «atrás» no vuelva a la página del anti-bot
        hideOverlay();
        if (mode == MODE_LOCAL && remoteFailed) {
            toast("El hosting no respondió: la app sigue sin servidor, con datos en vivo");
        }
    }

    /**
     * @param evenIfReady true solo para errores reales del documento principal (red, HTTP, SSL).
     *                    Los vencimientos de plazo o sondas se ignoran si la interfaz ya está lista.
     */
    private void failLoad(final int seq, final String reason, final boolean evenIfReady) {
        ui.post(() -> {
            if (seq != loadSeq) return;
            if (pageReady && !evenIfReady) return;
            lastFailure = reason;
            log("FALLO: " + reason);
            if (mode == MODE_REMOTE && !pageReady && localAvailable) {
                remoteFailed = true;
                loadMode(MODE_LOCAL, "respaldo");
                return;
            }
            pageReady = false;
            showOverlay(true);
            setStatus(reason, true);
        });
    }

    private boolean isCurrentDocument(Uri u) {
        String host = lower(u.getHost());
        return mode == MODE_LOCAL ? LOCAL_HOST.equals(host) : isOwnHost(host);
    }

    private String modeName() {
        return mode == MODE_LOCAL ? "sin servidor" : "desde el hosting";
    }

    /** Decide qué navegaciones quedan dentro del WebView y cuáles se abren afuera. */
    private boolean route(WebView view, Uri uri, boolean mainFrame) {
        String scheme = lower(uri.getScheme());
        String host = lower(uri.getHost());
        if (scheme.isEmpty() || scheme.equals("about") || scheme.equals("data")
                || scheme.equals("blob") || scheme.equals("javascript")) {
            return false;
        }
        boolean web = scheme.equals("https") || scheme.equals("http");
        if (web && LOCAL_HOST.equals(host)) return false;
        if (web && isOwnHost(host)) {
            if (scheme.equals("http")) {
                String https = uri.buildUpon().scheme("https").build().toString();
                log("Redirección http a https: " + shortUrl(https));
                view.loadUrl(https);
                return true;
            }
            return false; // incluye la redirección del anti-bot (&i=1): se queda en el WebView
        }
        if (!mainFrame) return false; // iframes de widgets navegan dentro de su marco
        openExternal(uri);              // exchanges, Telegram, mailto, intent://, etc.
        return true;
    }

    private void openExternal(Uri uri) {
        try {
            if ("intent".equals(lower(uri.getScheme()))) {
                Intent it = Intent.parseUri(uri.toString(), Intent.URI_INTENT_SCHEME);
                it.addCategory(Intent.CATEGORY_BROWSABLE);
                it.setComponent(null);
                if (Build.VERSION.SDK_INT >= 15) it.setSelector(null);
                try {
                    startActivity(it);
                    return;
                } catch (ActivityNotFoundException e) {
                    String fallback = it.getStringExtra("browser_fallback_url");
                    if (!TextUtils.isEmpty(fallback)) {
                        startActivity(new Intent(Intent.ACTION_VIEW, Uri.parse(fallback)));
                        return;
                    }
                    String pkg = it.getPackage();
                    if (!TextUtils.isEmpty(pkg)) {
                        startActivity(new Intent(Intent.ACTION_VIEW, Uri.parse("market://details?id=" + pkg)));
                        return;
                    }
                    throw e;
                }
            }
            Intent view = new Intent(Intent.ACTION_VIEW, uri);
            view.addCategory(Intent.CATEGORY_BROWSABLE);
            startActivity(view);
            log("Abierto afuera: " + shortUrl(uri.toString()));
        } catch (Exception e) {
            log("No se pudo abrir " + shortUrl(uri.toString()) + ": " + e.getMessage());
            toast("No hay una app instalada para abrir ese enlace");
        }
    }

    private void resetWebData() {
        log("Borrando caché y cookies del WebView");
        if (webView != null) webView.clearCache(true);
        if (Build.VERSION.SDK_INT >= 21) {
            CookieManager.getInstance().removeAllCookies(removed -> {
                CookieManager.getInstance().flush();
                log("Cookies borradas: " + removed);
                remoteFailed = false;
                loadMode(MODE_REMOTE, "reset");
            });
        } else {
            remoteFailed = false;
            loadMode(MODE_REMOTE, "reset");
        }
    }

    // ───────────────────────────── Clientes del WebView ─────────────────────────────

    private final class Client extends WebViewClient {

        @Override
        public boolean shouldOverrideUrlLoading(WebView view, WebResourceRequest request) {
            return route(view, request.getUrl(), request.isForMainFrame());
        }

        @SuppressWarnings("deprecation")
        @Override
        public boolean shouldOverrideUrlLoading(WebView view, String url) {
            return route(view, Uri.parse(url), true);
        }

        @Override
        public WebResourceResponse shouldInterceptRequest(WebView view, WebResourceRequest request) {
            try {
                return intercept(request);
            } catch (Throwable t) {
                log("Interceptor: " + t);
                return null;
            }
        }

        @Override
        public void onPageStarted(WebView view, String url, Bitmap favicon) {
            navSeq++;
            mainNavs++;
            log("Inicio: " + shortUrl(url));
            setLoadingStatus("Cargando la interfaz");
            if (mainNavs > MAX_MAIN_NAVS && !pageReady) {
                failLoad(loadSeq, "El hosting redirige en bucle (" + mainNavs + " veces): "
                        + "la verificación anti-bot no se completa.", false);
            }
        }

        @Override
        public void onPageCommitVisible(WebView view, String url) {
            startProbes(loadSeq, navSeq);
        }

        @Override
        public void onPageFinished(WebView view, String url) {
            log("Fin: " + shortUrl(url));
            if (Build.VERSION.SDK_INT >= 21) CookieManager.getInstance().flush();
            startProbes(loadSeq, navSeq);
        }

        @Override
        public void onReceivedError(WebView view, WebResourceRequest request, WebResourceError error) {
            String desc = String.valueOf(error.getDescription());
            log("Error de red " + error.getErrorCode() + " " + desc + ": " + shortUrl(request.getUrl().toString()));
            if (!request.isForMainFrame() || desc.contains("ERR_ABORTED") || !isCurrentDocument(request.getUrl())) {
                return;
            }
            failLoad(loadSeq, "No se pudo cargar la página: " + desc + ".", true);
        }

        @SuppressWarnings("deprecation")
        @Override
        public void onReceivedError(WebView view, int errorCode, String description, String failingUrl) {
            if (Build.VERSION.SDK_INT >= 23) return; // en Android 6+ lo maneja el método de arriba
            log("Error de red " + errorCode + " " + description + ": " + shortUrl(failingUrl));
            if (failingUrl != null && isCurrentDocument(Uri.parse(failingUrl))) {
                failLoad(loadSeq, "No se pudo cargar la página: " + description + ".", true);
            }
        }

        @Override
        public void onReceivedHttpError(WebView view, WebResourceRequest request, WebResourceResponse response) {
            int code = response.getStatusCode();
            log("HTTP " + code + " " + response.getReasonPhrase() + ": " + shortUrl(request.getUrl().toString()));
            if (request.isForMainFrame() && code >= 400 && isCurrentDocument(request.getUrl())) {
                failLoad(loadSeq, "El hosting respondió HTTP " + code + " " + response.getReasonPhrase() + ".", true);
            }
        }

        @Override
        public void onReceivedSslError(WebView view, SslErrorHandler handler, SslError error) {
            handler.cancel(); // nunca se acepta un certificado inválido
            String detail = describeSsl(error);
            log("SSL rechazado: " + detail);
            String url = error.getUrl();
            if (url != null && isCurrentDocument(Uri.parse(url))) {
                failLoad(loadSeq, "Android rechazó el certificado SSL del hosting: " + detail + ".", true);
            }
        }

        @Override
        public boolean onRenderProcessGone(WebView view, RenderProcessGoneDetail detail) {
            boolean crashed = Build.VERSION.SDK_INT >= 26 && detail.didCrash();
            log("El motor del WebView se cerró (crash=" + crashed + ")");
            boolean current = (view == webView);
            if (current) webView = null;
            try {
                root.removeView(view);
                view.destroy();
            } catch (Throwable ignored) {
                // la instancia ya no sirve; se reemplaza abajo
            }
            if (!current) return true;
            renderRestarts++;
            if (renderRestarts <= MAX_RENDER_RESTARTS) {
                ui.post(() -> {
                    if (createWebView()) loadMode(mode, "reinicio del motor");
                });
            } else {
                lastFailure = "El motor del WebView se cerró " + renderRestarts + " veces";
                showOverlay(true);
                setStatus("El motor del WebView se cerró varias veces seguidas. Actualizá "
                        + "«Android System WebView» desde Play Store.", true);
            }
            return true; // la app sigue viva
        }
    }

    private final class Chrome extends WebChromeClient {

        @Override
        public boolean onConsoleMessage(ConsoleMessage m) {
            ConsoleMessage.MessageLevel level = m.messageLevel();
            if (level == ConsoleMessage.MessageLevel.ERROR || level == ConsoleMessage.MessageLevel.WARNING) {
                log("JS " + level.name() + ": " + m.message() + " (" + shortUrl(m.sourceId()) + ":" + m.lineNumber() + ")");
            }
            return true;
        }

        @Override
        public void onProgressChanged(WebView view, int newProgress) {
            if (newProgress < 100) {
                setLoadingStatus("Cargando la interfaz (" + newProgress + " %)");
            }
        }
    }

    /**
     * Bridge «AndroidApp» que ya usaba el HTML. Si ArbitrARBridge.java existe se usa ese (por
     * reflexión, para no depender de él al compilar); si no, uno interno con la misma API conocida.
     */
    private Object createLegacyBridge() {
        try {
            Class<?> cls = Class.forName(PKG + ".ArbitrARBridge");
            for (Constructor<?> k : cls.getConstructors()) {
                Class<?>[] params = k.getParameterTypes();
                if (params.length == 1 && params[0].isAssignableFrom(MainActivity.class)) {
                    log("Bridge AndroidApp: ArbitrARBridge del proyecto");
                    return k.newInstance(this);
                }
            }
        } catch (Throwable ignored) {
            // no existe o no se pudo crear: se usa el interno
        }
        log("Bridge AndroidApp: versión interna");
        return new LegacyBridge();
    }

    /** Misma API que ArbitrARBridge: getPlatform(), log(msg) y fetchUrl(url). */
    public final class LegacyBridge {
        @JavascriptInterface
        public String getPlatform() {
            return "android";
        }

        @JavascriptInterface
        public void log(String message) {
            MainActivity.this.log("JS: " + message);
        }

        /** GET sincrónico (corre en el hilo del bridge, no en el de la interfaz). */
        @JavascriptInterface
        public String fetchUrl(String url) {
            if (url == null || !isAllowedApi(url)) return "";
            HttpURLConnection c = null;
            try {
                c = (HttpURLConnection) new URL(url).openConnection();
                c.setConnectTimeout(8000);
                c.setReadTimeout(10000);
                c.setUseCaches(false);
                c.setRequestProperty("Accept", "application/json, text/plain, */*");
                String ua = userAgent;
                if (ua != null) c.setRequestProperty("User-Agent", ua);
                int code = c.getResponseCode();
                if (code < 200 || code >= 300) {
                    readAll(c.getErrorStream());
                    return "";
                }
                return new String(readAll(c.getInputStream()), StandardCharsets.UTF_8);
            } catch (Exception e) {
                MainActivity.this.log("fetchUrl falló: " + shortUrl(url) + ": " + e.getClass().getSimpleName());
                return "";
            } finally {
                if (c != null) c.disconnect();
            }
        }
    }

    /** Métodos disponibles desde el HTML como window.ArbitrARNative. */
    public final class NativeBridge {
        @JavascriptInterface
        public String version() {
            return UI_VERSION;
        }

        @JavascriptInterface
        public String mode() {
            return modeName();
        }

        @JavascriptInterface
        public void showDiagnostics() {
            ui.post(MainActivity.this::showDiagnostics);
        }

        @JavascriptInterface
        public void log(String message) {
            MainActivity.this.log("JS: " + message);
        }

        /**
         * Capital y umbral de alerta elegidos en la interfaz, como JSON: {"capital":1000,"alertPct":0.5}.
         * Se reenvían a BotService, que los valida, los usa desde su próximo ciclo y los conserva.
         */
        @JavascriptInterface
        public void setBotConfig(String json) {
            if (json == null || json.length() > 200) return;
            final String config = json;
            ui.post(() -> MainActivity.this.sendBotConfig(config));
        }
    }

    // ───────────────────────────── Datos: resolución nativa ─────────────────────────────

    /** Las peticiones de Service Workers no pasan por WebViewClient: se interceptan acá también. */
    private void installServiceWorkerInterceptor() {
        if (Build.VERSION.SDK_INT < 24) return;
        try {
            ServiceWorkerController.getInstance().setServiceWorkerClient(new ServiceWorkerClient() {
                @Override
                public WebResourceResponse shouldInterceptRequest(WebResourceRequest request) {
                    try {
                        return intercept(request);
                    } catch (Throwable t) {
                        return null;
                    }
                }
            });
        } catch (Throwable t) {
            log("Service Worker: interceptor no disponible (" + t.getClass().getSimpleName() + ")");
        }
    }

    /** Corre en un hilo de red del WebView, nunca en el hilo de la interfaz. */
    private WebResourceResponse intercept(WebResourceRequest req) {
        Uri u = req.getUrl();
        String host = lower(u.getHost());
        if (LOCAL_HOST.equals(host)) return serveAsset(u.getPath());

        String method = req.getMethod() == null ? "GET" : req.getMethod().toUpperCase(Locale.US);
        String path = u.getPath() == null ? "" : u.getPath();
        String target = null;
        String via = null;
        if (isOwnHost(host) && path.endsWith("/proxy.php")) {
            target = u.getQueryParameter("url"); // mismo contrato que ar/proxy.php
            via = "proxy";
        } else if (host.equals("corsproxy.io")) { // versiones viejas del HTML
            target = u.getQueryParameter("url");
            if (target == null && u.getEncodedQuery() != null) target = Uri.decode(u.getEncodedQuery());
            via = "corsproxy";
        } else if (host.equals("api.allorigins.win") && path.startsWith("/raw")) {
            target = u.getQueryParameter("url");
            via = "allorigins";
        } else if (isApiHost(host) && "https".equals(lower(u.getScheme()))) {
            target = u.toString();
            via = "directo";
        }
        if (target == null || !isAllowedApi(target)) return null;
        if ("OPTIONS".equals(method)) return preflight();
        if (!"GET".equals(method)) return null;
        WebResourceResponse r = nativeGet(target, via);
        if (r == null && mode == MODE_LOCAL && !"directo".equals(via)) {
            // Sin servidor: no se cae al proxy del hosting (otro origen, anti-bot y SSL). Un 502 sin
            // cuerpo hace que la página trate el ciclo como fallido y reintente en el próximo.
            return emptyError(502, "Bad Gateway");
        }
        return r;
    }

    private WebResourceResponse emptyError(int code, String reason) {
        Map<String, String> h = new HashMap<>();
        h.put("Access-Control-Allow-Origin", "*");
        h.put("Cache-Control", "no-store");
        return new WebResourceResponse("application/json", "utf-8", code, reason, h,
                new ByteArrayInputStream(new byte[0]));
    }

    private WebResourceResponse nativeGet(String target, String via) {
        String host = lower(Uri.parse(target).getHost());
        long start = SystemClock.elapsedRealtime();
        synchronized (apiBreaker) {
            long[] b = apiBreaker.get(host);
            if (b != null && b[1] > start) return null; // vía nativa en pausa: la página usa su camino normal
        }
        HttpURLConnection c = null;
        try {
            c = (HttpURLConnection) new URL(target).openConnection();
            c.setConnectTimeout(8000);
            c.setReadTimeout(10000);
            c.setUseCaches(false);
            c.setInstanceFollowRedirects(true);
            c.setRequestProperty("Accept", "application/json, text/plain, */*");
            String ua = userAgent;
            if (ua != null) c.setRequestProperty("User-Agent", ua);
            int code = c.getResponseCode();
            if (code < 200 || code >= 300) {
                readAll(c.getErrorStream());
                throw new IOException("HTTP " + code);
            }
            byte[] body = readAll(c.getInputStream());
            String[] type = splitContentType(c.getContentType());
            String reason = c.getResponseMessage();
            if (TextUtils.isEmpty(reason)) reason = "OK";
            noteApi(target, via, code, body.length, SystemClock.elapsedRealtime() - start);
            synchronized (apiBreaker) {
                apiBreaker.remove(host);
            }
            Map<String, String> headers = new HashMap<>();
            headers.put("Access-Control-Allow-Origin", "*");
            headers.put("Cache-Control", "no-store");
            headers.put("X-ArbitrAR-Native", via);
            return new WebResourceResponse(type[0], type[1], code, reason, headers, new ByteArrayInputStream(body));
        } catch (Exception e) {
            noteApiFailure(host, target, via, e);
            return null; // la página sigue por su camino normal (proxy.php o red directa)
        } finally {
            if (c != null) c.disconnect();
        }
    }

    private void noteApi(String target, String via, int code, int bytes, long ms) {
        boolean changed;
        synchronized (apiLastCode) {
            Integer prev = apiLastCode.put(target, code);
            changed = prev == null || prev != code;
        }
        if (changed || ms > 3000) {
            log("API " + code + " vía app (" + via + "): " + shortUrl(target) + ", " + bytes + " B, " + ms + " ms");
        }
    }

    private void noteApiFailure(String host, String target, String via, Exception e) {
        long now = SystemClock.elapsedRealtime();
        boolean paused = false;
        synchronized (apiBreaker) {
            long[] b = apiBreaker.get(host);
            if (b == null) {
                b = new long[]{0, 0};
                apiBreaker.put(host, b);
            }
            b[0]++;
            if (b[0] >= 3) {
                b[0] = 0;
                b[1] = now + 60000;
                paused = true;
            }
        }
        synchronized (apiLastCode) {
            apiLastCode.remove(target);
        }
        log("API falló vía app (" + via + "): " + shortUrl(target) + ": " + e.getClass().getSimpleName()
                + " " + e.getMessage() + (paused ? ". Vía app en pausa 60 s para " + host : ""));
    }

    private WebResourceResponse preflight() {
        Map<String, String> h = new HashMap<>();
        h.put("Access-Control-Allow-Origin", "*");
        h.put("Access-Control-Allow-Methods", "GET, OPTIONS");
        h.put("Access-Control-Allow-Headers", "*");
        h.put("Access-Control-Max-Age", "600");
        return new WebResourceResponse("text/plain", "utf-8", 204, "No Content", h,
                new ByteArrayInputStream(new byte[0]));
    }

    private WebResourceResponse serveAsset(String path) {
        String p = path == null ? "" : path;
        if (p.startsWith("/assets/")) {
            p = p.substring("/assets/".length());
        } else if (p.startsWith("/")) {
            p = p.substring(1);
        }
        if (p.isEmpty()) p = LOCAL_ASSET;
        Map<String, String> h = new HashMap<>();
        h.put("Access-Control-Allow-Origin", "*");
        h.put("Cache-Control", "no-cache");
        if (p.contains("..")) {
            return new WebResourceResponse("text/plain", "utf-8", 403, "Forbidden", h,
                    new ByteArrayInputStream(new byte[0]));
        }
        try {
            InputStream is = getAssets().open(p);
            return new WebResourceResponse(mimeFor(p), "utf-8", 200, "OK", h, is);
        } catch (IOException e) {
            log("Asset no encontrado: " + p);
            return new WebResourceResponse("text/plain", "utf-8", 404, "Not Found", h,
                    new ByteArrayInputStream(new byte[0]));
        }
    }

    private boolean assetExists(String name) {
        try {
            InputStream is = getAssets().open(name);
            is.close();
            return true;
        } catch (IOException e) {
            return false;
        }
    }

    // ───────────────────────────── BotService ─────────────────────────────

    /** Llamado por BotService en cada ciclo. Se mantiene la firma original. */
    public void injectData(String dolarJson, String usdtJson, String daiJson, String btcJson) {
        final String js = "(function(){try{if(typeof window.receiveAndroidData!=='function')return;"
                + "window.receiveAndroidData(" + jsonOrNull(dolarJson) + "," + jsonOrNull(usdtJson) + ","
                + jsonOrNull(daiJson) + "," + jsonOrNull(btcJson) + ");"
                + "}catch(e){console.error('injectData: '+e);}})()";
        ui.post(() -> {
            if (webView != null && pageReady) webView.evaluateJavascript(js, null);
        });
    }

    private void requestNotificationPermission() {
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.TIRAMISU
                && ContextCompat.checkSelfPermission(this, Manifest.permission.POST_NOTIFICATIONS)
                != PackageManager.PERMISSION_GRANTED) {
            ActivityCompat.requestPermissions(this,
                    new String[]{Manifest.permission.POST_NOTIFICATIONS}, NOTIF_PERMISSION_CODE);
        }
    }

    private void startBotService() {
        try {
            Intent serviceIntent = new Intent().setClassName(this, PKG + ".BotService");
            if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
                startForegroundService(serviceIntent);
            } else {
                startService(serviceIntent);
            }
            log("BotService iniciado");
        } catch (Throwable t) {
            log("BotService no pudo iniciarse: " + t);
        }
    }

    /** Reenvía la configuración de la interfaz a BotService por el mismo camino con que se lo inicia. */
    private void sendBotConfig(String json) {
        try {
            Intent serviceIntent = new Intent().setClassName(this, PKG + ".BotService");
            serviceIntent.putExtra(BOT_CONFIG_EXTRA, json);
            if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
                startForegroundService(serviceIntent);
            } else {
                startService(serviceIntent);
            }
            log("Configuración enviada a BotService: " + json);
        } catch (Throwable t) {
            log("No se pudo enviar la configuración a BotService: " + t);
        }
    }

    // ───────────────────────────── Diagnóstico ─────────────────────────────

    private void log(String message) {
        long ms = SystemClock.elapsedRealtime() - bootAt;
        String line = String.format(Locale.US, "%7.2f  %s", ms / 1000.0, message);
        Log.d(TAG, message);
        boolean schedule;
        synchronized (logLines) {
            logLines.addLast(line);
            while (logLines.size() > LOG_MAX_LINES) logLines.removeFirst();
            schedule = !logRefreshQueued;
            logRefreshQueued = true;
        }
        if (schedule) ui.postDelayed(this::refreshLog, 250);
    }

    private void refreshLog() {
        String text;
        synchronized (logLines) {
            logRefreshQueued = false;
            text = TextUtils.join("\n", logLines);
        }
        if (logView == null || !overlayShown) return;
        logView.setText(text);
        logScroll.post(() -> logScroll.fullScroll(View.FOCUS_DOWN));
    }

    @SuppressWarnings("deprecation")
    private void logEnvironment() {
        String version = "?";
        long code = -1;
        String installed = "?";
        try {
            PackageInfo pi = getPackageManager().getPackageInfo(getPackageName(), 0);
            version = pi.versionName;
            code = Build.VERSION.SDK_INT >= 28 ? pi.getLongVersionCode() : pi.versionCode;
            installed = new SimpleDateFormat("dd/MM/yyyy 'a las' HH:mm", Locale.US).format(new Date(pi.lastUpdateTime));
        } catch (Exception ignored) {
            // sin datos de paquete: se muestran signos de pregunta
        }
        String webViewPkg = "desconocido";
        if (Build.VERSION.SDK_INT >= 26) {
            try {
                PackageInfo w = WebView.getCurrentWebViewPackage();
                if (w != null) webViewPkg = w.packageName + " " + w.versionName;
            } catch (Throwable ignored) {
                // se informa como desconocido
            }
        }
        infoLine = "Interfaz " + UI_VERSION + ", app " + version + " (código " + code + "), instalada el " + installed;
        infoView.setText(infoLine);
        log(infoLine);
        log("Android " + Build.VERSION.RELEASE + " (API " + Build.VERSION.SDK_INT + "), "
                + Build.MANUFACTURER + " " + Build.MODEL);
        log("WebView del sistema: " + webViewPkg);
    }

    private void copyDiagnostics() {
        String body;
        synchronized (logLines) {
            body = TextUtils.join("\n", logLines);
        }
        String report = "Diagnóstico ArbitrAR\n" + infoLine
                + "\nModo: " + modeName() + ", interfaz lista: " + (pageReady ? "sí" : "no")
                + "\nÚltimo fallo: " + lastFailure
                + "\nURL actual: " + (webView != null ? webView.getUrl() : "sin WebView")
                + "\nUser-Agent: " + userAgent
                + "\n\n" + body;
        ClipboardManager clipboard = (ClipboardManager) getSystemService(Context.CLIPBOARD_SERVICE);
        if (clipboard != null) {
            clipboard.setPrimaryClip(ClipData.newPlainText("Diagnóstico ArbitrAR", report));
            toast("Diagnóstico copiado. Pegalo en el chat.");
        }
    }

    private static String describeSsl(SslError e) {
        String kind;
        switch (e.getPrimaryError()) {
            case SslError.SSL_NOTYETVALID:
                kind = "certificado todavía no válido";
                break;
            case SslError.SSL_EXPIRED:
                kind = "certificado vencido";
                break;
            case SslError.SSL_IDMISMATCH:
                kind = "el certificado no corresponde al dominio";
                break;
            case SslError.SSL_UNTRUSTED:
                kind = "emisor no confiable (suele faltar el certificado intermedio en el hosting)";
                break;
            case SslError.SSL_DATE_INVALID:
                kind = "fecha del certificado inválida";
                break;
            default:
                kind = "certificado inválido";
        }
        String extra = "";
        SslCertificate cert = e.getCertificate();
        if (cert != null) {
            try {
                extra = ", emitido para " + (cert.getIssuedTo() != null ? cert.getIssuedTo().getCName() : "?")
                        + " por " + (cert.getIssuedBy() != null ? cert.getIssuedBy().getCName() : "?")
                        + ", vence " + cert.getValidNotAfterDate();
            } catch (Throwable ignored) {
                // detalle opcional
            }
        }
        return kind + extra;
    }

    // ───────────────────────────── Utilidades ─────────────────────────────

    private static String lower(String s) {
        return s == null ? "" : s.toLowerCase(Locale.US);
    }

    private static boolean isOwnHost(String host) {
        return host.equals(OWN_DOMAIN) || host.endsWith("." + OWN_DOMAIN);
    }

    private static boolean isApiHost(String host) {
        for (String d : API_DOMAINS) {
            if (host.equals(d) || host.endsWith("." + d)) return true;
        }
        return false;
    }

    private static boolean isAllowedApi(String url) {
        try {
            Uri t = Uri.parse(url);
            return "https".equals(lower(t.getScheme())) && isApiHost(lower(t.getHost()));
        } catch (Exception e) {
            return false;
        }
    }

    private static String jsonOrNull(String s) {
        if (s == null) return "null";
        String t = s.trim();
        return (t.startsWith("{") || t.startsWith("[")) ? t : "null";
    }

    private static String shortUrl(String url) {
        if (url == null) return "null";
        String s = url.replaceFirst("^https?://", "");
        return s.length() > 110 ? s.substring(0, 107) + "..." : s;
    }

    private static String[] splitContentType(String contentType) {
        String mime = "application/json";
        String charset = "utf-8";
        if (contentType != null) {
            String[] parts = contentType.split(";");
            if (parts.length > 0 && parts[0].trim().length() > 0) mime = parts[0].trim();
            for (String part : parts) {
                String q = part.trim().toLowerCase(Locale.US);
                if (q.startsWith("charset=")) charset = q.substring(8).replace("\"", "").trim();
            }
        }
        return new String[]{mime, charset};
    }

    private static String mimeFor(String path) {
        String p = path.toLowerCase(Locale.US);
        if (p.endsWith(".html") || p.endsWith(".htm")) return "text/html";
        if (p.endsWith(".js") || p.endsWith(".mjs")) return "application/javascript";
        if (p.endsWith(".css")) return "text/css";
        if (p.endsWith(".json") || p.endsWith(".webmanifest")) return "application/json";
        if (p.endsWith(".svg")) return "image/svg+xml";
        if (p.endsWith(".png")) return "image/png";
        if (p.endsWith(".jpg") || p.endsWith(".jpeg")) return "image/jpeg";
        if (p.endsWith(".webp")) return "image/webp";
        if (p.endsWith(".gif")) return "image/gif";
        if (p.endsWith(".ico")) return "image/x-icon";
        if (p.endsWith(".woff2")) return "font/woff2";
        if (p.endsWith(".woff")) return "font/woff";
        if (p.endsWith(".ttf")) return "font/ttf";
        if (p.endsWith(".mp3")) return "audio/mpeg";
        if (p.endsWith(".wav")) return "audio/wav";
        return "application/octet-stream";
    }

    private static byte[] readAll(InputStream is) throws IOException {
        if (is == null) return new byte[0];
        try {
            ByteArrayOutputStream out = new ByteArrayOutputStream();
            byte[] buf = new byte[8192];
            int n;
            while ((n = is.read(buf)) != -1) out.write(buf, 0, n);
            return out.toByteArray();
        } finally {
            try {
                is.close();
            } catch (IOException ignored) {
                // nada que hacer
            }
        }
    }
}
