/* ====================================================
 * 3Tick Scalper – Step Index 100 Assistant
 * Content script for dtrader.deriv.com
 * ==================================================== */
(function () {
  'use strict';

  // ── Constants & Config ────────────────────────────────────────────────────
  const WS_URL          = 'wss://ws.derivws.com/websockets/v3?app_id=1089';
  const WS_URL_FALLBACK = 'wss://ws.deriv.com/websockets/v3?app_id=1089';
  const FALLBACK_AFTER  = 3;
  const TICK_BUF        = 200;
  const SPEED_BUF       = 100;
  const RECONNECT_BASE  = 4000;
  const RECONNECT_MAX   = 64000;
  const SESSION_HISTORY_CAP = 30000;
  const WATCHDOG_INTERVAL   = 5000;
  const WATCHDOG_TICK_TIMEOUT = 25000;

  // ── DOM Selectors ─────────────────────────────────────────────────────────
  const SEL_SIDE_BTNS    = '.trade-params__option > button.item';
  const SEL_PURCHASE_BTN = 'button.purchase-button.purchase-button--single';
  const CLASS_RISE_ACTIVE = 'quill__color--primary-purchase';
  const CLASS_FALL_ACTIVE = 'quill__color--primary-sell';
  const SEL_FLYOUT       = '.dc-flyout';

  let cfg = {
    tickSize: 0.1,
    strategyMode: 'discoveryEvolution',
    seqMasterConfig: '',
    epsilon: 0.1,
    realTradeEnabled: false,
    realTimeoutMs: 40000,
    realCooldownMs: 5000,
    postTradeCooldownTicks: 5,
    postTradeCooldownMs: 5000,
    debugSignals: true,
    adxMin: undefined,
    adxMax: undefined,
    adxPeriod: 14,
    rsiPeriod: 14,
    trendEmaPeriod: 10,
    minBBWidth: undefined,
    maxBBWidth: undefined,
  };

  // ── State ─────────────────────────────────────────────────────────────────
  let ticks = [];
  let tickDirections = [];
  let speedHistory = [];
  let parsedSeqMasterConfig = null;
  let parsedDnaConfig = null;
  let dnaWorker = null;
  let activeTradePool = new Map();
  let discoveryDb = null;
  let sHigh = 0, sLow = 0, speedMean = 0, speedStd = 0, bbWidth = 0, prevBbWidth = 0;
  let currentStrain = 0, currentRegime = 'D', currentEntropy = 0;
  // ── Pattern Library Key ────────────────────────────────────────────────────
  // Key = sequence (5 chars) + regime ONLY.
  // Indicators (rsi, bbw, str) are stored as metadata on the entry for display
  // and audit purposes, but are NOT part of the lookup key.
  // Reason: the library stores indicators at the historical hitIdx (the moment
  // of discovery), while arming happens at a current tick — these are always
  // different timestamps and will never match byte-for-byte. The arm should
  // fire whenever the same sequence+regime reappears; the recorded hitState is
  // purely informational context about when it was first seen.
  function makePatternKey(sequence, regime) {
    return `${sequence}|${regime}`;
  }

  // ── Content-side indicator calculations (mirrors dnaWorker exactly) ────────
  // Content.js maintains its own rolling price buffer and computes current
  // RSI / BBW / STR / regime independently each tick — the same formulas the
  // worker uses — so the arming check always has fresh, self-consistent values.
  const EVO_BUF_MAX = 500;
  let evoPrices = []; // content-side rolling price buffer

  function evo_calcEMA(prices, period) {
    const k = 2 / (period + 1);
    const emas = [prices[0]];
    for (let i = 1; i < prices.length; i++) {
      emas.push(prices[i] * k + emas[i - 1] * (1 - k));
    }
    return emas;
  }

  function evo_calcRSI(prices, period) {
    const rsi = new Array(prices.length).fill(50);
    if (prices.length <= period) return rsi;
    let gain = 0, loss = 0;
    for (let i = 1; i <= period; i++) {
      const d = prices[i] - prices[i - 1];
      if (d > 0) gain += d; else loss -= d;
    }
    let avgGain = gain / period;
    let avgLoss = loss / period;
    rsi[period] = avgLoss === 0 ? 100 : 100 - (100 / (1 + avgGain / avgLoss));
    for (let i = period + 1; i < prices.length; i++) {
      const d = prices[i] - prices[i - 1];
      avgGain = (avgGain * (period - 1) + (d > 0 ? d : 0)) / period;
      avgLoss = (avgLoss * (period - 1) + (d < 0 ? -d : 0)) / period;
      rsi[i] = avgLoss === 0 ? 100 : 100 - (100 / (1 + avgGain / avgLoss));
    }
    return rsi;
  }

  function evo_calcStdDev(prices, period) {
    const res = new Array(prices.length).fill(0);
    for (let i = period - 1; i < prices.length; i++) {
      const slice = prices.slice(i - period + 1, i + 1);
      const mean = slice.reduce((a, b) => a + b, 0) / period;
      const variance = slice.reduce((a, b) => a + (b - mean) ** 2, 0) / period;
      res[i] = Math.sqrt(variance);
    }
    return res;
  }

  function evo_calcBBW(emaArr, stdDevArr) {
    return emaArr.map((ema, i) => (ema + 2 * stdDevArr[i]) - (ema - 2 * stdDevArr[i]));
  }

  function evo_calcStrain(prices, ema50Arr, stdDev20Arr) {
    return prices.map((p, i) => {
      const std2 = Math.max(stdDev20Arr[i], 0.0001) * 2;
      return Math.abs(p - ema50Arr[i]) / std2;
    });
  }

  function evo_detectRegime(prices, rsiArr, bbwArr, strainArr, idx) {
    const rsi    = rsiArr[idx];
    const bbw    = bbwArr[idx];
    const strain = strainArr[idx];
    if (strain > 2.0 && (rsi > 70 || rsi < 30)) return 'C';
    if (bbw < 0.6  && rsi >= 42 && rsi <= 58)   return 'A';
    if (strain < 0.5)                             return 'B';
    return 'D';
  }

  // Computes current RSI/BBW/STR/regime from the content-side price buffer.
  // Returns null if the buffer is too short to produce reliable values.
  function evo_getCurrentIndicators() {
    const n = evoPrices.length;
    if (n < 50) return null;
    const rsiArr    = evo_calcRSI(evoPrices, 14);
    const ema10Arr  = evo_calcEMA(evoPrices, 10);
    const std10Arr  = evo_calcStdDev(evoPrices, 10);
    const bbwArr    = evo_calcBBW(ema10Arr, std10Arr);
    const ema50Arr  = evo_calcEMA(evoPrices, 50);
    const std20Arr  = evo_calcStdDev(evoPrices, 20);
    const strArr    = evo_calcStrain(evoPrices, ema50Arr, std20Arr);
    const regime    = evo_detectRegime(evoPrices, rsiArr, bbwArr, strArr, n - 1);
    return {
      rsi:    rsiArr[n - 1],
      bbw:    bbwArr[n - 1],
      str:    strArr[n - 1],
      regime: regime
    };
  }

  // ── 3-Scalp Indicator Calculations ─────────────────────────────────────────
  // scalp_calcEMA: standard EMA over a price array
  function scalp_calcEMA(prices, period) {
    if (prices.length === 0) return [];
    const k = 2 / (period + 1);
    const out = [prices[0]];
    for (let i = 1; i < prices.length; i++) {
      out.push(prices[i] * k + out[i - 1] * (1 - k));
    }
    return out;
  }

  // scalp_calcBB: Bollinger Bands with EMA middle, period=12, 2 std devs
  // Returns array of { mid, upper, lower } per tick
  function scalp_calcBB(prices, period) {
    const emas = scalp_calcEMA(prices, period);
    const out = [];
    for (let i = 0; i < prices.length; i++) {
      if (i < period - 1) { out.push({ mid: emas[i], upper: emas[i], lower: emas[i] }); continue; }
      const slice = prices.slice(i - period + 1, i + 1);
      const mean = emas[i];
      const variance = slice.reduce((a, b) => a + (b - mean) ** 2, 0) / period;
      const std = Math.sqrt(variance);
      out.push({ mid: mean, upper: mean + 2 * std, lower: mean - 2 * std });
    }
    return out;
  }

  // scalp_calcMACD: classic MACD (12,26,9)
  // Returns array of { macd, signal, hist }
  function scalp_calcMACD(prices, fast, slow, sig) {
    const emaFast = scalp_calcEMA(prices, fast);
    const emaSlow = scalp_calcEMA(prices, slow);
    const macdLine = prices.map((_, i) => emaFast[i] - emaSlow[i]);
    const sigLine = scalp_calcEMA(macdLine, sig);
    return prices.map((_, i) => ({ macd: macdLine[i], signal: sigLine[i], hist: macdLine[i] - sigLine[i] }));
  }

  // scalp_calcSMI: Stochastic Momentum Index (8, 3, 3, 10)
  // Parameters: lookback=8, smooth1=3, smooth2=3, signal=10
  // Returns array of { smi, signal }
  function scalp_calcSMI(prices, lookback, smooth1, smooth2, sigPeriod) {
    const n = prices.length;
    const raw = new Array(n).fill(0);
    const rawD = new Array(n).fill(0); // denominator
    for (let i = lookback - 1; i < n; i++) {
      const slice = prices.slice(i - lookback + 1, i + 1);
      const hh = Math.max(...slice);
      const ll = Math.min(...slice);
      const mid = (hh + ll) / 2;
      raw[i] = prices[i] - mid;   // numerator: distance from midpoint
      rawD[i] = (hh - ll) / 2;    // denominator: half range
    }
    // First EMA smoothing on numerator and denominator separately
    const num1 = scalp_calcEMA(raw, smooth1);
    const den1 = scalp_calcEMA(rawD, smooth1);
    // Second EMA smoothing
    const num2 = scalp_calcEMA(num1, smooth2);
    const den2 = scalp_calcEMA(den1, smooth2);
    // SMI = 100 * (num2 / (den2 + 0.0001)) to avoid /0
    const smiLine = prices.map((_, i) => 100 * (num2[i] / (Math.abs(den2[i]) + 0.0001)));
    // Signal line = EMA(smiLine, sigPeriod)
    const sigLine = scalp_calcEMA(smiLine, sigPeriod);
    return prices.map((_, i) => ({ smi: smiLine[i], signal: sigLine[i] }));
  }

  // scalp_calcROC: 1-min candle ROC(2): rate of change over 2 candles
  function scalp_calcROC(closes, period) {
    return closes.map((v, i) => i >= period ? v - closes[i - period] : 0);
  }

  // ─── Weather update: called on every 1-min candle close ──────────────────
  function scalp_updateWeather() {
    if (scalp1mCandles.length < 3) return; // need at least 3 closes for ROC(2)
    const closes = scalp1mCandles.map(c => c.close);
    const n = closes.length;
    const roc = scalp_calcROC(closes, 2);
    const currentROC = roc[n - 1];
    const bbArr = scalp_calcBB(closes, Math.min(10, n));
    const bbMid = bbArr[n - 1].mid;
    const lastClose = closes[n - 1];

    const bullish = currentROC > 0 && lastClose > bbMid;
    const bearish = currentROC < 0 && lastClose < bbMid;
    scalpWeather = bullish ? 'BULLISH' : (bearish ? 'BEARISH' : 'FLAT');

    // Update UI badge
    const el = document.getElementById('tt-scalp-weather');
    if (el) {
      el.textContent = scalpWeather;
      el.style.color = scalpWeather === 'BULLISH' ? '#3ecf60' : (scalpWeather === 'BEARISH' ? '#e04040' : '#f0c040');
    }
  }

  // ─── 3-Scalp tick evaluation ─────────────────────────────────────────────
  function scalp_onTick(price) {
    // Duplication lock — realExecState covers isTradeActive
    if (realExecState !== 'IDLE') return;

    // Weather gate
    if (scalpWeather === 'FLAT') return;

    // Need enough tick history for indicators
    if (scalpTickPrices.length < 30) return;

    const prices = scalpTickPrices;
    const n = prices.length;

    // Tick BB (12, EMA)
    const bbPeriod = cfg.scalp_bbPeriod || 12;
    const bbArr = scalp_calcBB(prices, bbPeriod);
    const bb = bbArr[n - 1];

    // BB squeeze guard: avoid flat markets
    const minBbSpread = cfg.scalp_minBbSpread || 0.0;
    if ((bb.upper - bb.lower) < minBbSpread) return;

    // Tick MA (12, EMA) — same as bb.mid
    const bbMid = bb.mid;

    // Tick RSI (7 — faster for ultra-short scalping; configurable)
    const rsiPeriod = cfg.scalp_rsiPeriod || 7;
    const rsiArr = evo_calcRSI(prices, rsiPeriod);
    const rsi = rsiArr[n - 1];

    // Tick MACD (12, 26, 9)
    if (prices.length < 35) return; // need enough for MACD(26)
    const macdArr = scalp_calcMACD(prices, 12, 26, 9);
    const macdNow = macdArr[n - 1];
    const macdHistRising  = scalpPrevMacdHist !== null && macdNow.hist > scalpPrevMacdHist;
    const macdHistFalling = scalpPrevMacdHist !== null && macdNow.hist < scalpPrevMacdHist;

    // SMI (8, 3, 3, 10)
    const smiArr = scalp_calcSMI(prices, 8, 3, 3, 10);
    const smiNow = smiArr[n - 1];
    const smiK = smiNow.smi;
    const smiD = smiNow.signal;

    // SMI thresholds (configurable)
    const smiOversold   = cfg.scalp_smiOversold  !== undefined ? cfg.scalp_smiOversold  : -40;
    const smiOverbought = cfg.scalp_smiOverbought !== undefined ? cfg.scalp_smiOverbought :  40;

    // SMI crossover detection
    const smiCrossUp   = scalpPrevSmiK !== null && smiK > smiD   && scalpPrevSmiK <= scalpPrevSmiD;
    const smiCrossDown = scalpPrevSmiK !== null && smiK < smiD   && scalpPrevSmiK >= scalpPrevSmiD;

    // RSI thresholds (configurable, adjusted from 30/70 for tick speed)
    const rsiCallMin = cfg.scalp_rsiCallMin !== undefined ? cfg.scalp_rsiCallMin : 40;
    const rsiPutMax  = cfg.scalp_rsiPutMax  !== undefined ? cfg.scalp_rsiPutMax  : 60;

    let fired = false;

    if (scalpWeather === 'BULLISH') {
      const atFence    = price <= bb.lower;
      const rsiMacdOk  = rsi > rsiCallMin || macdHistRising;
      if (atFence && rsiMacdOk && smiCrossUp && smiK < smiOverbought) {
        triggerSignal('BUY', 90, '3SCALP:BULL-BB-SMI', null, null, null);
        scalpIsTradeActive = true;
        fired = true;
      }
    }

    if (!fired && scalpWeather === 'BEARISH') {
      const atFence    = price >= bb.upper;
      const rsiMacdOk  = rsi < rsiPutMax || macdHistFalling;
      if (atFence && rsiMacdOk && smiCrossDown && smiK > smiOversold) {
        triggerSignal('SELL', 90, '3SCALP:BEAR-BB-SMI', null, null, null);
        scalpIsTradeActive = true;
        fired = true;
      }
    }

    // Update live SMI display
    const smiEl = document.getElementById('tt-scalp-smi');
    if (smiEl) smiEl.textContent = `K:${smiK.toFixed(1)} D:${smiD.toFixed(1)}`;
    const rsiEl = document.getElementById('tt-scalp-rsi');
    if (rsiEl) rsiEl.textContent = `RSI:${rsi.toFixed(1)} BB-L:${bb.lower.toFixed(2)} BB-U:${bb.upper.toFixed(2)}`;

    // Save for next tick
    scalpPrevSmiK = smiK;
    scalpPrevSmiD = smiD;
    scalpPrevMacdHist = macdNow.hist;
  }

  let patternLibrary = {};
  let rollingDirections = "";
  let lastPriceForDir = null;
  let armedDiscoverySignal = null;
  let lastMetrics = null;
  let discoveryAuditLog = []; // Black Box: every-tick state recorder
  let lastProcessedSeq = ""; // Streak lock: prevents re-arming on unchanged sequence

  // ── 3-Scalp Strategy State ───────────────────────────────────────────────
  let scalpWeather = "FLAT";          // "BULLISH" | "BEARISH" | "FLAT"
  let scalpIsTradeActive = false;     // Duplication lock
  let scalp1mCandles = [];            // Rolling 1-min OHLC candles
  let scalp1mCurrentCandle = null;    // In-progress candle being built from ticks
  let scalp1mWsCandle = null;         // Separate WS for 1-min candle feed
  let scalpTickPrices = [];           // Rolling tick price buffer for scalp indicators
  const SCALP_TICK_BUF = 300;
  let scalpPrevSmiK = null;           // Previous SMI K for crossover detection
  let scalpPrevSmiD = null;           // Previous SMI D for crossover detection
  let scalpPrevMacdHist = null;       // Previous MACD histogram for rising/falling check
  let signals = [], sessionTradesAll = [];
  let tickSeq = 0, lastSignalTickIndex = -999, upStreak = 0, downStreak = 0;
  let lastTickProcessedAt = 0, lastSignalEvalAt = 0, watchdogInterval = null, evalErrorCount = 0;
  let realExecState = 'IDLE', realTrades = [], realOpenCount = 0, realWins = 0, realLosses = 0, realPnl = 0, realLockReason = '', lastRealTradeAt = 0, lastTradeClosedAt = 0, lastTradeClosedTick = -999, realExecTimer = null, lastSeenPnL = 0, lastSeenResult = null;
  let flyoutObserver = null, ws = null, wsState = 'disconnected', reconnectTimer = null, resolvedSymbol = null, manualClose = false, reconnectDelay = RECONNECT_BASE, failCount = 0, usingFallback = false, finalizationTimer = null;

  // UI Cache to prevent redundant DOM updates
  let lastUI = { state: '', pnl: null, wins: -1, losses: -1, price: '', stats: '', dist: '', dirStreak: '', unleashed: '' };

  // ── Overlay Build ─────────────────────────────────────────────────────────
  function buildOverlay() {
    if (document.getElementById('tt-overlay')) return;
    const el = document.createElement('div');
    el.id = 'tt-overlay';
    el.innerHTML = `
      <div id="tt-header">
        <span class="tt-title">3Tick Timing V2</span>
        <div class="tt-header-btns"><button id="tt-min-btn" title="Minimise">_</button><button id="tt-close-btn" title="Close">X</button></div>
      </div>
      <div id="tt-body">
        <div class="tt-row"><span class="tt-label">Status</span><span class="tt-val" id="tt-status">Disconnected</span></div>
        <div class="tt-row"><span class="tt-label">Last Price</span><span class="tt-val" id="tt-price">-</span></div>
        <div class="tt-row"><span class="tt-label">Dir / Streak</span><span class="tt-val" id="tt-dir-streak">- / 0</span></div>
        <div class="tt-row"><span class="tt-label">S_Low / S_High</span><span class="tt-val" id="tt-speed-stats">0.00 / 0.00</span></div>
        <div class="tt-row"><span class="tt-label">Mean / Std</span><span class="tt-val" id="tt-speed-dist">0.00 / 0.00</span></div>
        <div class="tt-row"><span class="tt-label">ADX / BB_W</span><span class="tt-val" id="tt-adx-stats">0 / 0.00</span></div>
        <div class="tt-row"><span class="tt-label">RSI / Trend</span><span class="tt-val" id="tt-rsi-stats">0 / 0.00</span></div>
        <div class="tt-row"><span class="tt-label">Int/Eps/Accel</span><span class="tt-val" id="tt-unleashed-stats">0 / 0 / 0.00000</span></div>
        <div class="tt-row" id="tt-regime-row" style="justify-content:center; font-weight:bold; color:#7ec8e3;"><span id="tt-regime-display">D · NOISE · BBW: 0.00</span></div>
        <div class="tt-row" id="tt-scalp-row" style="display:none; flex-direction:column; gap:2px; padding:3px 0;">
          <div style="display:flex; gap:6px; align-items:center; font-size:10px;">
            <span style="color:#7a8499;">WEATHER</span>
            <span id="tt-scalp-weather" style="font-weight:bold; color:#f0c040;">FLAT</span>
            <span style="color:#7a8499; margin-left:6px;">SMI</span>
            <span id="tt-scalp-smi" style="color:#7ec8e3; font-family:monospace;">K:- D:-</span>
          </div>
          <div style="font-size:9px; color:#7a8499; font-family:monospace;" id="tt-scalp-rsi">RSI:- BB-L:- BB-U:-</div>
        </div>
        <div class="tt-row"><span class="tt-label">Session W/L</span><span class="tt-val"><span id="tt-wins">0</span> / <span id="tt-losses">0</span></span></div>
        <div id="tt-signals-list"></div>
        <div id="tt-discovery-diag" style="display:none; padding:6px; background:rgba(0,0,0,0.2); border-radius:4px; margin-top:4px; max-height:400px; overflow:hidden; flex-direction:column; gap:4px;">
          <div style="display:flex; justify-content:space-between; align-items:center; border-bottom:1px solid #3a4260; padding-bottom:2px;">
            <div style="font-size:10px; color:#7a8499;">LIVE DISCOVERY FEED <span id="tt-armed-count" style="color:#7ec8e3; margin-left:4px;">(Armed: 0)</span><span id="tt-pattern-count" style="color:#f0a060; margin-left:6px;">[Patterns: 0]</span></div>
            <button id="tt-flush-ram" style="font-size:9px; background:#3d1a1a; color:#e04040; border:1px solid #7a3a10; border-radius:3px; cursor:pointer; padding:2px 6px; font-weight:bold; text-transform:uppercase;">Flush RAM</button>
          </div>
          <div id="tt-discovery-feed" style="flex:1; overflow-y:auto; font-size:10px; font-family:monospace; color:#3ecf60; max-height:150px; scrollbar-width:thin;"></div>
          <div style="font-size:10px; color:#e04040; border-bottom:1px solid #3d1a1a; padding-bottom:2px; margin-top:4px;">EXECUTION FAILURES (PURGED)</div>
          <div id="tt-fail-exec-list" style="flex:1; overflow-y:auto; font-size:10px; font-family:monospace; color:#e04040; max-height:100px; scrollbar-width:thin;"></div>
        </div>
        <div id="tt-dna-diag" style="display:none; padding:6px; background:rgba(0,0,0,0.2); border-radius:4px; margin-top:4px;">
          <div style="font-size:10px; color:#7a8499; margin-bottom:4px; display:flex; justify-content:space-between;">
            <span>DNA MATCH METER</span>
            <span id="tt-dna-match-label">0.0%</span>
          </div>
          <div style="height:6px; background:#1e2338; border-radius:3px; overflow:hidden; margin-bottom:8px;">
            <div id="tt-dna-match-bar" style="width:0%; height:100%; background:#e04040; transition:width 0.2s, background 0.2s;"></div>
          </div>
          <div style="display:grid; grid-template-columns: repeat(3, 1fr); gap:4px; text-align:center; font-size:10px; margin-bottom:8px;">
            <div class="tt-dna-metric">
              <div style="color:#7a8499;">RSI Δ</div>
              <div id="tt-dna-rsi-val">0.00</div>
              <div id="tt-dna-rsi-target" style="font-size:8px; opacity:0.6;">-</div>
            </div>
            <div class="tt-dna-metric">
              <div style="color:#7a8499;">BBW Δ</div>
              <div id="tt-dna-bbw-val">0.000</div>
              <div id="tt-dna-bbw-target" style="font-size:8px; opacity:0.6;">-</div>
            </div>
            <div class="tt-dna-metric">
              <div style="color:#7a8499;">STR Δ</div>
              <div id="tt-dna-str-val">0.000</div>
              <div id="tt-dna-str-target" style="font-size:8px; opacity:0.6;">-</div>
            </div>
          </div>
          <div style="display:flex; justify-content:space-between; align-items:center;">
            <div id="tt-dna-entropy-badge" style="font-size:9px; padding:2px 4px; border-radius:2px; background:#3d1a1a; color:#e04040;">ENTROPY: 0.00</div>
            <div id="tt-dna-vgate" style="font-size:14px; color:#e04040;" title="Expansion Gate (BBW Delta > 0)">⧓</div>
            <div id="tt-dna-regime" style="font-size:9px; padding:2px 4px; border-radius:2px; background:#1e2338; color:#7ec8e3;">REGIME: D</div>
          </div>
        </div>
        <div class="tt-config-section-label">Real Execution</div>
        <div id="tt-real-panel">
          <div class="tt-row"><span class="tt-label">Exec State</span><span class="tt-val" id="tt-real-state">IDLE</span></div>
          <div class="tt-row"><span class="tt-label">Real PnL</span><span class="tt-val" id="tt-real-pnl">0.00</span></div>
          <button id="tt-real-export">Download Real CSV</button>
          <button id="tt-real-reset" style="background:#3d1a1a;color:#e04040;margin-top:2px;">Reset Engine</button>
          <button id="tt-audit-export" style="background:#1a2d3d;color:#7ec8e3;margin-top:2px;border:1px solid #3a6080;border-radius:4px;cursor:pointer;width:100%;padding:4px;font-size:10px;">⬇ Download Audit CSV</button>
        </div>
        <div style="display:flex;gap:4px;margin-top:4px;">
          <button id="tt-config-toggle" style="flex:1;">Settings</button>
          <button id="tt-clear-logs" style="flex:1;background:#3d1a1a;color:#e04040;font-size:10px;border:1px solid #7a3a10;border-radius:4px;cursor:pointer;">Clear Logs</button>
        </div>
        <div id="tt-config">
          <div class="tt-config-row"><label>Mode</label><select id="tt-cfg-strategy-mode"><option value="discoveryEvolution">🧬 Discovery Evolution</option><option value="threeSecScalp">⚡ 3-Sec Scalp</option></select></div>
          <div id="tt-cfg-seq-master-container" style="display:none; flex-direction:column; gap:4px; margin-top:4px;">
            <label style="font-size:10px; color:#7a8499;">DNA JSON Config</label>
            <textarea id="tt-cfg-seq-master-json" placeholder='Paste JSON DNA here...' style="width:100%; height:120px; background:#1e2338; border:1px solid #3a4260; color:#e0e6f0; border-radius:4px; font-size:10px; font-family:monospace; resize:vertical;"></textarea>
          </div>
          <div class="tt-config-row"><label>Debug Signals</label><input type="checkbox" id="tt-cfg-debug"></div>
          <div id="tt-scalp-settings" style="display:none; flex-direction:column; gap:4px; margin-top:4px;">
            <div class="tt-config-section-label">⚡ 3-Sec Scalp Settings</div>
            <div class="tt-config-row" style="gap:4px;">
              <label style="flex:1.5;">RSI Period</label>
              <input type="number" id="tt-scalp-rsi-period" min="3" max="21" style="width:48px;background:#1e2338;border:1px solid #3a4260;color:#e0e6f0;border-radius:3px;padding:2px;font-size:10px;" placeholder="7">
            </div>
            <div class="tt-config-row" style="gap:4px;">
              <label style="flex:1.5;">RSI Min (CALL)</label>
              <input type="number" id="tt-scalp-rsi-call-min" min="20" max="60" style="width:48px;background:#1e2338;border:1px solid #3a4260;color:#e0e6f0;border-radius:3px;padding:2px;font-size:10px;" placeholder="40">
            </div>
            <div class="tt-config-row" style="gap:4px;">
              <label style="flex:1.5;">RSI Max (PUT)</label>
              <input type="number" id="tt-scalp-rsi-put-max" min="40" max="80" style="width:48px;background:#1e2338;border:1px solid #3a4260;color:#e0e6f0;border-radius:3px;padding:2px;font-size:10px;" placeholder="60">
            </div>
            <div class="tt-config-row" style="gap:4px;">
              <label style="flex:1.5;">SMI Oversold (≤)</label>
              <input type="number" id="tt-scalp-smi-oversold" min="-100" max="0" style="width:52px;background:#1e2338;border:1px solid #3a4260;color:#e0e6f0;border-radius:3px;padding:2px;font-size:10px;" placeholder="-40">
            </div>
            <div class="tt-config-row" style="gap:4px;">
              <label style="flex:1.5;">SMI Overbought (≥)</label>
              <input type="number" id="tt-scalp-smi-overbought" min="0" max="100" style="width:52px;background:#1e2338;border:1px solid #3a4260;color:#e0e6f0;border-radius:3px;padding:2px;font-size:10px;" placeholder="40">
            </div>
            <div class="tt-config-row" style="gap:4px;">
              <label style="flex:1.5;">BB Period (tick)</label>
              <input type="number" id="tt-scalp-bb-period" min="5" max="30" style="width:48px;background:#1e2338;border:1px solid #3a4260;color:#e0e6f0;border-radius:3px;padding:2px;font-size:10px;" placeholder="12">
            </div>
            <div class="tt-config-row" style="gap:4px;">
              <label style="flex:1.5;">Min BB Spread</label>
              <input type="number" id="tt-scalp-min-bb-spread" min="0" max="5" step="0.01" style="width:52px;background:#1e2338;border:1px solid #3a4260;color:#e0e6f0;border-radius:3px;padding:2px;font-size:10px;" placeholder="0.05">
            </div>
          </div>
          <div class="tt-config-section-label">Real Trade Master</div>
          <div class="tt-config-row"><label style="color:#f0a060;font-weight:700;">Enable Real Execution</label><label class="tt-switch"><input type="checkbox" id="tt-cfg-real-enabled"><span class="tt-slider"></span></label></div>
        </div>
        <button id="tt-export">Download Signals CSV</button>
      </div>
      <div id="tt-alert"></div>
    `;
    document.body.appendChild(el);
    const saved = safeStorage('get', 'tt-pos');
    if (saved) { el.style.right = 'auto'; el.style.left = saved.left + 'px'; el.style.top = saved.top + 'px'; }
    makeDraggable(el); bindButtons(el);
  }

  function makeDraggable(el) {
    const header = document.getElementById('tt-header');
    let ox = 0, oy = 0;
    header.addEventListener('mousedown', function (e) {
      if (e.target.tagName === 'BUTTON') return;
      e.preventDefault(); const rect = el.getBoundingClientRect(); ox = e.clientX - rect.left; oy = e.clientY - rect.top;
      document.addEventListener('mousemove', onMove); document.addEventListener('mouseup', onUp);
    });
    function onMove(e) {
      const left = e.clientX - ox, top = e.clientY - oy;
      el.style.right = 'auto';
      el.style.left = Math.max(0, Math.min(window.innerWidth - el.offsetWidth, left)) + 'px';
      el.style.top = Math.max(0, Math.min(window.innerHeight - el.offsetHeight, top)) + 'px';
    }
    function onUp() {
      document.removeEventListener('mousemove', onMove); document.removeEventListener('mouseup', onUp);
      safeStorage('set', 'tt-pos', { left: parseInt(el.style.left), top: parseInt(el.style.top) });
    }
  }

  function bindButtons(el) {
    document.getElementById('tt-min-btn').addEventListener('click', () => el.classList.toggle('tt-minimized'));
    document.getElementById('tt-close-btn').addEventListener('click', () => { manualClose = true; if (reconnectTimer) clearTimeout(reconnectTimer); if (ws) ws.close(); el.remove(); });
    document.getElementById('tt-config-toggle').addEventListener('click', () => document.getElementById('tt-config').classList.toggle('tt-open'));
    document.getElementById('tt-cfg-strategy-mode').addEventListener('change', function () {
      cfg.strategyMode = this.value;
      updateSeqMasterUIVisibility();
      initDnaWorker();
      saveCfg();
      // Auto-Focus/Expand Diagnostic Panels
      if (cfg.strategyMode === 'discoveryEvolution') {
          const config = document.getElementById('tt-config');
          if (config && config.classList.contains('tt-open')) config.classList.remove('tt-open');
          updateDnaUI({}); // Force panel layout update
      }
    });
    const seqJsonEl = document.getElementById('tt-cfg-seq-master-json');
    seqJsonEl.addEventListener('input', function() {
      cfg.seqMasterConfig = this.value;
      validateSeqMasterJSON(this.value);
      saveCfg();
    });
    document.getElementById('tt-cfg-debug').addEventListener('change', function () { cfg.debugSignals = this.checked; saveCfg(); });
    document.getElementById('tt-cfg-real-enabled').addEventListener('change', function () { cfg.realTradeEnabled = this.checked; saveCfg(); });
    document.getElementById('tt-real-export').addEventListener('click', exportRealCSV);
    document.getElementById('tt-real-reset').addEventListener('click', () => { if (confirm('Reset real-trade engine to IDLE and clear lock?')) { realExecState = 'IDLE'; realLockReason = ''; realOpenCount = 0; clearTimeout(realExecTimer); updateRealUI(); } });
    document.getElementById('tt-flush-ram').addEventListener('click', () => { if (confirm('Flush RAM and Clear Discovery Pool?')) { activeTradePool.clear(); document.getElementById('tt-discovery-feed').innerHTML = ''; document.getElementById('tt-fail-exec-list').innerHTML = ''; document.getElementById('tt-armed-count').textContent = '(Armed: 0)'; const _pc = document.getElementById('tt-pattern-count'); if (_pc) _pc.textContent = '[Patterns: 0]'; showAlert('RAM Flushed'); } });
    document.getElementById('tt-clear-logs').addEventListener('click', () => { if (confirm('Clear all session signal and tick logs?')) { sessionTradesAll = []; signals = []; realTrades = []; updateSignalsUI(); showAlert('Logs cleared'); } });
    document.getElementById('tt-audit-export').addEventListener('click', downloadDiscoveryAudit);
    document.getElementById('tt-export').addEventListener('click', exportCSV);
    applyConfigToUI();
  }

  // ── WebSocket & Percentiles ───────────────────────────────────────────────
  function resolveSymbol(symbols) {
    var candidates = ['stpRNG', 'STPRNG'];
    for (var i = 0; i < candidates.length; i++) if (symbols.find(s => s.symbol === candidates[i])) return candidates[i];
    var byName = symbols.find(s => /step\s*index\s*100/i.test(s.display_name));
    return byName ? byName.symbol : (symbols.find(s => /step/i.test(s.display_name))?.symbol || null);
  }

  function connect() {
    if (ws && [WebSocket.OPEN, WebSocket.CONNECTING].includes(ws.readyState)) return;
    var url = usingFallback ? WS_URL_FALLBACK : WS_URL; setWsState('connecting');
    ws = new WebSocket(url);
    ws.addEventListener('open', () => {
      setWsState('connected'); reconnectDelay = RECONNECT_BASE; failCount = 0; usingFallback = false;
      lastTickProcessedAt = Date.now(); lastSignalEvalAt = Date.now();
      ws.send(JSON.stringify({ active_symbols: 'brief', product_type: 'basic' }));
    });
    ws.addEventListener('message', (e) => {
      var msg; try { msg = JSON.parse(e.data); } catch (_) { return; }
      if (msg.error) return;
      if (msg.msg_type === 'active_symbols') {
        var sym = resolveSymbol(msg.active_symbols || []);
        if (sym) {
          resolvedSymbol = sym;
          ws.send(JSON.stringify({ ticks: resolvedSymbol, subscribe: 1 }));
          // Subscribe to 1-min candles for the 3-Scalp weather module
          const nowEpoch = Math.floor(Date.now() / 1000);
          ws.send(JSON.stringify({
            ticks_history: resolvedSymbol,
            style: 'candles',
            granularity: 60,
            count: 30,           // Seed with 30 historical 1-min candles for immediate warm-up
            end: 'latest',
            subscribe: 1
          }));
        }
        return;
      }
      if (msg.msg_type === 'tick') handleTick(msg.tick);
      // 1-min candle feed for 3-Scalp weather module
      if (msg.msg_type === 'candles' || msg.msg_type === 'ohlc') {
        if (msg.msg_type === 'candles' && msg.candles) {
          // Seed with historical candles
          scalp1mCandles = msg.candles.map(c => ({
            open: parseFloat(c.open), high: parseFloat(c.high),
            low: parseFloat(c.low),  close: parseFloat(c.close),
            epoch: c.epoch
          }));
          scalp_updateWeather();
        } else if (msg.msg_type === 'ohlc' && msg.ohlc) {
          // Live streaming candle update
          const o = msg.ohlc;
          const candle = { open: parseFloat(o.open), high: parseFloat(o.high), low: parseFloat(o.low), close: parseFloat(o.close), epoch: o.open_time || o.epoch };
          const last = scalp1mCandles.length ? scalp1mCandles[scalp1mCandles.length - 1] : null;
          if (last && last.epoch === candle.epoch) {
            // Same candle — update in-place (price still moving within this minute)
            scalp1mCandles[scalp1mCandles.length - 1] = candle;
          } else {
            // New candle = previous one closed — update weather on close
            scalp1mCandles.push(candle);
            if (scalp1mCandles.length > 100) scalp1mCandles.shift();
            scalp_updateWeather();
          }
        }
      }
    });
    ws.addEventListener('close', () => { setWsState('disconnected'); resolvedSymbol = null; if (!manualClose) scheduleReconnect(); });
    ws.addEventListener('error', () => { setWsState('disconnected'); ws.close(); });
  }

  function scheduleReconnect() {
    if (reconnectTimer) return; failCount++;
    if (failCount >= FALLBACK_AFTER) { usingFallback = !usingFallback; failCount = 0; }
    reconnectTimer = setTimeout(() => { reconnectTimer = null; connect(); }, reconnectDelay);
    reconnectDelay = Math.min(reconnectDelay * 2, RECONNECT_MAX);
  }

  function setWsState(state) {
    wsState = state; const el = document.getElementById('tt-status');
    if (el) el.textContent = state.charAt(0).toUpperCase() + state.slice(1);
  }

  function updateStatsUI() {
    const t0 = ticks[ticks.length - 1];
    if (!t0) return;

    const statsVal = `${sLow.toFixed(4)} / ${sHigh.toFixed(4)}`;
    const distVal = `${speedMean.toFixed(4)} / ${speedStd.toFixed(4)}`;
    const currentADX = t0.adx || 0;
    const adxVal = `${currentADX.toFixed(2)} / ${bbWidth.toFixed(2)}`;

    if (lastUI.stats !== statsVal) {
      const el = document.getElementById('tt-speed-stats');
      if (el) el.textContent = statsVal;
      lastUI.stats = statsVal;
    }
    if (lastUI.dist !== distVal) {
      const el = document.getElementById('tt-speed-dist');
      if (el) el.textContent = distVal;
      lastUI.dist = distVal;
    }
    if (lastUI.adx !== adxVal) {
      const el = document.getElementById('tt-adx-stats');
      if (el) {
        el.textContent = adxVal;
        const amin = cfg.adxMin || 25, amax = cfg.adxMax || 60;
        const minBBW = cfg.minBBWidth || 0.2;
        el.style.color = (currentADX >= amin && currentADX <= amax && bbWidth >= minBBW) ? '#3ecf60' : '#7a8499';
      }
      lastUI.adx = adxVal;
    }

    const currentRSI = t0.rsi || 50;
    const currentTrend = t0.trendEma || 0;
    const rsiTrendVal = `${currentRSI.toFixed(1)} / ${currentTrend.toFixed(2)}`;
    if (lastUI.rsiTrend !== rsiTrendVal) {
      const el = document.getElementById('tt-rsi-stats');
      if (el) {
        el.textContent = rsiTrendVal;
        const isUp = t0.price > currentTrend;
        el.style.color = isUp ? '#3ecf60' : '#e04040';
      }
      lastUI.rsiTrend = rsiTrendVal;
    }

    const currentIntensity = t0.intensity || 0;
    const currentEpsilon   = t0.deltaChange || 0;
    const currentAccel     = t0.accel5 || 0;
    const unleashedVal = `${currentIntensity.toFixed(2)} / ${currentEpsilon} / ${currentAccel.toFixed(4)}`;
    if (lastUI.unleashed !== unleashedVal) {
      const el = document.getElementById('tt-unleashed-stats');
      if (el) {
        el.textContent = unleashedVal;
          el.style.color = '#7a8499';
      }
      lastUI.unleashed = unleashedVal;
    }
  }

  function calculatePercentiles() {
    if (speedHistory.length >= 10) {
      const sorted = speedHistory.slice().sort((a, b) => a - b);
      const p30 = sorted[Math.floor(sorted.length * 0.3)], p70 = sorted[Math.floor(sorted.length * 0.7)];
      const sum = speedHistory.reduce((a, b) => a + b, 0); speedMean = sum / speedHistory.length;
      const sqDiff = speedHistory.map(v => Math.pow(v - speedMean, 2)); speedStd = Math.sqrt(sqDiff.reduce((a, b) => a + b, 0) / speedHistory.length);
      sHigh = Math.max(p70, speedMean + speedStd); sLow = Math.min(p30, Math.max(0, speedMean - speedStd));
    }

    updateStatsUI();
    const regimeRow = document.getElementById('tt-regime-row');
    const regimeDisplay = document.getElementById('tt-regime-display');

    if (cfg.strategyMode === 'discoveryEvolution') {
      if (regimeRow) regimeRow.style.display = 'flex';
      if (regimeDisplay) {
        const regimeName = currentRegime === 'A' ? 'A · CONSOLIDATION' : (currentRegime === 'B' ? 'B · TRENDING' : (currentRegime === 'C' ? 'C · VOLATILITY' : 'D · NOISE'));
        regimeDisplay.textContent = `${regimeName} · BBW: ${bbWidth.toFixed(2)}`;
      }
    } else {
      if (regimeRow) regimeRow.style.display = 'none';
    }
    // 3-Scalp row visibility
    const scalpRow = document.getElementById('tt-scalp-row');
    if (scalpRow) scalpRow.style.display = cfg.strategyMode === 'threeSecScalp' ? 'flex' : 'none';
  }

  function handleTick(tick) {
    if (!tick || tick.symbol !== resolvedSymbol) return;
    const price = parseFloat(tick.quote), epoch = tick.epoch, now = Date.now(); tickSeq++;
    const prevTick = ticks.length ? ticks[ticks.length - 1] : null;
    const delta = prevTick ? price - prevTick.price : 0, deltaSteps = Math.round(delta / 0.1), direction = delta > 0 ? 1 : (delta < 0 ? -1 : 0);
    const deltaTime = prevTick ? (now - prevTick.receivedAt) : 1000;
    const speed = deltaTime > 0 ? deltaSteps / deltaTime : 0, absSpeed = Math.abs(speed);
    const speedTrend = prevTick ? (absSpeed - prevTick.absSpeed) : 0;
    const lastDigit = Math.floor(Math.round(price * 100) / 10) % 10, deltaChange = prevTick ? deltaSteps - prevTick.deltaSteps : 0;
    const preSpeed = prevTick ? prevTick.speed : 0;
    const acceleration = Math.round((speed - preSpeed) * 100000) / 100000;
    const accel = acceleration; // Alias for compatibility with previous updates
    const intensity = Math.abs(speed) / (speedMean || 0.0007);
    const deltaChangeVal = prevTick ? deltaSteps - prevTick.deltaSteps : 0;
    const kTrend = 2 / ((cfg.trendEmaPeriod || 15) + 1);
    const trendEma = prevTick ? (price * kTrend + (prevTick.trendEma || price) * (1 - kTrend)) : price;

    let adx = 0;
    const adxP = cfg.adxPeriod || 14;
    if (ticks.length >= adxP) {
      let trSum = 0, pdmSum = 0, mdmSum = 0;
      for (let i = 0; i < adxP; i++) {
        const curr = i === 0 ? { price } : ticks[ticks.length - i];
        const prev = i === 0 ? ticks[ticks.length - 1] : ticks[ticks.length - i - 1];
        const tr = Math.abs(curr.price - prev.price);
        const pdm = curr.price > prev.price ? curr.price - prev.price : 0;
        const mdm = prev.price > curr.price ? prev.price - curr.price : 0;
        trSum += tr; pdmSum += pdm; mdmSum += mdm;
      }
      const pDI = trSum > 0 ? (pdmSum / trSum) * 100 : 0;
      const mDI = trSum > 0 ? (mdmSum / trSum) * 100 : 0;
      const dx = (pDI + mDI) > 0 ? (Math.abs(pDI - mDI) / (pDI + mDI)) * 100 : 0;
      adx = prevTick && prevTick.adx ? (prevTick.adx * (adxP - 1) + dx) / adxP : dx;
    }

    let rsi = 50;
    const rsiP = cfg.rsiPeriod || 14;
    if (ticks.length >= rsiP) {
      let up = 0, down = 0;
      for (let i = 0; i < rsiP; i++) {
        const curr = i === 0 ? { price } : ticks[ticks.length - i];
        const prev = i === 0 ? ticks[ticks.length - 1] : ticks[ticks.length - i - 1];
        const d = curr.price - prev.price;
        if (d > 0) up += d; else down += Math.abs(d);
      }
      const avgUp = up / rsiP, avgDown = down / rsiP;
      if (avgUp === 0 && avgDown === 0) rsi = 50;
      else rsi = avgDown === 0 ? 100 : 100 - (100 / (1 + avgUp / avgDown));
    }

    if (ticks.length >= 10) {
      const slice = ticks.slice(-10);
      const sqDiffSum = slice.reduce((a, b) => a + Math.pow(b.price - trendEma, 2), 0);
      const stdDev = Math.sqrt(sqDiffSum / 10);
      prevBbWidth = bbWidth;
      bbWidth = stdDev * 4; // Upper - Lower = 4 * stdDev
    }

    let speed5 = 0;
    if (ticks.length >= 6) {
      const tMinus5 = ticks[ticks.length - 6]; // T0 vs T-5 is 5 intervals
      speed5 = (price - tMinus5.price) / 5; // Displacement over 5 ticks / 5
    }
    const accel5 = prevTick ? Math.round((speed5 - (prevTick.speed5 || 0)) * 100000) / 100000 : 0;

    if (delta > 0) { upStreak++; downStreak = 0; } else if (delta < 0) { downStreak++; upStreak = 0; } else { upStreak = 0; downStreak = 0; }

    // Update tick directions
    let dirChar = delta > 0 ? 'U' : (delta < 0 ? 'D' : (tickDirections.length ? tickDirections[tickDirections.length - 1] : 'U'));
    tickDirections.push(dirChar);
    if (tickDirections.length > 20) tickDirections.shift();

    const state = { epoch, price, direction, deltaSteps, deltaTime, speed, absSpeed, speedTrend, upStreak, downStreak, lastDigit, deltaChange: deltaChangeVal, receivedAt: now, accel, intensity, preSpeed, acceleration, trendEma, ema10: trendEma, adx, rsi, speed5, accel5 };
    ticks.push(state); if (ticks.length > TICK_BUF) ticks.shift();
    speedHistory.push(absSpeed); if (speedHistory.length > SPEED_BUF) speedHistory.shift();
    calculatePercentiles(); lastTickProcessedAt = Date.now();



    const priceStr = price.toFixed(2);
    if (lastUI.price !== priceStr) {
      const el = document.getElementById('tt-price');
      if (el) el.textContent = priceStr;
      lastUI.price = priceStr;
    }

    const dirStr = direction === 1 ? 'UP' : (direction === -1 ? 'DOWN' : 'FLAT');
    const streakStr = `${dirStr} / ${Math.max(upStreak, downStreak)}`;
    if (lastUI.dirStreak !== streakStr) {
      const el = document.getElementById('tt-dir-streak');
      if (el) {
        el.textContent = streakStr;
        el.style.color = direction === 1 ? '#3ecf60' : (direction === -1 ? '#e04040' : '#fff');
      }
      lastUI.dirStreak = streakStr;
    }

    if (cfg.strategyMode === 'discoveryEvolution' && dnaWorker) {
      // 1. Send single price to worker
      dnaWorker.postMessage({ type: 'compute', price: price, seq: tickSeq, config: parsedDnaConfig });

      // 2. Feed content-side price buffer and compute fresh indicators independently.
      //    These mirror the worker's formulas exactly so arming always uses current values.
      evoPrices.push(parseFloat(price));
      if (evoPrices.length > EVO_BUF_MAX) evoPrices.shift();
      const evoIndicators = evo_getCurrentIndicators(); // null until 50 prices buffered
      let tickAction = "IDLE";

      if (evoIndicators) {
        // Keep currentRegime in sync for UI (handleDnaMetrics still updates it from worker
        // but evo_detectRegime gives us an independent value for arming — we use that directly)
        // 3. Update Rolling String (IGNORE FLAT TICKS)
        if (lastPriceForDir !== null && price !== lastPriceForDir) {
            const move = price > lastPriceForDir ? "U" : "D";
            const nextSeq = (rollingDirections + move).slice(-5);

            // ONLY process if the sequence has actually changed (prevents over-counting on sustained streaks)
            if (nextSeq !== lastProcessedSeq) {
                rollingDirections = nextSeq;
            }
        }

        // 4. Confirmation check (only if price actually moved)
        if (armedDiscoverySignal && lastPriceForDir !== null && price !== lastPriceForDir) {
            const currentDir = price > lastPriceForDir ? 'U' : 'D';
            const targetDir = armedDiscoverySignal.action === 'CALL' ? 'U' : 'D';

            if (currentDir === targetDir) {
                tickAction = `TRADE_${armedDiscoverySignal.action}`;
                const type = armedDiscoverySignal.action === 'CALL' ? 'BUY' : 'SELL';
                triggerSignal(type, 100, `EVO:${rollingDirections}`, null, null, armedDiscoverySignal);
            } else {
                tickAction = "ABORTED_WRONG_DIR";
                console.log("[EVO] Aborted: Wrong Direction");
            }
            // Remove from pool regardless of outcome — signal is consumed
            if (armedDiscoverySignal) {
                const _resolvedKey = `${armedDiscoverySignal.sequence}-${armedDiscoverySignal.action}`;
                activeTradePool.delete(_resolvedKey);
            }
            armedDiscoverySignal = null;
        } else if (!armedDiscoverySignal && rollingDirections.length === 5 && rollingDirections !== lastProcessedSeq) {
            // 5. Arming check — sequence + regime lookup using content-side computed regime.
            // Key is sequence+regime only; indicators are metadata, not part of the match.
            const armKey = makePatternKey(rollingDirections, evoIndicators.regime);
            const match = patternLibrary[armKey];
            if (match) {
                lastProcessedSeq = rollingDirections;
                armedDiscoverySignal = {
                    action: match.action,
                    sequence: rollingDirections,
                    patternKey: armKey,
                    hitState: match.indicators,
                    regime: match.regime || 'D'
                };
                match.count++;
                const _armKey = `${rollingDirections}-${match.action}`;
                activeTradePool.set(_armKey, { sequence: rollingDirections, action: match.action, armedAt: Date.now() });
                tickAction = `ARMED_${match.action}`;
                console.log("[EVO] ARMED:", armKey, match.action, `(count: ${match.count})`);
            }
        }
      } else {
        tickAction = "WARMING_UP";
      }

      // 6. Black Box — push a full state snapshot for every tick
      discoveryAuditLog.push({
        timestamp: new Date().toISOString(),
        price: price,
        dna_sequence: rollingDirections,
        rsi:    evoIndicators ? evoIndicators.rsi.toFixed(2)    : 'n/a',
        bbw:    evoIndicators ? evoIndicators.bbw.toFixed(4)    : 'n/a',
        strain: evoIndicators ? evoIndicators.str.toFixed(2)    : 'n/a',
        regime: evoIndicators ? evoIndicators.regime            : 'n/a',
        status: tickAction,
        armed: armedDiscoverySignal ? armedDiscoverySignal.action : "NONE"
      });
      // Cap memory: keep last 20,000 ticks (~5–6 hours of Step Index)
      if (discoveryAuditLog.length > 20000) discoveryAuditLog.shift();

      lastPriceForDir = price;
    }

    // 3-Scalp: feed tick prices + release trade lock on each tick
    scalpTickPrices.push(price);
    if (scalpTickPrices.length > SCALP_TICK_BUF) scalpTickPrices.shift();
    if (scalpIsTradeActive && realExecState === 'IDLE') scalpIsTradeActive = false;
    if (cfg.strategyMode === 'threeSecScalp') {
      try { scalp_onTick(price); } catch(e) { console.error('[3SCALP]', e); }
    }

    try { detectSignal(); lastSignalEvalAt = Date.now(); } catch (e) { evalErrorCount++; }

    // Update pending signals for strict Deriv 3-Tick simulation/logging
    signals.forEach(sig => {
      if (sig.result === 'PENDING' && !sig.isReal) { // Only auto-resolve paper trades
        sig.ticksAfter.push(price);

        // Wait for exactly 4 ticks after the signal (T1, T2, T3, T4)
        if (sig.ticksAfter.length === 4) {
          const entryPrice = sig.ticksAfter[0]; // T1: The official start tick
          const exitPrice = sig.ticksAfter[3];  // T4: The official exit tick

          if (sig.type === 'BUY') {
            sig.result = (exitPrice > entryPrice) ? 'WIN' : (exitPrice < entryPrice ? 'LOSS' : 'DRAW');
          } else if (sig.type === 'SELL') {
            sig.result = (exitPrice < entryPrice) ? 'WIN' : (exitPrice > entryPrice ? 'LOSS' : 'DRAW');
          }
          updateSignalsUI();
        }
      } else if (sig.result === 'PENDING' && sig.isReal) {
        sig.ticksAfter.push(price); // Real trades are resolved by the Flyout Observer
      }
    });
  }

  // ── Sequence Master Logic ─────────────────────────────────────────────────


  // ── Scoring Logic ─────────────────────────────────────────────────────────


  // ── Signal Detection Logic (Master Version) ───────────────────────────────
  function detectSignal() {
    const n = ticks.length; if (n < 2) return null;
    const t0 = ticks[n - 1], tMinus1 = ticks[n - 2], mode = cfg.strategyMode, eps = cfg.epsilon;
    const streak = Math.max(t0.upStreak, t0.downStreak), isEarly = streak <= 2, isLate = streak >= 4;
    const buyDigits = [0, 5, 6, 7], sellDigits = [2, 3, 4, 8];
    const buyDigitBias = buyDigits.includes(t0.lastDigit), sellDigitBias = sellDigits.includes(t0.lastDigit);

    // Filter indicators
    const currentADX = (t0.adx !== undefined) ? t0.adx : 0;
    const currentRSI = (t0.rsi !== undefined) ? t0.rsi : 50;
    const adxMin = (cfg.adxMin !== undefined) ? cfg.adxMin : 0;
    const adxMax = (cfg.adxMax !== undefined) ? cfg.adxMax : 100;
    const minBBW = (cfg.minBBWidth !== undefined) ? cfg.minBBWidth : 0;
    const isTrending = (currentADX >= adxMin && currentADX <= adxMax) && bbWidth >= minBBW;

    let res = null;

    // discoveryEvolution is handled directly in handleTick via the rolling direction engine
    // No additional signal detection needed here for this mode

    if (res) {
      triggerSignal(res.type, res.conf, res.triggerDesc, res.triggerDigit, res.startTickIndex);
    }
    return null;
  }


  function triggerSignal(type, conf, triggerDesc, triggerDigit, startTickIndex, patternRef) {
    // Decision stamp — visible in console for every trade
    const _rsi = lastMetrics ? lastMetrics.currentRSI.toFixed(1) : 'n/a';
    const _reason = patternRef
        ? `[DISCOVERY] Pattern:${patternRef.sequence} Action:${patternRef.action} RSI:${_rsi}`
        : `[LEGACY] ${triggerDesc || 'strategy signal'}`;
    console.log(`%c🚀 TRADE: ${type} | ${_reason}`, 'color:#3ecf60; font-weight:bold; font-size:12px;');

    const n = ticks.length; if (n === 0) return;
    const t0 = ticks[n - 1];
    const mode = cfg.strategyMode;
    const currentTickIndex = tickSeq;

    if (currentTickIndex - lastSignalTickIndex < cfg.postTradeCooldownTicks || Date.now() - lastTradeClosedAt < cfg.postTradeCooldownMs) return;
    if (realExecState !== 'IDLE') return;

    lastSignalTickIndex = currentTickIndex;
    let finalConf = conf;
    const buyDigits = [0, 5, 6, 7], sellDigits = [2, 3, 4, 8];
    const buyDigitBias = buyDigits.includes(t0.lastDigit), sellDigitBias = sellDigits.includes(t0.lastDigit);

    if (!triggerDesc?.includes('POWER') && ((type === 'BUY' && !buyDigitBias) || (type === 'SELL' && !sellDigitBias))) finalConf -= 10;

    const sig = {
      type: type,
      price: t0.price,
      time: t0.epoch,
      result: 'PENDING',
      ticksAfter: [],
      confidence: Math.min(100, finalConf),
      strategy: mode,
      isReal: cfg.realTradeEnabled,
      triggerDigit: triggerDigit || t0.lastDigit,
      triggerDesc: triggerDesc,
      startTickIndex: startTickIndex || tickSeq + 1,
      signalTime: Date.now(),
      patternRef: patternRef,
      metrics: {
        rsi: t0.rsi || 0,
        adx: t0.adx || 0,
        bbw: bbWidth,
        intensity: t0.intensity,
        epsilon: t0.deltaChange,
        accel: t0.accel5 || 0,
        sLow: sLow,
        sHigh: sHigh,
        trend: t0.trendEma,
        dir: t0.direction,
        streak: Math.max(t0.upStreak, t0.downStreak),
        mean: speedMean,
        std: speedStd
      }
    };
    signals.push(sig); if (signals.length > 50) signals.shift(); recordSessionTrade(sig); updateSignalsUI();
    // GUARD: only execute real trade when the toggle is explicitly ON
    if (cfg.realTradeEnabled === true) { realExecState = 'OPEN_PENDING'; realLockReason = 'EXECUTING'; updateRealUI(); executeRealTrade(type); }
  }

  // ── Infrastructure ────────────────────────────────────────────────────────
  function updateWinsLossesUI() {
    if (lastUI.wins !== realWins) {
      const we = document.getElementById('tt-wins');
      if (we) we.textContent = realWins;
      lastUI.wins = realWins;
    }
    if (lastUI.losses !== realLosses) {
      const le = document.getElementById('tt-losses');
      if (le) le.textContent = realLosses;
      lastUI.losses = realLosses;
    }
  }
  function updateSignalsUI() {
    const el = document.getElementById('tt-signals-list'); if (!el) return;
    el.innerHTML = ''; signals.slice(-10).reverse().forEach(sig => {
      const div = document.createElement('div'); div.className = `tt-signal tt-signal-${sig.type.toLowerCase()}`;
      const badge = sig.result === 'WIN' ? '<span class="tt-badge tt-badge-win">WIN</span>' : sig.result === 'LOSS' ? '<span class="tt-badge tt-badge-loss">LOSS</span>' : '<span class="tt-badge tt-badge-pending">...</span>';
      div.innerHTML = `<span class="tt-signal-type">${sig.type}</span><span class="tt-signal-price">${(sig.entryPriceReal || sig.price).toFixed(2)}</span><span class="tt-signal-time">${new Date(sig.time*1000).toLocaleTimeString([], {hour:'2-digit',minute:'2-digit',second:'2-digit'})} [${sig.confidence}%]</span>${badge}`;
      el.appendChild(div);
    });
  }
  function updateRealUI() {
    const stateStr = realExecState + (realLockReason ? ` (${realLockReason})` : '');
    if (lastUI.state !== stateStr) {
      const stEl = document.getElementById('tt-real-state');
      if (stEl) {
        stEl.textContent = stateStr;
        stEl.style.color = { IDLE: '#3ecf60', RECOVERY: '#e04040', OPEN: '#f0c040', OPEN_PENDING: '#7ec8e3' }[realExecState] || '#fff';
      }
      lastUI.state = stateStr;
    }
    const pnlEl = document.getElementById('tt-real-pnl');
    if (pnlEl) {
      pnlEl.textContent = realPnl.toFixed(2);
      pnlEl.style.color = realPnl >= 0 ? '#3ecf60' : '#e04040';
    }
    updateWinsLossesUI();
  }
  function showAlert(msg) { const el = document.getElementById('tt-alert'); if (el) { el.textContent = msg; el.classList.add('tt-visible'); setTimeout(() => el.classList.remove('tt-visible'), 5000); } }
  function recordSessionTrade(sig) { sessionTradesAll.push(sig); if (sessionTradesAll.length > SESSION_HISTORY_CAP) sessionTradesAll.shift(); }
  function downloadDiscoveryAudit() {
    if (discoveryAuditLog.length === 0) {
      showAlert("No audit logs recorded yet!");
      return;
    }
    const headers = Object.keys(discoveryAuditLog[0]).join(",");
    const rows = discoveryAuditLog.map(row =>
      Object.values(row).map(val => `"${String(val).replace(/"/g, '""')}"`).join(",")
    );
    const blob = new Blob([[headers, ...rows].join("\n")], { type: 'text/csv' });
    const url = URL.createObjectURL(blob);
    const a = document.createElement("a");
    a.href = url;
    a.download = `discovery_audit_${Date.now()}.csv`;
    a.click();
    URL.revokeObjectURL(url);
  }

  function exportCSV() {
    if (!sessionTradesAll.length) return;
    const head = ['Type', 'Strategy', 'Price', 'Tick Time', 'Signal Time', 'Confirm Time', 'Result', 'Digit', 'Desc', 'RSI', 'ADX', 'BBW', 'Intensity', 'Epsilon', 'Accel', 'SLow', 'SHigh', 'Trend', 'Dir', 'Streak', 'Mean', 'Std', 'Conf RSI', 'Conf ADX', 'Conf BBW', 'Conf Int', 'Conf Eps', 'Conf Accel', 'Conf SLow', 'Conf SHigh'];
    const rows = [head].concat(sessionTradesAll.map(s => {
      const m = s.metrics || {}, cm = s.confirmMetrics || {};
      return [s.type, s.strategy, s.price.toFixed(2), s.time, s.signalTime || '', s.confirmTime || '', s.result, s.triggerDigit ?? '', s.triggerDesc ?? '', m.rsi??'', m.adx??'', m.bbw??'', m.intensity??'', m.epsilon??'', m.accel??'', m.sLow??'', m.sHigh??'', m.trend??'', m.dir??'', m.streak??'', m.mean??'', m.std??'', cm.rsi??'', cm.adx??'', cm.bbw??'', cm.intensity??'', cm.epsilon??'', cm.accel??'', cm.sLow??'', cm.sHigh??''];
    }));
    const csv = rows.map(r => r.join(',')).join('\n'); const blob = new Blob([csv], { type: 'text/csv' });
    const url = URL.createObjectURL(blob); const a = document.createElement('a'); a.href = url; a.download = '3tick-signals.csv'; a.click();
  }
  function exportRealCSV() {
    if (!realTrades.length) return;
    const head = ['Signal Time', 'Confirm Time', 'Side', 'Result', 'PnL', 'Digit', 'Desc', 'Sig RSI', 'Sig ADX', 'Sig BBW', 'Sig Int', 'Sig Eps', 'Sig Accel', 'Sig SLow', 'Sig SHigh', 'Conf RSI', 'Conf ADX', 'Conf BBW', 'Conf Int', 'Conf Eps', 'Conf Accel', 'Conf SLow', 'Conf SHigh'];
    const rows = [head].concat(realTrades.map(t => {
      const s = t.signalRef || {}, m = s.metrics || {}, cm = t.confirmMetrics || {};
      return [t.time, t.confirmTime || '', t.side, t.result, t.pnl || '', s.triggerDigit ?? '', s.triggerDesc ?? '', m.rsi??'', m.adx??'', m.bbw??'', m.intensity??'', m.epsilon??'', m.accel??'', m.sLow??'', m.sHigh??'', cm.rsi??'', cm.adx??'', cm.bbw??'', cm.intensity??'', cm.epsilon??'', cm.accel??'', cm.sLow??'', cm.sHigh??''];
    }));
    const csv = rows.map(r => r.join(',')).join('\n'); const blob = new Blob([csv], { type: 'text/csv' });
    const url = URL.createObjectURL(blob); const a = document.createElement('a'); a.href = url; a.download = '3tick-real.csv'; a.click();
  }
  function safeStorage(op, key, val) { try { if (op === 'get') return JSON.parse(localStorage.getItem(key)); if (op === 'set') localStorage.setItem(key, JSON.stringify(val)); } catch (_) { } return null; }
  function saveCfg() { safeStorage('set', 'tt-cfg', cfg); }
  function loadCfg() { const stored = safeStorage('get', 'tt-cfg'); return Object.assign({ strategyMode: 'discoveryEvolution', epsilon: 0.1, realTradeEnabled: false, realTimeoutMs: 40000, realCooldownMs: 5000, postTradeCooldownTicks: 5, postTradeCooldownMs: 5000, debugSignals: true, adxMin: undefined, adxMax: undefined, adxPeriod: 14, rsiPeriod: 14, trendEmaPeriod: 10, minBBWidth: undefined, maxBBWidth: undefined, seqMasterConfig: '', scalp_rsiPeriod: 7, scalp_rsiCallMin: 40, scalp_rsiPutMax: 60, scalp_smiOversold: -40, scalp_smiOverbought: 40, scalp_bbPeriod: 12, scalp_minBbSpread: 0.05 }, stored || {}); }
  function updateSeqMasterUIVisibility() {
    const container = document.getElementById('tt-cfg-seq-master-container');
    if (container) container.style.display = 'none';
    // 3-Scalp: show settings panel and status row only when that mode is active
    const scalpSettings = document.getElementById('tt-scalp-settings');
    const scalpRow      = document.getElementById('tt-scalp-row');
    const regimeRow     = document.getElementById('tt-regime-row');
    const isScalp = cfg.strategyMode === 'threeSecScalp';
    if (scalpSettings) scalpSettings.style.display = isScalp ? 'flex' : 'none';
    if (scalpRow)      scalpRow.style.display      = isScalp ? 'flex' : 'none';
    if (regimeRow)     regimeRow.style.display      = (cfg.strategyMode === 'discoveryEvolution') ? 'flex' : 'none';
  }

  function validateSeqMasterJSON(raw) {
    const el = document.getElementById('tt-cfg-seq-master-json');
    if (!el) return;
    if (!raw.trim()) {
      el.style.borderColor = '#3a4260';
      parsedSeqMasterConfig = null;
      parsedDnaConfig = null;
      return;
    }
    try {
      const parsed = JSON.parse(raw);
      parsedDnaConfig = parsed;
      parsedSeqMasterConfig = null;
      el.style.borderColor = '#3ecf60';
    } catch (e) {
      el.style.borderColor = '#e04040';
      parsedSeqMasterConfig = null;
      parsedDnaConfig = null;
    }
  }

  async function initDnaWorker() {
    const isEvo = cfg.strategyMode === 'discoveryEvolution';

    if (!isEvo) {
      if (dnaWorker) {
        dnaWorker.terminate();
        dnaWorker = null;
      }
      return;
    }
    if (dnaWorker) return;
    try {
      const workerUrl = chrome.runtime.getURL('dnaWorker.js');
      const response = await fetch(workerUrl);
      const script = await response.text();
      const blob = new Blob([script], { type: 'application/javascript' });
      const blobUrl = URL.createObjectURL(blob);

      dnaWorker = new Worker(blobUrl);
      dnaWorker.onmessage = function(e) {
        if (e.data.type === 'signal') {
          handleDnaSignal(e.data.data);
        } else if (e.data.type === 'metrics') {
          lastMetrics = e.data.data;
          handleDnaMetrics(e.data.data);
        } else if (e.data.type === 'NEW_SIGNAL') {
          // Store worker's payload as-is. Key = sequence + regime only.
          // Indicators (hitState) are stored as metadata — not part of the key.
          const { sequence, hitState, action, regime } = e.data.data;
          const patKey = makePatternKey(sequence, regime);

          if (patternLibrary[patKey]) {
            patternLibrary[patKey].count++;
          } else {
            patternLibrary[patKey] = { indicators: hitState, action, regime, sequence, count: 1 };
          }

          updateDiscoveryUI(e.data.data);
        }
      };
    } catch (e) {
      console.error("Failed to init DNA worker", e);
      showAlert('DNA ENGINE ERROR: Check Console');
    }
  }


  function logDiscoveryFailure(pattern) {
    if (!discoveryDb) return;
    const tx = discoveryDb.transaction('fail_log', 'readwrite');
    const store = tx.objectStore('fail_log');
    store.add({
      timestamp: Date.now(),
      sequence: pattern.sequence,
      action: pattern.action,
      hitState: pattern.hitState,
      regime: pattern.regime
    });
  }

  function updateDiscoveryUI(s, isFail = false, actualMetrics = null) {
    const displayRegime = s.regime ? s.regime : "Unknown Regime";

    if (isFail) {
        // ── Fail-execution path — always appends a new row (failures are unique events) ──
        if (!actualMetrics || actualMetrics.rsi === undefined) {
            // Metrics not ready — skip render, DB log already handled by logDiscoveryFailure
            console.warn("[EVO] Fail-log skipped: metrics not available for", s.sequence);
            return;
        }
        if (!s.hitState) {
            // patternRef missing hitState (e.g. from an older armedDiscoverySignal) — skip safely
            console.warn("[EVO] Fail-log skipped: hitState missing on pattern", s.sequence);
            return;
        }
        const container = document.getElementById('tt-fail-exec-list');
        if (!container) return;
        const el = document.createElement('div');
        el.className = "tt-discovery-row";
        el.style.cssText = "border-bottom:1px solid #333; padding:5px; font-size:11px; background:rgba(224,64,64,0.1);";
        el.innerHTML = `
            <div style="display:flex; justify-content:space-between; margin-bottom: 4px;">
                <b style="color:#e04040;">FAILED: ${s.sequence} ${s.action}</b>
                <span style="color:#888;">${displayRegime}</span>
            </div>
            <div style="display:flex; justify-content:space-between; color:#7a8499; font-size:9px;">
                <div>RSI Act: ${actualMetrics?.rsi ? actualMetrics.rsi.toFixed(1) : 'WAITING'} (Exp: ${s.hitState.rsi.toFixed(1)})</div>
                <div>BBW Act: ${actualMetrics.bbw.toFixed(4)}</div>
            </div>
        `;
        container.prepend(el);
        if (container.children.length > 1000) container.lastChild.remove();
        return;
    }

    // ── Discovery feed path — collapsing: one row per unique sequence ─────────
    const feed = document.getElementById('tt-discovery-feed');
    if (!feed) return;

    // Display lookup uses sequence+regime key — same as write path.
    const _uiKey = makePatternKey(s.sequence, s.regime);
    const libEntry = patternLibrary[_uiKey] || null;
    const count = libEntry ? libEntry.count : 1;
    // Always show hit count — even at 1 so you can see patterns from first appearance
    const countDisplay = `<span style="color:#f0a060; font-weight:bold; margin-left:4px;">(${count}x)</span>`;

    const rowHTML = `
        <span style="color:#7a8499;">[${new Date().toLocaleTimeString([], {hour12:false})}]</span>
        <span style="color:${s.action === 'CALL' ? '#3ecf60' : '#e04040'}; font-weight:bold;"> ${s.sequence} ${s.action}</span>
        ${countDisplay}
        <span style="color:#7ec8e3; font-size:9px; margin-left:4px;">R:${s.hitState.rsi.toFixed(1)} B:${s.hitState.bbw.toFixed(3)}</span>
        <span style="background:#1e2338; color:#7ec8e3; padding:0 3px; border-radius:2px; font-size:8px; margin-left:4px;">${displayRegime}</span>
        <span style="color:#888; font-size:8px; margin-left:4px;">STR:${s.hitState.str.toFixed(2)} ext:${s.ext || '?'}</span>
    `;

    // Find existing row for this sequence+regime fingerprint and update in-place, or create a new one.
    const _feedKey = makePatternKey(s.sequence, s.regime);
    let entry = feed.querySelector(`[data-seq="${CSS.escape(_feedKey)}"]`);
    if (entry) {
        entry.innerHTML = rowHTML;
    } else {
        entry = document.createElement('div');
        entry.setAttribute('data-seq', _feedKey);
        entry.style.cssText = "margin-bottom:2px; border-bottom:1px solid rgba(255,255,255,0.05); padding-bottom:2px; font-size:10px; font-family:monospace;";
        entry.innerHTML = rowHTML;
    }

    // Always move to top (updated or new)
    feed.prepend(entry);

    // NOTE: No row cap — patterns are never deleted from the feed.
    //       The feed is scrollable so all discovered patterns remain visible.

    // Update Armed counter
    const countEl = document.getElementById('tt-armed-count');
    if (countEl) countEl.textContent = `(Armed: ${activeTradePool.size})`;

    // Update total unique pattern count in header — count composite keys in library
    const patCountEl = document.getElementById('tt-pattern-count');
    if (patCountEl) patCountEl.textContent = `[Patterns: ${Object.keys(patternLibrary).length}]`;
  }

  function handleDnaMetrics(data) {
    if (data) {
        currentRegime = data.regime || 'D';
        currentEntropy = data.entropy || 0;
        currentStrain = data.stats ? data.stats.str : 0;
    }
    updateDnaUI({ metrics: data });
  }

  function handleDnaSignal(data) {
    updateDnaUI(data);
    if (data.status === 'SIGNAL') {
      const type = data.action === 'CALL' ? 'BUY' : (data.action === 'PUT' ? 'SELL' : data.action);
      triggerSignal(type, 100, `DNA:${data.action} (${(data.similarity*100).toFixed(1)}%)`);
    } else if (cfg.debugSignals && tickSeq % 10 === 0) {
      console.log("[DNA Worker]", data);
    }
  }

  function updateDnaUI(data) {
    const diag = document.getElementById('tt-dna-diag');
    const discoveryDiag = document.getElementById('tt-discovery-diag');
    const signals = document.getElementById('tt-signals-list');

    if (cfg.strategyMode === 'discoveryEvolution') {
      if (diag) diag.style.display = 'none';
      if (discoveryDiag) discoveryDiag.style.display = 'flex';
      if (signals) signals.style.display = 'none';
    } else {
      if (diag) diag.style.display = 'none';
      if (discoveryDiag) discoveryDiag.style.display = 'none';
      if (signals) signals.style.display = 'flex';
      return;
    }

    if (!data || !data.metrics) return;
    const m = data.metrics;
    const stats = m.stats;
    if (!stats) return;

    // 1. Update Match Meter
    const sim = data.similarity || data.maxSimilarity || 0;
    const matchPct = (sim * 100).toFixed(1);
    const bar = document.getElementById('tt-dna-match-bar');
    const label = document.getElementById('tt-dna-match-label');
    if (bar) {
      bar.style.width = `${matchPct}%`;
      bar.style.background = sim >= 0.85 ? '#3ecf60' : (sim >= 0.70 ? '#f0c040' : '#e04040');
    }
    if (label) {
      label.textContent = `${matchPct}%`;
      label.style.color = sim >= 0.85 ? '#3ecf60' : (sim >= 0.70 ? '#f0c040' : '#e04040');
      if (sim >= 0.85) label.textContent += " - LATCHED";
    }

    // 2. Update Trinity Deltas with color logic
    const profiles = parsedDnaConfig?.dnaProfiles || {};
    // Determine which profile to compare against for color-coding (best match or current direction)
    const activeAction = data.action || (stats.rsiDelta > 0 ? 'CALL' : 'PUT');
    const targetMeans = profiles[activeAction]?.means || {};

    updateMetric('rsi', stats.rsiDelta, targetMeans.rsiDelta);
    updateMetric('bbw', stats.bbwDelta, targetMeans.bbwDelta, 3);
    updateMetric('str', stats.strDelta, targetMeans.strDelta, 3);

    function updateMetric(id, current, target, dp = 2) {
      const valEl = document.getElementById(`tt-dna-${id}-val`);
      const targetEl = document.getElementById(`tt-dna-${id}-target`);
      if (valEl) {
        valEl.textContent = current.toFixed(dp);
        if (target !== undefined) {
          // Cyan if moving toward target (current and target have same sign), Red if away
          const toward = (Math.sign(current) === Math.sign(target)) && (Math.abs(current) > 0);
          valEl.className = toward ? 'tt-color-toward' : 'tt-color-away';
        } else {
          valEl.className = 'tt-color-neutral';
        }
      }
      if (targetEl) targetEl.textContent = target !== undefined ? `Target: ${target.toFixed(dp)}` : '-';
    }

    // 3. Environmental Badges
    const entropyEl = document.getElementById('tt-dna-entropy-badge');
    if (entropyEl) {
      entropyEl.textContent = `ENTROPY: ${m.entropy.toFixed(2)}`;
      const ok = m.entropy >= (parsedDnaConfig?.minEntropy || 2.8);
      entropyEl.style.background = ok ? '#1a3d28' : '#3d1a1a';
      entropyEl.style.color = ok ? '#3ecf60' : '#e04040';
      if (!ok) entropyEl.textContent += " (LOW)";
    }

    const vgateEl = document.getElementById('tt-dna-vgate');
    if (vgateEl) {
      const ok = m.bbwDelta > 0;
      vgateEl.style.color = ok ? '#3ecf60' : '#e04040';
    }

    const regimeEl = document.getElementById('tt-dna-regime');
    if (regimeEl) {
      regimeEl.textContent = `REGIME: ${m.regime}`;
      regimeEl.style.color = m.regime === 'D' ? '#3ecf60' : '#f0c040';
    }
  }

  function applyConfigToUI() {
    const dbg = document.getElementById('tt-cfg-debug'),
          re = document.getElementById('tt-cfg-real-enabled'),
          mode = document.getElementById('tt-cfg-strategy-mode'),
          seqJson = document.getElementById('tt-cfg-seq-master-json');

    if (dbg) dbg.checked = cfg.debugSignals;
    if (re) re.checked = !!cfg.realTradeEnabled;
    if (mode) mode.value = cfg.strategyMode;
    if (seqJson) {
      seqJson.value = cfg.seqMasterConfig || '';
      validateSeqMasterJSON(seqJson.value);
    }

    // Wire 3-Scalp settings inputs
    const scalpFields = {
      'tt-scalp-rsi-period':    ['scalp_rsiPeriod',    v => parseInt(v)],
      'tt-scalp-rsi-call-min':  ['scalp_rsiCallMin',   v => parseFloat(v)],
      'tt-scalp-rsi-put-max':   ['scalp_rsiPutMax',    v => parseFloat(v)],
      'tt-scalp-smi-oversold':  ['scalp_smiOversold',  v => parseFloat(v)],
      'tt-scalp-smi-overbought':['scalp_smiOverbought',v => parseFloat(v)],
      'tt-scalp-bb-period':     ['scalp_bbPeriod',     v => parseInt(v)],
      'tt-scalp-min-bb-spread': ['scalp_minBbSpread',  v => parseFloat(v)]
    };
    Object.entries(scalpFields).forEach(([id, [key, parse]]) => {
      const el = document.getElementById(id);
      if (!el) return;
      el.value = cfg[key] !== undefined ? cfg[key] : el.placeholder;
      el.addEventListener('input', function() {
        const v = parse(this.value);
        if (!isNaN(v)) { cfg[key] = v; saveCfg(); }
      });
    });

    updateSeqMasterUIVisibility();
    updateRealUI();
  }
  function startWatchdog() { if (watchdogInterval) clearInterval(watchdogInterval); watchdogInterval = setInterval(() => { const now = Date.now(); if (wsState !== 'connected') return; if (lastTickProcessedAt > 0 && now - lastTickProcessedAt > WATCHDOG_TICK_TIMEOUT) { if (ws && ws.readyState !== WebSocket.CLOSED && ws.readyState !== WebSocket.CLOSING) ws.close(); scheduleReconnect(); } }, WATCHDOG_INTERVAL); }
  let subObserver = null, lastFlyoutNode = null;
  function setupFlyoutObserver() {
    if (flyoutObserver) return;
    flyoutObserver = new MutationObserver(() => {
      const flyout = document.querySelector(SEL_FLYOUT);
      if (flyout) {
        if (flyout !== lastFlyoutNode) {
          if (subObserver) subObserver.disconnect();
          lastFlyoutNode = flyout;
          subObserver = new MutationObserver(() => processFlyout(flyout));
          subObserver.observe(flyout, { childList: true, subtree: true, characterData: true });
          processFlyout(flyout);
        }
      } else {
        if (subObserver) { subObserver.disconnect(); subObserver = null; lastFlyoutNode = null; }
        if (realExecState === 'OPEN' || realExecState === 'RECOVERY') {
          if (finalizationTimer) clearTimeout(finalizationTimer);
          finalizationTimer = setTimeout(() => {
              if (!document.querySelector(SEL_FLYOUT)) {
                  realOpenCount = 0;
                  const finalResult = lastSeenResult || (lastSeenPnL > 0 ? 'WIN' : 'LOSS');
                  finalizeRealTrade({ pnl: lastSeenPnL, result: finalResult });
                  realExecState = 'IDLE'; realLockReason = ''; lastSeenPnL = 0; lastSeenResult = null; updateRealUI();
              }
              finalizationTimer = null;
          }, 1000);
        }
      }
    });
    flyoutObserver.observe(document.body, { childList: true, subtree: true });
  }

  function processFlyout(flyout) {
      const text = flyout.textContent || '';

      // Purchase confirmation
      if (text.includes("Contract bought") || text.includes("ID:") || text.includes("Reference ID") || text.includes("Reference no") || text.includes("Contract ID")) {
        // Reverse search for the most recent pending real signal
        const sig = sessionTradesAll.slice().reverse().find(s => s.result === 'PENDING' && s.isReal && !s.confirmMetrics);
        if (sig) {
          sig.startTickIndex = tickSeq + 1;
          sig.confirmTime = Date.now();
          const t0 = ticks[ticks.length - 1];
          if (t0) {
            sig.confirmMetrics = {
              rsi: t0.rsi,
              adx: t0.adx,
              bbw: bbWidth,
              intensity: t0.intensity,
              epsilon: t0.deltaChange,
              accel: t0.accel5 || 0,
              sLow: sLow,
              sHigh: sHigh
            };
          }
          const real = realTrades.slice().reverse().find(t => t.result === 'PENDING' && !t.confirmTime);
          if (real) {
            real.startTickIndex = sig.startTickIndex;
            real.confirmTime = sig.confirmTime;
            real.confirmMetrics = sig.confirmMetrics;
          }
        }
      }

      // 1. Buffer Result (Watch colors continually)
      const profitCard = flyout.querySelector('.dc-contract-card--profit, .dc-contract-card--green');
      const lossCard   = flyout.querySelector('.dc-contract-card--loss, .dc-contract-card--red');
      if (profitCard) lastSeenResult = 'WIN';
      else if (lossCard) lastSeenResult = 'LOSS';

      // 2. Buffer PnL
      const pnlSpan = flyout.querySelector('[data-testid="dt_span"]');
      if (pnlSpan) {
        const val = parseFloat((pnlSpan.textContent || '').replace(/[^-0-9.]/g, ''));
        if (!isNaN(val)) lastSeenPnL = val;
      }

      const noOpen = text.includes('no open positions');
      const hasActiveCard = !!flyout.querySelector('.dc-contract-card');
      const flyoutCount = noOpen ? 0 : (text.match(/(\d+)\s+open\s+position/i) ? parseInt(text.match(/(\d+)\s+open\s+position/i)[1], 10) : realOpenCount);

      if (flyoutCount === 0 && !hasActiveCard && (realExecState === 'OPEN' || realExecState === 'RECOVERY')) {
          finalizeRealTrade({ pnl: lastSeenPnL, result: lastSeenResult || (lastSeenPnL > 0 ? 'WIN' : 'LOSS') });
          realExecState = 'IDLE'; realLockReason = ''; lastSeenPnL = 0; lastSeenResult = null; updateRealUI();
      }

      if (flyoutCount !== realOpenCount) {
        realOpenCount = flyoutCount;
        updateRealExecStateFromDOM(flyoutCount);
      }
  }
  function updateRealExecStateFromDOM(count) {
    if (count > 0 && ['IDLE', 'OPEN_PENDING'].includes(realExecState)) {
      realExecState = 'OPEN';
      lastSeenPnL = 0;
      const pending = signals.find(s => s.result === 'PENDING' && !s.entryPriceReal);
      if (pending && ticks.length) {
        pending.entryPriceReal = ticks[ticks.length - 1].price;
        updateSignalsUI();
      }
    }
    updateRealUI();
  }
  function finalizeRealTrade(res) {
    if (!realTrades.length) return;
    const last = realTrades[realTrades.length - 1];
    if (last.result !== 'PENDING') return;
    last.result = res.result || 'LOSS';
    last.pnl = res.pnl || 0;
    if (last.result === 'WIN') {
      realWins++;
    } else {
      realLosses++;
      // Stop on Loss logic
      if (last.result === 'LOSS') {
        cfg.realTradeEnabled = false;
        saveCfg();
        const reToggle = document.getElementById('tt-cfg-real-enabled');
        if (reToggle) reToggle.checked = false;
        showAlert('TRADING STOPPED: LOSS DETECTED');
      }
    }
    realPnl += last.pnl;
    const simTrade = last.signalRef || signals.find(s => s.result === 'PENDING' && s.isReal);
    if (simTrade) {
      simTrade.result = res.result;
      simTrade.priceAfter = ticks.length ? ticks[ticks.length - 1].price : simTrade.price;

      // Discovery Evolution: The Purge
      if (simTrade.strategy === 'discoveryEvolution' && simTrade.patternRef) {
        const pattern = simTrade.patternRef;
        const key = `${pattern.sequence}-${pattern.action}`;
        if (res.result === 'LOSS') {
          activeTradePool.delete(key);
          logDiscoveryFailure(pattern);
          updateDiscoveryUI(pattern, true, simTrade.metrics);
        }
      }
    }
    lastTradeClosedAt = Date.now();
    lastTradeClosedTick = tickSeq;
    if (realExecTimer) { clearTimeout(realExecTimer); realExecTimer = null; }
    updateRealUI();
    updateSignalsUI();
  }
  async function executeRealTrade(side) {
    console.log(`[EXEC] Starting real trade sequence for ${side}`);
    // Double-failsafe: abort immediately if toggle was switched off between signal and execution
    if (!cfg.realTradeEnabled) {
      console.log(`[EXEC] Aborted: Real trade toggle is OFF`);
      realExecState = 'IDLE'; realLockReason = ''; updateRealUI(); return;
    }
    if (Date.now() - lastRealTradeAt < cfg.realCooldownMs) {
      console.log(`[EXEC] Aborted: Still in cooldown period`);
      return;
    }

    const buyLabel = side === 'BUY' ? 'Rise' : 'Fall', activeClass = side === 'BUY' ? CLASS_RISE_ACTIVE : CLASS_FALL_ACTIVE;
    try {
      console.log(`[EXEC] Attempting to set side to ${buyLabel} (expecting class: ${activeClass})`);
      if (!await setRealTradeSide(buyLabel, activeClass)) {
        throw new Error('side_failed');
      }

      console.log(`[EXEC] Waiting for purchase button to be ready...`);
      if (!await waitRealBuyReady()) {
        throw new Error('not_ready');
      }

      const btn = document.querySelector(SEL_PURCHASE_BTN);
      if (!btn) {
        throw new Error('btn_not_found');
      }
      if (!btn.classList.contains(activeClass)) {
        throw new Error(`btn_mismatch: missing ${activeClass}`);
      }

      console.log(`[EXEC] Firing click event on purchase button!`);
      simulateExternalClick(btn);
      lastRealTradeAt = Date.now();

      const signalToMark = signals.find(s => s.result === 'PENDING' && s.isReal);
      realTrades.push({ time: Date.now(), signal: side, side: buyLabel, result: 'PENDING', signalRef: signalToMark, startTickIndex: null, confirmTime: null });
      if (realTrades.length > SESSION_HISTORY_CAP) realTrades.shift();

      realExecTimer = setTimeout(() => {
        if (['OPEN_PENDING', 'OPEN'].includes(realExecState)) {
          console.warn(`[EXEC] Trade resolution timeout reached (no flyout detected). Entering RECOVERY.`);
          realExecState = 'RECOVERY'; realLockReason = 'TIMEOUT'; updateRealUI();
        }
      }, cfg.realTimeoutMs);

    } catch (e) {
      console.error(`[EXEC] Failed:`, e.message);
      realLockReason = 'ERR:' + e.message;
      updateRealUI();
      setTimeout(() => {
        if (realExecState === 'OPEN_PENDING') {
          console.log(`[EXEC] Releasing lock back to IDLE after error`);
          realExecState = 'IDLE'; realLockReason = ''; updateRealUI();
        }
      }, 3000);
    }
  }

  async function setRealTradeSide(label, activeClass) {
    for (let i = 0; i < 5; i++) { // Increased retries from 3 to 5
      const btn = document.querySelector(SEL_PURCHASE_BTN);
      if (btn && btn.classList.contains(activeClass)) {
        console.log(`[EXEC] Side already correct (${label})`);
        return true;
      }

      const target = Array.from(document.querySelectorAll(SEL_SIDE_BTNS)).find(b => (b.textContent || '').includes(label));
      if (target) {
        console.log(`[EXEC] Clicking side tab ${label} (Attempt ${i+1})`);
        simulateExternalClick(target);
        await new Promise(r => setTimeout(r, 200)); // Increased wait time to 200ms to allow DOM paint
      } else {
        console.warn(`[EXEC] Could not find side tab for ${label}`);
        await new Promise(r => setTimeout(r, 100));
      }
    }
    console.error(`[EXEC] Failed to set side to ${label} after 5 attempts`);
    return false;
  }

  function simulateExternalClick(el) {
    const opts = { bubbles: true, cancelable: true, view: window };
    el.dispatchEvent(new MouseEvent('mouseenter', opts));
    el.dispatchEvent(new MouseEvent('mousedown', opts));
    el.focus();
    el.dispatchEvent(new MouseEvent('mouseup', opts));
    el.dispatchEvent(new MouseEvent('click', opts));
    el.dispatchEvent(new MouseEvent('mouseleave', opts));
  }

  async function waitRealBuyReady() {
    for (let i = 0; i < 10; i++) { // Increased retries from 5 to 10
      const btn = document.querySelector(SEL_PURCHASE_BTN);
      if (btn) {
        const isLoading = btn.getAttribute('data-loading') === 'true';
        const isDisabledAttr = btn.getAttribute('aria-disabled') === 'true';
        if (!isLoading && !btn.disabled && !isDisabledAttr) {
           return true;
        }
        console.log(`[EXEC] Button not ready (loading: ${isLoading}, disabled: ${btn.disabled}, aria-disabled: ${isDisabledAttr}). Waiting...`);
      } else {
        console.warn(`[EXEC] Purchase button completely missing during wait check`);
      }
      await new Promise(r => setTimeout(r, 100)); // Wait 100ms between checks
    }
    console.error(`[EXEC] Purchase button never became ready`);
    return false;
  }
  function initIndexedDB() {
    const request = indexedDB.open("Discovery_Audit", 1);
    request.onupgradeneeded = (e) => {
      discoveryDb = e.target.result;
      if (!discoveryDb.objectStoreNames.contains('fail_log')) {
        discoveryDb.createObjectStore('fail_log', { keyPath: 'id', autoIncrement: true });
      }
    };
    request.onsuccess = (e) => { discoveryDb = e.target.result; };
    request.onerror = (e) => { console.error("IndexedDB error", e); };
  }

  function init() { if (document.getElementById('tt-overlay')) return; cfg = loadCfg(); buildOverlay(); initDnaWorker(); initIndexedDB(); connect(); startWatchdog(); setupFlyoutObserver(); window._tt_cfg = cfg; window._tt_detect = detectSignal; }
  if (document.body) init(); else document.addEventListener('DOMContentLoaded', init);
})();
