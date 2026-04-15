# 3Tick Scalper – Step Index 100 Assistant

A Chrome extension that overlays a real-time trading assistant on [dtrader.deriv.com](https://dtrader.deriv.com) for **Step Index 100** manual and automated scalping.

---

## Features

| Feature | Details |
|---|---|
| **Strategy Modes** | Features two main operational modes: **🧬 Discovery Evolution** (pattern matching DNA) and **⚡ 3-Sec Scalp** (momentum indicators). |
| **Discovery Evolution** | Analyzes rolling tick sequences, tracks metrics (RSI, BBW, Strain), detects market regimes (A, B, C, D), and discovers structural DNA patterns. |
| **3-Sec Scalp** | Utilizes 1-minute candle weather (Bullish/Bearish/Flat), SMI crossovers, MACD momentum, and tick-level Bollinger Bands for ultra-short setups. |
| **Micro-Timing Engine** | Streams Step Index 100 ticks via the public Deriv WebSocket and calculates real-time microstructure features (normalized speed, streaks, delta change). |
| **Real Execution Engine** | Master toggle to enable automated clicking of "Rise"/"Fall" and "Purchase" buttons with robust state management and outcome tracking via DOM observation. |
| **Draggable Overlay** | Floating statistics panel showing real-time price, strategy confidence, DNA metrics, and session W/L performance. |
| **CSV Export & Audit** | Export signal history and detailed Discovery Audit logs for rigorous performance analysis. |

---

## Strategy Details

### 🧬 Discovery Evolution
Uses a background worker (`dnaWorker.js`) to process rolling tick buffers and compute indicators (RSI, EMA, Standard Deviation, Bollinger Band Width, Strain). It categorizes market behavior into distinct "Regimes" (A=Consolidation, B=Trending, C=Volatility, D=Noise/Default). It records non-flat movement patterns and tracks their historical hit states, armed to strike when identical sequence and regime criteria align.

### ⚡ 3-Sec Scalp
Monitors 1-minute candles via a secondary WebSocket feed to determine market "Weather" (Bullish, Bearish, or Flat). Tick-level entries are triggered by identifying Bollinger Band touches confirmed by Stochastic Momentum Index (SMI) crossovers and supportive MACD histogram momentum.

---

## Real-Trade Execution Engine
When the "Enable Real Execution" toggle is engaged, the extension transitions from a passive signal generator to an active execution agent:
- Detects actionable signals.
- Verifies cooldown timers to prevent rapid over-trading.
- Automatically selects the correct "Rise" or "Fall" tab.
- Simulates external clicks on the primary "Purchase" button.
- Observes the Deriv `dc-flyout` DOM elements to track trade outcomes (WIN/LOSS) and accurately record PnL.
- Halts real trading automatically upon encountering a LOSS as a capital protection safeguard.

---

## Installation (Unpacked Extension)

1. **Download / clone this repository.**
2. Open Chrome and go to `chrome://extensions`.
3. Enable **Developer mode** (toggle in the top-right corner).
4. Click **Load unpacked** and select the repository folder.
5. Navigate to [https://dtrader.deriv.com](https://dtrader.deriv.com).
   The **3Tick Timing V2** panel appears in the top-right corner.

---

## License

MIT
