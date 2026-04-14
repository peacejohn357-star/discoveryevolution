# 3Tick Scalper – Step Index 100 Assistant

A Chrome extension that overlays a real-time trading assistant on [dtrader.deriv.com](https://dtrader.deriv.com) for **Step Index 100** manual and automated scalping using 3-tick micro-timing logic.

---

## Features

| Feature | Details |
|---|---|
| **Micro-Timing Engine** | Streams Step Index 100 ticks via the public Deriv WebSocket and calculates real-time microstructure features (normalized speed, speed trend, streaks, delta change, and last digits). |
| **Adaptive Speed Bands** | Uses a 100-tick rolling buffer to calculate dynamic $S_{high}$ and $S_{low}$ thresholds using a hybrid of 70th/30th percentiles and Standard Deviation ($mean \pm std$). |
| **4 Advanced Strategies** | Includes **Structural** (base layer), **Hybrid** (optimal balance), **Momentum** (early entry), and **Reversal** (exhaustion) logic. |
| **Peak Speed Prevention** | Momentum strategy detects acceleration and enters *before* price reaches peak speed ($S_{high}$) to maximize 3-tick window efficiency. |
| **No-Trade Filters** | Global filters block entries during transition streak zones (3-4), neutral momentum (within 0.2 step epsilon), or flat mid-range trends. |
| **Real Execution** | Master toggle to enable automated clicking of "Rise"/"Fall" and "Purchase" buttons with robust state management and outcome tracking via DOM observation. |
| **Draggable Overlay** | Floating statistics panel showing real-time price, speed distribution, strategy confidence, and session W/L performance. |
| **CSV Export** | Export signal history and real-trade execution logs for performance analysis. |

---

## How signals work (Mathematical Model)

1. **Feature Extraction**
   - **Speed**: $delta\_steps / delta\_time\_ms$ (where 1 step = 0.1 price units).
   - **Speed Trend**: Change in absolute speed (Acceleration vs. Deceleration).
   - **Streaks**: Consecutive ticks in the same direction.
   - **Epsilon**: Neutral momentum zone defined as $\pm 0.2$ steps.

2. **Adaptive Thresholds**
   - $S_{high} = \max(p70, mean + std)$
   - $S_{low} = \min(p30, mean - std)$

3. **Strategy Hierachy**
   - **Structural**: Enters on digit-set bias ({0,5,6} for BUY, {2,3,8} for SELL) aligned with delta change.
   - **Hybrid**: Combines digit bias with momentum timing and early-streak confirmation.
   - **Momentum**: Targets start of move. Requires Early Streak (0-2), positive speed trend, and speed *below* $S_{high}$.
   - **Reversal**: Targets exhaustion. Requires Late Streak ($\ge 5$), negative speed trend, and speed *at or below* $S_{low}$.

4. **Scoring & Bias**
   - Price last digits act as a **bias filter/boost**, increasing or decreasing signal confidence.
   - Signals are evaluated in order of priority: Structural $\to$ Hybrid $\to$ Momentum $\to$ Reversal.

---

## Installation (unpacked extension)

1. **Download / clone this repository.**
2. Open Chrome and go to `chrome://extensions`.
3. Enable **Developer mode** (toggle in the top-right corner).
4. Click **Load unpacked** and select the repository folder.
5. Navigate to [https://dtrader.deriv.com](https://dtrader.deriv.com).
   The **3Tick Timing V2** panel appears in the top-right corner.

---

## License

MIT
