/**
 * DNA Worker for Statistical DNA Strategy
 */

let lastDiscoveredStreakStart = "";

// Rolling price buffer — content.js sends ONE price at a time
const PRICE_BUF_MAX = 500;
let rollingPrices = [];

self.onmessage = function(e) {
    const { type, price, config } = e.data;

    if (type === 'compute') {
        if (price === undefined || price === null) return;

        // Append incoming single price to the rolling buffer
        rollingPrices.push(parseFloat(price));
        if (rollingPrices.length > PRICE_BUF_MAX) rollingPrices.shift();

        const prices = rollingPrices; // Alias for all downstream functions
        if (prices.length < 50) return;

        // 1. Existing DNA Logic
        const result = computeDNA(prices, config);
        if (result) {
            self.postMessage({ type: 'signal', data: result });
        }

        // 2. Discovery Evolution Logic
        const rsiArr = calcRSI(prices, 14);
        const ema10Arr = calcEMA(prices, 10);
        const stdDev10Arr = calcStdDev(prices, 10);
        const bbwArr = calcBBW(ema10Arr, stdDev10Arr);
        const ema50Arr = calcEMA(prices, 50);
        const stdDev20Arr = calcStdDev(prices, 20);
        const strainArr = calcStrain(prices, ema50Arr, stdDev20Arr);
        const roc2Arr = calcAbsoluteROC(prices, 2);

        // Continuous metric reporting
        const n = prices.length;
        const currentRSI = rsiArr[n - 1];
        const currentBBW = bbwArr[n - 1];
        const currentStr = strainArr[n - 1];
        const rsiDelta = n >= 5 ? currentRSI - rsiArr[n - 5] : 0;
        const bbwDelta = n >= 5 ? currentBBW - bbwArr[n - 5] : 0;
        const strDelta = n >= 5 ? currentStr - strainArr[n - 5] : 0;
        const regime = detectCurrentRegime(prices, rsiArr, bbwArr, strainArr, n - 1);
        const entropy = calcShannonEntropy(prices.slice(-100));

        const metricsData = {
            regime,
            entropy,
            bbwDelta,
            currentBBW,
            currentRSI,   // top-level — content.js destructures this directly
            currentStr,   // top-level — content.js destructures this directly
            stats: {
                rsi: currentRSI,
                rsiDelta: rsiDelta,
                bbw: currentBBW,
                bbwDelta: bbwDelta,
                str: currentStr,
                strDelta: strDelta,
                roc2: roc2Arr[n - 1]
            }
        };

        self.postMessage({
            type: 'metrics',
            data: metricsData
        });

        discoverPatterns(prices, rsiArr, bbwArr, strainArr, regime);
        checkMicroTrap(prices, ema10Arr, roc2Arr);
    }
};

function computeDNA(prices, config) {
    if (!config || !config.dnaProfiles) return null;

    // 1. Calculate Indicators
    const n = prices.length;
    const currentPrice = prices[n - 1];

    // We need at least 10-15 ticks for indicators to stabilize, and 50 for EMA50
    const rsiArr = calcRSI(prices, 14);
    const ema10Arr = calcEMA(prices, 10);
    const stdDev10Arr = calcStdDev(prices, 10);
    const bbwArr = calcBBW(ema10Arr, stdDev10Arr);

    const ema50Arr = calcEMA(prices, 50);
    const stdDev20Arr = calcStdDev(prices, 20);
    const strainArr = calcStrain(prices, ema50Arr, stdDev20Arr);

    const currentRSI = rsiArr[n - 1];
    const currentBBW = bbwArr[n - 1];
    const currentStr = strainArr[n - 1];

    // 2. Calculate Deltas (5-tick Delta: Current - T-4)
    // End of 5th tick means we look back 4 intervals
    if (n < 5) return null;
    const rsiDelta = currentRSI - rsiArr[n - 5];
    const bbwDelta = currentBBW - bbwArr[n - 5];
    const strDelta = currentStr - strainArr[n - 5];

    const currentStats = {
        rsi: currentRSI,
        rsiDelta: rsiDelta,
        bbw: currentBBW,
        bbwDelta: bbwDelta,
        str: currentStr,
        strDelta: strDelta
    };

    // 3. Regime Detection (Regime D: Noise)
    const regime = detectCurrentRegime(prices, rsiArr, bbwArr, strainArr, n - 1);
    const minEntropy = config.minEntropy || 2.8;
    const entropy = calcShannonEntropy(prices.slice(-100)); // Last 100 digits

    // 4. Gates
    const isRegimeD = regime === 'D';
    const entropyPass = entropy >= minEntropy;
    const bbwDeltaPass = bbwDelta > (config.vetos?.minBbwDelta || 0);

    // Veto: Low Volatility Trap
    const bbwVeto = currentBBW <= (config.vetos?.failDnaBbwMax || 0.40);

    if (!isRegimeD || !entropyPass || !bbwDeltaPass || bbwVeto) {
        return {
            status: 'GATED',
            metrics: { regime, entropy, bbwDelta, currentBBW, stats: currentStats }
        };
    }

    // 5. Z-Score Matching
    let bestMatch = null;
    let maxSimilarity = 0;

    for (const action in config.dnaProfiles) {
        const profile = config.dnaProfiles[action];
        const similarity = calculateDNAMatch(currentStats, profile);

        if (similarity > maxSimilarity) {
            maxSimilarity = similarity;
            bestMatch = action;
        }
    }

    if (bestMatch && maxSimilarity >= (config.matchThreshold || 0.85)) {
        return {
            status: 'SIGNAL',
            action: bestMatch,
            similarity: maxSimilarity,
            metrics: { regime, entropy, bbwDelta, currentBBW, stats: currentStats }
        };
    }

    return {
        status: 'NO_MATCH',
        maxSimilarity,
        metrics: { regime, entropy, bbwDelta, currentBBW, stats: currentStats }
    };
}

function calculateDNAMatch(stats, profile) {
    const means = profile.means;
    const sigmas = profile.sigmas;
    let zSum = 0;
    let count = 0;

    for (const key in means) {
        if (stats[key] !== undefined && sigmas[key] > 0) {
            const z = Math.abs((stats[key] - means[key]) / sigmas[key]);
            zSum += z;
            count++;
        }
    }

    if (count === 0) return 0;
    const avgZ = zSum / count;
    return 1 / (1 + avgZ);
}

function calcShannonEntropy(prices) {
    const counts = new Array(10).fill(0);
    prices.forEach(p => {
        const d = Math.round(Math.round(p * 10) % 10);
        counts[d]++;
    });

    const n = prices.length;
    let entropy = 0;
    counts.forEach(c => {
        if (c > 0) {
            const p = c / n;
            entropy -= p * Math.log2(p);
        }
    });
    return entropy;
}

function detectCurrentRegime(prices, rsiArr, bbwArr, strainArr, idx) {
    const rsi = rsiArr[idx];
    const bbw = bbwArr[idx];
    const strain = strainArr[idx];

    // Priority: C > A > B > D
    if (strain > 2.0 && (rsi > 70 || rsi < 30)) return 'C';
    if (bbw < 0.6 && rsi >= 42 && rsi <= 58) return 'A';

    // Simplification for B: Trend Detection
    if (idx >= 3) {
        const adx = 25; // Dummy ADX or calculate properly if needed
        const isB = strain < 0.5; // Placeholder for Regime B logic
        if (isB) return 'B';
    }

    return 'D';
}

// ─── Math Helpers ────────────────────────────────────────────────────────────

function calcEMA(prices, period) {
    const k = 2 / (period + 1);
    const emas = [prices[0]];
    for (let i = 1; i < prices.length; i++) {
        emas.push(prices[i] * k + emas[i - 1] * (1 - k));
    }
    return emas;
}

function calcRSI(prices, period) {
    const rsi = new Array(prices.length).fill(50);
    if (prices.length <= period) return rsi;
    let gain = 0, loss = 0;
    for (let i = 1; i <= period; i++) {
        const d = prices[i] - prices[i-1];
        if (d > 0) gain += d; else loss -= d;
    }
    let avgGain = gain / period;
    let avgLoss = loss / period;
    rsi[period] = avgLoss === 0 ? 100 : 100 - (100 / (1 + avgGain / avgLoss));

    for (let i = period + 1; i < prices.length; i++) {
        const d = prices[i] - prices[i-1];
        avgGain = (avgGain * (period - 1) + (d > 0 ? d : 0)) / period;
        avgLoss = (avgLoss * (period - 1) + (d < 0 ? -d : 0)) / period;
        rsi[i] = avgLoss === 0 ? 100 : 100 - (100 / (1 + avgGain / avgLoss));
    }
    return rsi;
}

function calcStdDev(prices, period) {
    const res = new Array(prices.length).fill(0);
    for (let i = period - 1; i < prices.length; i++) {
        const slice = prices.slice(i - period + 1, i + 1);
        const mean = slice.reduce((a, b) => a + b, 0) / period;
        const variance = slice.reduce((a, b) => a + (b - mean) ** 2, 0) / period;
        res[i] = Math.sqrt(variance);
    }
    return res;
}

function calcBBW(emaArr, stdDevArr) {
    return emaArr.map((ema, i) => (ema + 2 * stdDevArr[i]) - (ema - 2 * stdDevArr[i]));
}

function calcStrain(prices, ema50Arr, stdDev20Arr) {
    return prices.map((p, i) => {
        const std2 = Math.max(stdDev20Arr[i], 0.0001) * 2;
        return Math.abs(p - ema50Arr[i]) / std2;
    });
}

function calcAbsoluteROC(prices, period) {
    const roc = new Array(prices.length).fill(0);
    for (let i = period; i < prices.length; i++) {
        roc[i] = prices[i] - prices[i - period];
    }
    return roc;
}

function checkMicroTrap(prices, ema10Arr, roc2Arr) {
    const n = prices.length;
    if (n < 10) return;

    const currentPrice = prices[n - 1];
    const ema10 = ema10Arr[n - 1];
    const roc2 = roc2Arr[n - 1];
    const prevRoc2 = roc2Arr[n - 2];

    const isRocFlat = Math.abs(roc2 - prevRoc2) <= 0.1001; // Accounting for precision
    const distToEma = Math.abs(currentPrice - ema10);
    const isHuggingEma = distToEma <= 0.2001;

    // Bearish Trap Logic (PUT)
    const last5 = prices.slice(-5);
    const isBelowEma = last5.every(p => p < ema10);
    if (isBelowEma && isHuggingEma && isRocFlat) {
        self.postMessage({
            type: 'MICRO_TRAP_ARMED',
            data: {
                action: 'PUT',
                hitState: { price: currentPrice, ema: ema10, roc: roc2 }
            }
        });
    }

    // Bullish Trap Logic (CALL)
    const isAboveEma = last5.every(p => p > ema10);
    if (isAboveEma && isHuggingEma && isRocFlat) {
        self.postMessage({
            type: 'MICRO_TRAP_ARMED',
            data: {
                action: 'CALL',
                hitState: { price: currentPrice, ema: ema10, roc: roc2 }
            }
        });
    }
}

function discoverPatterns(prices, rsiArr, bbwArr, strainArr, currentRegime) {
    if (prices.length < 50) return;

    // 1. Extract pure non-flat moves — mirrors content.js rollingDirections logic exactly
    //    A flat tick (price === previous price) is completely skipped,
    //    so the sequence string is never polluted by flat-tick inheritance.
    const moves = [];
    for (let i = 1; i < prices.length; i++) {
        const diff = prices[i] - prices[i - 1];
        if (diff !== 0) {
            moves.push({
                dir: diff > 0 ? 'U' : 'D',
                idx: i // original price array index where this move landed
            });
        }
    }

    if (moves.length < 10) return;

    // 2. Measure the current non-flat streak
    const lastMove = moves[moves.length - 1];
    let streakLen = 1;
    let streakStartMoveIdx = moves.length - 1;

    for (let i = moves.length - 2; i >= 0; i--) {
        if (moves[i].dir === lastMove.dir) {
            streakLen++;
            streakStartMoveIdx = i;
        } else {
            break;
        }
    }

    // 3. Register valid streak (5+ non-flat moves, new start only)
    if (streakLen >= 5) {
        const actualStartIndex = moves[streakStartMoveIdx].idx;

        // Create a stable ID using the price at the start of the streak (immune to array shifts)
        const stableStreakID = prices[actualStartIndex].toString();

        // Guard against re-registering the same streak
        if (stableStreakID === lastDiscoveredStreakStart) return;

        // Need at least 5 non-flat moves before the streak to build the presequence
        if (streakStartMoveIdx < 5) return;

        // Validation: move immediately before streak must be OPPOSITE direction
        const preMove = moves[streakStartMoveIdx - 1];
        if (preMove.dir === lastMove.dir) return; // not a clean edge

        // Build the exact 5-movement presequence string from non-flat moves
        let sequenceStr = '';
        for (let i = streakStartMoveIdx - 5; i < streakStartMoveIdx; i++) {
            sequenceStr += moves[i].dir;
        }

        // Hit state = the price-array index of the last presequence move
        const hitIdx = preMove.idx;

        lastDiscoveredStreakStart = stableStreakID;

        self.postMessage({
            type: 'NEW_SIGNAL',
            data: {
                sequence: sequenceStr,
                action: lastMove.dir === 'U' ? 'CALL' : 'PUT',
                regime: detectCurrentRegime(prices, rsiArr, bbwArr, strainArr, hitIdx),
                hitState: {
                    rsi: rsiArr[hitIdx],
                    bbw: bbwArr[hitIdx],
                    str: strainArr[hitIdx]
                },
                ext: streakLen + 't'
            }
        });
    }
}
