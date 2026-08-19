/* ============================================================================
 *  CHAKRAVYUHA ARCADE
 *  Pattern-recognition & reaction-time game for ESP32-WROOM-32 DevKit V1
 *
 *  Hardware   : 24 microswitches -> 8 parallel zones, 16-LED WS2812B ring,
 *               piezo/speaker via 2N2222 low-side driver.
 *  Networking : SoftAP "Chakravyuha-Arcade" / "123456789", dashboard on port 80.
 *  Design     : Fully non-blocking. loop() never calls delay(); every subsystem
 *               (audio, LEDs, debounce, FSM, HTTP) is millis()-driven so the web
 *               server stays responsive during gameplay.
 *
 *  Libraries  : Adafruit NeoPixel (Library Manager), WiFi.h + WebServer.h (core).
 *  Board core : Arduino-ESP32 2.x or 3.x — LEDC API differences are handled.
 * ==========================================================================*/

#include <Arduino.h>
#include <WiFi.h>
#include <WebServer.h>
#include <Adafruit_NeoPixel.h>

/* Cores older than 2.0.3 do not define the version macros. */
#ifndef ESP_ARDUINO_VERSION_MAJOR
  #define ESP_ARDUINO_VERSION_MAJOR 2
#endif

/* ------------------------------------------------------------------ PINOUT */
static const uint8_t ZONE_PIN[8] = { 13, 14, 16, 17, 18, 19, 21, 22 };

#define LED_PIN          4      /* WS2812B DIN, through 390R                 */
#define NUM_LEDS         16     /* 8 zones x 2 LEDs                          */
#define BUZZ_PIN         25     /* 2N2222 base, through 1k                   */
#define BUZZ_CHANNEL     0      /* LEDC channel (Arduino-ESP32 2.x only)     */
#define LED_BRIGHTNESS   70     /* 0-255. Keep low: see WIRING.md note 3.    */

/* -------------------------------------------------------------- GAME TUNING */
#define BASE_SEQ_LEN     3      /* sequence length at round 1                */
#define MAX_SEQ_LEN      32     /* hard ceiling                              */
#define DEBOUNCE_MS      25     /* software debounce window per zone         */
#define INPUT_TIMEOUT_MS 5000   /* per-press patience before TIMEOUT         */
#define SHOW_GAP_MS      160    /* dark gap between pattern steps            */
#define SHOW_ON_MAX_MS   420    /* lit time at round 1                       */
#define SHOW_ON_MIN_MS   240    /* lit time once the game speeds up          */
#define FEEDBACK_MS      170    /* echo of the player's own press            */
#define SUCCESS_MS       900    /* victory animation length                  */
#define FAIL_MS          1500   /* defeat animation length                   */
#define HIST_MAX         12     /* rounds kept in the dashboard log          */
#define RENDER_INTERVAL  20     /* ring refresh, ~50 fps                     */

/* --------------------------------------------------------------- IDENTITIES */
static const uint16_t ZONE_FREQ[8] = { 262, 294, 330, 392, 440, 523, 587, 659 };

static const uint8_t ZONE_RGB[8][3] = {
  { 255,   0,  30 },   /* Z1 crimson  */
  { 255, 110,   0 },   /* Z2 amber    */
  { 235, 215,   0 },   /* Z3 gold     */
  {   0, 255,  70 },   /* Z4 green    */
  {   0, 220, 210 },   /* Z5 cyan     */
  {   0,  95, 255 },   /* Z6 blue     */
  { 150,   0, 255 },   /* Z7 violet   */
  { 255,   0, 150 }    /* Z8 magenta  */
};

/* ------------------------------------------------------------- WIFI / HTTP */
static const char* AP_SSID = "Chakravyuha-Arcade";
static const char* AP_PASS = "123456789";

WebServer        server(80);
Adafruit_NeoPixel strip(NUM_LEDS, LED_PIN, NEO_GRB + NEO_KHZ800);

/* ------------------------------------------------------------ STATE MACHINE */
enum GameState : uint8_t {
  ST_IDLE = 0,      /* ambient rainbow, waiting for the first press */
  ST_SHOW,          /* replaying the pattern to the player          */
  ST_INPUT,         /* player is repeating it, timer running        */
  ST_SUCCESS,       /* victory chime + green sweep                  */
  ST_FAIL           /* defeat chime + red flash                     */
};

static GameState state = ST_IDLE;

/* Sequence + progress */
static uint8_t  sequence[MAX_SEQ_LEN];
static uint8_t  seqLen     = BASE_SEQ_LEN;
static uint8_t  showIdx    = 0;      /* index being displayed  */
static uint8_t  inputIdx   = 0;      /* index awaited from player */
static uint16_t roundNo    = 1;

/* Timers */
static uint32_t stateEnteredMs = 0;
static uint32_t stepStartMs    = 0;
static bool     showLedOn      = false;
static uint32_t roundStartMs   = 0;  /* start of the whole round   */
static uint32_t lastEventMs    = 0;  /* for per-press reaction time */
static uint32_t inputDeadline  = 0;
static int8_t   feedbackZone   = -1;
static uint32_t feedbackUntil  = 0;
static uint32_t lastRenderMs   = 0;
static uint16_t rainbowHue     = 0;

/* Session statistics */
static uint32_t lastRoundMs  = 0;
static uint32_t bestRoundMs  = 0;
static uint16_t highScore    = 0;    /* longest sequence cleared */
static uint16_t roundsWon    = 0;
static uint16_t roundsFailed = 0;
static uint32_t zoneSumMs[8] = { 0 };
static uint16_t zoneHits[8]  = { 0 };

/* Attempt history (ring buffer, newest first when served) */
enum ResultCode : uint8_t { RES_OK = 0, RES_WRONG = 1, RES_TIMEOUT = 2 };

struct HistEntry {
  uint16_t   rnd;
  uint8_t    len;
  uint8_t    reached;   /* how many steps were entered correctly */
  uint32_t   ms;
  ResultCode res;
};

static HistEntry hist[HIST_MAX];
static uint8_t   histCount = 0;
static uint8_t   histHead  = 0;

/* Debounce bookkeeping */
static bool     rawState[8]    = { false };
static bool     stableState[8] = { false };
static uint32_t lastEdgeMs[8]  = { 0 };
static bool     pressEvent[8]  = { false };

/* ==========================================================================
 *  AUDIO ENGINE — non-blocking note queue on LEDC hardware PWM
 * ========================================================================*/

struct Note { uint16_t freq; uint16_t dur; };   /* freq 0 == rest */

static Note     noteQueue[16];
static uint8_t  noteCount = 0;
static uint8_t  noteIndex = 0;
static uint32_t noteStartMs = 0;
static bool     audioBusy = false;

static void audioBegin() {
#if ESP_ARDUINO_VERSION_MAJOR >= 3
  ledcAttach(BUZZ_PIN, 1000, 10);
#else
  ledcSetup(BUZZ_CHANNEL, 1000, 10);
  ledcAttachPin(BUZZ_PIN, BUZZ_CHANNEL);
#endif
}

static void audioFreq(uint16_t f) {
#if ESP_ARDUINO_VERSION_MAJOR >= 3
  if (f == 0) ledcWrite(BUZZ_PIN, 0);
  else        ledcWriteTone(BUZZ_PIN, f);      /* sets 50% duty internally */
#else
  if (f == 0) ledcWrite(BUZZ_CHANNEL, 0);
  else        ledcWriteTone(BUZZ_CHANNEL, f);
#endif
}

/* Queue a phrase. Replaces anything still playing — the newest cue always wins. */
static void audioPlay(const Note* notes, uint8_t count) {
  if (count == 0) return;
  if (count > 16) count = 16;
  for (uint8_t i = 0; i < count; i++) noteQueue[i] = notes[i];
  noteCount   = count;
  noteIndex   = 0;
  noteStartMs = millis();
  audioBusy   = true;
  audioFreq(noteQueue[0].freq);
}

static void audioTone(uint16_t freq, uint16_t dur) {
  Note n = { freq, dur };
  audioPlay(&n, 1);
}

static void audioStop() {
  audioBusy = false;
  noteCount = 0;
  audioFreq(0);
}

static void audioUpdate() {
  if (!audioBusy) return;
  if (millis() - noteStartMs < noteQueue[noteIndex].dur) return;

  noteIndex++;
  if (noteIndex >= noteCount) { audioStop(); return; }
  noteStartMs = millis();
  audioFreq(noteQueue[noteIndex].freq);
}

/* Fixed phrases */
static const Note CHIME_VICTORY[] = {
  { 523, 90 }, { 659, 90 }, { 784, 90 }, { 1047, 200 }, { 0, 60 }, { 784, 70 }, { 1047, 240 }
};
static const Note CHIME_DEFEAT[] = {
  { 330, 160 }, { 262, 160 }, { 208, 200 }, { 0, 70 }, { 165, 420 }
};
static const Note CHIME_START[] = {
  { 392, 80 }, { 523, 80 }, { 659, 150 }
};

/* ==========================================================================
 *  INPUT — per-zone software debounce, falling-edge press events
 * ========================================================================*/

static void inputBegin() {
  for (uint8_t i = 0; i < 8; i++) {
    pinMode(ZONE_PIN[i], INPUT_PULLUP);
    rawState[i]    = false;
    stableState[i] = false;
    lastEdgeMs[i]  = 0;
    pressEvent[i]  = false;
  }
}

/* Any of the 3 parallel switches pulling the line LOW counts as "pressed". */
static void inputUpdate() {
  const uint32_t now = millis();
  for (uint8_t i = 0; i < 8; i++) {
    const bool level = (digitalRead(ZONE_PIN[i]) == LOW);

    if (level != rawState[i]) {          /* line moved — restart the window */
      rawState[i]   = level;
      lastEdgeMs[i] = now;
    }
    if ((now - lastEdgeMs[i]) >= DEBOUNCE_MS && stableState[i] != rawState[i]) {
      stableState[i] = rawState[i];
      if (stableState[i]) pressEvent[i] = true;   /* latch on press only */
    }
  }
}

/* Consume the lowest-numbered pending press, or -1 if none. */
static int8_t inputTake() {
  for (uint8_t i = 0; i < 8; i++) {
    if (pressEvent[i]) { pressEvent[i] = false; return (int8_t)i; }
  }
  return -1;
}

static void inputFlush() {
  for (uint8_t i = 0; i < 8; i++) pressEvent[i] = false;
}

/* ==========================================================================
 *  LED RING — 2 LEDs per zone, all animations time-sliced
 * ========================================================================*/

static void ringClear() { strip.clear(); }

static void ringZone(uint8_t zone, uint8_t scalePct) {
  if (zone > 7) return;
  const uint8_t r = (uint16_t)ZONE_RGB[zone][0] * scalePct / 100;
  const uint8_t g = (uint16_t)ZONE_RGB[zone][1] * scalePct / 100;
  const uint8_t b = (uint16_t)ZONE_RGB[zone][2] * scalePct / 100;
  strip.setPixelColor(zone * 2,     strip.Color(r, g, b));
  strip.setPixelColor(zone * 2 + 1, strip.Color(r, g, b));
}

static void ringRainbow() {
  for (uint8_t i = 0; i < NUM_LEDS; i++) {
    const uint16_t hue = rainbowHue + (uint16_t)(i * (65536L / NUM_LEDS));
    strip.setPixelColor(i, strip.gamma32(strip.ColorHSV(hue, 255, 200)));
  }
  rainbowHue += 420;                 /* ~1 revolution every 3 s at 50 fps */
}

/* Dim teal read-out of how far the player has got this round. */
static void ringProgress() {
  for (uint8_t s = 0; s < inputIdx && s < seqLen; s++) {
    const uint8_t led = (uint8_t)((uint16_t)s * NUM_LEDS / seqLen);
    strip.setPixelColor(led, strip.Color(0, 40, 45));
  }
}

static void ringRender() {
  const uint32_t now = millis();
  if (now - lastRenderMs < RENDER_INTERVAL) return;
  lastRenderMs = now;

  ringClear();

  switch (state) {
    case ST_IDLE:
      ringRainbow();
      break;

    case ST_SHOW:
      if (showLedOn && showIdx < seqLen) ringZone(sequence[showIdx], 100);
      break;

    case ST_INPUT:
      if (feedbackZone >= 0) ringZone((uint8_t)feedbackZone, 100);
      else                   ringProgress();
      break;

    case ST_SUCCESS: {                       /* green comet sweep */
      const uint32_t t   = now - stateEnteredMs;
      const uint8_t  head = (uint8_t)((t * NUM_LEDS) / SUCCESS_MS) % NUM_LEDS;
      for (uint8_t k = 0; k < 5; k++) {
        const uint8_t led = (head + NUM_LEDS - k) % NUM_LEDS;
        const uint8_t v   = 255 >> k;
        strip.setPixelColor(led, strip.Color(0, v, v / 4));
      }
      break;
    }

    case ST_FAIL: {                          /* 4 hard red flashes */
      const uint32_t t = now - stateEnteredMs;
      if (((t / (FAIL_MS / 8)) % 2) == 0) {
        for (uint8_t i = 0; i < NUM_LEDS; i++) strip.setPixelColor(i, strip.Color(255, 0, 0));
      }
      break;
    }
  }
  strip.show();
}

/* ==========================================================================
 *  GAME LOGIC — finite state machine
 * ========================================================================*/

static void histAdd(uint16_t rnd, uint8_t len, uint8_t reached,
                    uint32_t ms, ResultCode res) {
  hist[histHead] = { rnd, len, reached, ms, res };
  histHead = (uint8_t)((histHead + 1) % HIST_MAX);
  if (histCount < HIST_MAX) histCount++;
}

static void statsReset() {
  lastRoundMs = 0;
  bestRoundMs = 0;
  highScore   = 0;
  roundsWon   = 0;
  roundsFailed = 0;
  for (uint8_t i = 0; i < 8; i++) { zoneSumMs[i] = 0; zoneHits[i] = 0; }
  histCount = 0;
  histHead  = 0;
}

static void enterState(GameState s) {
  state          = s;
  stateEnteredMs = millis();
}

/* Lit time shortens as the sequence grows — the game gets harder, not just longer. */
static uint16_t showOnMs() {
  const uint16_t drop = (uint16_t)(seqLen - BASE_SEQ_LEN) * 12;
  if (drop >= (SHOW_ON_MAX_MS - SHOW_ON_MIN_MS)) return SHOW_ON_MIN_MS;
  return (uint16_t)(SHOW_ON_MAX_MS - drop);
}

static void generateSequence(uint8_t len) {
  for (uint8_t i = 0; i < len && i < MAX_SEQ_LEN; i++) {
    sequence[i] = (uint8_t)random(0, 8);
  }
}

/* Lead-in silence before the first step, so an opening chime is never clipped. */
static uint16_t showLeadMs = SHOW_GAP_MS;

static void beginShow(uint16_t leadMs) {
  showIdx     = 0;
  showLedOn   = false;          /* start in the dark: the lead-in gap */
  showLeadMs  = leadMs;
  stepStartMs = millis();
  inputFlush();
  enterState(ST_SHOW);
}

static void beginInput() {
  inputIdx      = 0;
  feedbackZone  = -1;
  roundStartMs  = millis();
  lastEventMs   = roundStartMs;
  inputDeadline = roundStartMs + INPUT_TIMEOUT_MS;
  inputFlush();
  enterState(ST_INPUT);
}

static void startGame() {
  seqLen  = BASE_SEQ_LEN;
  roundNo = 1;
  generateSequence(seqLen);
  audioPlay(CHIME_START, sizeof(CHIME_START) / sizeof(Note));
  beginShow(420);                 /* let the 310 ms start chime finish */
}

static void roundWon() {
  lastRoundMs = millis() - roundStartMs;
  if (bestRoundMs == 0 || lastRoundMs < bestRoundMs) bestRoundMs = lastRoundMs;
  if (seqLen > highScore) highScore = seqLen;
  roundsWon++;
  histAdd(roundNo, seqLen, seqLen, lastRoundMs, RES_OK);

  audioPlay(CHIME_VICTORY, sizeof(CHIME_VICTORY) / sizeof(Note));
  enterState(ST_SUCCESS);
}

static void roundLost(ResultCode why) {
  lastRoundMs = millis() - roundStartMs;
  roundsFailed++;
  histAdd(roundNo, seqLen, inputIdx, lastRoundMs, why);

  audioPlay(CHIME_DEFEAT, sizeof(CHIME_DEFEAT) / sizeof(Note));
  enterState(ST_FAIL);
}

/* ---- per-state tick handlers ------------------------------------------- */

static void tickIdle() {
  if (inputTake() >= 0) startGame();
}

static void tickShow() {
  const uint32_t now = millis();

  if (showLedOn) {
    if (now - stepStartMs >= showOnMs()) {   /* lit phase over */
      showLedOn   = false;
      stepStartMs = now;
      showIdx++;                             /* this step is consumed */
      audioStop();
    }
    return;
  }

  /* Dark phase: a long lead-in before step 0, a short gap between steps. */
  const uint16_t wait = (showIdx == 0) ? showLeadMs : SHOW_GAP_MS;
  if (now - stepStartMs < wait) return;

  if (showIdx >= seqLen) { beginInput(); return; }   /* whole pattern shown */

  showLedOn   = true;
  stepStartMs = now;
  audioTone(ZONE_FREQ[sequence[showIdx]], showOnMs());
}

static void tickInput() {
  const uint32_t now = millis();

  if (feedbackZone >= 0 && now >= feedbackUntil) feedbackZone = -1;

  if ((int32_t)(now - inputDeadline) >= 0) { roundLost(RES_TIMEOUT); return; }

  const int8_t z = inputTake();
  if (z < 0) return;

  /* Echo the press immediately — the player must feel the button, right or wrong. */
  feedbackZone  = z;
  feedbackUntil = now + FEEDBACK_MS;
  audioTone(ZONE_FREQ[z], FEEDBACK_MS);

  if ((uint8_t)z != sequence[inputIdx]) { roundLost(RES_WRONG); return; }

  /* Correct: bank the reaction time against that zone. */
  const uint32_t reaction = now - lastEventMs;
  lastEventMs   = now;
  zoneSumMs[z] += reaction;
  zoneHits[z]++;

  inputIdx++;
  if (inputIdx >= seqLen) { roundWon(); return; }

  inputDeadline = now + INPUT_TIMEOUT_MS;
}

static void tickSuccess() {
  if (millis() - stateEnteredMs < SUCCESS_MS) return;

  roundNo++;
  if (seqLen < MAX_SEQ_LEN) {
    sequence[seqLen] = (uint8_t)random(0, 8);   /* extend, keep the prefix */
    seqLen++;
  } else {
    generateSequence(seqLen);                   /* ceiling: reshuffle instead */
  }
  beginShow(SHOW_GAP_MS * 2);
}

static void tickFail() {
  if (millis() - stateEnteredMs < FAIL_MS) return;

  seqLen  = BASE_SEQ_LEN;
  roundNo = 1;
  generateSequence(seqLen);
  inputIdx = 0;
  inputFlush();
  enterState(ST_IDLE);
}

static void gameUpdate() {
  switch (state) {
    case ST_IDLE:    tickIdle();    break;
    case ST_SHOW:    tickShow();    break;
    case ST_INPUT:   tickInput();   break;
    case ST_SUCCESS: tickSuccess(); break;
    case ST_FAIL:    tickFail();    break;
  }
}

static const char* stateName() {
  switch (state) {
    case ST_IDLE:    return "IDLE";
    case ST_SHOW:    return "PATTERN_SHOW";
    case ST_INPUT:   return "USER_INPUT";
    case ST_SUCCESS: return "EVALUATION_SUCCESS";
    case ST_FAIL:    return "EVALUATION_FAILURE";
  }
  return "UNKNOWN";
}

static const char* stateLabel() {
  switch (state) {
    case ST_IDLE:    return "Ready";
    case ST_SHOW:    return "Watch the pattern";
    case ST_INPUT:   return "Your turn";
    case ST_SUCCESS: return "Round cleared";
    case ST_FAIL:    return "Sequence broken";
  }
  return "-";
}

/* ==========================================================================
 *  EMBEDDED DASHBOARD — single-page app held in flash (PROGMEM)
 * ========================================================================*/

static const char INDEX_HTML[] PROGMEM = R"rawliteral(
<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Chakravyuha Arcade</title>
<style>
:root{
  --bg:#07080d; --panel:#111420; --panel2:#161a2a; --line:#232838;
  --txt:#e8ecf6; --dim:#8791a8; --accent:#00e5c0; --accent2:#7c5cff;
  --ok:#22d67b; --warn:#ffb020; --bad:#ff4a5e;
  --mono:ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;
}
*{box-sizing:border-box;margin:0;padding:0}
body{
  background:
    radial-gradient(1100px 600px at 85% -10%,rgba(124,92,255,.16),transparent 60%),
    radial-gradient(900px 500px at 5% 0%,rgba(0,229,192,.12),transparent 55%),
    var(--bg);
  color:var(--txt);
  font-family:system-ui,-apple-system,"Segoe UI",Roboto,sans-serif;
  min-height:100vh;padding:20px 16px 44px;
}
.wrap{max-width:1180px;margin:0 auto}
header{display:flex;flex-wrap:wrap;gap:14px;align-items:center;justify-content:space-between;margin-bottom:22px}
.brand{display:flex;align-items:center;gap:13px}
.logo{width:42px;height:42px;border-radius:12px;flex:none;
  background:conic-gradient(from 220deg,var(--accent),var(--accent2),#ff4a9e,var(--accent));
  box-shadow:0 0 26px rgba(124,92,255,.45)}
h1{font-size:20px;letter-spacing:.34em;text-transform:uppercase;font-weight:650}
.sub{font-size:11.5px;color:var(--dim);letter-spacing:.16em;text-transform:uppercase;margin-top:3px}
.link{display:flex;align-items:center;gap:8px;font-size:12px;color:var(--dim);
  background:var(--panel);border:1px solid var(--line);border-radius:999px;padding:8px 15px}
.dot{width:8px;height:8px;border-radius:50%;background:var(--ok);box-shadow:0 0 10px var(--ok)}
.dot.off{background:var(--bad);box-shadow:0 0 10px var(--bad)}
.grid{display:grid;gap:16px;grid-template-columns:repeat(12,1fr)}
.card{background:linear-gradient(180deg,var(--panel),var(--panel2));border:1px solid var(--line);
  border-radius:18px;padding:20px;box-shadow:0 18px 42px rgba(0,0,0,.42)}
.c5{grid-column:span 5}.c7{grid-column:span 7}
@media(max-width:900px){.c5,.c7{grid-column:span 12}}
.card h2{font-size:11px;letter-spacing:.2em;text-transform:uppercase;color:var(--dim);
  font-weight:600;margin-bottom:16px;display:flex;justify-content:space-between;align-items:center}
.pill{display:inline-flex;align-items:center;gap:9px;font-family:var(--mono);font-size:13px;
  padding:7px 14px;border-radius:999px;border:1px solid var(--line);background:#0d101a;color:var(--dim)}
.pill.idle{color:var(--accent);border-color:rgba(0,229,192,.4);background:rgba(0,229,192,.09)}
.pill.show{color:var(--accent2);border-color:rgba(124,92,255,.45);background:rgba(124,92,255,.12)}
.pill.input{color:var(--warn);border-color:rgba(255,176,32,.42);background:rgba(255,176,32,.11)}
.pill.ok{color:var(--ok);border-color:rgba(34,214,123,.42);background:rgba(34,214,123,.11)}
.pill.bad{color:var(--bad);border-color:rgba(255,74,94,.45);background:rgba(255,74,94,.12)}
.headline{font-size:30px;font-weight:660;margin:16px 0 4px;letter-spacing:-.5px}
.headline .u{font-size:14px;color:var(--dim);font-weight:500;margin-left:6px}
.note{font-size:12.5px;color:var(--dim);line-height:1.6}
.stats{display:grid;grid-template-columns:repeat(3,1fr);gap:12px;margin-top:18px}
.stat{background:#0d101a;border:1px solid var(--line);border-radius:13px;padding:13px 14px}
.stat .k{font-size:10px;letter-spacing:.16em;text-transform:uppercase;color:var(--dim)}
.stat .v{font-family:var(--mono);font-size:21px;margin-top:6px;font-variant-numeric:tabular-nums}
.steps{display:flex;gap:6px;flex-wrap:wrap;margin-top:18px}
.step{width:22px;height:7px;border-radius:4px;background:#1e2333;transition:background .12s}
.step.done{background:var(--accent)}
.step.cur{background:var(--warn);box-shadow:0 0 10px rgba(255,176,32,.6)}
.zone{display:grid;grid-template-columns:14px 58px 1fr 74px 46px;gap:11px;align-items:center;
  padding:8px 0;border-bottom:1px solid rgba(35,40,56,.6)}
.zone:last-child{border-bottom:0}
.zc{width:12px;height:12px;border-radius:50%}
.zn{font-family:var(--mono);font-size:12.5px;color:var(--dim)}
.bar{height:8px;border-radius:5px;background:#0d101a;overflow:hidden}
.bar i{display:block;height:100%;border-radius:5px;transition:width .3s ease}
.zv{font-family:var(--mono);font-size:13px;text-align:right;font-variant-numeric:tabular-nums}
.zh{font-family:var(--mono);font-size:11px;color:var(--dim);text-align:right}
table{width:100%;border-collapse:collapse;font-family:var(--mono);font-size:12.5px}
th{text-align:left;font-size:10px;letter-spacing:.16em;text-transform:uppercase;color:var(--dim);
  font-weight:600;padding:0 10px 11px;border-bottom:1px solid var(--line)}
td{padding:10px;border-bottom:1px solid rgba(35,40,56,.55);font-variant-numeric:tabular-nums}
tr:last-child td{border-bottom:0}
.tag{display:inline-block;padding:2px 9px;border-radius:6px;font-size:11px}
.tag.ok{background:rgba(34,214,123,.14);color:var(--ok)}
.tag.bad{background:rgba(255,74,94,.14);color:var(--bad)}
.tag.to{background:rgba(255,176,32,.14);color:var(--warn)}
.empty{padding:26px 10px;text-align:center;color:var(--dim);font-size:13px}
button{font:inherit;font-size:12px;color:var(--txt);background:#0d101a;border:1px solid var(--line);
  border-radius:9px;padding:7px 14px;cursor:pointer;transition:.15s}
button:hover{border-color:var(--accent);color:var(--accent)}
footer{margin-top:22px;text-align:center;font-size:11.5px;color:var(--dim);font-family:var(--mono)}
</style>
</head>
<body>
<div class="wrap">
  <header>
    <div class="brand">
      <div class="logo"></div>
      <div>
        <h1>Chakravyuha</h1>
        <div class="sub">Pattern &middot; Reaction &middot; Telemetry</div>
      </div>
    </div>
    <div class="link"><span class="dot" id="link-dot"></span><span id="link-txt">connecting</span></div>
  </header>
  <div class="grid">
    <section class="card c5">
      <h2>Game State</h2>
      <span class="pill" id="state-pill"><b id="state-code">--</b></span>
      <div class="headline" id="state-label">Waiting for controller</div>
      <div class="note" id="state-note">Press any zone on the arcade to begin a session.</div>
      <div class="stats">
        <div class="stat"><div class="k">Round</div><div class="v" id="v-round">--</div></div>
        <div class="stat"><div class="k">Seq Length</div><div class="v" id="v-len">--</div></div>
        <div class="stat"><div class="k">Step</div><div class="v" id="v-step">--</div></div>
      </div>
      <div class="steps" id="steps"></div>
    </section>

    <section class="card c7">
      <h2>Timing &amp; Score</h2>
      <div class="headline"><span id="v-last">--</span><span class="u">ms last round</span></div>
      <div class="note">Millisecond timer starts the instant the pattern finishes playing.</div>
      <div class="stats">
        <div class="stat"><div class="k">Best Round</div><div class="v" id="v-best">--</div></div>
        <div class="stat"><div class="k">High Score</div><div class="v" id="v-high">--</div></div>
        <div class="stat"><div class="k">Avg Reaction</div><div class="v" id="v-avg">--</div></div>
      </div>
      <div class="stats">
        <div class="stat"><div class="k">Rounds Won</div><div class="v" id="v-won">--</div></div>
        <div class="stat"><div class="k">Failures</div><div class="v" id="v-fail">--</div></div>
        <div class="stat"><div class="k">Uptime</div><div class="v" id="v-up">--</div></div>
      </div>
    </section>

    <section class="card c5">
      <h2>Average Reaction / Zone</h2>
      <div id="zones"></div>
    </section>

    <section class="card c7">
      <h2>Attempt History<button id="btn-reset" type="button">Reset session</button></h2>
      <div id="hist-wrap"><div class="empty">No attempts logged yet.</div></div>
    </section>
  </div>
  <footer>Chakravyuha Arcade &middot; ESP32 SoftAP &middot; <span id="v-ip">192.168.4.1</span></footer>
</div>
<script>
const ZC = ['#ff001e','#ff6e00','#ebd700','#00ff46','#00dcd2','#005fff','#9600ff','#ff0096'];
const PILL = {IDLE:'idle', PATTERN_SHOW:'show', USER_INPUT:'input',
              EVALUATION_SUCCESS:'ok', EVALUATION_FAILURE:'bad'};
const NOTE = {
  IDLE:'Press any zone on the arcade to begin a session.',
  PATTERN_SHOW:'Ring is replaying the sequence. Inputs are ignored until playback ends.',
  USER_INPUT:'Timer running. Each press must land within 5000 ms of the previous one.',
  EVALUATION_SUCCESS:'Round cleared. Sequence extends by one zone.',
  EVALUATION_FAILURE:'Sequence broken. Resetting to the base length and returning to idle.'
};
const RES = [['OK','ok'],['WRONG','bad'],['TIMEOUT','to']];
const $ = id => document.getElementById(id);

function fmt(v){ return (!v) ? '--' : v; }
function upt(s){
  const h=Math.floor(s/3600), m=Math.floor(s%3600/60), x=s%60;
  return (h?h+'h ':'')+(h||m?m+'m ':'')+x+'s';
}

function drawSteps(d){
  const box=$('steps');
  if(box.children.length!==d.seqLen){
    box.innerHTML='';
    for(let i=0;i<d.seqLen;i++){ const e=document.createElement('div'); e.className='step'; box.appendChild(e); }
  }
  const active = (d.state==='PATTERN_SHOW') ? d.showIdx
               : (d.state==='USER_INPUT')   ? d.step : -1;
  [...box.children].forEach((e,i)=>{
    e.className = 'step' + (i<active ? ' done' : i===active ? ' cur' : '');
  });
}

function drawZones(z){
  const peak = Math.max(1, ...z.map(v=>v.avg));
  $('zones').innerHTML = z.map((v,i)=>`
    <div class="zone">
      <span class="zc" style="background:${ZC[i]};box-shadow:0 0 9px ${ZC[i]}"></span>
      <span class="zn">ZONE ${i+1}</span>
      <span class="bar"><i style="width:${v.avg?Math.max(4,Math.round(v.avg/peak*100)):0}%;background:${ZC[i]}"></i></span>
      <span class="zv">${v.avg?v.avg+' ms':'--'}</span>
      <span class="zh">${v.hits}x</span>
    </div>`).join('');
}

function drawHist(h){
  if(!h.length){ $('hist-wrap').innerHTML='<div class="empty">No attempts logged yet.</div>'; return; }
  const rows = h.map(e=>{
    const r = RES[e.res] || RES[1];
    return `<tr><td>#${e.r}</td><td>${e.len}</td><td>${e.reached}/${e.len}</td>`
         + `<td>${e.ms} ms</td><td><span class="tag ${r[1]}">${r[0]}</span></td></tr>`;
  }).join('');
  $('hist-wrap').innerHTML = '<table><thead><tr><th>Round</th><th>Length</th>'
    + '<th>Reached</th><th>Time</th><th>Result</th></tr></thead><tbody>' + rows + '</tbody></table>';
}

function render(d){
  $('state-code').textContent  = d.state;
  $('state-pill').className    = 'pill ' + (PILL[d.state]||'');
  $('state-label').textContent = d.label;
  $('state-note').textContent  = NOTE[d.state] || '';

  $('v-round').textContent = d.round;
  $('v-len').textContent   = d.seqLen;
  $('v-step').textContent  = (d.state==='USER_INPUT') ? (d.step+' / '+d.seqLen) : '--';

  $('v-last').textContent = fmt(d.lastMs);
  $('v-best').textContent = d.bestMs ? d.bestMs+' ms' : '--';
  $('v-high').textContent = fmt(d.high);
  $('v-won').textContent  = d.won;
  $('v-fail').textContent = d.failed;
  $('v-up').textContent   = upt(d.uptime);
  $('v-ip').textContent   = d.ip;

  const tot = d.zones.reduce((a,z)=>a+z.avg*z.hits,0);
  const cnt = d.zones.reduce((a,z)=>a+z.hits,0);
  $('v-avg').textContent = cnt ? Math.round(tot/cnt)+' ms' : '--';

  drawSteps(d); drawZones(d.zones); drawHist(d.hist);
}

function online(ok){
  $('link-dot').className = ok ? 'dot' : 'dot off';
  $('link-txt').textContent = ok ? 'live' : 'disconnected';
}

async function poll(){
  try{
    const r = await fetch('/api/state',{cache:'no-store'});
    if(!r.ok) throw new Error('http');
    render(await r.json());
    online(true);
  }catch(e){ online(false); }
}

$('btn-reset').addEventListener('click', async ()=>{
  try{ await fetch('/api/reset',{method:'POST'}); poll(); }catch(e){}
});

poll();
setInterval(poll, 250);
</script>
</body>
</html>
)rawliteral";

/* ==========================================================================
 *  HTTP HANDLERS
 * ========================================================================*/

static String buildStateJson() {
  String j;
  j.reserve(1200);

  j += "{\"state\":\"";  j += stateName();
  j += "\",\"label\":\""; j += stateLabel();
  j += "\",\"round\":";  j += roundNo;
  j += ",\"seqLen\":";   j += seqLen;
  j += ",\"step\":";     j += inputIdx;
  j += ",\"showIdx\":";  j += showIdx;
  j += ",\"lastMs\":";   j += lastRoundMs;
  j += ",\"bestMs\":";   j += bestRoundMs;
  j += ",\"high\":";     j += highScore;
  j += ",\"won\":";      j += roundsWon;
  j += ",\"failed\":";   j += roundsFailed;
  j += ",\"uptime\":";   j += (millis() / 1000UL);
  j += ",\"clients\":";  j += WiFi.softAPgetStationNum();
  j += ",\"ip\":\"";     j += WiFi.softAPIP().toString();
  j += "\",\"zones\":[";

  for (uint8_t i = 0; i < 8; i++) {
    if (i) j += ',';
    const uint32_t avg = zoneHits[i] ? (zoneSumMs[i] / zoneHits[i]) : 0;
    j += "{\"avg\":"; j += avg;
    j += ",\"hits\":"; j += zoneHits[i];
    j += '}';
  }

  j += "],\"hist\":[";
  for (uint8_t k = 0; k < histCount; k++) {          /* newest first */
    const uint8_t idx = (uint8_t)((histHead + HIST_MAX - 1 - k) % HIST_MAX);
    if (k) j += ',';
    j += "{\"r\":";        j += hist[idx].rnd;
    j += ",\"len\":";      j += hist[idx].len;
    j += ",\"reached\":";  j += hist[idx].reached;
    j += ",\"ms\":";       j += hist[idx].ms;
    j += ",\"res\":";      j += (uint8_t)hist[idx].res;
    j += '}';
  }
  j += "]}";
  return j;
}

static void handleRoot() {
  server.sendHeader("Cache-Control", "no-store");
  server.send_P(200, "text/html", INDEX_HTML);
}

static void handleState() {
  server.sendHeader("Cache-Control", "no-store");
  server.send(200, "application/json", buildStateJson());
}

static void handleReset() {
  statsReset();
  server.send(200, "application/json", "{\"ok\":true}");
}

static void handleNotFound() {
  /* Captive-portal friendly: bounce every unknown path at the dashboard. */
  server.sendHeader("Location", "/", true);
  server.send(302, "text/plain", "");
}

/* ==========================================================================
 *  SETUP / LOOP
 * ========================================================================*/

void setup() {
  Serial.begin(115200);
  delay(200);                       /* one-off, before the game starts */
  Serial.println();
  Serial.println(F("=== Chakravyuha Arcade booting ==="));

  /* Entropy from the hardware RNG so the pattern differs every power-up. */
  randomSeed(esp_random());

  inputBegin();
  audioBegin();

  strip.begin();
  strip.setBrightness(LED_BRIGHTNESS);
  strip.clear();
  strip.show();

  WiFi.mode(WIFI_AP);
  WiFi.softAP(AP_SSID, AP_PASS);
  Serial.print(F("SoftAP  : ")); Serial.println(AP_SSID);
  Serial.print(F("Password: ")); Serial.println(AP_PASS);
  Serial.print(F("Open    : http://")); Serial.println(WiFi.softAPIP());

  server.on("/",           HTTP_GET,  handleRoot);
  server.on("/api/state",  HTTP_GET,  handleState);
  server.on("/api/reset",  HTTP_POST, handleReset);
  server.on("/api/reset",  HTTP_GET,  handleReset);   /* convenience */
  server.onNotFound(handleNotFound);
  server.begin();

  generateSequence(seqLen);
  enterState(ST_IDLE);
  Serial.println(F("Ready. Press any zone to start."));
}

void loop() {
  server.handleClient();   /* HTTP first — keeps the dashboard snappy */
  inputUpdate();           /* debounce all 8 zones                    */
  gameUpdate();            /* advance the FSM                         */
  audioUpdate();           /* step the note queue                     */
  ringRender();            /* repaint the ring at ~50 fps             */
}
