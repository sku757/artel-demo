/* =========================================================================
   ARTEL — премиальный scroll-scrubbing секвенции
   ---------------------------------------------------------------------
   Архитектура (по итогам исследования Apple-подобных реализаций):
   1. Кадры грузятся как Blob (сжатые, мало памяти) с параллельной загрузкой.
   2. Вокруг плейхеда поддерживается «окно» декодированных ImageBitmap
      (createImageBitmap из Blob не блокирует главный поток) — отрисовка
      никогда не ждёт декодирования: нет рывков.
   3. Дробный плейхед + блендинг соседних кадров = непрерывное движение.
   4. Snap-навигация: свободного скролла нет, жест = плавный перелёт
      к соседней остановке с фиксированным темпом.
   5. Таймлайн: hold – move – hold – move – hold. В hold кадр стоит,
      в move едет с easeInOutSine (плавный разгон и плавное торможение).
   ========================================================================= */

/* ---------------- конфиг ---------------- */
var FRAME_COUNT = 383;
/* Набор выбираем по ширине (cover тянет кадр на всю ширину).
   Фолбэк-цепочка на случай нулевого innerWidth; ?set=d|m — принудительный выбор. */
var _vw = window.innerWidth || document.documentElement.clientWidth || screen.width || 1280;
var _setParam = new URLSearchParams(location.search).get("set");
var IS_MOBILE = _setParam ? _setParam === "m" : _vw <= 640;
var FRAME_DIR = IS_MOBILE ? "frames-m/" : "frames/";

function framePath(i) {
  return FRAME_DIR + "frame_" + String(i + 1).padStart(4, "0") + ".webp";
}

/* Ключевые кадры остановок */
var KA = 191;               // середина
var KB = FRAME_COUNT - 1;   // крыша

/* Таймлайн: веса = доли длины скролла */
var SEG = [
  { type: "hold", frame: 0,         w: 0.4 },
  { type: "move", from: 0,  to: KA, w: 2.6 },
  { type: "hold", frame: KA,        w: 1.0 },
  { type: "move", from: KA, to: KB, w: 2.6 },
  { type: "hold", frame: KB,        w: 1.0 }
];
(function () {
  var total = 0, acc = 0, i;
  for (i = 0; i < SEG.length; i++) total += SEG[i].w;
  for (i = 0; i < SEG.length; i++) {
    SEG[i].p0 = acc / total; acc += SEG[i].w; SEG[i].p1 = acc / total;
  }
})();

/* Текстовые остановки: привязаны к hold-сегментам */
var _h0 = SEG[0], _m1 = SEG[1], _hA = SEG[2], _m2 = SEG[3], _hB = SEG[4];
var OVERLAYS = [
  { id: "stop1", a: -1,
                 b: 0,
                 c: _h0.p1 * 0.55,
                 d: _h0.p1 + (_m1.p1 - _m1.p0) * 0.22 },
  { id: "stop2", a: _hA.p0 - (_m1.p1 - _m1.p0) * 0.22,
                 b: _hA.p0 + (_hA.p1 - _hA.p0) * 0.10,
                 c: _hA.p1 - (_hA.p1 - _hA.p0) * 0.10,
                 d: _hA.p1 + (_m2.p1 - _m2.p0) * 0.22 },
  { id: "stop3", a: _hB.p0 - (_m2.p1 - _m2.p0) * 0.22,
                 b: _hB.p0 + (_hB.p1 - _hB.p0) * 0.10,
                 c: 1.5, d: 2 }
];

/* Окно декодирования (кол-во кадров) */
var AHEAD = 26, BACK = 10, EVICT = 36, DECODE_PAR = 4;

/* ---------------- DOM ---------------- */
var canvas = document.getElementById("seq");
var ctx = canvas.getContext("2d");
var track = document.getElementById("track");
var preloader = document.getElementById("preloader");
/* FX-слои остановок (только лёгкие затемнения — блюр убран:
   анимация backdrop-filter мерцает в Chrome, а затемнение через
   opacity обычного div идеально гладкое) */
var fxTint1 = document.getElementById("fxTint1");
var fxTint2 = document.getElementById("fxTint2");
var fxTint3 = document.getElementById("fxTint3");

var reduceMotion = window.matchMedia("(prefers-reduced-motion: reduce)").matches;

/* ---------------- состояние ---------------- */
var blobs = new Array(FRAME_COUNT);      // сжатые кадры
var bitmaps = new Array(FRAME_COUNT);    // декодированные (окно вокруг плейхеда)
var inflight = {};                       // idx -> true (декодируется сейчас)
var inflightCount = 0;

var renderedProgress = 0;
var lastFF = -1;
var lastDrawExact = false;
var dirSign = 1;                          // направление движения (для префетча)

/* =========================================================================
   ЗАГРУЗКА: все кадры как Blob, параллельно с лимитом
   ========================================================================= */
function preloadBlobs(onProgress, onDone) {
  var next = 0, done = 0, PAR = 14;
  function pump() {
    while (inflightLoads < PAR && next < FRAME_COUNT) {
      load(next++);
    }
  }
  var inflightLoads = 0;
  function load(i) {
    inflightLoads++;
    fetch(framePath(i))
      .then(function (r) { return r.blob(); })
      .then(function (b) { blobs[i] = b; })
      .catch(function () { blobs[i] = null; })
      .then(function () {
        inflightLoads--; done++;
        onProgress(done / FRAME_COUNT);
        if (done === FRAME_COUNT) onDone(); else pump();
      });
  }
  pump();
}

/* =========================================================================
   ДЕКОДИРОВАНИЕ: окно ImageBitmap вокруг плейхеда
   ========================================================================= */
function wantRange(center) {
  var ahead = dirSign >= 0 ? AHEAD : BACK;
  var back  = dirSign >= 0 ? BACK  : AHEAD;
  var lo = Math.max(0, center - back);
  var hi = Math.min(FRAME_COUNT - 1, center + ahead);
  return [lo, hi];
}

function decodePump(center) {
  var r = wantRange(center), lo = r[0], hi = r[1];
  /* приоритет: от центра наружу */
  for (var d = 0; d <= (hi - lo) && inflightCount < DECODE_PAR; d++) {
    var cands = [center + d * dirSign, center - d * dirSign];
    for (var k = 0; k < 2 && inflightCount < DECODE_PAR; k++) {
      var i = cands[k];
      if (i < lo || i > hi) continue;
      if (bitmaps[i] || inflight[i] || !blobs[i]) continue;
      startDecode(i);
    }
  }
  /* выселение далёких кадров, чтобы память не росла */
  for (var j = 0; j < FRAME_COUNT; j++) {
    if (bitmaps[j] && Math.abs(j - center) > EVICT) {
      bitmaps[j].close();
      bitmaps[j] = null;
    }
  }
}

function startDecode(i) {
  inflight[i] = true; inflightCount++;
  createImageBitmap(blobs[i])
    .then(function (bm) { bitmaps[i] = bm; })
    .catch(function () { /* кадр пропустим, nearestReady подставит соседний */ })
    .then(function () { delete inflight[i]; inflightCount--; });
}

function nearestReady(i) {
  if (bitmaps[i]) return i;
  for (var d = 1; d < FRAME_COUNT; d++) {
    if (i - d >= 0 && bitmaps[i - d]) return i - d;
    if (i + d < FRAME_COUNT && bitmaps[i + d]) return i + d;
  }
  return -1;
}

/* =========================================================================
   CANVAS: размер (DPR) и cover-отрисовка с блендингом
   ========================================================================= */
function resize() {
  var dpr = Math.min(window.devicePixelRatio || 1, 1.75);
  var vw = document.documentElement.clientWidth;
  var vh = window.innerHeight;
  canvas.width = Math.round(vw * dpr);
  canvas.height = Math.round(vh * dpr);
  canvas.style.width = vw + "px";
  canvas.style.height = vh + "px";
  lastFF = -1;                       /* форсируем перерисовку */
}

function drawBitmapCover(bm) {
  var cw = canvas.width, ch = canvas.height;
  var iw = bm.width, ih = bm.height;
  var s = Math.max(cw / iw, ch / ih);
  var dw = iw * s, dh = ih * s;
  ctx.drawImage(bm, (cw - dw) / 2, (ch - dh) / 2, dw, dh);
}

function drawFrame(ff) {
  var i0 = Math.floor(ff);
  var i1 = Math.min(i0 + 1, FRAME_COUNT - 1);
  var frac = ff - i0;

  var r0 = nearestReady(i0);
  if (r0 < 0) return false;                       /* ещё ничего не декодировано */
  var exact = (r0 === i0);

  ctx.clearRect(0, 0, canvas.width, canvas.height);
  ctx.globalAlpha = 1;
  drawBitmapCover(bitmaps[r0]);

  if (frac > 0.002 && i1 !== i0) {
    var r1 = bitmaps[i1] ? i1 : -1;               /* блендим только точным кадром */
    if (r1 >= 0) {
      ctx.globalAlpha = frac;
      drawBitmapCover(bitmaps[r1]);
      ctx.globalAlpha = 1;
    } else exact = false;
  }
  lastDrawExact = exact;
  return true;
}

/* =========================================================================
   ТАЙМЛАЙН: прогресс -> дробный кадр (hold стоит, move c easeInOutSine)
   ========================================================================= */
function frameFloatFromProgress(p) {
  for (var i = 0; i < SEG.length; i++) {
    var s = SEG[i];
    if (p < s.p1 || i === SEG.length - 1) {
      if (s.type === "hold") return s.frame;
      var t = (p - s.p0) / (s.p1 - s.p0);
      if (t < 0) t = 0; if (t > 1) t = 1;
      t = 0.5 * (1 - Math.cos(Math.PI * t));       /* плавный разгон/торможение */
      return s.from + (s.to - s.from) * t;
    }
  }
  return 0;
}

/* ---------------- оверлеи и подсказка ---------------- */
function trapezoid(p, a, b, c, d) {
  if (p <= a || p >= d) return 0;
  if (p < b) return (p - a) / (b - a);
  if (p <= c) return 1;
  return (d - p) / (d - c);
}
function updateOverlays(p) {
  for (var i = 0; i < OVERLAYS.length; i++) {
    var o = OVERLAYS[i];
    if (!o.node) continue;
    var op = trapezoid(p, o.a, o.b, o.c, o.d);
    o.op = op;
    o.node.style.opacity = op;
    o.node.style.setProperty("--ty", ((1 - op) * 14).toFixed(1) + "px");
    o.node.classList.toggle("is-active", op > 0.5);   /* интерактив только когда видим */
  }
  /* FX: затемнения повторяют кривую своей остановки, блюр — радиусом.
     Остановки 1 и 2 используют общий полноэкранный блюр, 3-я — левый с маской. */
  fxTint1.style.opacity = OVERLAYS[0].op;
  fxTint2.style.opacity = OVERLAYS[1].op;
  fxTint3.style.opacity = OVERLAYS[2].op;
}

/* =========================================================================
   НАВИГАЦИЯ ПО ОСТАНОВКАМ (snap)
   Свободного скролла нет: любой жест (колесо / свайп / клавиши) запускает
   плавный перелёт к соседней остановке. Остановиться между точками нельзя —
   пользователь всегда оказывается там, где есть текст.
   ========================================================================= */
var STOPS = [0, (_hA.p0 + _hA.p1) / 2, 1];   /* прогресс трёх остановок */
var ANIM_MS = 2400;          /* длительность перелёта между остановками */
var GESTURE_PX = 30;         /* сколько «прокрутки» запускает перелёт */
var COOLDOWN_MS = 450;       /* игнор инерционного хвоста трекпада после перелёта */

var stopIndex = 0;
var animating = false;
var animFrom = 0, animTo = 0, animStart = 0;
var cooldownUntil = 0;
var wheelAccum = 0;

function goTo(idx) {
  if (animating) return;
  if (idx < 0) idx = 0;
  if (idx > STOPS.length - 1) idx = STOPS.length - 1;
  if (idx === stopIndex) return;
  animating = true;
  animFrom = STOPS[stopIndex];
  animTo = STOPS[idx];
  stopIndex = idx;
  animStart = performance.now();
}

function tick(now) {
  if (animating) {
    var t = (now - animStart) / ANIM_MS;
    if (t >= 1) {
      t = 1; animating = false;
      cooldownUntil = now + COOLDOWN_MS;   /* гасим инерцию жеста */
      wheelAccum = 0;
    }
    /* время линейное: разгон и торможение даёт easeInOutSine внутри таймлайна,
       а плоские hold-зоны по краям — паузы на появление/уход текста */
    renderedProgress = animFrom + (animTo - animFrom) * t;
  }

  var p = renderedProgress;

  updateOverlays(p);

  var ff = frameFloatFromProgress(p);
  if (ff !== lastFF) dirSign = ff >= lastFF ? 1 : -1;

  decodePump(Math.round(ff));

  /* перерисовка: если кадр сдвинулся ИЛИ прошлый раз рисовали заменой */
  if (Math.abs(ff - lastFF) > 0.002 || !lastDrawExact) {
    if (drawFrame(ff)) lastFF = ff;
  }
}

/* ---------------- жесты ---------------- */
function onWheel(e) {
  e.preventDefault();
  var now = performance.now();
  if (animating || now < cooldownUntil) return;
  wheelAccum += e.deltaY;
  if (wheelAccum > GESTURE_PX)       { wheelAccum = 0; goTo(stopIndex + 1); }
  else if (wheelAccum < -GESTURE_PX) { wheelAccum = 0; goTo(stopIndex - 1); }
}

var touchY = null, touchUsed = false;
function onTouchStart(e) { touchY = e.touches[0].clientY; touchUsed = false; }
function onTouchMove(e) {
  e.preventDefault();
  if (touchY == null || touchUsed || animating || performance.now() < cooldownUntil) return;
  var dy = touchY - e.touches[0].clientY;
  if (dy > 24)       { touchUsed = true; goTo(stopIndex + 1); }
  else if (dy < -24) { touchUsed = true; goTo(stopIndex - 1); }
}

function onKey(e) {
  if (e.key === "ArrowDown" || e.key === "PageDown" || e.key === " ") { e.preventDefault(); goTo(stopIndex + 1); }
  else if (e.key === "ArrowUp" || e.key === "PageUp")                 { e.preventDefault(); goTo(stopIndex - 1); }
}

/* =========================================================================
   СТАРТ
   ========================================================================= */
function startLoop() {
  window.addEventListener("wheel", onWheel, { passive: false });
  window.addEventListener("touchstart", onTouchStart, { passive: true });
  window.addEventListener("touchmove", onTouchMove, { passive: false });
  window.addEventListener("keydown", onKey);
  (function raf(now) {
    tick(now || performance.now());
    requestAnimationFrame(raf);
  })(performance.now());
}

function boot() {
  for (var i = 0; i < OVERLAYS.length; i++) {
    OVERLAYS[i].node = document.getElementById(OVERLAYS[i].id);
  }
  resize();
  window.addEventListener("resize", function () { resize(); });

  if (reduceMotion) {
    /* статичный первый кадр + первый текст */
    fetch(framePath(0)).then(function (r) { return r.blob(); })
      .then(function (b) { return createImageBitmap(b); })
      .then(function (bm) {
        bitmaps[0] = bm; drawFrame(0); updateOverlays(0);
        preloader.classList.add("is-hidden");
      });
    return;
  }

  preloadBlobs(
    function () { /* спиннер — прогресс не отображаем */ },
    function () {
      /* декодируем стартовое окно, затем открываем сцену */
      decodePump(0);
      var waitFirst = setInterval(function () {
        if (bitmaps[0]) {
          clearInterval(waitFirst);
          drawFrame(0); lastFF = 0;
          updateOverlays(0);
          preloader.classList.add("is-hidden");
          setTimeout(function () { preloader.style.display = "none"; }, 650);
          startLoop();
        } else {
          decodePump(0);
        }
      }, 40);
    }
  );
}

boot();
