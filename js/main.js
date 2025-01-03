import $ from "./machine.js";
import Common from "./common.js";
import Persist from "./storage.js";
import { Chord } from "./mapping.js";
import { HarmonicLattice, Harmonic, Interval } from "./interval.js";
import { Keyboard, Scale } from "./keyboard.js";



// TODO Unify experience across Chrome and Safari (minimum)
if (/Firefox/.exec(navigator.userAgent) === null) $("#browser-advice").showModal();



// Interval Manager

class IntervalManager {
  static #ivs = {}
  static set (name, fn, ms) {
    this.#ivs[name] = setInterval(fn, ms)
  }
  static clear (name) {
    const iv = this.#ivs[name];
    delete this.#ivs[name]
    clearInterval(iv);
  }
  static has (name) { return name in this.#ivs }
}



// Track

class Track {}



// Menu state

class MenuState {}



// Page state

class Listeners {
  static dragDropTouch = ((img, dx, dy) => ({
    touchstart (e) {
      e.preventDefault();
      const
        { changedTouches: [ { pageX, pageY } ] } = e,
        { left, top } = this.getBoundingClientRect();
      $("body").classList.add("copying");
      dx = pageX - left;
      dy = pageY - top;
      img = this.cloneNode(true);
      img.id = "drag-feedback";
      img.style.setProperty("left", pageX - dx + 40 + "px");
      img.style.setProperty("top", pageY - dy + 40 + "px")
      document.body.appendChild(img);
      if (this.classList.contains("chord")) this.dataset.active = ""
    },
    touchmove ({ changedTouches: [ { pageX, pageY } ] }) {
      img.style.setProperty("left", pageX - dx + 40 + "px");
      img.style.setProperty("top", pageY - dy + 40 + "px");
      const clipboardEl = $("#clipboard-item-select");
      $("#clipboard-item-select").classList
        .toggle("active", document.elementsFromPoint(pageX, pageY).includes(clipboardEl))
    },
    touchend ({ changedTouches: [ { pageX, pageY } ] }) {
      img.remove();
      const clipboardEl = $("#clipboard-item-select"), { classList } = this;
      if (document.elementsFromPoint(pageX, pageY).includes(clipboardEl)) {
        const
          e = new Event("drop", { bubbles: true, cancelable: true }),
          tr = new DataTransfer();
        let data;
        if (classList.contains("harm-obj")) data = { type: "harmonic", order: this.parentElement.dataset.harm };
        else if (classList.contains("subharm-obj")) data = { type: "subharmonic", order: this.parentElement.dataset.harm };
        else if (classList.contains("interval-obj")) data = { type: "interval", interval: this.parentElement.dataset.interval };
        else if (classList.contains("chord")) {
          this.dataset.active = "";
          data = { type: "chord" };
        }
        tr.setData("text/plain", JSON.stringify(data));
        tr.effectAllowed = "copy";
        tr.dropEffect = "copy";
        e.dataTransfer = tr;
        clipboardEl.dispatchEvent(e)
      } else if (classList.contains("chord")) delete this.dataset.active;
      $("body").classList.remove("copying")
    }
  }))()
}



// App state

// TODO: add freeze property feature to machine.js
const
  app = self.app = new $.Machine({
  // Global
    version: "0.0.7",
    storage: null,
    globalBatchSize: 10,

  // Navigation
    menuState: [],

  // Keyboard
    maxEdo: 270,
    maxKeyboardNameLength: 255,
    maxHarmonic: 57,

    keyboard: null,
    keyboards: null,
    keyboardSelection: null,

    canvas: null,
    gridctx: null,
    audioctx: null,
    masterVolume: null,

    octaves: null,

  // Track
    tracks: {},
    trackSelection: null
  });



// Events

$.targets({

  DOMContentLoaded () { app.emit("init") },

  document: { fonts: { loadingdone () {
    if (!Keyboard.ready) return;
    app.emit("resize", true);
    app.keyboard.hexGrid.redraw(true)
  } } },

  // blur () { $("body").classList.remove("copying") },

  async pointerdown (e) {
    if (e.pointerType !== "mouse") {
      const name = crypto.randomUUID();
      await $.pipe("userActivate", () => new Promise(r => $.targets({
        pointerup: ({ [name] () {
          $.targets({ pointerup: name }, self);
          r()
        } })[name]
      }, self))).then(() => $.pipe("userActivate"))
    }
    $.targets({ pointerdown: "pointerdown" }, self);
    Keyboard.userActivate();
    const audioctx = app.audioctx = new AudioContext(), masterVolume = app.masterVolume = audioctx.createGain();
    masterVolume.connect(audioctx.destination);
    masterVolume.gain.value = Common.scaleVolume($("#volume > input").valueAsNumber);
  },

  resize () {
    if (!Keyboard.ready) return;
    app.emit("resize", true);
    app.keyboard.hexGrid.redraw(true)
  },

  keydown (e) { switch (e.key) {
    case "Control": $("body").classList.add("copying"); break
    case "Escape": document.activeElement.blur()
  } },
  keyup (e) { if (e.key === "Control") $("body").classList.remove("copying") },

  "touchstart touchend touchmove" (e) {
    if (!Keyboard.ready) return;
    const nav = $("nav");
    if (e.type === "touchstart" && document.activeElement === nav && !e.composedPath().includes(nav)) nav.blur();
    const canvas = $("canvas");
    if (e.target === $("main")) for (const { clientX, clientY, identifier } of e.changedTouches) {
      const
        x = clientX - canvas.offsetLeft, y = clientY - canvas.offsetTop,
        { keyboard } = app, { hexGrid } = keyboard;
      if (keyboard && (keyboard.touches.has("touch-" + identifier) || e.type === "touchstart") &&
        (hexGrid.hasHex(...hexGrid.getCoord(x, y)) || e.type === "touchend"))
        app.emit("press", x, y, "touch", e.type.slice(5), identifier)
    }
  },

  mousedown (e) {
    if (!Keyboard.ready) return;
    const { keyboard } = app, { hexGrid } = keyboard;
    if (e.target === $("main") && hexGrid.hasHex(...hexGrid.getCoord(e.layerX, e.layerY))) {
      keyboard.mousedown = true;
      app.emit("press", e.layerX, e.layerY, "mouse", "start")
    } else if (e.ctrlKey) {
      const mbCopy = e.target.closest(".copyable");
      if (mbCopy) app.emit("copy", { node: mbCopy })
    }
  },
  mousemove (e) {
    if (!Keyboard.ready) return;
    const
      { keyboard } = app, { hexGrid, mousedown } = keyboard,
      hex = hexGrid.getHex(...hexGrid.getCoord(e.layerX, e.layerY)), main = $("main");
    main.classList.toggle("hover", (mousedown || e.target === main) && Boolean(hex));
    if (!mousedown) keyboard.hoveredKey = e.target === main ? hex?.note.key : null;
    if (mousedown && hex) app.emit("press", e.layerX, e.layerY, "mouse", "move");
  },
  "mouseup mouseout" (e) {
    if (!Keyboard.ready) return;
    const { keyboard } = app;
    if (keyboard.mousedown && e.type !== "mouseout") {
      keyboard.mousedown = false;
      app.emit("press", e.layerX, e.layerY, "mouse", "end")
    }
  },

  wheel (e) {
    const { keyboard } = app;
    if (keyboard.hoveredKey) keyboard.cycle("label", e.deltaY);
    else if (e.composedPath().includes($("#clipboard-peek"))) keyboard.cycle("clipboard", e.deltaY)
  },

  contextmenu (e) { e.preventDefault() },

  "fullscreenchange fullscreenerror" () { $("#fullscreen").classList.toggle("active", document.fullscreenElement) },

  visibilitychange () { if (document.visibilityState === "hidden") app.keyboard.save() },

  app: {

    async init () {
      this.storage = new Persist(app.version);
      await this.storage.ready;
      this.canvas = $("#hex");
      this.gridctx = this.canvas.getContext("2d");

      Keyboard.attach({
        // Keyboard selection
        selectEl: $("#keyboard-select > select"),
        edoInfoEl: $("#edo-info"),
        limitInfoEl: $("#limit-info"),

        // Keyboard settings

        nameFieldEl: $("#keyboard-name-field"),
        nameTextEl: $("#keyboard-name-text"),
        gstepEl: $("#gstep > input"),
        hstepEl: $("#hstep > input"),
        orientationSelectEl: $("#orientation > select"),
        unitEl: $("#unit > input"),
        refNoteEl: $("#refNote > input"),
        freqBasisEl: $("#freqBasis > input"),
        edoEl: $("#edo > input"),
        limitEl: $("#limit > input"),
        maxErrorEl: $("#maxError > input"),
        displayKeyNamesEl: $("#hexbutton-labels"),
        scaleOutputEl: $("#scale > output")
      });
      Keyboard.limitEl.max = this.maxHarmonic;
      await this.emitAsync("load-presets");

      // Resize cbs called around pageshow (ie after load); TODO Put these elsewhere?
      const navEl = $("nav"), clipboardEl = $("#clipboard-item-select");
      new ResizeObserver(() => clipboardEl.style.setProperty("--nav-height", navEl.offsetHeight + "px")).observe(navEl);
      new ResizeObserver(() => {
        this.emit("resize", true);
        this.keyboard.hexGrid.redraw(true)
      }).observe($("main"));
      const
        keyboardSettingsEl = $("#keyboard-settings"),
        mappingFieldsetEl = $("#harmonic-mapping"),
        ivInnerTableEl = $("#interval-table"), diamondEl = $("#diamond");
      new ResizeObserver(() =>
        mappingFieldsetEl.style.setProperty("--iv-height", `${Math.round(keyboardSettingsEl.offsetHeight)}px`)
      ).observe(keyboardSettingsEl);
      const
        ro1 = new ResizeObserver(() => {
          const height = diamondEl.offsetHeight || ivInnerTableEl.offsetHeight;
          mappingFieldsetEl.style.setProperty("--iv-scrollHeight", `${Math.round(height)}px`)
        }),
        ro2 = new ResizeObserver(() => {
          const
            { offsetHeight, offsetTop } = $("#interval-view"), { offsetTop: fsTop } = mappingFieldsetEl,
            { offsetLeft: x } = $("#keyboard-settings > form");
          mappingFieldsetEl.style.setProperty("--iv-offsetTop", `${Math.round(offsetHeight + offsetTop - fsTop - x)}px`)
        });
      ro1.observe(diamondEl);
      ro1.observe(ivInnerTableEl);
      ro2.observe(keyboardSettingsEl);
      ro2.observe($("#mapping"));
      ro2.observe($("#ivtable-wrapper"));
      const
        tempsEl = $("#temperaments"), tempsListEl = $("#temperament-list"),
        loadingCommasEl = $("#computing-commas");
      let isInt;
      new IntersectionObserver(es => es.forEach(e => {
        const { isIntersecting } = e;
        if (!IntervalManager.has("loading-commas")) IntervalManager.set("loading-commas", () => {
          if (isInt) this.emit("generate-temperaments");
          else IntervalManager.clear("loading-commas")
        }, 0);
        loadingCommasEl.classList.toggle("active", isInt = isIntersecting)
      }), { threshold: [0, .01] }).observe(loadingCommasEl);
      new ResizeObserver(() => {
        tempsListEl.style.setProperty("--tp-height", `${Math.round(tempsEl.offsetHeight)}px`);
        tempsListEl.style.setProperty("--tp-width", `${
          Math.max(parseInt(tempsListEl.style.getPropertyValue("--tp-width")) , Math.round(tempsListEl.offsetWidth))}px`)
      }).observe(tempsListEl);

      $.all("input[size]").forEach(el => el.style.setProperty("--size", el.size));

      $("#track-select > select").selectedIndex = 0
    },

    "clear-storage": Persist.reset,

    async "load-presets" () {  // Once, initially
      this.octaves = $("#octaves > input").value = parseInt(this.storage.loadItem("octaves", 2));

      // Keyboards
      const { storage } = this;
      await storage.ready;
      const
        keyboards = this.keyboards = (await storage.loadKeyboards()).reduce((obj, kb) => ({ ...obj, [kb.name]: kb }), {}),
        keyboardSelection = this.keyboardSelection = storage.loadItem("keyboardSelection", Object.keys(keyboards)[0]),
        keyboard = keyboards[keyboardSelection], clipboard = keyboard.clipboard ?? [], kbSelectHrEl = $("#keyboard-select hr");
      this.keyboard = new Keyboard(keyboard);
      Object.keys(keyboards).forEach(name => {
        const el = $.load("option", "", Keyboard.selectEl)[0][0]
        el.innerText = name;
        el.setAttribute("name", name);
        Keyboard.selectEl.insertBefore(el, kbSelectHrEl)
      });
      Keyboard.selectEl.value = keyboardSelection;
      Keyboard.noteColours = JSON.parse(storage.loadItem("noteColours", JSON.stringify(Keyboard.noteColours)));
      await this.keyboard.fillSettings();
      Keyboard.ready = true;

      // Tracks
      const
        tracks = this.tracks = (await storage.loadTracks()).reduce((obj, tr) => ({ ...obj, [tr.name]: tr }), {}),
        trackSelEl = $("#track-select select"), trackSelectHrEl = $("#track-select hr");
      Object.keys(this.tracks).forEach(name => {
        const el = $.load("option", "#track-select > select")[0][0];
        el.innerText = name;
        el.setAttribute("name", name);
        trackSelEl.insertBefore(el, trackSelectHrEl)
      })

    },

    resize (reset) {
      const
        { hexGrid } = this.keyboard,
        { canvas, octaves } = this, { unit, orientation: [g, h], theta } = hexGrid,
        x = (2 * g + h) * Math.sqrt(3) / 2, y = h * 1.5,
        { width, height } = $("main").getBoundingClientRect(),
        r = hexGrid.r = Math.min(unit * 2, width / (Math.hypot(x, y) * octaves + 2) * 2);
      if (reset) {
        hexGrid.w = canvas.width = Math.ceil(width) * 2,
        hexGrid.h = canvas.height = Math.ceil(height) * 2;
        this.gridctx.textBaseline = "middle"
      }
      hexGrid.c = (octaves % 2) * Math.hypot(x, y) * r / 2;
      hexGrid.octLen = Math.hypot(x, y) * r;

      const tempsListEl = $("#temperament-list");
      if (tempsListEl) {
        tempsListEl.style.setProperty("--tp-height", `${Math.round($("#temperaments").offsetHeight)}px`);
        tempsListEl.style.setProperty("--tp-width", `${Math.round(tempsListEl.offsetWidth)}px`)
      }
    },

    press (x, y, type, action, id) {
      id = type + "-" + id;
      const { keyboard } = this, coord = keyboard.hexGrid.getCoord(x, y), [ g, h ] = coord;
      switch (action) {
        case "start": keyboard.play(g, h, id); break;
        case "move":
          if (keyboard.touches.get(id).hexes[0].coord.some((v, i) => v !== coord[i])) {
            keyboard.stop(id);
            keyboard.play(g, h, id)
          }
          break;
        case "end": keyboard.stop(id)
      }
    },

    copy ({ node, text }) {  // Move to Keyboard?
      let type, chord;
      const
        clipboardEl = $("#clipboard-item-select"), clipboardPeekEl = $("#clipboard-peek"),
        { keyboard } = this, { scale, clipboard } = keyboard, { mapping } = scale, { lattice } = mapping;
      if (text) {
        const data = JSON.parse(text);
        ({ type } = data);
        const { inversion, internalIntervals, ...opts } = data.data ?? {};
        switch (type) {
          case "harmonic": node = $(`[data-harm="${data.order}"] > .harm-obj`); break
          case "subharmonic": node = $(`[data-harm="${data.order}"] > .subharm-obj`); break
          case "interval": node = $(`[data-interval="${data.interval}"] > .interval-obj`); break
          case "chord":
            delete (node = $(".chord[data-active]"))?.dataset.active;
            if (!node) {
              if (internalIntervals) opts.internalIntervals = internalIntervals
                .map(ivs => ivs.map(([n, d]) => mapping.intervalSet.addRatio(n, d)));
              chord = new Chord({ keyboard, mapping, ...opts }).withInversion(inversion, true)
            }
        }
      } else {
        const { classList } = node;
        let data;
        if (classList.contains("harm-obj")) data = { type: "harmonic", order: this.parentElement.dataset.harm };
        else if (classList.contains("subharm-obj")) data = { type: "subharmonic", order: this.parentElement.dataset.harm };
        else if (classList.contains("interval-obj")) data = { type: "interval", interval: this.parentElement.dataset.interval };
        else if (classList.contains("chord")) data = { type: "chord" };
        ({ type } = data);
        text = JSON.stringify(data)
      }
      let
        data = {
          start: function (id) {
            this.classList.add("active");
            chord.start("pointer-" + id)
          }.bind(clipboardPeekEl),
          stop: function (id) {
            this.classList.remove("active");
            chord.stop("pointer-" + id)
          }.bind(clipboardPeekEl)
        };
      switch (type) {
        case "harmonic": case "subharmonic":
          data.item = lattice.harmonicList.get(parseInt(node.parentElement.dataset.harm)).withQuality(type);
          chord = new Chord({
            keyboard, mapping, type: "harmonic series", voicing: [0, 0],
            harmonics: [ data.item.order, 1 ], bass: 1, isSubHarm: data.item.isSubHarm
          })
          break
        case "interval":
          data.item = mapping.intervalSet.getRatio(...node.parentElement.dataset.interval.split("/"));
          const { n, d } = data.item;
          chord = new Chord({ keyboard, mapping, type: "harmonic series", harmonics: [ n, d ], bass: n < d ? n : d, isSubHarm: n < d });
          break
        case "chord":
          if (chord) data.item = chord;
          else {
            data.item = this.keyboard.scale.mapping.temperament
              .getChordByIntervals(JSON.parse($(".chord-intervals", node).dataset.intervals).map(v => v.map(BigInt)));
            // Chord.fromRepr({ keyboard, mapping, type: "essentially tempered", chordRaw: { edo, limit, nd, dd, internalIntervalsRaw } })
            chord = data.item;
            text = JSON.stringify({ type, data: JSON.parse(chord.toString()) })
          }
      }
      data.text = text;
      clipboard.unshift(data);
      keyboard.save();
      keyboard.clipboardPeekIndex = 0;
      this.emit("clipboard-display-peek")
    },

    uncopy () {
      const { keyboard } = this, { clipboard, clipboardPeekIndex } = keyboard;
      keyboard.clipboard.splice(clipboardPeekIndex, 1);
      keyboard.save();
      keyboard.clipboardPeekIndex = clipboard.length === 0 ? null :
        Math.min(clipboardPeekIndex, clipboard.length - 1);
      this.emit("clipboard-display-peek")
    },

    "clipboard-display-peek" () {
      const { clipboard, clipboardPeekIndex } = this.keyboard, data = clipboard[clipboardPeekIndex];
      $("#clipboard-peek > *")?.remove();
      if (!data) return;
      else if (Harmonic.prototype.isPrototypeOf(data.item)) {
        const
          itemEl = $.load("clipboard-item-harmonic", "#clipboard-peek")[0][0],
          [ hColourEl, hOrderEl, hSpellingEl ] = itemEl.children,
          colours = $.all(`.harmonic[data-harm="${data.item.order}"] > .hcolour`).map(el => el.value)
        if (colours.length === 1) hColourEl.style.setProperty("--colour", colours[0]);
        else {  // TODO: won't work for 15 without 3 and 5
          hColourEl.classList.add("split-colours");
          hColourEl.style.setProperty("--colour-1", colours[0]);
          hColourEl.style.setProperty("--colour-2", colours[1]);
        }
        hOrderEl.innerText = Common.ordinal(data.item.order);
        hSpellingEl.innerText = data.item.label
      } else if (Interval.prototype.isPrototypeOf(data.item)) {
        const
          itemEl = $.load("clipboard-item-interval", "#clipboard-peek")[0][0],
          [ iColourEl, ratioEl, spellingEl ] = itemEl.children, { fraction, splitDecomp } = data.item,
          colours = splitDecomp.map(side => side.findLast(([p]) => p !== 3)?.[0])
            .filter(Boolean).map(h => Keyboard.noteColours[h]);
        if (colours.length === 1) iColourEl.style.setProperty("--colour", colours[0]);
        else {
          if (colours.length === 0) ([ colours[0], colours[1] ] = [ Keyboard.noteColours.white, Keyboard.noteColours.black ]);
          iColourEl.classList.add("split-colours");
          iColourEl.style.setProperty("--colour-1", colours[0]);
          iColourEl.style.setProperty("--colour-2", colours[1]);
        }
        ratioEl.innerHTML = `<sup>${fraction[0]}</sup>⁄<sub>${fraction[1]}</sub>`;
        spellingEl.innerText = data.item.noteSpelling.number
      } else if (Chord.prototype.isPrototypeOf(data.item)) {
        $.load("clipboard-item-chord", "#clipboard-peek")[0][0].innerText = data.item.chordName.values().next().value
      }
    },

    panic () {
      this.audioctx.close();
      const
        audioctx = this.audioctx = new AudioContext(),
        masterVolume = this.masterVolume = audioctx.createGain();
      masterVolume.connect(audioctx.destination);
      masterVolume.gain.value = Common.scaleVolume($("#volume > input").valueAsNumber);
      IntervalManager.clear("pointerdown")
    },

    fullscreen () { document.fullscreenElement ? document.exitFullscreen() : $("body").requestFullscreen() },



    // Keyboard

    async "keyboard-select" (name) {
      if (this.menuState.at(-2) === "keyboard-settings") await this.keyboard.save(); // TODO get menu state nicely
      this.storage.saveItem("keyboardSelection", this.keyboardSelection = name);
      this.keyboard = new Keyboard(this.keyboards[name]); // From here if settings open, app.keyboard !== menuState[1]
      await this.keyboard.fillSettings();
      this.emit("generate-keyboard");

      $.all("#commas > .comma, #chords > .chord").forEach(el => el.remove());
      IntervalManager.clear("loading-commas");
      if (app.menuState[0] === "temperaments") app.emit("menu-select", [ "temperaments" ]);
    },

    "keyboard-name-update" (name) {
      const
        { keyboard, keyboards, storage } = this,
        { name: oldName } = keyboard, keyboardObj = keyboards[oldName];
      if (name === "New" || name in keyboards && Keyboard.selectEl.value !== name) {
        $("#keyboard-name-field").classList.add("invalid");
        return
      }
      app.keyboardSelection = keyboard.name = keyboardObj.name = name;
      delete keyboards[oldName];
      keyboards[name] = keyboardObj;
      Keyboard.nameTextEl.innerText = name;
      Keyboard.nameFieldEl.classList.remove("invalid");
      $("#keyboard-name").classList.remove("editing");
      $(`#keyboard-select option[name='${oldName}']`)?.remove();
      const
        el = $.load("option", "#keyboard-select > select")[0][0],
        nextEl = [...Keyboard.selectEl.options].slice(1)
          .find(el => el.value.localeCompare(name) > 0);
      el.innerText = name;
      el.setAttribute("name", name);
      nextEl ? Keyboard.selectEl.insertBefore(el, nextEl) : Keyboard.selectEl.append(el);
      el.selected = true;

      storage.saveItem("keyboardSelection", name);
      storage.deleteKeyboard(oldName).then(() => keyboard.save())
    },

    "keyboard-create" () {
      if (Keyboard.nameFieldEl.classList.contains("invalid")) return;
      const
        { name } = this.keyboard,
        nth = Object.keys(this.keyboards)
          .map(kn => kn.match(/(\(([1-9]\d*)\))?$/)?.slice(2).map(v => v ? parseInt(v) : 0))
          .flat().sort((a, b) => a > b).findLastIndex((k, i) => k === i) + 1,
        newName = name.match(/^(.*?)(?:\([1-9]\d*\))?$/)[1] + `(${nth})`,
        keyboardObj = this.keyboards[newName] = this.keyboards[name];
      this.keyboard = new Keyboard(keyboardObj);
      this.keyboardSelection = this.keyboard.name = keyboardObj.name = newName
      Keyboard.nameTextEl.innerText = newName;
      Keyboard.nameFieldEl.value = newName;
      const
        el = $.load("option", "#keyboard-select > select")[0][0],
        nextEl = Keyboard.selectEl.namedItem(name).nextElementSibling;
      el.innerText = newName;
      el.setAttribute("name", newName);
      nextEl ? Keyboard.selectEl.insertBefore(el, nextEl) : Keyboard.selectEl.append(el);
      el.selected = true;

      this.storage.saveItem("keyboardSelection", newName);
      this.keyboard.save()
    },

    async "keyboard-delete" (response) {
      $("#delete-keyboard-dialog").close();
      if (response === "Cancel") return;
      const
        { keyboards, keyboardSelection, storage } = this, { selectEl } = Keyboard,
        { index } = selectEl.namedItem(keyboardSelection);
      const optionEl = selectEl[index + (index < selectEl.length - 1 ? 1 : -1)]; // Cover empty case
      optionEl.selected = true;
      await app.emitAsync("keyboard-select", optionEl.value);
      app.menuState[1] = { keyboard: app.keyboard };
      await this.emit("menu-cancel");
      $(`#keyboard-select option[name='${keyboardSelection}']`).remove();
      await storage.deleteKeyboard(keyboardSelection);
      delete this.keyboards[keyboardSelection];
    },

    "generate-keyboard" () {
      const
        { limitEl, maxErrorEl, edoEl, refNoteEl, freqBasisEl } = Keyboard,
        limit = limitEl.valueAsNumber,
        maxError = maxErrorEl.valueAsNumber,
        edo = edoEl.valueAsNumber,
        refNote = refNoteEl.valueAsNumber,
        freqBasis = freqBasisEl.valueAsNumber,
        { keyboard } = this;
      $.all(".harmonic").forEach(el => el.remove());
      
      const
        scale = new Scale({ keyboard, limit, maxError, refNote, freqBasis }), { mapping } = scale,
        { rawHarmonicList, lattice, intervalSet } = mapping, { harmonicList, primes, indexPrimes } = lattice;

      for (const [ harmonic, steps ] of rawHarmonicList) {
        const
          dec = Common.decomp(harmonic)[0],
          primeHarmonic = [ ...dec ][0][0],
          isPrime = primes.concat(indexPrimes).includes(harmonic),
          harmObj = harmonicList.get(harmonic),
          just = Math.log2(harmonic) % 1,
          labelEl = $.load("harmonic", "#mapping")[0][0],
          [ , spellingEl, inputEl, compositeStepsEl, ,
            , subSpellingEl, subStepsEl, , errorEl, colourEl ] = labelEl.children;
        labelEl.dataset.harm = harmonic;
        $.all(".nth-harmonic", labelEl).forEach(el => el.innerText = Common.ordinal(harmonic));
        spellingEl.innerText = mapping.intervalSet.getRatio(harmonic, 1).noteSpelling.roman;
        inputEl.setAttribute("value", steps);
        inputEl.setAttribute("min", Math.max(1, Math.ceil((just - maxError / 1200) * edo)));
        inputEl.setAttribute("max", Math.min(edo - 1, Math.floor((just + maxError / 1200) * edo)));
        inputEl.style.setProperty("--size", inputEl.size);
        // TODO eg hcolour when 15 in but 3, 5 out
        if (harmObj.isBasis) labelEl.classList.add("basis");
        if (isPrime) labelEl.classList.add("prime");
        else {
          compositeStepsEl.innerText = steps;
          if (dec.size === 1 && [ ...dec ][0][1] > 1) labelEl.classList.add("prime", "power"); // Not correct
        }
        subSpellingEl.innerText = mapping.intervalSet.getRatio(1, harmonic).noteSpelling.romanlow;
        subStepsEl.innerText = edo - steps;
        errorEl.innerText = ((steps / edo - just) * 1200).toFixed(2);
        if (harmObj.isBasis && primeHarmonic === 3) { // Not correct!
          colourEl.value = Keyboard.noteColours.white;
          labelEl.appendChild(colourEl.cloneNode()).value = Keyboard.noteColours.black
        } else if (isPrime) colourEl.value = Keyboard.noteColours[harmonic] ??= Keyboard.noteColours.default;
        const
          harm = new Chord({
            keyboard, mapping, type: "harmonic series", voicing: [0, 0],
            harmonics: [ harmonic, 1 ], bass: 1
          }),
          subharm = new Chord({
            keyboard, mapping, type: "harmonic series", voicing: [0, 0],
            harmonics: [ harmonic, 1 ], bass: harmonic, isSubHarm: true
          });

        $.queries({
          "input.steps": { change () { app.emit("generate-keyboard") } },
          "input.hcolour": { change () {
            Keyboard.setColour(primeHarmonic, this.value, this === $.all("input.hcolour", labelEl)[1])
          } },
          button: {
            pointerdown ({ pointerId }) {
              this.setPointerCapture(pointerId);
              ("isSubharm" in this.dataset ? subharm : harm).start("pointer-" + pointerId)
            },
            "pointerup lostpointercapture" ({ pointerId }) {
              if (!this.hasPointerCapture(pointerId)) return;
              ("isSubharm" in this.dataset ? subharm : harm).stop("pointer-" + pointerId);
              this.releasePointerCapture(pointerId)
            }
          },
          ".copyable": {
            dragstart (e) {
              $("body").classList.add("copying");
              e.dataTransfer.effectAllowed = "copy";
              e.dataTransfer.dropEffect = "copy";
              e.dataTransfer.setData("text/plain", JSON.stringify({
                type: this.classList.contains("harm-obj") ? "harmonic" : "subharmonic",
                order: this.parentElement.dataset.harm
              }))
            },
            dragend () { $("body").classList.remove("copying") },
            ...Listeners.dragDropTouch
          }
        }, labelEl)
      }
      Object.assign(keyboard, { edo, scale });

      // Tonality diamond
      const diamondEl = $("#diamond");
      $.all(":scope > *", diamondEl).forEach(el => el.remove());
      const
        temperings = $.all(".harmonic").map(el => [ parseInt(el.dataset.harm), $("input", el).valueAsNumber ])
          .sort(([p], [q]) => Math.log2(p) % 1 > Math.log2(q) % 1),
        h = temperings.length, intervals = new Map(), chords = new Map();
      diamondEl.style.setProperty("--size", 2 * h + 1);
      for (let i = 0; i <= h; i++) {
        const
          cell = $.load("interval-cell", "#diamond")[0][0],
          [ interval, note, width, button ] = $.all(":scope > *", cell);
        cell.style.gridArea = `${h + 1}/${2 * i + 1}/span 1/span 2`;
        interval.innerHTML = "<sup>1</sup>⁄<sub>1</sub>";
        note.innerText = "I";
        width.innerText = button.dataset.steps = 0
        cell.dataset.interval = "1/1"
      }
      for (let i = h; i > 0; i--) for (let j = 0; j < i; j++) {
        const
          upperCell = $.load("interval-cell", "#diamond",)[0][0],
          lowerCell = $.load("interval-cell", "#diamond",)[0][0],
          [ upperInterval, upperNote, upperWidth, upperButton ] = $.all(":scope > *", upperCell),
          [ lowerInterval, lowerNote, lowerWidth, lowerButton ] = $.all(":scope > *", lowerCell),
          upperIv = intervalSet.getRatio(temperings[h - i + j][0], temperings[j - 1]?.[0] ?? 1).withOctave(0),
          lowerIv = intervalSet.getRatio(temperings[j - 1]?.[0] ?? 1, temperings[h - i + j][0]).withOctave(0),
          [nUp, dUp] = upperIv.fraction.map(Number), [nLo, dLo] = lowerIv.fraction.map(Number);
        upperCell.style.gridArea = `${i}/${h - i + 2 + 2 * j}/span 1/span 2`;
        lowerCell.style.gridArea = `${2 * h + 2 - i}/${h - i + 2 + 2 * j}/span 1/span 2`;
        upperInterval.innerHTML = `<sup>${nUp}</sup>⁄<sub>${dUp}</sub>`;
        lowerInterval.innerHTML = `<sup>${nLo}</sup>⁄<sub>${dLo}</sub>`;
        upperNote.innerText = upperIv.noteSpelling[upperIv.n > upperIv.d ? "roman" : "romanlow"];
        lowerNote.innerText = lowerIv.noteSpelling[lowerIv.n > lowerIv.d ? "roman" : "romanlow"];
        upperCell.dataset.interval = upperIv.fraction.join("/");
        lowerCell.dataset.interval = lowerIv.fraction.join("/");
        upperWidth.innerText = upperButton.dataset.steps = mapping.steps(upperIv);
        lowerWidth.innerText = lowerButton.dataset.steps = mapping.steps(lowerIv);
        chords.set(upperInterval, new Chord({ keyboard, mapping, type: "harmonic series", harmonics: [ nUp, dUp ], bass: dUp }));
        chords.set(lowerInterval, new Chord({ keyboard, mapping, type: "harmonic series", harmonics: [ nLo, dLo ], bass: dLo }))
      }
      app.emit("resize", true);
      keyboard.hexGrid.redraw(true);

      // Interval table
      const ivTable = $("#interval-table"), ps = primes.concat(indexPrimes).sort((a, b) => a > b);
      $.all(":scope > *", ivTable).forEach(el => el.remove());
      ivTable.style.setProperty("--harms", ps.length);
      ivTable.style.setProperty("--edo", edo);
      const [ cornerEl, firstBorderEl ] = $.load("interval-th", "", ivTable)[0];
      cornerEl.classList.add("column-head", "row-head");
      $("span", cornerEl).innerText = "Steps";
      firstBorderEl.remove();
      ps.forEach((p, k) => {
        const [ el, bel ] = $.load("interval-th", "", ivTable)[0];
        el.classList.add("column-head");
        el.style.gridColumnStart = 2 * k + 2;
        $("span", el).innerText = p;
        bel.style.gridArea = `1/${2 * k + 3}/span calc(2 * var(--edo))/span 1`;
      });
      $("div:last-of-type", ivTable).remove();
      for (let k = 0; k < edo; k++) {
        const [ el, bel ] = $.load("interval-th", "", ivTable)[0];
        el.classList.add("row-head");
        el.style.gridRowStart = 2 * k + 2;
        $("span", el).innerText = k;
        bel.style.gridArea = `${2 * k + 3}/1/span 1/span calc(2 * var(--harms))`;
      }
      $("div:last-of-type", ivTable).remove();
      $.all(".column-head:last-of-type, .row-head:last-of-type")
      for (let steps = 0; steps < edo; steps++) scale.getKey(steps).labels
        .forEach(({ interval: iv, number, keyClass }) => {
          const // TODO removable?
            [ n, d ] = iv.map(side => side.reduce(([big, log], [p, rad]) =>
              [big * BigInt(p) ** BigInt(rad), log + Math.log2(p) * rad], [1n, 0]))
              .reduce(([bn, ln], [bd, ld]) => {
                const oct = BigInt(Math.floor(ln - ld));
                return [oct < 0 ? bn << -oct : bn, oct > 0 ? bd << oct : bd]
              }),
            curh = keyClass.match(/\d{1,2}/g)
              ?.map(s => parseInt(s)).sort((a, b) => a < b)[0] ?? (steps ? 3 : 1);
          let td = $(`.interval-td[data-cell="${steps},${curh}"]`);
          if (!td) {
            td = $.load("interval-td", "", ivTable)[0][0];
            td.style.gridArea = steps === 0 ?
              `2/2/span 1/span ${2 * ps.length}` :
              `${2 * steps + 2}/${2 * ps.findIndex(p => p % curh === 0) + 2}`;
            td.dataset.cell = `${steps},${curh}`
          }
          const
            cell = $.load("interval-cell", "", td)[0][0],
            [ interval, note, width, button ] = $.all(":scope > *", cell);
          if (steps === 0) cell.id = "table-unison";
          interval.innerHTML = `<sup>${n}</sup>⁄<sub>${d}</sub>`;
          note.innerText = number;
          width.innerText = button.dataset.steps = steps
          cell.dataset.interval = `${n}/${d}`
        });

      // Play interval buttons
      $.queries({

        '.interval-display button[data-steps="0"]': {
          pointerdown ({ pointerId }) {
            this.setPointerCapture(pointerId);
            if (this.closest("#diamond"))
              $.all('.interval-display button[data-steps="0"]').forEach(el => el.parentElement.classList.add("activeEnharmonic"));
              app.keyboard.play(0, 0, "pointer-" + pointerId)
          },
          "pointerup lostpointercapture" ({ pointerId }) {
            if (!this.hasPointerCapture(pointerId)) return;
            $.all(".activeEnharmonic").forEach(el => el.classList.remove("activeEnharmonic"));
            app.keyboard.stop("pointer-" + pointerId);
            this.releasePointerCapture(pointerId)
          }
        },

        '.interval-display button:not([data-steps="0"])': {
          pointerdown ({ pointerId }) {
            this.setPointerCapture(pointerId);
            const { keyboard } = app, { mapping } = keyboard.scale, steps = parseInt(this.dataset.steps);
            $.all(`button[data-steps="${steps}"]`, this.closest(".interval-display"))
              .forEach(el => el.parentElement.classList.add("activeEnharmonic"));
            if (this.closest("#interval-table")) {
              const
                [n, d] = this.parentElement.dataset.interval.split("/").map(v => Common.non2(BigInt(v))),
                key = keyboard.scale.getKey(steps),
                enhi = key.labels.findIndex(({ interval: iv }) => Common.comp(iv[0]) === n && Common.comp(iv[1]) === d);
              ~enhi && (key.label = enhi);
              keyboard.hexGrid.redraw();
              keyboard.play(0, 0, `pointer-${pointerId}-0`);
              keyboard.play(...key.home.coord, `pointer-${pointerId}-1`);
            } else if (this.closest("#diamond")) {
              const chord = chords.get($(".interval-obj", this.parentElement));
              chord.start("pointer-" + pointerId)
            }
          },
          "pointerup lostpointercapture" ({ pointerId }) {
            if (!this.hasPointerCapture(pointerId)) return;
            $.all(".activeEnharmonic").forEach(el => el.classList.remove("activeEnharmonic"));
            if (this.closest("#interval-table")) {
              const { keyboard } = app;
              keyboard.stop(`pointer-${pointerId}-0`);
              keyboard.stop(`pointer-${pointerId}-1`);
            } else if (this.closest("#diamond")) chords.get($(".interval-obj", this.parentElement)).stop("pointer-" + pointerId)
            this.releasePointerCapture(pointerId)
          }
        },

        ".interval-display .copyable": {
          dragstart (e) {
            $("body").classList.add("copying");
            e.dataTransfer.effectAllowed = "copy";
            e.dataTransfer.dropEffect = "copy";
            e.dataTransfer.setData("text/plain", JSON.stringify({ type: "interval", interval: this.parentElement.dataset.interval }))
          },
          dragend () { $("body").classList.remove("copying") },
          ...Listeners.dragDropTouch
        }
        
      })
    },



    // Temperaments

    async "generate-temperaments" () {
      const
        { keyboard, storage } = this, { edo } = keyboard, { mapping, limit } = keyboard.scale, { lattice } = mapping,
        ps = lattice.primes.concat(lattice.index).sort((a, b) => a > b), commasEl = $("#commas");
      let boundN, hasFresh, upperBound = parseInt(commasEl.dataset.upperBound), prevn, prevd;

      const temperamentsLi = $("#temperaments");
      for (const h of lattice.primes) temperamentsLi.style.setProperty(`--hcolour-${h}`,
        Common.colourMix(Keyboard.noteColours[h === 3 ? "white" : h] ?? Keyboard.noteColours.default, Keyboard.noteColours.black, .5));

      if ($.all("#harmonic-filter > .harmonic-checkbox").length === 0) {
        for (const h of lattice.harmonicList.keys()) {
          const harmCheckboxEl = $.load("harmonic-checkbox", "#harmonic-filter")[0][0];
          harmCheckboxEl.dataset.harmonic = harmCheckboxEl.children[1].innerText = h
        }
        $.queries({
          'input[type="checkbox"].ternary': { change (e) {
            if (!this.classList.contains("active")) {
              this.classList.add("active");
              this.checked = true
            } else if (this.checked) this.classList.remove("active") }
          }
        })
      }

      await mapping.waitForCommaGen;
      const newCommas = [];
      for await (const { source, value: { n, d, nd, dd, upperBound: chordBound } } of mapping.takeCommas(upperBound)) {
        if (n === prevn && d === prevd) continue;
        prevn = n; prevd = d;
        if (source === "worker") boundN = n;
        const iv = mapping.commas.addRatio(n, d); // better version?
        if (Common.mod(mapping.steps(iv), edo) === 0) {
          mapping.commas.addRatio(n, d);
          hasFresh = true;
          // debounce and batch? move into class?
          if (source === "worker") await storage.saveComma({ edo, limit, n, d, nd, dd });
          else if (chordBound) mapping.commasBounds.set(iv, chordBound);
          const
            commaEl = $.load("comma", "", commasEl)[0][0],
            [ , diagramDiv, ratioDiv, primesDiv, sizeDiv, spellingDiv ] = commaEl.children,
            [ nDecompSpan, dDecompSpan ] = primesDiv.children;
          newCommas.push(commaEl);
          commaEl.dataset.comma = [ n, d ];
          commaEl.dataset.factors = JSON.stringify(iv.splitDecomp);
          for (const [ n ] of iv.splitDecomp[0]) $.load("hcolour-disc", ".hcolour-upper", diagramDiv)[0][0].style.setProperty("color", `var(--hcolour-${n})`);
          for (const [ d ] of iv.splitDecomp[1]) $.load("hcolour-disc", ".hcolour-lower", diagramDiv)[0][0].style.setProperty("color", `var(--hcolour-${d})`);
          ratioDiv.innerText = `${n}/${d}`;
          const t1 = Common.bigLog2(n & -n), t2 = Common.bigLog2(d & -d);
          nDecompSpan.innerHTML = (t1 > 0 ? [[2, t1]] : []).concat(iv.splitDecomp[0])
            .map(([p, rad]) => p + (rad > 1 ? `<sup>${rad}</sup>` : "")).join(".");
          dDecompSpan.innerHTML = (t2 > 0 ? [[2, t2]] : []).concat(iv.splitDecomp[1])
            .map(([p, rad]) => p + (rad > 1 ? `<sup>${rad}</sup>` : "")).join(".");
          sizeDiv.innerText = `${((Common.bigLog2(n) - Common.bigLog2(d)) * 1200).toFixed(2)}`;
          spellingDiv.innerText = iv.noteSpelling.letter;
          $.queries({ "": { click () { app.emit("generate-chords", this) } } }, commaEl)
        }
      }
      this.emit("update-temperament-filter", newCommas);
      if (!boundN) return;
      // TODO fix!
      if (hasFresh) commasEl.scrollTo(0, $("#computing-commas").offsetTop - commasEl.offsetTop - commasEl.offsetHeight - 1)
      commasEl.dataset.upperBound = upperBound = (1n + boundN / 100n) * 100n;
      await storage.saveScale({ edo, limit, upperBound }) // commaBuffer?
    },

    "update-temperament-filter" (newCommas) {
      if (newCommas === undefined) $.all("#commas > .comma.filtered").forEach(el => el.classList.remove("filtered"));
      const
        filterEls = [ ...$("#temperament-list").elements ],
        harmsRaw = filterEls.filter(el => !el.classList.contains("active") || el.checked)
          .map(el => parseInt(el.parentElement.dataset.harmonic)),
        reqs = filterEls.filter(el => el.classList.contains("active") && el.checked)
          .map(el => parseInt(el.parentElement.dataset.harmonic)),
        filterLattice = new HarmonicLattice({ harmsRaw }), blockedCommaSet = new Map();
      for (const el of (newCommas ?? $.all("#commas > .comma"))) {
        const [ n, d ] = el.dataset.comma.split(",");
        for (const h of [null].concat(reqs)) {
          const dec = filterLattice.decomp(n, d)?.() ?? null;
          if (dec === null || (h !== null && !~dec.findIndex(([c]) => c === h)))
            blockedCommaSet.set(n, (blockedCommaSet.get(n) ?? new Set()).add(d))
        }
      }
      for (const [ n, dSet ] of blockedCommaSet) for (const d of dSet)
        $(`#commas > .comma[data-comma="${[n,d]}"]`).classList.add("filtered")
    },

    async "generate-chords" (commaEl) {

      $(".comma.active")?.classList.remove("active");
      commaEl.classList.add("active");
      $.all(".comma.factor").forEach(el => el.classList.remove("factor"));
      $.all(".chord").forEach(el => el.remove());
      const
        [ n, d ] = commaEl.dataset.comma.split(",").map(x => BigInt(x)),
        [ nd, dd ] = JSON.parse(commaEl.dataset.factors),
        { keyboard, storage } = this, { edo, scale } = keyboard, { limit, mapping } = scale,
        { commas, temperaments } = mapping,
        tempsEl = $("#temperaments"), chordsFieldsetEl = $("#chord-list"), chordsEl = $("#chords"),
        [ ,, ratioDiv, primesDiv ] = commaEl.children, [ numSpan, denSpan ] = primesDiv.children;

      (async () => {
        mapping.resetWaitForTemperament();
        await mapping.waitForTemperament;
        temperaments.get(commas.getRatio(...commaEl.dataset.comma.split(",").map(h => parseInt(h)))).factors
          .forEach(({ fraction }) => $(`.comma[data-comma="${fraction}"]`)?.classList.add("factor"));
      })();
      $("#comma-info").innerHTML = `${ratioDiv.innerHTML} (${numSpan.innerHTML}/${denSpan.innerHTML})`;

      await new Promise(requestAnimationFrame);
      tempsEl.scrollTo(0, 32767);
      chordsFieldsetEl.classList.add("computing");
      await new Promise(requestAnimationFrame);
      
      const iv = commas.getRatio(n, d), chords = mapping.temperaments.get(iv)?.chords;
      mapping.resetChords(iv);
      let cursor = 0, upperBound = mapping.commasBounds.get(iv) ?? new Map();
      if (chords) {
        mapping.temperament = [n, d];
        for (const chord of chords) this.emit("populate-chord", chord, chordsEl)["populate-chord"]
      } else {
        for await (const { source, value } of mapping.takeChords(upperBound)) {
          const { done, ...ordChordRaw } = value, { internalIntervalsRaw, i, ...chordRaw } = ordChordRaw;
          chordRaw.internalIntervalsRaw = [ internalIntervalsRaw.map(ivs => [[1n, 1n]].concat(ivs)) ];
          await mapping.waitForTemperament;
          const chord = Chord.fromRepr({ keyboard, mapping, type: "essentially tempered", chordRaw });

          const existingChord = mapping.temperament.addChord(chord);
          if (chord !== existingChord) {
            existingChord.addInterpretation(chord);
            continue;
          }
          // Group chords by stack
          const
            cpart = mapping.temperament.commaPartitions[ mapping.stackMaps.get(iv)[i] ],
            stack = mapping.temperament.partitionStacks.get(cpart).find(ivs => Common.bagEq(ivs, chord.intervals)),
            stackData = mapping.temperament.stackChords.get(stack) ?? { commaPartitions: new Set(), chords: new Set() };
          stackData.commaPartitions.add(cpart);
          stackData.chords.add(chord);
          mapping.temperament.stackChords.set(stack, stackData);

          if (source === "worker") {
            await storage.saveChord(ordChordRaw);
            if (!done) upperBound.set(i, ordChordRaw.ord);
            await storage.saveComma({ edo, limit, n, d, nd, dd, upperBound });
          }
          cursor = this.emit("populate-chord", chord, chordsEl, cursor, done)["populate-chord"]
        }
        for (const { chords } of mapping.temperament.stackChords.values()) {
          const chordList = [ ...chords ];
          for (let i = 0; i < chordList.length; i++) for (let j = 0; j < i; j++) {
            chordList[i].dual = chordList[j];
            chordList[j].dual = chordList[i];
          }
        }
        mapping.temperament.genChordGraph()
      }
      await storage.saveComma({ edo, limit, n, d, nd, dd, upperBound });
      chordsFieldsetEl.classList.remove("computing");
      tempsEl.scrollTo(0, $("fieldset:has(#chords)").offsetTop - tempsEl.offsetTop)
    },

    "populate-chord" (chord, chordsEl, cursor = 0, done = false) {
      const
        chordEls = $.all(".chord", chordsEl), chordEl = $.load("chord", "#chords")[0][0],
        chordIvsEl = $(".chord-intervals", chordEl);
      chordIvsEl.dataset.intervals = JSON.stringify(chord.intervals.map(({ fraction }) => fraction.map(String)));
      chordEl.dataset.ord = JSON.stringify(chord.ord);
      const ix = chordEls.slice(cursor).findIndex(el => Common.LTE(chord.ord, JSON.parse(el.dataset.ord ?? "[]")));
      if (ix === -1) {
        cursor = chordEls.length - 1;
        chordsEl.append(chordEl)
      } else chordEls[cursor += ix].insertAdjacentElement("beforebegin", chordEl);
      cursor++;
      if (done) cursor = 0;

      app.emit("display-chord", chord, chordEl);
      $.queries({

        "button.play-chord": {
          pointerdown ({ pointerId }) {
            this.setPointerCapture(pointerId);
            if ($(".switch input:checked")) IntervalManager.set("pointerdown", () => {
              chord.stop("pointer-" + pointerId);
              chord.inversion++;
              app.emit("display-chord", chord, chordEl);
              setTimeout(() => chord.start("pointer-" + pointerId), 50)
            }, 1000);
            chord.start("pointer-" + pointerId)
          },
          "pointerup lostpointercapture" ({ pointerId }) {
            if (!this.hasPointerCapture(pointerId)) return;
            IntervalManager.clear("pointerdown");
            chord.stop("pointer-" + pointerId);
            this.releasePointerCapture(pointerId)
          }
        },

        "button.inversion": { click () {
          chord.inversion++;
          app.emit("display-chord", chord, chordEl)
        } },

        button: { "touchstart touchmove touchend" (e) { e.stopPropagation() } },
        
        "": {
          dragstart (e) {
            $("body").classList.add("copying");
            e.dataTransfer.effectAllowed = "copy";
            this.dataset.active = "";
            e.dataTransfer.setData("text/plain", "{ \"type\": \"chord\" }")
          },
          dragend () {
            $("body").classList.remove("copying");
            delete this.dataset.active
          },
          ...Listeners.dragDropTouch
        }
      }, chordEl);
      return cursor
    },

    "display-chord" (chord, chordEl) {
      const
        { keyboard } = this, { edo } = keyboard, { mapping } = keyboard.scale,
        [ chNameEl, chIntervalsEl, chPitchesEl, chSpellingEl, chControlsEl ] = chordEl.children,
        [ chIvHarmonicEl, chIvStepsEl ] = chIntervalsEl.children,
        [ chPcHarmonicEl, chPcStepsEl ] = chPitchesEl.children,
        [ chIvSpellingEl, chPcSpellingEl ] = chSpellingEl.children,
        [ chIsSymmetricEl, chNextInvBtn, chPlayChordBtn ] = chControlsEl.children;
      $.all(".chord-edo", chordEl).forEach(el => el.innerText = edo);
      chNameEl.children[0].innerHTML = chord.chordName.values().next().value; // Obviously, to be improved
      chIvHarmonicEl.innerHTML = chord.intervals.map(({ noteSpelling }) => noteSpelling.fraction).join(" ");
      chIvStepsEl.innerText = chord.temperedIntervals.map(tiv => mapping.steps(tiv)).join(" ");
      chPcHarmonicEl.innerHTML = chord.internalIntervals.map(({ noteSpelling }) => noteSpelling.fraction).join(" – ");
      chPcStepsEl.innerText = chord.internalIntervals.map(iv => mapping.steps(iv)).join("-");
      chIvSpellingEl.innerText = chord.intervals.map(({ noteSpelling }) => noteSpelling.number).join(" ");
      chPcSpellingEl.innerText = chord.internalIntervals.map(({ noteSpelling }) => noteSpelling.letter).join(" – ");
    },



    // Track editor

    "track-name-update" (name) {
      const { tracks, trackSelection, storage } = this, trackSelEl = $("#track-select > select");
      if (name === "New" || name in tracks && trackSelEl.value !== name) {
        $("#track-name-field").classList.add("invalid");
        return
      }
      $("#track-file").classList.add("saved");
      delete this.tracks[trackSelection];
      const track = this.tracks[name] = { name, text: $("#track-edit").value };
      this.trackSelection = name;
      $("#track-name-text").innerText = name;
      $("#track-name-field").classList.remove("invalid");
      $("#track-name").classList.remove("editing");
      $(`#track-select option[name='${trackSelection}']`)?.remove();
      const el = $.load("option", "#track-select > select")[0][0];
      el.innerText = name;
      el.setAttribute("name", name);
      trackSelEl.insertBefore(el, $("#track-select hr"));
      el.selected = true;

      storage.deleteKeyboard(trackSelection).then(() => storage.saveTrack(track))
    },

    "track-editor" (name) {
      const { tracks } = this;
      if (!name) {
        const
          nth = Object.keys(tracks)
            .map(tn => tn.match(/^Untitled( [1-9]\d*)?$/)?.slice(1).map(v => v ? parseInt(v) : 0))
            .flat().sort((a, b) => a > b).findLastIndex((k, i) => k === i) + 1;
        name = "Untitled" + (nth ? " " + nth : "");
        $("#track-edit").value = "";
        $("#track-file").classList.remove("saved")
      } else {
        $("#track-edit").value = tracks[name].text;
        $("#track-file").classList.add("saved")
      }
      this.trackSelection = name;
      $("#track-name-field").value = name;
      $("#track-name-field").classList.remove("invalid");
      $("#track-name-text").innerText = name;
      $("#track-name").classList.remove("editing");
    },

    "track-save" () {
      $("#track-file").classList.add("saved");
      $("#track-savestate").classList.add("saving");
      clearInterval(this.menuState[1].saveDebounce);
      this.menuState[1].saveDebounce = setTimeout(() => {
        app.storage.saveTrack(this.tracks[name]); // Hmmm
        $("#track-savestate").classList.remove("saving")
      }, 500)
      const trackSelection = $("#track-name-field").value;
      let el;
      if (!(trackSelection in this.tracks)) {
        el = $.load("option", "#track-select > select")[0][0];
        el.innerText = trackSelection;
        el.setAttribute("name", trackSelection);
        $("#track-select select").insertBefore(el, $("#track-select hr"));
        el.selected = true
      } else el = $("#track-select > select").namedItem(trackSelection);
      const name = this.trackSelection = $("#track-name-field").value;
      this.tracks[name] = { name, text: $("#track-edit").value };
      el.innerText = trackSelection;
      el.setAttribute("name", trackSelection)
    },

    "track-delete" (response) {
      $("#delete-track-dialog").close();
      if (response === "Cancel") return;
      const { tracks, trackSelection } = this;
      delete this.tracks[trackSelection];
      this.trackSelection = null;
      $(`#track-select option[name='${trackSelection}']`).remove();
      app.storage.deleteTrack(trackSelection);
      this.emit("menu-cancel")
    },



    // Menu

    async "menu-select" (which, ...data) {
      const
        breadcrumbText = {
          "keyboard-settings": "Keyboard ⛭",
          "temperaments": "Temperament 💡",
          "track-editor": "Track ✏"
        },
        prevMenu = this.menuState;
      document.activeElement.blur();
      this.menuState = which.concat([null]);
      const menuLeaf = which.at(-1);
      $("body").classList.add("menuActive");
      $("menu > .activeMenu")?.classList.remove("activeMenu");
      $("#" + menuLeaf).classList.add("activeMenu");
      $.all("#breadcrumb-text > *").forEach(el => el.remove());
      which.forEach((level, i) => {
        const levelEl = $.load("breadcrumb-level", "#breadcrumb-text")[0][0];
        levelEl.innerText = breadcrumbText[level];
        if (i < which.length - 1) levelEl.dataset.menu = which.toSpliced(i + 1)
      });
      $.queries({ "#breadcrumb-text > :nth-last-child(n+2)": { click () {
        app.emit("menu-select", this.dataset.menu.split(","))
      } } });
      let cancelEl, applyEl;
      switch (menuLeaf) {
        case "keyboard-settings":
          cancelEl = $.load("menu-action", "#menu-actions")[0][0];
          Object.assign(cancelEl, { innerText: "Cancel", id: "keyboard-settings-cancel" });
          applyEl = $.load("menu-action", "#menu-actions")[0][0];
          Object.assign(applyEl, { innerText: "Apply", id: "keyboard-settings-apply" });
          $.queries({
            "#keyboard-settings-cancel": { click () { app.emit("menu-cancel", { apply: false }) } },
            "#keyboard-settings-apply": { async click () {
              await Keyboard.applySettings();
              app.emit("generate-keyboard");
              app.emit("menu-cancel", { apply: true })
            } }
          });
          this.menuState[1] = { keyboard: this.keyboard };
          this.keyboard = new Keyboard(app.keyboards[Keyboard.selectEl.value]);
          await this.keyboard.fillSettings();
          this.emit("generate-keyboard");
          break;
        case "temperaments":
          cancelEl = $.load("menu-action", "#menu-actions")[0][0];
          Object.assign(cancelEl, { innerText: "Close", id: "temperaments-close" });
          $.queries({ "#temperaments-close": { click () { app.emit("menu-cancel") } } });
          $.all("#harmonic-filter > .harmonic-checkbox").forEach(el => el.remove());
          $.all("#commas > .comma").forEach(el => el.remove());
          $.all("#chords > .chord").forEach(el => el.remove());
          this.menuState[1] = { keyboard: this.keyboard };
          this.emit("resize", true);
          let { upperBound } = await this.storage.loadScale({ edo: this.keyboard.edo, limit: this.keyboard.scale.limit });
          $("#commas").dataset.upperBound = upperBound;
          await this.keyboard.scale.mapping.resetCommas(upperBound); //?
          this.emit("generate-temperaments");
          break;
        case "track-editor":
          $("#track-controls").classList.add("activeControls");
          $("#track-select > select").namedItem(data[0] ?? "New").selected = true;
          closeEl = $.load("menu-action", "#menu-actions")[0][0];
          Object.assign(closeEl, { innerText: "Close", id: "track-editor-close" });
          $.queries({ "#track-editor-close": {
            click () { app.emit("menu-cancel") }
          } });
          this.menuState[1] = { saveDebounce: null };
          this.emit("track-editor", ...data)
      }
    },
    
    async "menu-cancel" (data) {
      $("body").classList.remove("menuActive");
      $("menu > .activeMenu")?.classList.remove("activeMenu");
      $.all("#menu-actions > *").forEach(el => el.remove());
      switch(this.menuState[0]) {
        case "keyboard-settings":
          if (!data.apply) app.keyboard = app.menuState[1].keyboard;
          Keyboard.selectEl.value = app.keyboardSelection = app.keyboard.name;
          app.keyboard.fillSettings();
          break
        case "track-editor":
          $("#track-controls").classList.remove("activeControls");
          $("#track-select > select").selectedIndex = 0
      }
      this.menuState = [];
      this.emit("resize", true);
      this.keyboard.hexGrid.redraw(true)
    },

    "volume-change" (value) { this.masterVolume.gain.value = Common.scaleVolume(value) }

  }
}, self);



// Elements

$.queries({

  nav: { touchstart (e) { if ($.all(".non-focus").every(el => e.target !== el)) this.focus() } },
  form: { submit (e) { e.preventDefault() } },
  "#volume > input": { change () { app.emit("volume-change", this.valueAsNumber) } },
  "#octaves > input": { change () {
    app.storage.saveItem("octaves", app.octaves = this.valueAsNumber);
    app.emit("resize", true);
    app.keyboard.hexGrid.redraw(true)
  } },
  "#refresh": { click () {
    app.emit("resize", true);
    app.keyboard.refresh()
  } },
  "#panic": { click () { app.emit("panic") } },
  "#fullscreen": { click () { app.emit("fullscreen") } },
  "#reset": { click () { $("#reset-dialog").showModal() } },
  "#reset-dialog button": { click () {
    $("#reset-dialog").close();
    if (this.dataset.action === "Cancel") return;
    app.emit("clear-storage");
    location.reload()
  } },

  "#keyboard-settings-button": { click () {
    if (app.menuState[0] === "keyboard-settings") app.emit("menu-cancel"); 
    else app.emit("menu-select", [ "keyboard-settings" ])
  } },
  "#keyboard-settings": {
    scroll ({ SCROLL_PAGE_DOWN }) {  // TODO: Allow simultaneous x and y scrolling
      if (!$("#table-choice > input").checked) return;
      const
        { scrollTop } = this, el = $("#ivtable-wrapper"), { scrollLeft } = el,
        { offsetTop, offsetHeight } = $("#interval-view"), { clientHeight } = $("#keyboard-settings"),
        { offsetTop: y, offsetLeft: x, offsetHeight: height } = $("#keyboard-settings > form"),
        offset = offsetTop + offsetHeight - y + x;
      if (Common.between(offset, height - clientHeight + 2 * x, scrollTop)) el.scrollTo(scrollLeft, scrollTop - offset);
      else if (scrollTop < offset) el.scrollTo(scrollLeft, 0);
      else el.scrollTo(scrollLeft, SCROLL_PAGE_DOWN)
    }
  },
  "#keyboard-select > select": { change () { app.emit("keyboard-select", this.value) } },
  "#keyboard-name-text": { click () {
    $("#keyboard-name").classList.add("editing");
    $("#keyboard-name-field").focus()
  } },
  "#keyboard-name-field": { "keyup blur" (e) {
    if (e.type === "blur" || e.key === "Enter") app.emit("keyboard-name-update", this.value = this.value.trim())
  } },
  "#keyboard-create": { click () { app.emit("keyboard-create") } },
  "#keyboard-delete": { click () {
    $("#delete-keyboard-name").innerText = app.keyboardSelection;
    $("#delete-keyboard-dialog").showModal()
  } },
  "#delete-keyboard-dialog button": { click () { app.emit("keyboard-delete", this.dataset.action) } },
  ":is(#gstep, #hstep) > input": { change () {
    const { keyboard } = app, { orientationSelectEl } = Keyboard;
    keyboard.updateShape();
    if (orientationSelectEl.children.length) {
      app.emit("resize", true);
      keyboard.hexGrid.redraw(true);
      orientationSelectEl.showPicker();
    }
  } },
  "#orientation > select": { change () {
    const { hexGrid } = app.keyboard;
    hexGrid.orientation = JSON.parse(`[${this.value}]`);
    app.emit("resize", true);
    hexGrid.redraw(true);
    this.focus()
  } },
  "#unit > input": { change () {
    const { hexGrid } = app.keyboard;
    hexGrid.unit = this.valueAsNumber;
    app.emit("resize", true);
    hexGrid.redraw(true)
  } },
  ":is(#limit, #maxError) > input": { change () { app.emit("generate-keyboard") } },
  "#edo > input": { change () {
    const
      { refNoteEl, maxErrorEl, scaleOutputEl } = Keyboard,
      edo = this.valueAsNumber;
    refNoteEl.value = Math.round(Math.log2(5 / 3) * edo); // C-A = 5/3
    scaleOutputEl.value = `One step of ${edo}edo = ${(1200 / edo).toFixed(2)}¢`;
    maxErrorEl.value = Math.floor(400 / edo);
    app.keyboard.updateShape();
    app.emit("generate-keyboard");
    this.focus()
  } },
  "#hexbutton-labels input": { change () {
    const { hexGrid } = app.keyboard;
    hexGrid.displayKeyNames = this.closest("label").id === "key-name-choice";
    hexGrid.redraw(true)
  } },

  "#temperament-list": { change () { app.emit("update-temperament-filter") } },

  "#generate-temperaments": { click () { app.emit("menu-select", [ "temperaments" ]) } },

  "#clipboard-item-select": {
    "dragenter dragover" (e) {
      e.preventDefault();
      this.classList.add("active")
    },
    dragleave (e) { this.classList.remove("active") },
    drop (e) {
      e.stopPropagation();
      this.classList.remove("active");
      const text = e.dataTransfer.getData('text/plain');
      if (text !== "self") app.emit("copy", { text });
      $("nav").focus();
      $("body").classList.remove("copying")
    },
    dragstart (e) { e.dataTransfer.setData("text/plain", "self") },
    dragend ({ x, y }) {
      if (!document.elementsFromPoint(x, y).includes(this)) app.emit("uncopy")
    }
  },
  "#clipboard-peek": {
    ...((x, prevX, y, threshhold, phase) => ({
      pointerdown ({ pointerId, ctrlKey, pageX, pageY }) {
        this.setPointerCapture(pointerId);
        if (!this.firstChild) return;
        if (ctrlKey) return app.emit("uncopy");
        const
          { height } = this.getBoundingClientRect(),
          { clipboard, clipboardPeekIndex } = app.keyboard,
          data = clipboard[clipboardPeekIndex];
        x = pageX;
        y = pageY;
        threshhold = height;
        phase = 0;
        data.start(pointerId)
      },
      pointermove ({ clientX, pageX, pageY, pointerId }) {
        if (this.children.length === 0) return;
        const { keyboard } = app, { clipboard, clipboardPeekIndex } = keyboard;
        if (phase === 0 && Math.hypot(pageX - x, pageY - y) > threshhold) {
          phase = 1 + (Math.abs(pageX - x) < Math.abs(pageY - y));
          prevX = pageX;
          if (Math.abs(pageX - x) < Math.abs(pageY - y)) {
            clipboard[clipboardPeekIndex].stop(pointerId);
            app.emit("uncopy")
          }
        } else if (phase === 1) {
          keyboard.cycle("clipboard", (-prevX + (prevX = pageX)) * 4);
          if (keyboard.clipboardPeekIndex !== clipboardPeekIndex) {
            clipboard[clipboardPeekIndex].stop(pointerId);
            clipboard[keyboard.clipboardPeekIndex].start(pointerId)
          }
        }
      },
      "pointerup lostpointercapture" ({ type, pointerId }) {
        if (type === "pointerup" && !this.hasPointerCapture(pointerId)) return;
        const { clipboard, clipboardPeekIndex } = app.keyboard;
        clipboard[clipboardPeekIndex]?.stop(pointerId);
        this.releasePointerCapture(pointerId)
      }
    }))()
  },

  "#track-select > select": { change () {
    if (this.value === "None") app.emit("menu-cancel");
    else app.emit("menu-select", [ "track-editor" ], ...(this.value === "New" ? [] : [ this.value ]))
  } },
  "#track-name-text": { click () {
    $("#track-name").classList.add("editing");
    $("#track-name-field").focus()
  } },
  "#track-name-field": { "keyup blur" (e) {
    if (e.type === "blur" || e.key === "Enter") app.emit("track-name-update", this.value = this.value.trim())
  } },
  "#track-delete": { click () {
    $("#delete-track-name").innerText = app.trackSelection;
    $("#delete-track-dialog").showModal()
  } },
  "#delete-track-dialog button": { click () { app.emit("track-delete", this.dataset.action) } },
  "#track-edit": { keyup () { if (this.value !== app.tracks[app.trackSelection]) app.emit("track-save") } },
  "#toggle-accidentals": { click () { $("#insert-accidental").classList.toggle("activeSelect") } },
  "#insert-accidental > *": { click () {
    const { value } = $("#track-edit"), editorEl = $("#track-edit"), selStart = editorEl.selectionStart;
    $("#track-edit").value = value.slice(0, selStart) + this.innerText + value.slice(editorEl.selectionEnd)
    if ($("#track-edit").value !== app.tracks[app.trackSelection]) app.emit("track-save")
    editorEl.setSelectionRange(selStart + 1, selStart + 1);
    editorEl.focus()
  } }

});



export { app }