import $ from "./machine.js";
import Common from "./common.js";
import { app } from "./main.js";
import { HarmonicMapping } from "./mapping.js";
import { HexGrid } from "./grid.js"



// Keyboard

class Keyboard {

  // Static
  static presets = [ {
    name: "12edo", gstep: 2, hstep: 1, orientation: [5, 2], unit: 45, refNote: 9, freqBasis: 220,
    edo: 12, limit: 9, maxError: 33, hmap: [[3, 7], [5, 4], [7, 10], [9, 2]], instrument: "triangle"
  }, {
    name: "19edo", gstep: 3, hstep: 2, orientation: [5, 2], unit: 45, refNote: 14, freqBasis: 220,
    edo: 19, limit: 9, maxError: 22, hmap: [[3, 11], [5, 6], [7, 15], [9, 3]], instrument: "triangle"
  }, {
    name: "22edo", gstep: 4, hstep: 1, orientation: [5, 2], unit: 45, refNote: 16, freqBasis: 220,
    edo: 22, limit: 11, maxError: 18, hmap: [[3, 13], [5, 7], [7, 18], [9, 4], [11, 10]], instrument: "triangle"
  }, {
    name: "31edo", gstep: 5, hstep: 3, orientation: [5, 2], unit: 45, refNote: 23, freqBasis: 220,
    edo: 31, limit: 11, maxError: 12, hmap: [[3, 18], [5, 10], [7, 25], [9, 5], [11, 14]], instrument: "triangle"
  }, {
    name: "41edo", gstep: 7, hstep: 3, orientation: [5, 2], unit: 45, refNote: 30, freqBasis: 220,
    edo: 41, limit: 15, maxError: 9, hmap: [[3, 24], [5, 13], [7, 33], [9, 7], [11, 19], [13, 29], [15, 37]], instrument: "triangle"
  }, {
    name: "53edo", gstep: 5, hstep: 4, orientation: [5, 7], unit: 45, refNote: 39, freqBasis: 220,
    edo: 53, limit: 15, maxError: 8, hmap: [[3, 31], [5, 17], [7, 43], [9, 9], [11, 24], [13, 37], [15, 48]], instrument: "triangle"
  }, {
    name: "94edo", gstep: 9, hstep: 7, orientation: [5, 7], unit: 45, refNote: 69, freqBasis: 220,
    edo: 94, limit: 21, maxError: 4, hmap: [[3, 55], [5, 30], [7, 76], [9, 16], [11, 43], [13, 66], [15, 85], [17, 8], [19, 23], [21, 37]], instrument: "triangle"
  } ]

  static noteColours = {
    default: "#333333", active: "#ffff00", echo: "#ffffff22",
    white: "#222222", black: "#777777",
    5: "#ff0000", 7: "#0000ff", 11: "#00ff00", 13: "#ff00ff", 17: "#ffff00"
  }

  static selectEl; static edoInfoEl; static limitInfoEl; static displayKeyNamesEl
  static nameFieldEl; static nameTextEl
  static gstepEl; static hstepEl; static orientationSelectEl; static unitEl
  static refNoteEl; static freqBasisEl; static edoEl; static limitEl; static maxErrorEl
  static scaleOutputEl; static clipboardPeekEl
  static attach ({
    selectEl, edoInfoEl, limitInfoEl, displayKeyNamesEl, nameFieldEl, nameTextEl,
    gstepEl, hstepEl, orientationSelectEl, unitEl, refNoteEl, freqBasisEl,
    edoEl, limitEl, maxErrorEl, scaleOutputEl, clipboardPeekEl
  }) { Object.assign(this, {
    selectEl, edoInfoEl, limitInfoEl, displayKeyNamesEl, nameFieldEl, nameTextEl,
    gstepEl, hstepEl, orientationSelectEl, unitEl, refNoteEl, freqBasisEl,
    edoEl, limitEl, maxErrorEl, scaleOutputEl, clipboardPeekEl
  }) }

  static async applySettings () {
    const keyboardObj = {
      name: Keyboard.nameFieldEl.value,
      orientation: Keyboard.orientationSelectEl.value.split(",").map(v => parseInt(v)),
      displayKeyNames: $("#hexbutton-labels input:checked").parentElement.id === "key-name-choice",
      clipboard: app.keyboard.clipboard.slice()
    };
    [ "gstep", "hstep", "unit", "refNote", "freqBasis", "edo", "limit", "maxError" ]
      .forEach(dataname => keyboardObj[dataname] = Keyboard[dataname + "El"].valueAsNumber);
    Keyboard.edoInfoEl.innerText = keyboardObj.edo;
    Keyboard.limitInfoEl.innerText = keyboardObj.limit;
    const keyboard = app.keyboard = new Keyboard(keyboardObj);
    await keyboard.save()
  }

  static setColour (harm, colour, isBlackKeys) {
    if (harm === 3) Keyboard.noteColours[isBlackKeys ? "black" : "white"] = colour;
    else Keyboard.noteColours[harm] = colour;
    app.storage.saveItem("noteColours", JSON.stringify(Keyboard.noteColours));
    app.keyboard.hexGrid.redraw()
  }

  static ready = false
  static #userResolver
  static userIsActive = new Promise(r => this.#userResolver = r);
  static userActivate () { this.#userResolver() }

  // Instance
  name; edo; hexGrid; scale; instrument = "triangle"
  touches = new Map(); mousedown = false
  hoveredKey; wheelVal = 0; wheelSensitivity = 200
  clipboard; clipboardPeekIndex; clipboardHolding
  root = 0 // TODO: load/save
  constructor ({
    name, edo,
    gstep, hstep, unit, orientation, displayKeyNames,
    limit, refNote, freqBasis, maxError,
    clipboard = []
    // instrument
  }) {
    // TODO: validation helper?
    if (typeof name !== "string" || name === "" || name.length > app.maxKeyboardNameLength) throw new Error("Keyboard error: bad name");
    if (typeof edo !== "number" || edo < 0 || edo > app.maxEdo || edo % 1) throw new Error("Keyboard error: bad EDO");
    this.name = name;
    this.edo = edo;
    this.hexGrid = new HexGrid({ keyboard: this, gstep, hstep, unit, orientation, displayKeyNames });
    this.scale = new Scale({ keyboard: this, limit, refNote, freqBasis, maxError });
    this.clipboard = clipboard
  }

  async save () {
    const
      { name, edo, hexGrid, scale, clipboard } = this,
      { gstep, hstep, unit, orientation, displayKeyNames } = hexGrid,
      { limit, refNote, freqBasis, maxError } = scale,
      keyboard = {
        name, edo, gstep, hstep, unit, orientation, displayKeyNames,
        limit, refNote, freqBasis, maxError,
        clipboard: clipboard.map(({ text }) => ({ text }))
      };
    Object.assign(app.keyboards[app.keyboardSelection], keyboard)
    await app.storage.saveKeyboard(keyboard);
  }

  async fillSettings () {
    const
      { gstepEl, hstepEl, orientationSelectEl, unitEl, refNoteEl, freqBasisEl,
        edoEl, limitEl, maxErrorEl, displayKeyNamesEl, scaleOutputEl,
        edoInfoEl, limitInfoEl, nameFieldEl, nameTextEl } = Keyboard,
      { name, edo, hexGrid, scale } = this,
      { gstep, hstep, unit, orientation, orientations, displayKeyNames } = hexGrid,
      { limit, refNote, freqBasis, maxError } = scale,
      { upperBound } = await app.storage.loadScale({ edo, limit });
    $("#commas").dataset.upperBound = upperBound;
    nameFieldEl.value = name;
    nameFieldEl.classList.remove("invalid");
    nameTextEl.innerText = name;
    nameTextEl.parentElement.classList.remove("editing");
    gstepEl.value = gstep;
    hstepEl.value = hstep;
    $.all(":scope > *", orientationSelectEl).forEach(el => el.remove());
    orientations.forEach(coord => {
      const el = $.load("option", "", orientationSelectEl)[0][0];
      el.innerText = coord;
      el.setAttribute("name", coord)
    });
    orientationSelectEl.options.namedItem(orientation.join(",")).selected = true;
    unitEl.value = unit;
    refNoteEl.value = refNote;
    freqBasisEl.value = freqBasis;
    edoEl.value = edo;
    limitEl.value = limit;
    maxErrorEl.value = maxError;
    $(`#key-${displayKeyNames ? "name" : "rank"}-choice > input`, displayKeyNamesEl).checked = true;
    scaleOutputEl.value = `One step of ${edo}EDO = ${(1200 / edo).toFixed(2)}¢`;
    $.all("#clipboard-peek > *").forEach(el => el.remove());
    edoInfoEl.innerText = edo;
    limitInfoEl.innerText = limit;
  }

  updateShape () { // Soft update while settings is open
    // TODO edo and limit info hinting?
    const
      { orientationSelectEl, gstepEl, hstepEl, edoEl } = Keyboard,
      { hexGrid } = this,
      gstep = gstepEl.valueAsNumber,
      hstep = hstepEl.valueAsNumber,
      edo = edoEl.valueAsNumber,
      applyButton = $("#keyboard-settings-apply");
    $.all(":scope > *", orientationSelectEl).forEach(el => el.remove());
    if (Common.gcd(gstep, hstep) !== 1) return applyButton.disabled = true;
    this.edo = edo;
    applyButton.disabled = false;
    if (!hexGrid.setLattice({ gstep, hstep })) return applyButton.disabled = true;
    hexGrid.orientations.forEach(coord => {
      const el = $.load("option", "", orientationSelectEl)[0][0];
      el.innerText = coord;
      el.setAttribute("name", coord)
    })
    orientationSelectEl.namedItem(hexGrid.orientation).selected = true
  }

  play (g, h, id) { // Convert g, h to hex?
    const
      { hexGrid, scale, touches } = this, rank = hexGrid.coordToRank(g, h), octave = hexGrid.coordToOctave(g, h),
      note = scale.getNote({ octave, rank }) ?? scale.addNote({ rank, octave }),
      key  = scale.getKey(rank), hex = hexGrid.getHex(g, h), hexes = hex ? [hex] : key.hexes;
    let flag = true;
    const to = setTimeout(() => {
      hexes.forEach(h => hexGrid.addToActiveClass(hex ? "active" : "echo", h, id));
      hexGrid.colour();
      note.turnOn(id);
      flag = false;
    }, 0);
    touches.set(id, { hexes, note, to, cb: () => flag });
  }

  stop (id) {
    const { hexGrid, touches } = this, touch = touches.get(id);
    if (!touch) return;
    if (touch.cb()) return clearTimeout(touch.to);
    touch.hexes.forEach(hex => hexGrid.removeFromActiveClasses(hex, id)); // remove from single class?
    hexGrid.colour();
    touch.note.turnOff(id);
    touches.delete(id);
  }

  changeKey (note) {}

  cycle (which, delta) {
    const { wheelSensitivity } = this;
    if (Common.between(0, wheelSensitivity, this.wheelVal += delta)) return;
    const { wheelVal } = this;
    this.wheelVal = Common.mod(wheelVal, wheelSensitivity);
    switch (which) {
      case "label":
        const { hoveredKey } = this;
        hoveredKey.label = Common.mod(Math.floor(wheelVal / wheelSensitivity) + hoveredKey.labelIndex, hoveredKey.labels.length);
        app.emit("resize", true);
        this.hexGrid.redraw();
        break
      case "clipboard":
        const { clipboard, clipboardPeekIndex } = this;
        this.clipboardPeekIndex = Common.mod(Math.floor(wheelVal / wheelSensitivity) + clipboardPeekIndex, clipboard.length);
        app.emit("clipboard-display-peek")
    }
  }

  refresh () {
    this.touches = new Map();
    this.scale.refresh();
    this.hexGrid.clearActiveClasses();
    this.hexGrid.redraw(true)
  }

}



// Musical aspect of keyboard

class Scale {
  #keyboard; limit
  mapping; refNote; freqBasis; maxError
  #keys = new Map() // Map([ rank, key ])
  #active = new Map() // Map([ note, Set(id) ])
  constructor ({ keyboard, limit, refNote, freqBasis, maxError }) {
    if (!(Keyboard.prototype.isPrototypeOf(keyboard))) throw new Error("Scale error: must provide Keyboard object");
    this.#keyboard = keyboard;
    const { edo } = keyboard;
    if (typeof limit !== "number" || limit < 3 || limit > app.maxHarmonic || limit % 2 !== 1) throw new Error("Scale error: bad harmonic limit");
    if (typeof refNote !== "number" || refNote < 0 || refNote >= edo || refNote % 1) throw new Error("Scale error: bad reference note");
    if (typeof freqBasis !== "number" || freqBasis < 10 || freqBasis > 4e4) throw new Error("Scale error: bad reference frequency");
    if (typeof maxError !== "number" || freqBasis < 0 || freqBasis > 1200) throw new Error("Scale error: bad max pitch variation");
    this.limit = limit;
    this.maxError = maxError;
    this.refNote = refNote;
    this.mapping = new HarmonicMapping({ keyboard, scale: this, hmap: this.#genRawHMap({ edo, limit, maxError }) });
    this.freqBasis = freqBasis;

    for (let i = 0; i < edo; i++) this.#keys.set(i, new Key({ keyboard, scale: this, rank: i }))
  }
  * [ Symbol.iterator ] () { for (const s of this.#keys.values()) yield s }
  #genRawHMap ({ edo, limit, maxError }) {
    let hmap = new Map();
    for (let i = 3; i <= limit; i += 2) {
      const
        just = Math.log2(i) % 1,
        maybeSteps = Math.round(just * edo),
        error = (maybeSteps / edo - just) * 1200;
      if (Math.abs(error) < maxError && maybeSteps + edo * maxError / 1200 >= 1 &&
        maybeSteps - edo * maxError / 1200 < edo) hmap.set(i, maybeSteps)
    }
    return hmap
  }

  getKey (rank) { return this.#keys.get(rank) }
  addNote ({ rank, octave }) { return this.#keys.get(rank).addNote(octave) }
  getNote ({ rank, octave }) { return this.#keys.get(rank)?.getNote(octave) }
  play (note, id) {
    const active = this.#active, ids = active.get(note);
    if (ids) ids.add(id);
    else {
      active.set(note, new Set([id]))
      note.start();
    } 
  }
  stop (note, id) {
    const active = this.#active, ids = active.get(note);
    if (!ids) return;
    ids.delete(id);
    if (ids.size === 0) {
      note.stop();
      active.delete(note)
    }
  }
  refresh () { this.#active = new Map() }
}



class Key {
  #keyboard; #scale; #notes = new Map(); #labels = []; #labelIndex = 0; #home; rank
  hexes = new Set()
  constructor ({ keyboard, scale, rank }) {
    if (!(Keyboard.prototype.isPrototypeOf(keyboard))) throw new Error("Key error: must provide Keyboard object");
    this.#keyboard = keyboard;
    if (!(Scale.prototype.isPrototypeOf(scale))) throw new Error("Key error: must provide Scale object");
    this.#scale = scale;
    this.rank = rank
  }
  addNote (octave) {
    const note = new Note({ keyboard: this.#keyboard, scale: this.#scale, rank: this.rank, octave });
    this.#notes.set(octave, note);
    return note
  }
  getNote (octave) { return this.#notes.get(octave) }
  get notes () { return [ ...this.#notes.values() ] }
  get labels () { return this.#labels.slice() }
  get label () { return this.#labels[this.#labelIndex] ?? this.rank }
  get labelIndex () { return this.#labelIndex }
  set labels (labels) { this.#labels = labels }
  set label (i) { this.#notes.forEach(note => {
    if (Common.between(0, this.#labels.length - 1, i)) this.#labelIndex = i
  }) }
  set home (hex) { this.#home = hex }
  get home () { return this.#home }
}



class Note {
  #keyboard; #scale; rank; octave
  #maxVolume = .333; #attack = .2; #decay = .5
  #note
  constructor ({ keyboard, scale, rank, octave }) {
    if (!(Keyboard.prototype.isPrototypeOf(keyboard))) throw new Error("HexGrid error: must provide Keyboard object");
    if (!Scale.prototype.isPrototypeOf(scale)) throw new Error("Note error: must provide Scale object");
    const existing = scale.getNote({ rank, octave })
    if (existing) return existing;
    this.#keyboard = keyboard;
    this.#scale = scale;
    this.rank = rank;
    this.octave = octave
  }
  get key () { return this.#scale.getKey(this.rank) }
  async start () {
    if (this.#note) return;
    await Keyboard.userIsActive;
    const
      { audioctx, masterVolume } = app,
      { rank, octave } = this, { freqBasis, refNote } = this.#scale, { edo } = this.#keyboard,
      osc = audioctx.createOscillator(),
      volume = audioctx.createGain(),
      now = audioctx.currentTime;
    osc.type = "triangle";
    osc.frequency.value = freqBasis * 2 ** (octave + ((refNote + rank) / edo));
    osc.connect(volume);
    volume.gain.value = .001;
    volume.gain.setValueAtTime(.001, now);
    volume.gain.setTargetAtTime(this.#maxVolume, now, this.#attack / 5);
    volume.connect(masterVolume);
    this.#note = { osc, volume, t0: now };
    osc.start(now);
  }
  async stop () {
    await Keyboard.userIsActive;
    if (!this.#note) return;
    const
      { audioctx } = app, now = audioctx.currentTime,
      { osc, volume, t0 } = this.#note, dt = now - t0, decay = this.#decay;
    this.#note = null;
    volume.gain.cancelScheduledValues(now);
    volume.gain.setTargetAtTime(.001, now, decay / 5);
    osc.stop(now + decay);
  }

  turnOn (id) { this.#scale.play(this, id) }
  turnOff (id) { this.#scale.stop(this, id) }
}



export { Keyboard, Scale, Key, Note }