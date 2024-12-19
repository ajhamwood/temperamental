import $ from "./machine.js";
import { Keyboard } from "./keyboard.js";



// Local data

class Persist {
  static reset () {
    localStorage.clear();
    return new Promise((success, error) => $.targets({ success, error }, indexedDB.deleteDatabase("userdata")))
  }
  static #txWait = tx => new Promise((complete, error) => $.targets({ complete, error }, tx));
  static #schemaTxWait = (vn, runTx = () => {}, blocked = () => {}) => new Promise((success, error) => {
    $.targets({ success, error, async upgradeneeded (evt) { try {
      await runTx(evt); success(evt)
    } catch (err) { error(err) } }, blocked (e) { blocked(e, success, error) } }, indexedDB.open("userdata", vn))
  })
  static #runSchemaTxs = async (vn, fns) => (await Promise.all(fns.map(async (fn, i) => {
    const db = (await Persist.#schemaTxWait(vn + i + 1, fn)).target.result;
    if (i < fns.length - 1) db.close();
    else return db
  }))).at(-1)
  static async * #cursorWait (index) {
    let r, p = new Promise(res => r = res), csr;
    $.targets({ success (e) { r(e.target.result); p = new Promise(res => r = res) } }, index);
    while (csr = await p) { const { value } = csr; yield value; csr.continue() }
  }
   
  static async #upgradeFromVersion0 (vn) {
    return await Persist.#runSchemaTxs(vn, [
      // Initialise keyboards
      async evt => {
        const
          createKbStore = evt.target.result.createObjectStore("keyboards", { keyPath: "name" }),
          createKbTx = Persist.#txWait(createKbStore.transaction);
        await createKbTx; // mode: versionchange
        const
          kbStore = evt.target.result.transaction("keyboards", "readwrite").objectStore("keyboards"),
          seedKbTx = Persist.#txWait(kbStore.transaction);
        Keyboard.presets.forEach(obj => kbStore.add(obj));
        await seedKbTx; // mode: readwrite
      },

      // Create scale store
      async evt => {
        const
          createScaleStore = evt.target.result.createObjectStore("scales", { keyPath: ["edo", "limit"] }), // maxError?
          createScalesTx = Persist.#txWait(createScaleStore.transaction);
        await createScalesTx;
      },

      // Create comma store
      async evt => {
        const
          createCommaStore = evt.target.result.createObjectStore("commas", { keyPath: ["edo", "limit", "ln", "ld"] }),
          createCommasTx = Persist.#txWait(createCommaStore.transaction);
        createCommaStore.createIndex("commas", ["edo", "limit"]);
        await createCommasTx;
      },

      // Create chord store
      async evt => {  
        const
          createChordStore = evt.target.result.createObjectStore("chords", { keyPath: ["edo", "limit", "ln", "ld", "ord"] }),
          createChordsTx = Persist.#txWait(createChordStore.transaction);
        createChordStore.createIndex("chords", ["edo", "limit", "ln", "ld"]);
        await createChordsTx
      },

      // Create track store
      async evt => {
        const
          createTrackStore = evt.target.result.createObjectStore("tracks", { keyPath: "name" }),
          createTracksTx = Persist.#txWait(createTrackStore.transaction);
        await createTracksTx
      }

      // TODO: comma and chord: ln, ld => decomp + BigInt n, d
    ])
  }

  #db; #resolveReady; #rejectReady
  #promiseReady = new Promise((res, rej) => [ this.#resolveReady, this.#rejectReady ] = [ res, rej ]);
  get ready () { return this.#promiseReady }
  set ready (_) { return false }
  constructor (version) { this.#init(version) }
  async #init (version) {
    const
      dbv = parseInt(this.loadItem("version") ??
        version.match(/^(\d{1,3})\.(\d{1,3})\.(\d{1,3})/)?.slice(1)
          .reduce((n, s, i) => n + parseInt(s) * 100 ** (3 - i), 0)),
      oldVersion = (await indexedDB.databases()).find(({ name }) => name === "userdata")?.version ?? 0;
    try {
      if (oldVersion < 304) this.#db = await Persist.#upgradeFromVersion0(dbv);
      else this.#db = (await Persist.#schemaTxWait(dbv)).target.result;
      this.saveItem("version", this.#db.version)
      this.#resolveReady()
    } catch (e) { this.#rejectReady(e) }
  }

  loadItem (key, initial) {
    let value = localStorage.getItem(key);
    if (value === null) localStorage.setItem(key, value = initial);
    return value
  }
  saveItem (key, val) { localStorage.setItem(key, val) }

  // Keyboards
  async loadKeyboards () {
    const
      kbStore = this.#db.transaction("keyboards").objectStore("keyboards"),
      readKbTx = Persist.#txWait(kbStore.transaction), req = kbStore.getAll();
    await readKbTx;
    return req.result
  }
  async saveKeyboard (keyboard) {
    const
      kbStore = this.#db.transaction("keyboards", "readwrite").objectStore("keyboards"),
      saveKbTx = Persist.#txWait(kbStore.transaction), req = kbStore.put(keyboard);
    await saveKbTx
  }
  async deleteKeyboard (name) {
    const
      kbStore = this.#db.transaction("keyboards", "readwrite").objectStore("keyboards"),
      delKbTx = Persist.#txWait(kbStore.transaction), reqR = kbStore.delete(name);
    await delKbTx;
  }
  resetPresetKeyboards () {} //

  // Scales

  async loadScale ({ edo, limit }) {
    const
      scaleStore = this.#db.transaction("scales").objectStore("scales"),
      readScaleTx = Persist.#txWait(scaleStore.transaction), req = scaleStore.get([ edo, limit ]);
    await readScaleTx;
    if (req.result !== undefined) return req.result;
    const initial = { edo, limit, upperBound: 0n };
    await this.saveScale(initial);
    return initial
  }
  async saveScale (scale) {
    const
      scaleStore = this.#db.transaction("scales", "readwrite").objectStore("scales"),
      saveScaleTx = Persist.#txWait(scaleStore.transaction), req = scaleStore.put(scale);
    await saveScaleTx
  }

  // Commas
  async * yieldCommas ({ edo, limit }) {
    const
      commaStore = this.#db.transaction("commas").objectStore("commas"),
      csr = commaStore.index("commas").openCursor(IDBKeyRange.only([ edo, limit ])),
      yieldCommaCsr = Persist.#cursorWait(csr);
    for await (const value of yieldCommaCsr) yield value
  }
  async saveComma (comma) {
    const
      commaStore = this.#db.transaction("commas", "readwrite").objectStore("commas"),
      saveCommaTx = Persist.#txWait(commaStore.transaction), req = commaStore.put(comma);
    await saveCommaTx
  }

  // Chords
  async * yieldChords ({ edo, limit, ln, ld }) {
    const
      chordStore = this.#db.transaction("chords").objectStore("chords"),
      csr = chordStore.index("chords").openCursor(IDBKeyRange.only([ edo, limit, ln, ld ])),
      yieldChordCsr = Persist.#cursorWait(csr);
    for await (const value of yieldChordCsr) yield value
  }
  async saveChord (chord) {
    const
      chordStore = this.#db.transaction("chords", "readwrite").objectStore("chords"),
      saveChordTx = Persist.#txWait(chordStore.transaction), req = chordStore.put(chord);
    await saveChordTx
  }

  // Tracks
  async loadTracks () {
    const
      kbStore = this.#db.transaction("tracks").objectStore("tracks"),
      readKbTx = Persist.#txWait(kbStore.transaction), req = kbStore.getAll();
    await readKbTx;
    return req.result
  }
  async saveTrack (track) {
    const
      kbStore = this.#db.transaction("tracks", "readwrite").objectStore("tracks"),
      saveKbTx = Persist.#txWait(kbStore.transaction), req = kbStore.put(track);
    await saveKbTx
  }
  async deleteTrack (name) {
    const
      kbStore = this.#db.transaction("tracks", "readwrite").objectStore("tracks"),
      delKbTx = Persist.#txWait(kbStore.transaction), reqR = kbStore.delete(name);
    await delKbTx;
  }
}




export default Persist