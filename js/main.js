import $ from "./machine.js";
import Common from "./common.js";
import { HarmonicLattice, IntervalSet, Interval } from "./interval.js";



// Harmonic mapping

class HarmonicMapping {

  // Static
  static #isPrime (pdec) {
    let sum = 0;
    for (let [, rad] of pdec) sum += rad;
    return sum === 1
  }
  static #transp = mat => Array(mat[0].length).fill()
    .reduce((row, _, i) => row.concat([mat.reduce((cols, row) =>
      cols.concat([row[i]]), [])]), [])

  static #invDet (mat, decs, ps) { // TODO: use leading value
    const
      rows = mat.length, cols = mat[0].length,
      aug = mat.map((row, i) => row.concat(Array(rows).fill(0).with(i, 1)));
    if (mat.length === 0) return null;
    let det = 1, lcm = 1;
    for (let i = 0; i < rows; i++) {
      if (aug[i][i] === 0) {
        let m = 0;
        for (m = i + 1; m < rows; m++) if (aug[m][i] !== 0) {
          ([ aug[m], aug[i], decs[m], decs[i] ] = [ aug[i], aug[m], decs[i], decs[m] ]);
          for (let j = 0; j < rows; j++)
            ([ aug[j][cols + m], aug[j][cols + i] ] = [ aug[j][cols + i], aug[j][cols + m] ]);
          det = -det;
          break
        }
        if (m === rows) return {}
      }
      const val0 = aug[i][i];
      lcm = val0 / Common.gcd(lcm, val0);
      for (let j = 0; j < rows; j++) if (i !== j) {
        const val1 = aug[j][i], c = Common.gcd(val0, val1);
        if (i < ps.length) det *= val0 / c;
        for (let k = 0; k < rows + cols; k++)
          aug[j][k] = (val0 * aug[j][k] - val1 * aug[i][k]) / c;
      }
    }
    mat = this.#transp(aug);
    det = mat.slice(0, ps.length).reduce((acc, row, i) => acc * row[i], 1) / det
    const degen = aug.findIndex(row => !row.slice(0, cols).some(x => x));
    if (~degen) aug.splice(degen);
    return {
      det, lcm,
      mods: aug.slice(0, ps.length).map((row, i) => [ ps[i], lcm / row[i] ]),
      inv: mat.slice(cols, cols + ps.length).map((row, i) => [ decs[i][0], row ]),
      verify: mat.slice(aug.length, cols).map((vec, i) => [ ps[aug.length + i], vec ])
    }
  }

  static * #subsets (args, { minlength = 1, maxlength = args.length } = {}) {
    for (let n = minlength; n <= maxlength; n++) {
      let max = -1, counter = [];
      while (max + n <= args.length) {
        if (~max) yield counter.map(k => args[k]);
        const i = counter.findLastIndex((j, k) => j < max + k);
        if (~i) counter[i]++;
        else counter = Array(n).fill().map((_, j) => j).with(-1, n + max++);
      }
    }
  }

  // Instance
  #keyboard; #scale
  rawHarmonicList; harmonicList = new Map()
  nonHarmonics = new Set() // TODO: Cached blacklist
  indexPrimes = []; primes = []; params = []; index = []; verify = () => true; stepsBasis
  #properIntervalSet; intervalSet
  ready = false
  #temperaments = new Map(); #temperament
  filterLattice

  constructor ({ keyboard, scale, hmap }) { // Map([ odd, number ])
    if (!(Keyboard.prototype.isPrototypeOf(keyboard))) throw new Error("Mapping error: must provide Keyboard object");
    this.#keyboard = keyboard;
    if (!(Scale.prototype.isPrototypeOf(scale))) throw new Error("Mapping error: must provide Scale object");
    this.#scale = scale;
    const { edo } = keyboard, { maxError, limit } = scale;
    if (!Map.prototype.isPrototypeOf(hmap) || [ ...hmap ].some(v => v.some(u => typeof u !== "number") ||
      v.some(u => u % 1) || v[0] < 3 || v[0] > app.maxHarmonic || v[0] % 2 !== 1 || v[1] < 0 || v[1] > edo)) throw new Error("Mapping error: bad interval-step mapping");
    const harr = [ ...hmap ];

    // Generate steps
    const stepsBasis = new Map(hmap);
    if (this.index.some(h => {  // BUG this.index requires residue not empty
      const s = hmap.get(h);
      return s === undefined || s < 0 || s % 1
    })) throw new Error("Could not set steps for mapping");
    for (let [h, steps] of hmap) stepsBasis.set(h, steps + edo * Math.floor(Math.log2(h)));
    this.stepsBasis = stepsBasis;

    this.#properIntervalSet = new IntervalSet({ edo, stepsBasis });
    this.intervalSet = new IntervalSet({ edo, stepsBasis });

    const
      decs = Common.decomp(...harr.map(([h]) => h)).map((pdec, i) => [ harr[i][0], pdec ]),
      { true: primeDecs = [], false: compositeDecs = [] } = Common.groupBy(
        decs, ([, a]) => HarmonicMapping.#isPrime(a)),
      { true: simpleDecs = [], false: residueDecs = [] } = Common.groupBy(
        compositeDecs.map(([ h, pdec ]) => [ h, [...pdec].filter(([p]) => !~primeDecs.findIndex(([q]) => q === p)) ]),
        ([ , pp ]) => pp.length === 0, ([p]) => compositeDecs.find(([q]) => q === p)),
      ps = [ ...residueDecs.reduce((acc, [, pdec]) => {
        for (let [p] of pdec) acc.add(p);
        return acc
      }, new Set()).values() ].sort((a, b) => a > b),
      { true: residuePrimeDecs = [], false: simplePrimeDecs = [] } = Common.groupBy(
        primeDecs, ([p]) => ps.includes(p)),
      residue = residuePrimeDecs.concat(residueDecs);
      
    this.indexPrimes = ps;
    this.primes = simplePrimeDecs.map(([h]) => h);

    simplePrimeDecs.forEach(([h]) => this.harmonicList.set(h, new Harmonic({ keyboard, mapping: this, order: h,
      countingFn: (...params) => params[ simplePrimeDecs.findIndex(([p]) => p === h) ] })));
    simpleDecs.forEach(([h, hdec]) => {
      const
        just = Math.log2(h) % 1,
        steps = [ ...hdec ].reduce((acc, [p, rad]) => acc + hmap.get(p) * rad, 0) % edo,
        error = (steps / edo - just) * 1200;
      if (Math.abs(error) >= maxError || steps + edo * maxError / 1200 < 1 ||
        steps - edo * maxError / 1200 > edo - 1) hmap.delete(i);
      else this.harmonicList.set(h, new Harmonic({ keyboard, mapping: this, order: h }))
    });

    console.log("residue", residue);

    if (residue.length) {
      let system, best = 0, dims = -1;
      const cols = ps.length;
      for (let hs of HarmonicMapping.#subsets(residue)) { // TODO: memoise?
        const mat = [], rows = hs.length;
        for (let [, pdec] of hs) mat.push(ps.map(p => pdec.get(p) ?? 0));
        if (rows < cols) mat.splice(Infinity, Infinity, ...Array(cols - rows).fill().map(() => mat.at(-1).slice()));
        if (rows > cols) mat.forEach((row, i) => row.splice(Infinity, Infinity, ...(i < cols ? Array(rows - cols).fill(0) :
          Array(rows - cols).fill(0).with(i - cols, -1))));
        const { inv, det } = HarmonicMapping.#invDet(mat, hs, ps);
        if (det === undefined) continue;
        if ((best !== 0 && Math.abs(det) < Math.abs(best)) || (best === 0 && (det !== 0 || inv.length > dims)))
          ([system, best, dims] = [hs, det, inv.length]);
        if (Math.abs(det) === 1) break;
      }
      const
        hs = system.reduce((acc, [h], i) => { // TODO: nicer ordering
          const j = acc.findIndex(([p]) => p === h);
          ([ acc[i], acc[j] ] = [ acc[j], acc[i] ]);
          return acc
        }, residue),
        rows = hs.length, mat = [];
      for (let [, pdec] of hs) mat.push(ps.map(p => pdec.get(p) ?? 0));
      if (rows > cols) mat.forEach((row, i) => row.splice(Infinity, Infinity, ...(i < cols ? Array(rows - cols).fill(0) :
        Array(rows - cols).fill(0).with(i - cols, -1))));

      // TODO: Can I use det to exclude harmonics before running the counting function?
      const { mods, inv, det, lcm, verify } = HarmonicMapping.#invDet(mat, hs, ps);

      this.index = system.map(([h]) => h);
      this.params = residue.filter(([d]) => !~system.findIndex(([h]) => h === d));

      // if underdetermined, the params must be provided
      // if overdetermined, these components must be verified
      this.verify = (...primeVec) => {
        const
          dps = primeVec.slice(0, residue.length),
          vps = primeVec.slice(residue.length);
        return verify.every(([p, vec], i) => dps.reduce((a, x, j) => a + x * vec[j] * (mods[j]?.[1] ?? 1), 0) === vps[i])
      };

      inv.forEach(([h, vec]) => this.harmonicList.set(h, new Harmonic({ keyboard, mapping: this, order: h,
        countingFn: (...params) => {
          const rawNum = hs.reduce((a, _, i) => a + (params[i] ?? 0) * vec[i] * (mods[i]?.[1] ?? 1), 0);
          return rawNum % lcm ? null : rawNum / lcm // Null means failure
        } }), true));
      residue.filter(([d]) => !~inv.findIndex(([h]) => h === d))
        .forEach(([h, dec]) => {
          if (~residueDecs.findIndex(([p]) => p === h)) {
            const
              just = Math.log2(h) % 1,
              primeVec = this.indexPrimes.map(p => dec.get(p) ?? 0),
              steps = this.index.reduce(
                (count, h) => count + hmap.get(h) * this.harmonicList.get(h).countingFn(...primeVec),
                this.primes.reduce((count, p) => count + hmap.get(p) * (dec.get(p) ?? 0), 0)) % edo,
              error = (steps / edo - just) * 1200;
            if (Math.abs(error) >= maxError || steps + edo * maxError / 1200 < 1 ||
              steps - edo * maxError / 1200 > edo - 1) {
              hmap.delete(i);
              return
            }
          }
          this.harmonicList.set(h, new Harmonic({ keyboard, mapping: this, order: h }))
      })
    }
    this.rawHarmonicList = hmap;

    // Generate all intervals
    const withUnison = [1].concat(decs.map(([h]) => h));
    for (let n of withUnison) for (let d of withUnison) {
      this.#properIntervalSet.addRatio(n, d);
      this.intervalSet.addRatio(n, d);
      if (d === 1 && n !== 1) this.harmonicList.get(n).withQuality("harmonic", true)
    }

    this.ready = true
  }

  decomp (n, d) { //Null is failure
    const decomp = typeof n === "bigint" ? Common.decompBig : Common.decomp;
    const pdec = decomp(n)[0], dec = [];
    if (d) {
      for (let [p, rad] of decomp(d)[0]) if (pdec.has(p)) {
        const nrad = pdec.get(p);
        if (nrad === rad) pdec.delete(p);
        else pdec.set(p, nrad - rad)
      } else pdec.set(p, -rad)
    }
    const { params, index, indexPrimes, primes, harmonicList, verify } = this;
    for (let p of primes) {
      if (!pdec.has(p)) continue;
      else dec.push([ p, pdec.get(p) ]);
      pdec.delete(p)
    }
    const primeVec = indexPrimes.map(p => pdec.get(p) ?? 0);
    for (let [p] of pdec) if (!indexPrimes.includes(p)) return null;
    if (!verify(...primeVec)) return null;
    return index.reduce((fn, h) => (...params) => {
      const acc = fn(...params);
      if (acc === null) return null;
      const res = harmonicList.get(h).countingFn(...primeVec, ...params);
      return res === null ? null : res === 0 ? acc : acc.concat([[ h, res ]])
    }, () => dec)
  }

  steps (iv, params = []) {
    const { stepsBasis } = this, { edo } = this.#keyboard;
    if (!this.intervalSet.add(iv)) return null;
    return this.decomp(...iv.fraction)(...params).reduce((acc, [h, r]) => acc + stepsBasis.get(h) * r, edo * -Number(iv.octave))
  }

  get properIntervals () { return new IntervalSet({
    edo: this.#keyboard.edo, stepsBasis: this.stepsBasis, intervalSet: this.#properIntervalSet
  }) }
  addInterval (interval) { intervalSet.add(interval) }

  // Temperaments (in worker)
  #commasworker
  #commas (upperBound) {
    const
      worker = this.#commasworker = new Worker("js/commaworker.js", { type: "module" }), self = this,
      { primes, index } = this, { edo } = this.#keyboard, { limit, maxError } = this.#scale,
      { globalBatchSize: batchSize } = app;
    worker.postMessage({ params: { primes, index, maxError, edo, limit, batchSize } });
    let id = 0, ar = new Map(), ap = new Map(), // Resolve data
        br = new Map(), bp = new Map(), // Wait for yields
        cr = new Map(), cp = new Map(); // Concatenate streams
    cp.set(0, new Promise(res => cr.set(0, res)));
    cr.get(0)();
    $.targets({ async message ({ data }) {
      const { i } = data;
      await bp.get(i).shift();
      ar.get(i).shift()(data);
      ap.get(i).push(new Promise(res => ar.get(i).push(res)));
      bp.get(i).push(new Promise(res => br.get(i).push(res)));
    } }, worker);
    const fresh = async function * ({ retrieve, params }) {
      const i = id++, { upperBound } = params;
      let batch = [], done;
      cp.set(i + 1, new Promise(res => cr.set(i + 1, res)));
      await cp.get(i);
      ap.set(i, [ new Promise(res => ar.set(i, [ res ])) ]);
      bp.set(i, [ new Promise(res => br.set(i, [ res ])) ]);
      self.#commasworker.postMessage({ upperBound, retrieve, i });
      do {
        br.get(i).shift()();
        ({ batch, done } = await ap.get(i).shift());
        for (const value of batch) yield value
      } while (!done);
      [ ar, ap, br, bp, cr, cp ].map(m => m.delete(i));
      cr.get(i + 1)();
    };
    return { fresh, setup: async () => fresh({ retrieve: false, params: { upperBound } }).next() }
  }
  #commaGen
  async * takeCommas (upperBound) { yield * this.#commaGen({ upperBound }) }
  async resetCommas (upperBound) {
    const { edo } = this.#keyboard, { limit } = this.#scale;
    this.#commasworker?.terminate();
    this.#commaGen = Common.cacheAside({
      cacheGen: app.storage.yieldCommas({ edo, limit }),
      ...this.#commas(upperBound)
    });
    this.#resolveCommaGen()
  }
  #resolveCommaGen; #promiseCommaGen = new Promise(res => this.#resolveCommaGen = res);
  get waitForCommaGen () { return this.#promiseCommaGen }
  set waitForCommaGen (_) { return false }

  // Chords (in worker)
  #chordsworker
  async #chords (iv) {
    const
      existing = this.#temperaments.get(iv), self = this,
      { globalBatchSize: batchSize } = app;
    if (existing) {
      this.temperament = existing.comma.fraction;
      return { setup: () => {}, fresh: function * () {} }
    } else {
      const comma = iv.fraction, ln = Common.bigLog2(comma[0]), ld = Common.bigLog2(comma[1]);
      if (ln - ld >= this.#scale.maxError / 400)
        throw new Error("Mapping error: comma to temper must be within error bounds");
      const
        { stepsBasis } = this, { edo } = this.#keyboard, { limit } = this.#scale, { storage } = app,
        hdecomp = [ ...this.harmonicList ].map(([ n, { primeDecomp } ]) => [ n, primeDecomp ]),
        intervalList = [ ...this.properIntervals ].map(iv => iv.fraction),
        worker = this.#chordsworker = new Worker("js/chordworker.js", { type: "module" }), self = this,

        intervalSet = new IntervalSet({ edo, stepsBasis, intervalList: [ [1, 1] ] });

      let id = 0, ar = new Map(), ap = new Map(), // Resolve data
          br = new Map(), bp = new Map(), // Wait for yields
          sr, sp = new Promise(r => sr = r); // Setup callback
      $.targets({ async message ({ data }) {
        const { enharmsRaw, i } = data;
        if (enharmsRaw !== undefined) return sr(enharmsRaw); // TODO save enharms with comma?
        await bp.get(i).shift();
        ar.get(i).shift()(data);
        ap.get(i).push(new Promise(res => ar.get(i).push(res)));
        bp.get(i).push(new Promise(res => br.get(i).push(res)));
      } }, worker);

      worker.postMessage({ params: { edo, stepsBasis, hdecomp, intervalList, comma, batchSize } });

      return {
        setup: async () => {
          const
            enharmsRaw = await sp,
            enharms = new Map(enharmsRaw.map(ivp => ivp.map(([n, d]) => intervalSet.getRatio(n, d)))),
            temperament = new Temperament({ keyboard: self.#keyboard, mapping: self, comma: iv, intervalSet, chords: [], enharms });

          self.#temperaments.set(iv, temperament);
          self.temperament = comma;
        },
        fresh: async function * ({ retrieve, params }) {
          const i = id++, { upperBoundCb } = params;
          let batch = [], done;
          ap.set(i, [ new Promise(res => ar.set(i, [ res ])) ]);
          bp.set(i, [ new Promise(res => br.set(i, [ res ])) ]);
          self.#chordsworker.postMessage({ upperBound: upperBoundCb(), retrieve, i }); // initialStack value?
          do {
            br.get(i).shift()();
            ({ batch, done } = await ap.get(i).shift());
            for (const { internalIntervalsRaw, ord } of batch) yield { edo, limit, ln, ld, internalIntervalsRaw, ord }
          } while (!done);
        }
      }
    }
  }
  #chordGen
  async * takeChords (upperBoundCb) { yield * await this.#chordGen({ upperBoundCb }) }
  async resetChords (iv) {
    const
      { edo } = this.#keyboard, { limit } = this.#scale,
      comma = iv.fraction, ln = Common.bigLog2(comma[0]), ld = Common.bigLog2(comma[1]);
    this.#chordsworker?.terminate();
    this.#chordGen = Common.cacheAside({
      cacheGen: app.storage.yieldChords({ edo, limit, ln, ld }),
      ...await this.#chords(iv)
    })  // BUG computes #chords every time
  }

  get temperaments () { return this.#temperaments }
  set temperament ([ n, d ]) {
    const temp = this.#temperaments.get(this.intervalSet.getRatio(n, d));
    if (temp) {
      this.#temperament = temp;
      this.#resolveTemperament();
      return true
    } else return false
  }
  get temperament () { return this.#temperament }
  #resolveTemperament; #promiseTemperament = new Promise(res => this.#resolveTemperament = res);
  get waitForTemperament () { return this.#promiseTemperament }
  set waitForTemperament (_) { return false }

}

class Harmonic {
  #keyboard; #mapping; order; isBasis; countingFn = null; decomp; primeDecomp
  isSubHarm = false; label
  constructor ({ keyboard, mapping, order, countingFn, isSubHarm = false }) {
    if (!(Keyboard.prototype.isPrototypeOf(keyboard))) throw new Error("Harmonic error: must provide Keyboard object");
    if (!(HarmonicMapping.prototype.isPrototypeOf(mapping))) throw new Error("Harmonic error: must provide HarmonicMapping object");
    this.#keyboard = keyboard;
    this.#mapping = mapping;
    this.order = order;
    this.isSubHarm = isSubHarm;
    this.primeDecomp = [ ...Common.decomp(order)[0] ];
    if (order === 1) { // Unison
      this.isBasis = false;
      this.decomp = () => []
    } else {
      const
        { nonHarmonics, index, primes, ready } = mapping,
        doErr = () => { throw new Error("Harmonic not in mapping") };
      if (ready) {
        let decomp = mapping.decomp(order);
        if (nonHarmonics.has(order) || decomp === null) doErr();
        this.isBasis = false;
        this.decomp = decomp
      } else {
        if (this.isBasis = primes.concat(index).includes(order)) this.countingFn = countingFn;
        else this.decomp = mapping.decomp(order)()
      }
    }
  }
  withQuality (q, mutate = false) {
    if (!["harmonic", "subharmonic"].includes(q)) return;
    const mapping = this.#mapping, { order } = this, isSubHarm = q === "subharmonic";
    if (mutate) {
      this.isSubHarm = isSubHarm;
      this.label = isSubHarm ?
        mapping.intervalSet.getRatio(1, order).noteSpelling.romanlow :
        mapping.intervalSet.getRatio(order, 1).noteSpelling.roman;
      return this
    } else return new Harmonic({
      keyboard: this.#keyboard, mapping,
      order: this.order, countingFn: this.countingFn, isSubHarm
    }).withQuality(q, true)
  }
}



// Temperaments

class Temperament {
  #keyboard; #mapping; comma; #intervalSet; #temperedIntervalSet = new Map(); enharms; #chords
  constructor ({ keyboard, mapping, comma, intervalSet, chords, enharms }) {
    if (!(Keyboard.prototype.isPrototypeOf(keyboard))) throw new Error("Temperament error: must provide Keyboard object");
    if (!(HarmonicMapping.prototype.isPrototypeOf(mapping))) throw new Error("Temperament error: must provide HarmonicMapping object");
    this.#keyboard = keyboard;
    this.#mapping = mapping;
    this.#intervalSet = intervalSet;
    this.comma = comma;
    this.enharms = enharms;
    for (let iv of intervalSet) this.addInterval(iv);
    this.#chords = chords; // Map by intervals?
  }
  addInterval (iv) {
    this.#intervalSet.add(iv);
    const enh = this.enharms.get(iv);
    if (enh) {
      const existing = this.#temperedIntervalSet.get(enh);
      if (existing) this.#temperedIntervalSet.set(iv, existing);
      else this.#temperedIntervalSet.set(iv, new TemperedInterval({
        keyboard: this.#keyboard, temperament: this, enharmonicSet: new Set([ iv, enh ])
      }))
    } else this.#temperedIntervalSet.set(iv, new TemperedInterval({
      keyboard: this.#keyboard, temperament: this, enharmonicSet: new Set([ iv ])
    }))
  }
  get chords () { return this.#chords.map(ch => ch.withInversion(0, true)) }
  addChord (chord) {
    for (let i = 0; i < chord.adicity; i++) for (const iv of chord.withInversion(i).internalIntervals) this.addInterval(iv);
    this.#chords.push(chord) // Set?
  }
  getTemperedInterval (iv) { return this.#temperedIntervalSet.get(this.#intervalSet.getRatio(...iv)) }
  getChordByIntervals (ivs) { // TODO make interval using method
    ivs = ivs.map(([n, d]) => new Interval({ intervalSet: this.#intervalSet, n, d }));
    for (let chord of this.chords) {
      const civs = chord.intervals, m = ivs.length;
      if (m !== civs.length) continue;
      const i = civs.findIndex((_, j) => ivs.every((iv, k) => iv === civs[(j + k) % m]));
      if (~i) return chord.withInversion(i)
    }
  }
}

class TemperedInterval {
  #keyboard; #temperament; enharmonicSet
  constructor ({ keyboard, temperament, enharmonicSet }) {
    if (!(Keyboard.prototype.isPrototypeOf(keyboard))) throw new Error("TemperedInterval error: must provide Keyboard object");
    if (!(Temperament.prototype.isPrototypeOf(temperament))) throw new Error("TemperedInterval error: must provide Temperament object");
    if (!(Set.prototype.isPrototypeOf(enharmonicSet)) || !Common.between(1, 2, enharmonicSet.size))
      throw new Error("Bad enharmonic set");
    this.#keyboard = keyboard;
    this.#temperament = temperament;
    this.enharmonicSet = enharmonicSet;
    const [ number, roman, romanlow, letter, fraction ] = [ ...enharmonicSet ]
      .map(({ noteSpelling: { number, roman, romanlow, letter }, fraction: [ n, d ] }) =>
        [ number, roman, romanlow, letter, `<sup>${n}</sup>⁄<sub>${d}</sub>` ])
      .reduce((fst, snd) => fst.map((str, i) => `(${str}≅${snd[i]})`));
    this.noteSpelling = { number, roman, romanlow, letter, fraction }
  }
}

class Chord {  // TODO BigNum
   // TODO { harmonicSeries: { harmonics, bass, isSubharm } } | { essentiallyTempered: { internalIntervals } }
  static types = [ "harmonic series", "essentially tempered" ]
  static fromRepr = ({ keyboard, mapping, type, chordRaw: { edo, limit, ln, ld, internalIntervalsRaw } }) => {
    if (keyboard.edo !== edo) throw new Error("Unhandled - chord edo different to current edo");
    if (keyboard.scale.limit !== limit) throw new Error("Unhandled - chord limit different to current limit");
    const ivset = mapping.intervalSet, intervalsRaw = internalIntervalsRaw.map(ivs => ivs[1]);
    let iv = ivset.addRatio(...intervalsRaw.reduce(([a, b], [c, d]) => [a * c, b * d], [1, .5]));
    if (Common.mod(mapping.steps(iv), edo) !== 0) throw new Error("Unhandled - chord comma not tempered");
    if (mapping.steps(iv) === edo) iv = iv.inverse();
    // console.log(iv);
    if (!mapping.temperaments.has(iv)) throw new Error("Unhandled - chord temperament not yet loaded");
    const [n, d] = iv.fraction;
    if (Common.bigLog2(n) !== ln || Common.bigLog2(d) !== ld) throw new Error("Unhandled - comma / interval mismatch");
    return new Chord({ keyboard, mapping, type, internalIntervals: internalIntervalsRaw.map(ivs => ivs.map(iv => ivset.addRatio(...iv))) })
  }
  #keyboard; #mapping; type; adicity; #intervals; #internalIntervals
  harmonics; #harmonicIntervals; isSubHarm; #inversion
  voicing
  constructor ({ keyboard, mapping, type, harmonics, bass, isSubHarm = false, internalIntervals, voicing }) {
    if (!(Keyboard.prototype.isPrototypeOf(keyboard))) throw new Error("Chord error: must provide Keyboard object");
    if (!(HarmonicMapping.prototype.isPrototypeOf(mapping))) throw new Error("Chord error: must provide HarmonicMapping object");
    this.#keyboard = keyboard;
    this.#mapping = mapping;
    if (typeof type !== "string" && !Chord.types.includes(type)) throw new Error("Chord error: unknown type");
    this.type = type;
    switch (type) {
      case "harmonic series":
      if (typeof bass !== "number" || !harmonics.includes(bass) || !("length" in harmonics) || harmonics.length < 2 ||
        harmonics.some(h => typeof h !== "number" || !mapping.decomp(h, bass)()))
        throw new Error("Chord error: harmonic not supported by temperament");
      this.adicity = harmonics.length;
      this.voicing = voicing ?? Array(this.adicity).fill(-1);
      this.harmonics = harmonics;
      this.isSubHarm = isSubHarm;
      if (isSubHarm) this.harmonics.sort((a, b) => Common.mod(Math.log2(1 / a), 1) > Common.mod(Math.log2(1 / b), 1));
      else this.harmonics.sort((a, b) => Common.mod(Math.log2(a), 1) > Common.mod(Math.log2(b), 1));
      const
        len = this.adicity = harmonics.length,
        inv = this.#inversion = harmonics.indexOf(bass);
      this.#harmonicIntervals = harmonics.map((h, i) => isSubHarm ?
        [ h, harmonics[++i % len] ] : [ harmonics[++i % len], h ]);
      this.#internalIntervals = harmonics.map((_, i) => harmonics.map((h, j) =>
        mapping.intervalSet.getRatio(harmonics[(i + j) % len], 1).withOctave(i + j >= len).fraction))
      break
    case "essentially tempered":
      if (!("length" in internalIntervals) || internalIntervals.length < 2 ||
        internalIntervals.some((ivs, _, ar) => !("length" in ivs) || ivs.length !== ar.length ||
          !ivs.every(iv => Interval.prototype.isPrototypeOf(iv))))
        throw new Error("Chord error: malformed interval data");
      this.adicity = internalIntervals.length;
      this.voicing = voicing ?? Array(this.adicity).fill(0);
      this.#inversion = 0;
      this.#internalIntervals = internalIntervals;
      this.#intervals = internalIntervals.map(ivs => ivs[1])
    }
  }
  get inversion () { return this.#inversion }
  set inversion (i) { this.#inversion = Common.mod(i, this.adicity) }
  get intervals () {
    const
      inv = this.#inversion, { type } = this,
      ivs = type === "harmonic series" ? this.#harmonicIntervals :
        type === "essentially tempered" ? this.#intervals : []
    return ivs.toSpliced(0, inv).concat(ivs.toSpliced(inv))
  }
  get intervalNames () {
    const { temperament } = this.#mapping;
    return this.intervals.map(({ fraction }) => temperament.getTemperedInterval(fraction).noteSpelling)
  }
  get internalIntervals () {
    const mapping = this.#mapping
    return this.type === "harmonic series" ?
      this.#internalIntervals[this.#inversion].map(iv => mapping.intervalSet.getRatio(...iv)) :
      this.type === "essentially tempered" ? this.#internalIntervals[this.#inversion].slice() : []
  }
  get internalIntervalNames () {
    const { temperament } = this.#mapping;
    return this.internalIntervals.map(iv => temperament.getTemperedInterval(iv.fraction).noteSpelling)
  }
  get chordName () {}
  get #repr () {
    const { type, harmonics, voicing } = this;
    let opts = { type, inversion: this.#inversion, voicing }
    if (type === "harmonic series") Object.assign(opts, { harmonics, bass: harmonics[0], isSubHarm: this.isSubHarm });
    else if (type === "essentially tempered") opts.internalIntervals = this.#internalIntervals;
    return opts
  }
  toString () {
    const { internalIntervals, ...opts } = this.#repr;
    if (internalIntervals) opts.internalIntervals = internalIntervals.map(ivs => ivs.map(iv => iv.fraction));
    return JSON.stringify(opts)
  }
  withInversion (i, mutate = false) {
    if (!Common.between(0, this.adicity - 1, i)) return;
    if (mutate) {
      this.#inversion = i;
      return this
    } else {
      const { inversion, ...opts } = this.#repr;
      return new Chord({ keyboard: this.#keyboard, mapping: this.#mapping, ...opts }).withInversion((inversion + i) % this.adicity, true)
    }
  }
  withQuality (q) {
    if (this.isSubHarm === q) return;
    if (this.type === "essentially tempered") return;
    if (this.isSubHarm = !this.isSubHarm) this.harmonics.sort((a, b) => Common.mod(Math.log2(1 / a), 1) > Common.mod(Math.log2(1 / b), 1));
    else this.harmonics.sort((a, b) => Common.mod(Math.log2(a), 1) > Common.mod(Math.log2(b), 1));
    const { harmonics, adicity } = this;
    this.#harmonicIntervals.reverse().forEach(ivs => ivs.reverse());
    this.#internalIntervals = harmonics.map((_, i) => harmonics.map((_, j) => {
      const h = harmonics[(i + j) % adicity];
      return this.#mapping.intervalSet.getRatio(...(q ? [ 1, h ] : [ h, 1 ])).withOctave(i + j >= adicity).fraction
    }));
    this.#inversion = adicity - this.#inversion - 1;
    return this
  }
  start (id) {
    const
      { voicing } = this, keyboard = this.#keyboard, mapping = this.#mapping,
      { scale, edo, hexGrid } = keyboard, { orientation: [ gO, hO ] } = hexGrid;
    this.internalIntervals.forEach((iv, i) => {
      const key = scale.getKey(mapping.steps(iv) % edo);
      key.label = key.labels.findIndex(({ letter }) => letter === iv.noteSpelling.letter)
    });
    keyboard.hexGrid.redraw(true);
    this.internalIntervals.forEach((iv, i) => {
      const
        steps = mapping.steps(iv), rank = steps % edo, octave = Math.floor(steps / edo),
        [ g, h ] = scale.getKey(rank).home.coord;
      keyboard.play(g + gO * (voicing[i] + octave), h + hO * (voicing[i] + octave), id + "-" + i)
    })
  }
  stop (id) { for (let i = 0; i < this.adicity; i++) this.#keyboard.stop(id + "-" + i) }
}



// Keyboard grid

class HexGrid { // TODO: set w, h, theta within HexGrid
  #keyboard
  w = 0; h = 0; c; unit; r; octLen
  gstep; hstep; orientations; displayKeyNames; theta = 0
  #orientation
  #hexes = new Map(); #edges; #notes
  #activeClasses = new Map() // Map([classname, Map([hex, Set(id)])])
  #bgImgCache

  constructor ({ keyboard, gstep, hstep, unit, orientation, displayKeyNames = true }) {
    if (!(Keyboard.prototype.isPrototypeOf(keyboard))) throw new Error("HexGrid error: must provide Keyboard object");
    this.#keyboard = keyboard;
    if (typeof gstep !== "number" || gstep < 1 || gstep > app.maxEdo || gstep % 1 ||
      typeof hstep !== "number" || hstep < 1 || hstep > app.maxEdo || hstep % 1) throw new Error("Keyboard error: bad grid steps");
    if (typeof unit !== "number" || unit < 5 || unit > 1e4) throw new Error("Keyboard error: bad button size");
    if (!("length" in orientation) || orientation.length !== 2 || orientation.some(v => v < 0 || v > app.maxEdo || v % 1) ||
      orientation[0] * gstep + orientation[1] * hstep !== keyboard.edo) throw new Error("Keyboard error: bad orientation");
    this.gstep = gstep;
    this.hstep = hstep;
    this.genOrientations();
    this.orientation = orientation;
    this.displayKeyNames = Boolean(displayKeyNames);
    this.unit = unit;
    this.r = this.unit * 2
  }

  #newHex (g, h, isGhost) {
    const row = this.#hexes.get(g) ?? this.#hexes.set(g, new Map()).get(g),
          hex = new HexButton({ keyboard: this.#keyboard, hexGrid: this, g, h, isGhost });
    row.set(h, hex);
    return hex
  }

  getHex (g, h) { return this.#hexes.get(g)?.get(h) }
  hasHex (g, h) { return this.#hexes.get(g)?.has(h) ?? false }

  coordToSteps (g, h) { return g * this.gstep + h * this.hstep }
  coordToRank (g, h) { return Common.mod(this.coordToSteps(g, h), this.#keyboard.edo) }
  coordToOctave (g, h) { return Math.floor(this.coordToSteps(g, h) / this.#keyboard.edo) }

  * [Symbol.iterator] () { for (let [ , row ] of this.#hexes) for (let [ , hex ] of row) yield hex }

  addToActiveClass(name, hex, id) {
    const activeClasses = this.#activeClasses, activeHexes = activeClasses.get(name) ?? new Map();
    activeClasses.set(name, activeHexes.set(hex, (activeHexes.get(hex) ?? new Set()).add(id)))
  }
  removeFromActiveClasses(hex, id) {
    for (const [ name, activeHexes ] of this.#activeClasses) {
      const ids = activeHexes.get(hex);
      if (!ids) return;
      ids.delete(id);
      if (ids.size === 0) activeHexes.delete(hex)
      if (activeHexes.size === 0) this.#activeClasses.delete(name)
    }
  }

  genOrientations () {
    const { gstep, hstep } = this, { edo } = this.#keyboard, res = [];
    for (let y = 0; y <= edo / hstep; y++) {
      const x = (edo - hstep * y) / gstep;
      if (x === Math.floor(x)) res.push ([ x, y ])
    }
    this.orientations = res;
  }
  get orientation () { return this.#orientation }
  set orientation ([g, h]) {
    this.#orientation = [ g, h ];
    const { unit, w } = this, x = (2 * g + h) * Math.sqrt(3) / 2, y = h * 1.5;
    this.theta = Math.atan(y / x)
  }
  setLattice ({ gstep, hstep }) {
    Object.assign(this, { gstep, hstep });
    this.genOrientations();
    const
      { orientations } = this,
      orientation = orientations.find(([g, h]) => g + h === 7) || orientations[0];
    if (!orientation) return false;
    this.orientation = orientation;
    return true
  }

  updateGrid (force) {
    if (this.#notes && !force) return;
    const
      { gstep, hstep, c, w, octLen, orientation: [ g, h ] } = this,
      { edo } = this.#keyboard;

    // Central line
    this.#hexes = new Map();
    this.#edges = new Set([this.#newHex(0, 0, false)]);
    this.#notes = new Set([0]);
    let left = .5, right = .5, focus = [ [0, 0], [0, 0] ];
    for (let i = 1; i <= g + h; i++) {
      if (left / i <= h / (g + h)) { left++; focus[0][1]++ } else focus[0][0]++;
      if (right / i < h / (g + h)) { right++; focus[1][1]++ } else focus[1][0]++;
      this.#edges.add(this.#newHex(...focus[0], false));
      this.#notes.add(this.coordToSteps(focus[0][0], focus[0][1]));
      if (focus[0].every((v, i) => v === focus[1][i])) continue
      this.#edges.add(this.#newHex(...focus[1], false));
      this.#notes.add(this.coordToSteps(focus[1][0], focus[1][1]))
    }

    // One octave
    const dev = coord => Math.abs(this.h / 2 - HexButton.centre(...coord, this)[1]);
    this.fillGrid({
      candidate: (g0, h0) => Common.between(w / 2 - c, w / 2 - c + octLen, HexButton.centre(g0, h0, this)[0]) &&
        !this.#notes.has(this.coordToRank(g0, h0)),
      filter: hexes => Common.group(hexes, ([a, b], [c, d]) => this.coordToRank(a - c, b - d) === 0)
        .map(enhs => enhs.sort((a, b) => dev(a) > dev(b))[0]),
      isGhost: () => false
    });

    // Two octaves
    this.#notes = new Set();
    this.fillGrid({
      candidate: (g0, h0) => Common.between(w / 2 - c, w / 2 - c + octLen, HexButton.centre(g0, h0, this)[0]) &&
        !this.#notes.has(this.coordToRank(g0, h0)),
      filter: hexes => Common.group(hexes, ([a, b], [c, d]) => this.coordToRank(a - c, b - d) === 0)
        .filter(([[g0, h0]]) => !this.#notes.has(this.coordToRank(g0, h0)))
        .map(enhs => enhs.sort((a, b) => dev(a) > dev(b))[0]),
      isGhost: () => true
    });

    // Fill to sides
    const home = [ ...this ];
    this.fillGrid({
      candidate: (g0, h0) => {
        const homeEquiv = ~home.findIndex(hex => {
                const [ baseG, baseH ] = hex.coord;
                return (baseG - g0) * h === (baseH - h0) * g // require gcd(g, h) === 1
              });
        return homeEquiv && HexButton.vertices(g0, h0, this).some(([ px, py ]) =>
          px > 0 && px < this.w && py > 0 && py < this.h)
      },
      isGhost: (g0, h0) => home.find(hex => {
        const [ baseG, baseH ] = hex.coord;
        return (baseG - g0) * h === (baseH - h0) * g
      }).isGhost
    });

    // Notes
    for (let hex of this) if (!hex.isGhost) {
      const { octave, rank } = hex, note = this.#keyboard.scale.addNote({ octave, rank });
      if (octave === 0) note.key.home = hex
    }
  }

  async fillGrid ({ candidate, filter = x => x, isGhost }) {
    let viewEdges = new Set([ ...this.#edges ]);
    while (viewEdges.size > 0) {
      let newViewEdges = new Map(), removeViewEdges = new Set(), newNotes = new Set();
      for (let hex of viewEdges) {
        let remove = true;
        for (let [g, h] of hex.neighbours()) {
          const thisHex = this.getHex(g, h);
          if (thisHex) { if (viewEdges.has(thisHex)) removeViewEdges.add(thisHex) }
          else if (candidate(g, h)) {
            newViewEdges.get(g)?.add(h) ?? newViewEdges.set(g, new Set([h]));
            newNotes.add(this.coordToRank(g, h));
          } else remove = false;
        }
        removeViewEdges.add(hex)
        if (remove) this.#edges.delete(hex)
      }
      filter([ ...(function * () {
        for (let [g, s] of newViewEdges) for (let h of s) yield [g, h]
      })() ]).forEach(([g, h]) => {
        const nextHex = this.#newHex(g, h, isGhost(g, h));
        this.#edges.add(nextHex);
        viewEdges.add(nextHex)
      });
      removeViewEdges.forEach(hex => viewEdges.delete(hex));
      this.#notes = new Set([ ...this.#notes, ...newNotes ])
    }
  }

  rotate (x, y, rev = false) {
    const cx = this.w / 2, cy = this.h / 2, theta = rev ? -this.theta : this.theta,
          cos = Math.cos(theta), sin = Math.sin(theta);
    return [ cos * (x - cx) + sin * (y - cy) + cx, cos * (y - cy) - sin * (x - cx) + cy ]
  }

  getCoord (x, y) {
    const { r, w: width, h: height, c } = this;
    ([ x, y ] = this.rotate(x * 2 + c, y * 2, true));
    const a = (x - width / 2) / r / Math.sqrt(3) * 2,
          b = (y - height / 2) / r * 2,
          band = Math.floor(Math.floor((b + 1) / 3));
    if (((Math.floor(b % 3)) + 3) % 3 === 1) {
      const clampedA = ((a % 1) + 1) % 1, clampedB = ((b % 1) + 1) % 1,
            topLeft = clampedA + clampedB > 1, bottomLeft = clampedA < clampedB,
            h = 2 * Math.floor((b + 4) / 6), g = Math.floor((a - h) / 2);
      if (band % 2) return Math.floor(a) % 2 ? [ g + 1, h - !topLeft ] : [ g + !bottomLeft, h - !bottomLeft ];
      else return Math.floor(a) % 2 ? [ g + !bottomLeft, h + bottomLeft ] : [ g, h + topLeft ]
    } else return [ Math.floor((a - band + 1) / 2), band ]
  }

  // TODO urgent: needs BigInt Interval
  classifyKeys (force) {
    if (this.#notes && !force) return;
    const 
      { scale, edo } = this.#keyboard, { mapping } = scale,
      { primes, indexPrimes, index, intervalSet, harmonicList, rawHarmonicList } = mapping,
      bases = primes.map(p => [ p, p ])
        .concat(indexPrimes.map(p => [ p, index.find(h => harmonicList.get(h).primeDecomp.some(([q]) => q === p)) ]))
        .sort(([a], [b]) => a > b).map(([ , h ]) => intervalSet.getRatio(h, 1).withOctave(0));
    let i = edo - 1, full, prev, k = 0, result = Array(edo).fill(), prevResult,
        { properIntervals: ivset } = mapping, prevIvset;
    result[0] = [[[], []]];
    for (let basis of bases) {
      const [ pn, pd ] = basis.fraction.map(Common.non2), pstep = mapping.steps(basis);
      prevIvset = new IntervalSet({ edo, stepsBasis: mapping.stepsBasis, intervalSet: ivset });
      full = i;
      prev = null;
      while (i > 0 && (i !== prev || i === full) && rawHarmonicList.size) {
        full = null;
        prev = i;
        prevResult = structuredClone(result);
        for (let iv of prevIvset) {
          const [ n, d ] = iv.fraction.map(Common.non2), step = mapping.steps(iv);
          let s = Common.mod(step + k * pstep, edo);
          if (prevResult[s] === undefined && mapping.decomp(n * pn ** k, d * pd ** k)()) {
            const newIv = intervalSet.addRatio(n * pn ** k, d * pd ** k);
            (result[s] ??= (i--, [])).push(newIv.splitDecomp);
            ivset.add(newIv)
          }
          s = Common.mod(step - k * pstep, edo);
          if (k > 0 && prevResult[s] === undefined && mapping.decomp(n * pd ** k, d * pn ** k)()) {
            const newIv = intervalSet.addRatio(n * pd ** k, d * pn ** k);
            (result[s] ??= (i--, [])).push(newIv.splitDecomp);
            ivset.add(newIv)
          }
        }
        k++
      }
      if (i <= 0) break;
      k = 1
    }
    for (let iv of ivset) mapping.intervalSet.add(iv);
    for (let key of scale) key.hexes.clear();
    for (let hex of this) {
      const
        { octave, rank } = hex, labels = [],
        scaleKey = scale.getKey(rank),
        note = scaleKey.addNote(octave);
      scaleKey.hexes.add(hex);
      hex.note = note;
      if (result[rank]) for (let i = 0, ivs = result[rank]; i < ivs.length; i++) {
        const { accid, ...labelStrings } = Common.noteFromFactors(ivs[i]);
        let keyClass = Common.between(6, 10, Common.mod(accid[3], 12)) ? "black" : "white";
        const ot = ivs[i][0].findLast(([p]) => p !== 3);
        if (ot) keyClass += ot[0] + "o";
        const ut = ivs[i][1].findLast(([p]) => p !== 3);
        if (ut) keyClass += ut[0] + "u";
        labels.push({ ...labelStrings, keyClass, interval: ivs[i] })
      }
      if (!scaleKey.labels.length) scaleKey.labels = labels
    }
  }

  redraw (force) {
    const { gridctx, canvas } = app.state(), { width, height } = canvas;
    this.updateGrid(force);
    this.classifyKeys(force);
    gridctx.fillStyle = "#000000";
    gridctx.fillRect(0, 0, width, height);
    for (let hex of this) hex.colour();  // Redraw by local hexes?
    canvas.toBlob(blob => {
      const url = URL.createObjectURL(new Blob([blob]));
      canvas.style.backgroundImage = `url('${url}'), url('${this.#bgImgCache ?? url}')`;
      this.#bgImgCache = url
    })
  }

  colour () {
    const { gridctx, canvas } = app.state(), { width, height } = canvas;
    gridctx.clearRect(0, 0, width, height);
    for (const [ name, activeHexes ] of this.#activeClasses)
      for (const [ hex, ids ] of activeHexes) hex.colour({ bgColour: Keyboard.noteColours[name] })
  }
}

class HexButton {
  static #colourMix = (hc1, hc2, t) => {
    if (![hc1, hc2].every(hc => hc.match(/#\p{Hex_Digit}{6}/ug))) return null;
    const [r1, g1, b1] = hc1.slice(1).match(/.{2}/g).map(s => parseInt(s, 16));
    const [r2, g2, b2] = hc2.slice(1).match(/.{2}/g).map(s => parseInt(s, 16));
    return "#" + [[r1, r2], [g1, g2], [b1, b2]].reduce((a, [l, r]) => a + Math.round(Common.lerp(l, r, t)).toString(16).padStart(2, "0"), "")
  }
  static #contrast = hc => {
    if (!hc.match(/#\p{Hex_Digit}{6,8}/ug)) return null;
    const [r, g, b, a] = hc.slice(1).match(/.{2}/g).map(s => parseInt(s, 16));
    return r * .299 + g * .587 + b * .114 >= 32768 / ((a ?? 255) + 1) ? "#222222" : "#dddddd"
  }

  static vertices (g, h, grid) {
    const { r, w, h: ht, c } = grid, x = w / 2, y = ht / 2, k = .5 * Math.sqrt(3),
          origin = [
            [ x, y - r ], [ x - r * k, y - r / 2 ], [ x - r * k, y + r / 2 ],
            [ x, y + r ], [ x + r * k, y + r / 2 ], [ x + r * k, y - r / 2 ]
          ];
    return origin.map(([ a, b ]) => {
      const [ rx, ry ] = grid.rotate(
              Math.floor(a + r * k * (h + 2 * g)),
              Math.floor(b + 1.5 * r * h)
            );
      return [ rx - c, ry ]
    })
  }
  static centre (g, h, grid) {
    const { r, w: width, h: height, c } = grid, k = .5 * Math.sqrt(3),
          [ rx, ry ] = grid.rotate(
            Math.floor(width / 2 + r * k * (h + 2 * g)),
            Math.floor(height / 2 + 1.5 * r * h)
          );
    return [ rx - c, ry ]
  }

  #keyboard; #hexGrid; #g; #h; #note; isGhost
  constructor ({ keyboard, hexGrid, g, h, isGhost = false }) {
    if (!(Keyboard.prototype.isPrototypeOf(keyboard))) throw new Error("HexButton error: must provide Keyboard object");
    this.#keyboard = keyboard;
    if (!(HexGrid.prototype.isPrototypeOf(hexGrid))) throw new Error("HexButton error: must provide HexGrid object");
    this.#hexGrid = hexGrid;
    this.#g = g;
    this.#h = h;
    this.isGhost = isGhost
  }
  vertices () { return HexButton.vertices(this.#g, this.#h, this.#hexGrid) }
  centre () { return HexButton.centre(this.#g, this.#h, this.#hexGrid) }

  neighbours () {
    const g = this.#g, h = this.#h;
    return [
      [ g - 1, h ], [ g, h - 1 ], [ g + 1, h - 1 ],
      [ g + 1, h ], [ g, h + 1 ], [ g - 1, h + 1 ]
    ]
  }

  get coord () { return [ this.#g, this.#h ] }
  get #steps () { return this.#hexGrid.coordToSteps(this.#g, this.#h) }
  get rank () { return Common.mod(this.#steps, this.#keyboard.edo) }
  get octave () { return Math.floor(this.#steps / this.#keyboard.edo) }
  set note (note) { this.#note = note }
  get note () { return this.#note }

  colour ({ bgColour, ctx } = {}) {
    ctx ??= app.state().gridctx;
    const
      { noteColours } = Keyboard, hexGrid = this.#hexGrid,
      [ colourBase, oharm, uharm ] = this.#note.key.label.keyClass
        ?.match(/(black|white)(?:(\d{1,2})o)?(?:(\d{1,2})u)?/)?.slice(1) ?? [],
      vertices = this.vertices(), { isGhost } = this,
      drawHex = c => {
        ctx.beginPath();
        ctx.moveTo(...vertices[5]);
        for (let [ x, y ] of vertices) ctx.lineTo(x, y);
        ctx.strokeStyle = isGhost ? c : "#dddddd";
        ctx.fillStyle = isGhost ? "#00000000" : c;
        ctx.lineWidth = isGhost ? 6 : 1;
        ctx.fill();
        ctx.stroke();
      }
    ctx.globalCompositeOperation = isGhost ? "lighten" : "source-over";
    if (bgColour) drawHex(bgColour);
    else if (colourBase) {
      const
        bc = noteColours[isGhost ? colourBase === "white" ? "black" : "white" : colourBase],
        oc = oharm ? HexButton.#colourMix(bc, noteColours[oharm] ?? noteColours.default, .1) : null,
        uc = uharm ? HexButton.#colourMix(bc, noteColours[uharm] ?? noteColours.default, .1) : null;
      if (oc && uc) {
        bgColour = HexButton.#colourMix(oc, uc, .5);
        drawHex(HexButton.#colourMix(oc, noteColours.white, .1));
        const [cx, cy] = this.centre();
        ctx.save();
        ctx.beginPath();
        ctx.arc(cx, cy, hexGrid.r, 0, Math.PI);
        ctx.closePath();
        ctx.clip();
        drawHex(HexButton.#colourMix(uc, noteColours.black, .1));
        ctx.restore();
      } else drawHex(bgColour = (oc ? HexButton.#colourMix(oc, noteColours.white, .1) : uc ?
        HexButton.#colourMix(uc, noteColours.black, .1) : bc))
    } else drawHex(bgColour = noteColours.default);
    ctx.font = (isGhost ? "bold  " : "") + (.5 * hexGrid.r) + "px HEJI2, Ratafly";
    const [ x, y ] = this.centre(),
          label = this.#note.key.label.letter ?? this.#note.key.label,
          { width } = ctx.measureText(label);
    ctx.fillStyle = isGhost ? bgColour : HexButton.#contrast(bgColour);
    ctx.fillText(label ?? this.rank, x - width / 2, y)
  }

}



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
    } catch (e) { this.#rejectReady() }
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
    5: "#ff0000", 7: "#0000ff", 11: "#00ff00", 13: "#ff00ff"
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
      hmap: $.all(".harmonic.prime > input.steps")
        .map(el => [ parseInt(el.parentElement.dataset.harm), el.valueAsNumber ])
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
    this.scope.keyboard.hexGrid.redraw()
  }

  static ready = false

  // Instance
  name; edo; hexGrid; scale; instrument = "triangle"
  touches = new Map(); mousedown = false
  hoveredKey; wheelVal = 0; wheelSensitivity = 200
  clipboard = []; clipboardPeekIndex
  root = 0 // TODO: load/save
  constructor ({
    name, edo,
    gstep, hstep, unit, orientation, displayKeyNames,
    limit, refNote, freqBasis, maxError,
      hmap,
    // instrument
  }) {
    // TODO: validation helper?
    if (typeof name !== "string" || name === "" || name.length > app.maxKeyboardNameLength) throw new Error("Keyboard error: bad name");
    if (typeof edo !== "number" || edo < 0 || edo > app.maxEdo || edo % 1) throw new Error("Keyboard error: bad EDO");
    this.name = name;
    this.edo = edo;
    this.hexGrid = new HexGrid({ keyboard: this, gstep, hstep, unit, orientation, displayKeyNames });
    this.scale = new Scale({ keyboard: this, limit, refNote, freqBasis, maxError })
  }

  async save () {
    const
      { name, edo, hexGrid, scale, clipboard } = this,
      { gstep, hstep, unit, orientation, displayKeyNames } = hexGrid,
      { limit, refNote, freqBasis, maxError, mapping } = scale,
      { hmap } = mapping,
      keyboard = {
        name, edo, gstep, hstep, unit, orientation, displayKeyNames,
        limit, refNote, freqBasis, maxError, hmap,
        clipboard: clipboard.map(({ text }) => text)
      };
    Object.assign(app.keyboards[app.keyboardSelection], keyboard)
    await app.storage.saveKeyboard(keyboard);
  }

  async fillSettings () {
    const
      { gstepEl, hstepEl, orientationSelectEl, unitEl, refNoteEl, freqBasisEl,
        edoEl, limitEl, maxErrorEl, displayKeyNamesEl, scaleOutputEl,
        edoInfoEl, limitInfoEl, nameFieldEl, nameTextEl } = Keyboard,
      { name, edo, hexGrid, scale, clipboard } = this,
      { gstep, hstep, unit, orientation, orientations, displayKeyNames } = hexGrid,
      { limit, refNote, freqBasis, maxError } = scale,
      { upperBound } = await app.storage.loadScale({ edo, limit });
    $("#commas").dataset.upperBound = upperBound; //
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
    clipboard.forEach(({ text }) => this.emit("copy", { text }));
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
    const { hexGrid, scale, touches } = this, touch = touches.get(id);
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
    this.hexGrid.redraw(true)
  }

}

// Musical aspect of keyboard
class Scale {
  #keyboard; limit
  mapping; refNote; freqBasis; maxError
  #keys = new Map() // Map([ rank, key ])
  #active = new Map() // Map([ note, Set(id) ])
  constructor ({ keyboard, limit, hmap, refNote, freqBasis, maxError }) {
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
  * [ Symbol.iterator ] () { for (let [ , s ] of this.#keys) yield s }
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
  start () {
    if (this.#note) return;
    const
      { audioctx, masterVolume } = app.state(),
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
  stop () {
    if (!this.#note) return;
    const
      { audioctx } = app.state(), now = audioctx.currentTime,
      { osc, volume, t0 } = this.#note, dt = now - t0, decay = this.#decay;
    this.#note = null;
    volume.gain.cancelScheduledValues(now);
    volume.gain.setTargetAtTime(.001, now, decay / 5);
    osc.stop(now + decay);
  }

  turnOn (id) { this.#scale.play(this, id) }
  turnOff (id) { this.#scale.stop(this, id) }
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
      document.appendChild(img);
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
    version: "0.0.6",
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

  "touchstart mousedown" () {
    if (this.audioctx) return;
    const audioctx = app.audioctx = new AudioContext(), masterVolume = app.masterVolume = audioctx.createGain();
    masterVolume.connect(audioctx.destination);
    masterVolume.gain.value = Common.scaleVolume($("#volume > input").valueAsNumber);
    $.targets({ "touchstart mousedown": "touchstart mousedown" }, self);
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
    if (e.target === $("main")) for (let { clientX, clientY, identifier } of e.changedTouches) {
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
      let iv, isInt;
      new IntersectionObserver(es => es.forEach(e => {
        const { isIntersecting } = e;
        if (!iv) iv = setInterval(() => {
          if (isInt) this.emit("generate-temperaments");
          else {
            clearInterval(iv);
            iv = false
          }
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
      let hex, note;
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
        { keyboard } = this, { scale, clipboard } = keyboard, { mapping } = scale;
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
        itemEl,
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
          data.item = mapping.harmonicList.get(parseInt(node.parentElement.dataset.harm)).withQuality(type);
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
          else { // TODO need to check getChordByIntervals
            data.item = this.keyboard.scale.mapping.temperament
              .getChordByIntervals(JSON.parse($(".chord-intervals", node).dataset.intervals));
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
      } else if (Chord.prototype.isPrototypeOf(data.item))
        $.load("clipboard-item-chord", "#clipboard-peek")[0][0].innerText = data.item.internalIntervalNames.map(({ letter }) => letter).join(" ")
    },

    panic () {
      this.audioctx.close();
      const
        audioctx = this.audioctx = new AudioContext(),
        masterVolume = this.masterVolume = audioctx.createGain();
      masterVolume.connect(audioctx.destination);
      masterVolume.gain.value = Common.scaleVolume($("#volume > input").valueAsNumber);
    },

    fullscreen () { document.fullscreenElement ? document.exitFullscreen() : $("body").requestFullscreen() },



    // Keyboard

    async "keyboard-select" (name) {
      if (this.menuState.at(-2) === "keyboard-settings") await this.keyboard.save(); // TODO get menu state nicely
      this.storage.saveItem("keyboardSelection", this.keyboardSelection = name);
      this.keyboard = new Keyboard(this.keyboards[name]); // From here if settings open, app.keyboard !== menuState[1]
      await this.keyboard.fillSettings();
      this.emit("generate-keyboard");

      $.all("#commas > .comma, #chords > .chord").forEach(el => el.remove())
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
        { rawHarmonicList, harmonicList, primes, indexPrimes, index, intervalSet } = mapping;

      for (let [ harmonic, steps ] of rawHarmonicList) {
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
          labelEl.appendChild(colourEl.cloneNode()).value = Keyboard.noteColours.black;
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
          "input.hcolour": { change () { Keyboard.setColour(primeHarmonic, this.value, this === $.all("input.hcolour", labelEl)[1]) } },
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
          [nUp, dUp] = upperIv.fraction, [nLo, dLo] = lowerIv.fraction;
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
          const
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
                [n, d] = this.parentElement.dataset.interval.split("/").map(v => Common.non2(parseInt(v))),
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
        { keyboard, storage } = this, { edo } = keyboard, { mapping, limit } = keyboard.scale,
        ps = mapping.primes.concat(mapping.index).sort((a, b) => a > b), commasEl = $("#commas");
      let boundN, hasFresh, upperBound = parseInt(commasEl.dataset.upperBound), prevn, prevd;

      if ($.all("#harmonic-search > *").length === 0) {
        for (const h of mapping.harmonicList.keys()) {
          const harmCheckboxEl = $.load("harmonic-checkbox", "#harmonic-search")[0][0];
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
      for await (const { source, value: { n, d, ln, ld } } of mapping.takeCommas(upperBound)) {
        if (n === prevn && d === prevd) continue;
        prevn = n; prevd = d;
        if (source === "worker") boundN = n;
        const iv = mapping.intervalSet.addRatio(n, d); // better version?
        if (Common.mod(mapping.steps(iv), edo) === 0) {
          hasFresh = true;
          // debounce and batch? move into class?
          if (source === "worker")
            await storage.saveComma({ edo, limit, n, d, ln, ld });
          const
            commaEl = $.load("comma", "", commasEl)[0][0],
            [ ratioSpan, nDecompSpan, dDecompSpan, sizeSpan, spellingSpan ] = commaEl.children;
          commaEl.dataset.comma = [ n, d ];
          commaEl.dataset.factors = JSON.stringify(iv.splitDecomp);
          ratioSpan.innerText = `${n}/${d}`;
          const t1 = Common.bigLog2(n & -n), t2 = Common.bigLog2(d & -d);
          nDecompSpan.innerHTML = (t1 > 0 ? [[2, t1]] : []).concat(iv.splitDecomp[0])
            .map(([p, rad]) => p + (rad > 1 ? `<sup>${rad}</sup>` : "")).join(".");
          dDecompSpan.innerHTML = (t2 > 0 ? [[2, t2]] : []).concat(iv.splitDecomp[1])
            .map(([p, rad]) => p + (rad > 1 ? `<sup>${rad}</sup>` : "")).join(".");
          sizeSpan.innerText = `${((ln - ld) * 1200).toFixed(2)}`;
          spellingSpan.innerText = iv.noteSpelling.letter;
          $.queries({ "": { click () { app.emit("generate-chords", this) } } }, commaEl)
        }
      }
      if (!boundN) return;
      if (hasFresh) commasEl.scrollTo(0, $("#computing-commas").offsetTop - commasEl.offsetTop - commasEl.offsetHeight - 1)
      commasEl.dataset.upperBound = upperBound = (1n + boundN / 100n) * 100n;
      await storage.saveScale({ edo, limit, upperBound }) // commaBuffer?
    },

    "update-temperament-filter" (harmCheckboxEl) {},

    async "generate-chords" (commaEl) {
      $(".comma.active")?.classList.remove("active");
      commaEl.classList.add("active");
      $.all(".chord").forEach(el => el.remove());
      const
        [ n, d ] = commaEl.dataset.comma.split(",").map(x => parseInt(x)),
        ln = Common.bigLog2(n), ld = Common.bigLog2(d),
        { keyboard, storage } = this, { scale, edo } = keyboard, { mapping, limit } = scale,
        tempsEl = $("#temperaments"),
        [ ratioSpan, numSpan, denSpan ] = commaEl.children;
      $("#comma-info").innerHTML = `${ratioSpan.innerHTML} (${numSpan.innerHTML}/${denSpan.innerHTML})`;

      await new Promise(requestAnimationFrame);
      tempsEl.scrollTo(0, 32767);
      $("#chords").classList.add("computing");
      await new Promise(requestAnimationFrame);
      
      await mapping.resetChords(mapping.intervalSet.addRatio(n, d));
      $("#chords").classList.remove("computing");
      let upperBound = [];
      for await (const { source, value: chordRaw } of mapping.takeChords(() => upperBound)) {
        if (source === "worker") await storage.saveChord(chordRaw);
        if (Common.LTE(upperBound, chordRaw.ord)) upperBound = chordRaw.ord;
        delete chordRaw.ord;
        chordRaw.internalIntervalsRaw.forEach(ivs => ivs.unshift([1, 1]));
        await mapping.waitForTemperament;
        const chord = Chord.fromRepr({ keyboard, mapping, type: "essentially tempered", chordRaw });
        mapping.temperament.addChord(chord);
        const chordEl = $.load("chord", "#chords")[0][0], chordIvsEl = $(".chord-intervals", chordEl);
        chordIvsEl.dataset.intervals = JSON.stringify(chord.intervals.map(({ fraction }) => fraction));

        app.emit("display-chord", chord, chordEl);
        let clearId;
        $.queries({

          "button.play-chord": {
            pointerdown ({ pointerId }) {
              this.setPointerCapture(pointerId);
              if ($(".switch input:checked")) clearId = setInterval(() => {
                chord.stop("pointer-" + pointerId);
                chord.inversion++;
                app.emit("display-chord", chord, chordEl);
                setTimeout(() => chord.start("pointer-" + pointerId), 50)
              }, 1000);
              chord.start("pointer-" + pointerId)
            },
            "pointerup lostpointercapture" ({ pointerId }) {
              if (!this.hasPointerCapture(pointerId)) return;
              clearInterval(clearId);
              chord.stop("pointer-" + pointerId);
              this.releasePointerCapture(pointerId)
            }
          },

          "button.inversion": { click () {
            chord.inversion++;
            chordIvsEl.dataset.intervals = JSON.stringify(chord.intervals.map(({ fraction }) => fraction));
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
        }, chordEl)
      }
      tempsEl.scrollTo(0, $("fieldset:has(#chords)").offsetTop - tempsEl.offsetTop)
    },

    "display-chord" (chord, chordEl) {
      const
        { keyboard } = this, { edo } = keyboard, { mapping } = keyboard.scale,
        [ chIntervalsEl, chPitchesEl, chSpellingEl, chControlsEl ] = chordEl.children,
        [ chIvHarmonicEl, chIvStepsEl ] = chIntervalsEl.children,
        [ chPcHarmonicEl, chPcStepsEl ] = chPitchesEl.children,
        [ chIvSpellingEl, chPcSpellingEl ] = chSpellingEl.children,
        [ chIsSymmetricEl, chNextInvBtn, chPlayChordBtn ] = chControlsEl.children;
      $.all(".chord-edo", chordEl).forEach(el => el.innerText = edo);
      chIvHarmonicEl.innerHTML = chord.intervalNames.map(({ fraction }) => fraction).join(" ");
      chIvStepsEl.innerText = chord.intervals.map(iv => mapping.steps(iv)).join(" ");
      chPcHarmonicEl.innerHTML = chord.internalIntervalNames.map(({ fraction }) => fraction).join(" – ");
      chPcStepsEl.innerText = `${chord.internalIntervals.map(iv => mapping.steps(iv)).join("-")}-${edo}`;
      chIvSpellingEl.innerText = chord.intervalNames.map(({ number }) => number).join(" – ");
      chPcSpellingEl.innerText = chord.internalIntervalNames.map(({ letter }) => letter).join(" – ");
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
          $.all("#harmonic-search > .harmonic-checkbox").forEach(el => el.remove());
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

  "#temperament-list": { change ({ target }) { app.emit("update-temperament-filter", target) } },

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
      "pointerup lostpointercapture" ({ pointerId }) {
        if (!this.hasPointerCapture(pointerId)) return;
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