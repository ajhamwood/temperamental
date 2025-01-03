import $ from "./machine.js";
import Common from "./common.js";
import { app } from "./main.js";
import { Keyboard, Scale } from "./keyboard.js";
import { HarmonicLattice, IntervalSet, Interval } from "./interval.js";



// Harmonic mapping

class HarmonicMapping {

  // Instance
  #keyboard; #scale
  rawHarmonicList
  nonHarmonics = new Set() // TODO: Cached blacklist
  lattice; decomp; intervalSet = new IntervalSet()
  stepsBasis
  #commasworker; #commas = new IntervalSet();
  commasBounds = new Map(); stackMaps = new Map() // Map([ comma, [ index in commaPartitions ] ])
  #temperaments = new Map(); #temperament
  #chordsworkers = new Map(); #chordGen

  constructor ({ keyboard, scale, hmap }) { // Map([ odd, number ])
    if (!(Keyboard.prototype.isPrototypeOf(keyboard))) throw new Error("Mapping error: must provide Keyboard object");
    this.#keyboard = keyboard;
    if (!(Scale.prototype.isPrototypeOf(scale))) throw new Error("Mapping error: must provide Scale object");
    this.#scale = scale;
    const { edo } = keyboard;
    if (!Map.prototype.isPrototypeOf(hmap) || [ ...hmap ].some(v => v.some(u => typeof u !== "number") ||
      v.some(u => u % 1) || v[0] < 3 || v[0] > app.maxHarmonic || v[0] % 2 !== 1 || v[1] < 0 || v[1] > edo)) throw new Error("Mapping error: bad interval-step mapping");

    // Generate steps
    const stepsBasis = new Map(hmap);
    for (const [h, steps] of hmap) stepsBasis.set(h, steps + edo * Math.floor(Math.log2(h)));
    this.stepsBasis = stepsBasis;

    const harmsRaw = [ ...hmap.keys() ], lattice = this.lattice = new HarmonicLattice({ harmsRaw });
    if (lattice.index.some(h => {
      const s = hmap.get(h);
      return s === undefined || s < 0 || s % 1
    })) throw new Error("Could not set steps for mapping");

    this.rawHarmonicList = hmap;

    // Generate all intervals
    const withUnison = [1].concat(harmsRaw);
    for (const n of withUnison) for (const d of withUnison) this.intervalSet.addRatio(n, d);

    // The neutral temperament
    const unison = this.intervalSet.getRatio(1, 1);
    this.#temperaments.set(unison, new Temperament({ keyboard, mapping: this, comma: unison, intervalSet: lattice.properIntervalSet }));

    this.decomp = lattice.decomp.bind(lattice);
    this.lattice.ready = true // TODO replace with promise resolver
  }

  steps (iv, params = []) { // This kind of sucks
    const { stepsBasis, decomp } = this, { edo } = this.#keyboard;
    if (TemperedInterval.prototype.isPrototypeOf(iv)) iv = iv.enharmonicSet.values().next().value;
    return Common.steps({ edo, stepsBasis, iv, params, decomp })
  }

  get properIntervals () { return new IntervalSet({ intervalSet: this.lattice.properIntervalSet }) }
  addInterval (interval) { this.intervalSet.add(interval) }

  // Temperaments (in worker)
  #genCommas (upperBound) {
    const
      worker = this.#commasworker = new Worker("js/commaworker.js", { type: "module" }), self = this,
      { primes, index } = this.lattice, { edo } = this.#keyboard, { limit, maxError } = this.#scale,
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
      cr.get(i + 1)()
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
      ...this.#genCommas(upperBound)
    });
    this.#resolveCommaGen()
  }
  #resolveCommaGen; #promiseCommaGen = new Promise(res => this.#resolveCommaGen = res);
  get waitForCommaGen () { return this.#promiseCommaGen }
  set waitForCommaGen (_) { return false }
  get commas () { return this.#commas }
  set commas (_) {}

  // Chords (in worker)
  // TODO: dynamically split large commaPartition jobs across finished workers (use priority)
  
  #genChords (iv) {
    const
      existing = this.#temperaments.get(iv), self = this,
      { globalBatchSize: batchSize } = app;
    if (existing) {
      this.temperament = existing.comma.fraction;
      return { setup: () => {}, fresh: function * () {} }
    } else {
      const comma = iv.fraction, [ nd, dd ] = iv.splitDecomp;
      if (Common.bigLog2(comma[0]) - Common.bigLog2(comma[1]) >= this.#scale.maxError / 400)
        throw new Error("Mapping error: comma to temper must be within error bounds");
      const
        { stepsBasis } = this, { edo } = this.#keyboard, { limit } = this.#scale,
        { properIntervalSet } = this.lattice, intervalList = [ ...properIntervalSet ].map(iv => iv.withOctave(0).fraction),
        coreCount = navigator.hardwareConcurrency, workers = this.#chordsworkers, freeWorkers = Array(coreCount - 1).fill(0).map((_, i) => i);

      let ar = new Map(), ap = new Map(), // Resolve data
          br = new Map(), bp = new Map(), // Wait for yields
          cr = new Map(), cp = new Map(), // Concatenate streams
          id = 0, yieldQueue = new Map(); // Map([ job -> ord ])

      const partitionStacks = new Map();
      let jobKeys;
      cp.set(0, new Promise(res => cr.set(0, res)));
      cr.get(0)();
      return {
        setup: async () => {
          const
            temperament = self.temperaments.get(iv) ??
              new Temperament({ keyboard: self.#keyboard, mapping: self, comma: iv, intervalSet: properIntervalSet }),
            { hdecomp, commaPartitions } = temperament;
          self.addTemperament(temperament);
          self.temperament = comma;

          const
            ivOrder = (a, b) => {
              const [ an, ad ] = a.fraction, [ bn, bd ] = b.fraction;
              return an * bd > ad * bn
            },
            harms = [1n].concat(hdecomp.map(([h]) => BigInt(h))
              .filter(h => Common.gcd(h, iv.n) > 1 || Common.gcd(h, iv.d) > 1)
              .sort((a, b) => Common.bigLog2(a) % 1 < Common.bigLog2(b) % 1)),
            taggedStacks = commaPartitions.map(cpart => cpart.reduce((acc, iv) => {
              const
                ni = harms.indexOf(iv.n), di = harms.indexOf(iv.d),
                divs = ni > di ?
                  harms.slice(ni + 1).concat(harms.toSpliced(di)) :
                  harms.slice(ni + 1, di),
                ivPartitions = divs.reduce((acc, h) => acc.map(basePart => {
                  const [ n, d ] = basePart.at(-1);
                  return [ basePart, basePart.toSpliced(-1).concat([ [n, h], [h, d] ]) ]
                }).flat(), [[ iv.fraction ]])
                .map(ivs => ivs.map(([n, d]) => properIntervalSet.getRatio(n, d).withOctave(0)));
              return acc.map(([pch]) => ivPartitions.map(ivpart => [ pch.concat(ivpart), cpart ])).flat()
            }, [[ [], cpart ]])).flat()
              .reduce((acc, [ ivs, cpart ]) => {
                ivs.sort((a, b) => ivOrder(b, a)); // Ascending order
                let low = 0, high = acc.length;
                while (low < high) {
                  const mid = (low + high) >>> 1, checkIvs = acc[mid][0];
                  if (checkIvs.length < ivs.length || (checkIvs.length === ivs.length &&
                    checkIvs.reduce((b, iv, i) => {
                      if (b !== null) return b;
                      const [ an, ad ] = iv.fraction, [ bn, bd ] = ivs[i].fraction, l = an * bd, r =  ad * bn;
                      return l < r ? true : l > r ? false : null
                    }, null))) low = mid + 1;  // Lex order
                  else high = mid
                }
                if (acc[low]?.[0].every((iv, i) => iv === ivs[i])) return acc;
                return acc.toSpliced(low, 0, [ ivs, cpart ])
              }, []);
          Common.group(taggedStacks, ([, a], [, b]) => a.length === b.length && a.every((v, i) => v === b[i]))
            .forEach(job => partitionStacks.set(job[0][1], job.map(([v]) => v)));
          self.temperament.partitionStacks = partitionStacks;
          self.stackMaps.set(iv, (jobKeys = [ ...partitionStacks.keys() ])
            .map(k => commaPartitions.findIndex(cpart => k === cpart)));

          for (let identifier = 0; identifier < coreCount - 1; identifier++) {
            const worker = new Worker("js/chordworker.js", { type: "module" })
            workers.set(identifier, worker);
            worker.postMessage({ params: { identifier, edo, stepsBasis, hdecomp, intervalList, comma, batchSize } });
            $.targets({ async message ({ data }) { // TODO call as named function?
              const { i } = data, ord = yieldQueue.has(i) ? yieldQueue.get(i) : (yieldQueue.set(i, id), id++);
              await bp.get(ord).shift();
              ar.get(ord).shift()(data);
              ap.get(ord).push(new Promise(res => ar.get(ord).push(res)));
              bp.get(ord).push(new Promise(res => br.get(ord).push(res)));
            } }, worker);
          }
        },
        fresh: async function * ({ retrieve, params }) {
          const { upperBound } = params;
          (async () => {
            for (let i = 0; i < jobKeys.length; i++) {
              cp.set(i + 1, new Promise(res => cr.set(i + 1, res)));
              const lowerIndex = Math.max(0, i - coreCount + 2);
              await cp.get(lowerIndex);
              ap.set(i, [ new Promise(res => ar.set(i, [ res ])) ]);
              bp.set(i, [ new Promise(res => br.set(i, [ res ])) ]);
              const
                wid = freeWorkers.shift(),
                stacks = partitionStacks.get(jobKeys[i]).map(ivs => ivs.map(iv => iv.fraction));
              self.#chordsworkers.get(wid).postMessage({ stacks, retrieve, upperBound, i });
            }
          })();
          let batch, done, identifier, i;
          for (let ord = 0; ord < jobKeys.length; ord++) {
            await cp.get(ord);
            do {
              br.get(ord).shift()();
              ({ batch, done, identifier, i } = await ap.get(ord).shift());
              for (const { internalIntervalsRaw, ord } of batch) yield { edo, limit, nd, dd, internalIntervalsRaw, ord, done, i }
            } while (!done);
            [ ar, ap, br, bp ].map(m => m.delete(ord));
            freeWorkers.push(identifier);
            cr.get(ord + 1)();
          }
        }
      }
    }
  }
  async * takeChords (upperBound) { yield * await this.#chordGen({ upperBound }) }
  resetChords (iv) {
    const
      { edo } = this.#keyboard, { limit } = this.#scale,
      comma = iv.fraction, [ nd, dd ] = iv.splitDecomp;
    this.#chordsworkers.forEach(w => w.terminate());
    this.#chordsworkers = new Map();
    this.#chordGen = Common.cacheAside({
      cacheGen: app.storage.yieldChords({ edo, limit, nd, dd }),
      ...this.#genChords(iv)
    })
  }

  get temperaments () { return this.#temperaments }
  set temperament ([ n, d ]) {
    // TODO test within bounds
    const temp = this.#temperaments.get(this.#commas.getRatio(n, d));
    if (temp) {
      this.#temperament = temp;
      this.#resolveTemperament();
      return true
    } else return false
  }
  get temperament () { return this.#temperament }
  resetWaitForTemperament () { this.#promiseTemperament = new Promise(res => this.#resolveTemperament = res) }
  #resolveTemperament; #promiseTemperament
  get waitForTemperament () { return this.#promiseTemperament }
  set waitForTemperament (_) { return false }
  addTemperament (temp) { // TODO test that it is supported?
    if (!Temperament.prototype.isPrototypeOf(temp) || this.#temperaments.has(temp.comma)) return false;
    this.#commas.add(temp.comma);
    this.#temperaments.set(temp.comma, temp)
  }
  hasTemperament (iv) { return this.#temperaments.has(iv) }

}



// Temperaments

class Temperament {

  #harmCombs = (dec, acc = [], cur = 0) => this.hdecomp
    .reduce((ar, [ n, primeDecomp ], i) => {
      if (cur > i) return ar;
      const
        newDec = primeDecomp.reduce((a, [ p, prad ]) => {
          if (a === null) return null;
          const rad = a.get(p);
          return rad >= prad ? rad === prad ? (a.delete(p), a) : a.set(p, rad - prad) : null
        }, new Map(dec));
      return newDec === null ? ar : ar.concat([[n, newDec, i]])
    }, [])
    .reduce((ar, [n, newDec, cur]) => ar.concat(newDec.size === 0 ?
      [ acc.concat([n]) ] : this.#harmCombs(newDec, acc.concat([n]), cur)), [])

  #enumStacks (ots, uts) {
    let flag = ots.flat().length > uts.flat().length;
    if (flag) ([ots, uts] = [uts, ots]);  // ots lesser than uts
    return ots.reduce((a, oharm) =>
      oharm.reduce((b, h, i) => 
        b.concat(a.map(([o, ivs]) => [
          i === oharm.length - 1 ? o : o.concat([ oharm.toSpliced(oharm.length - 1 - i) ]),
          ivs.concat(oharm.toSpliced(i + 1).map(h => [h, 1]))
        ])), a.map(([o, ivs]) => [ o.concat([oharm]), ivs ])),
      [[[], []]])
      .reduce((a, [o, ivs]) =>
        a.concat(o.reduce((b, oharm) => 
          b.reduce((c, [puts, pivs]) =>
            c.concat(puts.reduce((d, puharm, i) =>
              d.reduce((e, [pputs, ppivs, poharm]) => {
                const min = Math.max(0, poharm.length - pputs.slice(i + 1).flat().length)
                return e.concat(
                  poharm.slice(min, puharm.length)
                    .map((oh, k) => [
                      pputs.with(i, puharm.slice(min + k)),
                      ppivs.concat(Array(min + k).fill([oh, puharm[0]])),
                      poharm.slice(min + k)
                    ])
                    .concat([[
                      pputs.with(i, puharm.slice(poharm.length)),
                      ppivs.concat(poharm.toSpliced(puharm.length).fill([poharm[0], puharm[0]])),
                      poharm.slice(puharm.length)
                    ]])
                )
              }, []),
              [[puts, pivs, oharm]])),
            []),
          [[uts, ivs]])),
        [])
      .map(([puts, pivs]) => flag ?
        pivs.map(([u, o]) => [o, u]).concat(puts.flat().map(h => [h, 1])):
        pivs.concat(puts.flat().map(h => [1, h])))
  }

  #partitionComma ({ octaves = 1 } = {}) {
    const
      { comma: iv } = this, { edo } = this.#keyboard, { stepsBasis, lattice, decomp } = this.#mapping,
      { properIntervalSet } = lattice, [ nCombs, dCombs ] = iv.splitDecomp.map(side => side.length ?
        this.#harmCombs(new Map(side)).map(p => Common.group(p)) : [[]]),
      acc = [];
    for (const otones of nCombs) for (const utones of dCombs)
      for (const partition of this.#enumStacks(otones, utones)) {
        const
          partIvs = partition.map(([n, d]) => properIntervalSet.getRatio(n, d).withOctave(0)),
          invIvs = partition.map(([d, n]) => properIntervalSet.getRatio(n, d).withOctave(0));
        if (partIvs.reduce((a, iv) => a + Common.steps({ edo, stepsBasis, iv, decomp }), 0) === octaves * edo) acc.push(partIvs);
        if (invIvs.reduce((a, iv) => a + Common.steps({ edo, stepsBasis, iv, decomp }), 0) === octaves * edo) acc.push(invIvs)
      }
    return acc
  }

  #keyboard; #mapping; comma; intervalSet; #temperedIntervalSet
  commaPartitions; enharms; factors; #chords = new Map() // Trie with TemperedInterval symbols: Map([ TemperedInterval, Map | Chord ])
  stackChords = new Map() // Map([ stack (Bag) : [ Interval ], { commaPartitions: Set([ [ Interval ] ]), chords : Set([ Chord ]) } ])
  partitionStacks // Map([ commaPartition: [ Interval ], stacks: [ (Bag): [ Interval ] ] ])
  constructor ({ keyboard, mapping, comma, intervalSet }) {
    if (!(Keyboard.prototype.isPrototypeOf(keyboard))) throw new Error("Temperament error: must provide Keyboard object");
    this.#keyboard = keyboard;
    if (!(HarmonicMapping.prototype.isPrototypeOf(mapping))) throw new Error("Temperament error: must provide HarmonicMapping object");
    this.#mapping = mapping;
    const { harmonicList, properIntervalSet } = mapping.lattice;
    if (!(Interval.prototype.isPrototypeOf(comma))) throw new Error("Temperament error: comma must be Interval object");
    this.comma = comma;
    if (!(IntervalSet.prototype.isPrototypeOf(intervalSet))) throw new Error("Temperament error: intervalSet must be IntervalSet object");
    this.intervalSet = intervalSet;

    // TODO: limit to harmonics non-coprime to comma!
    this.hdecomp = [ ...harmonicList ].map(([ n, { primeDecomp } ]) => [ n, primeDecomp ]);
    const { true: pairs = [], false: commaPartitions = [] } = Common.groupBy(this.#partitionComma(), ivs => ivs.length === 2);
    this.commaPartitions = commaPartitions;
    this.enharms = pairs.reduce((m, [a, b]) => a === b ?
      m.set(a, a.inverse()) : m.set(a, b.inverse()).set(b, a.inverse()), new Map());
    
    for (const iv of intervalSet) this.intervalSet.add(iv);
    this.#temperedIntervalSet = new TemperedIntervalSet({ temperament: this })

    // Splittable?
    const { splitDecomp } = comma, factors = this.factors = new Map();
    mapping.addTemperament(this);
    for (const iv of mapping.commas) { // TODO also test whether this comma is a factor of each
      if (iv.decomp.length === 0 || iv === comma) continue;
      const
        [n, d] = Common.splitMult(splitDecomp, iv.splitDecomp.toReversed()).map(dec => Common.comp(dec)),
        div = mapping.commas.getRatio(n, d)?.withOctave(0);
        
      if (div) {
        factors.set(iv, div);
        factors.set(div, iv);
        if (!mapping.hasTemperament(iv)) new Temperament({ keyboard, mapping, comma: iv, intervalSet: properIntervalSet });
        if (!mapping.hasTemperament(div)) new Temperament({ keyboard, mapping, comma: div, intervalSet: properIntervalSet })
      }
    }
  }

  * #yieldFromChordTrie (subtrie = this.#chords) {
    if (!Map.prototype.isPrototypeOf(subtrie)) new Error("Temperament error: must yield from Map object");
    for (const value of subtrie.values()) {
      if (Chord.prototype.isPrototypeOf(value)) yield value;
      else if (Map.prototype.isPrototypeOf(value)) yield * this.#yieldFromChordTrie(value);
      else throw new Error("Temperament error: Chords trie must have only either Map nodes or Chord leaves");
    }
  }
  get chords () { return [ ...this.#yieldFromChordTrie() ] }
  set chords (_) {}
  
  #addChordToSubtrie (i, subtrie, chord) {
    const tiv = chord.temperedIntervals[i], curLevel = subtrie.get(tiv);
    if (curLevel === undefined) {
      subtrie.set(tiv, chord);
      return chord
    } else if (Map.prototype.isPrototypeOf(curLevel)) return this.#addChordToSubtrie(i + 1, curLevel, chord);
    else if (curLevel !== chord) {
      if (chord.temperedIntervals.every((tiv, i) => tiv === curLevel.temperedIntervals[i])) return curLevel;
      // TODO compute the correct index
      const newSubtrie = new Map([[curLevel.withInversion(0).temperedIntervals[i + 1], curLevel]]);
      subtrie.set(tiv, newSubtrie);
      return this.#addChordToSubtrie(i + 1, newSubtrie, chord)
    }
  }
  addChord (chord) {
    if (!Chord.prototype.isPrototypeOf(chord)) new Error("Temperament error: this method only accepts Chords");
    const { inversion: i } = chord;
    return this.#addChordToSubtrie(0, this.#chords, chord.withInversion(0, true)).withInversion(i, true)
  }

  #findChordInSubtrie (i, subtrie, chord) {
    const tiv = chord.temperedIntervals[i], curLevel = subtrie.get(tiv);
    if (curLevel === chord) return true;
    else if (Map.prototype.isPrototypeOf(curLevel)) return this.#findChordInSubtrie(i + 1, curLevel, chord);
    else return false
  } 
  hasChord (chord) { // Also has chord by ratios?
    if (!Chord.prototype.isPrototypeOf(chord)) new Error("Temperament error: this method only accepts Chords");
    const { inversion: i } = chord, result = this.#findChordInSubtrie(0, this.#chords, chord.withInversion(0, true))
    chord.withInversion(i, true);
    return result
  }
  // BUG use getTemperedInterval
  getChordByIntervals (ivs) {
    for (let i = 0, subtrie = this.#chords; i < ivs.length; i++) {
      const mbIv = this.getTemperedInterval(...ivs[i]);
      if (!mbIv) return false;
      const curLevel = subtrie.get(mbIv);
      if (Chord.prototype.isPrototypeOf(curLevel)) {
        const // BUG octave...
          { inversion: i } = curLevel, { intervals } = curLevel.withInversion(0, true),
          matches = ivs.slice(i).every((frac, j) => intervals[i + j].fraction.every((h, k) => h === frac[k])); // intervals[0]
        curLevel.withInversion(i, true);
        return matches ? curLevel : false
      } else if (Map.prototype.isPrototypeOf(curLevel)) subtrie = curLevel;
      else return false
    }
  }

  getTemperedInterval (n, d) { return this.#temperedIntervalSet.getRatio(n, d) }

  genChordGraph () { // Is the minimum chord adicity always 3?
    const adicityChords = Common.group([ ...this.chords ], (ch1, ch2) => ch1.adicity === ch2.adicity)
      .sort(([ch1], [ch2]) => ch1.adicity < ch2.adicity);
    if (adicityChords.length > 1)
      for (let i = 0; i < adicityChords.length - 1; i++)
        for (const chord of adicityChords[i]) {
          const { inversion, interpretation } = chord
          for (let int = 0; int < chord.interpretations; int++) {
            chord.interpretation = int;
            for (let inv = 0; inv < chord.adicity; inv++) {
              chord.inversion = inv;
              const mbSubch = this.getChordByIntervals([ chord.internalIntervals[2] ]
                .concat(chord.intervals.slice(2)).map(({ fraction }) => fraction));
              if (mbSubch) {
                chord.subchords.add(mbSubch);
                mbSubch.superchords.add(chord)
              }
            }
          }
          chord.interpretation = interpretation;
          chord.inversion = inversion
        }
  }

}



class TemperedInterval {
  #temperament; enharmonicSet // Enharmonies are like tempered dyadic chords...
  constructor ({ temperament, enharmonicSet }) {
    if (!(Temperament.prototype.isPrototypeOf(temperament))) throw new Error("TemperedInterval error: must provide Temperament object");
    if (!(Set.prototype.isPrototypeOf(enharmonicSet)) || !Common.between(1, 2, enharmonicSet.size)) throw new Error("Bad enharmonic set");
    this.#temperament = temperament;
    this.enharmonicSet = enharmonicSet;
    const [ number, roman, romanlow, letter, fraction ] = [ ...enharmonicSet ]
      .map(({ noteSpelling: { number, roman, romanlow, letter }, fraction: [ n, d ] }) =>
        [ number, roman, romanlow, letter, `<sup>${n}</sup>⁄<sub>${d}</sub>` ])
      .reduce((fst, snd) => fst.map((str, i) => `(${str}≅${snd[i]})`));
    this.noteSpelling = { number, roman, romanlow, letter, fraction }
  }
}



class TemperedIntervalSet {
  #rawMap = new Map() // Map([ denominator, Map([ numerator, temperedInterval ]) ])
  constructor ({ temperament, temperedIntervalSet }) {
    if (!(Temperament.prototype.isPrototypeOf(temperament))) throw new Error("TemperedIntervalSet error: must provide Temperament object");
    this.temperament = temperament;
    if (temperedIntervalSet) for (const tiv of temperedIntervalSet) this.add(tiv);
    else {
      const { intervalSet, enharms } = temperament;
      for (const iv of intervalSet) {
        const enh = enharms.get(iv);
        if (enh) this.add(new TemperedInterval({ temperament, enharmonicSet: new Set([ iv, enh ]) }));
        else this.add(new TemperedInterval({ temperament, enharmonicSet: new Set([ iv ]) }))
      }
    }
  }
  add (tiv) {
    for (const iv of tiv.enharmonicSet) {
      const { n, d } = iv, dMap = this.#rawMap.get(d) ?? this.#rawMap.set(d, new Map()).get(d);
      dMap.has(n) || dMap.set(n, tiv)
    }
    return tiv
  }
  has (tiv) {
    const { n, d } = tiv.enharmonicSet.values().next().value;
    return this.#rawMap.get(d)?.get(n).enharmonicSet.symmetricDifference(tiv.enharmonicSet).size === 0
  }
  hasRatio (n, d) {
    n = BigInt(n); d = BigInt(d);
    const c = Common.gcd(n, d);
    return this.#rawMap.get(Common.non2(d / c))?.has(Common.non2(n / c)) ?? false
  }
  getRatio (n, d) {
    n = BigInt(n); d = BigInt(d);
    const c = Common.gcd(n, d);
    return this.#rawMap.get(Common.non2(d / c))?.get(Common.non2(n / c))
  }
}



class Chord {
  // A tempered chord has a natural temperament, but is compatible with any temperament with it as a factor
  // * Should factor temperaments be added to mapping.temperaments?
  static types = [ "harmonic series", "essentially tempered" ]
  static fromRepr = ({ keyboard, mapping, type, voicing, chordRaw: { edo, limit, nd, dd, internalIntervalsRaw } }) => {
    if (keyboard.edo !== edo) throw new Error("Unhandled - chord edo different to current edo");
    if (keyboard.scale.limit !== limit) throw new Error("Unhandled - chord limit different to current limit");
    const intervalsRaw = internalIntervalsRaw.map(interp => interp.map(ivs => ivs[1]));
    const frac = intervalsRaw[0].reduce(([a, b], [c, d]) => [a * c, b * d], [1n, 2n]);
    if (Common.bigLog2(frac[0]) < Common.bigLog2(frac[1])) frac.reverse();
    const iv = mapping.commas.addRatio(...frac).withOctave(0);
    if (Common.mod(mapping.steps(iv), edo) !== 0) throw new Error("Unhandled - chord comma not tempered");
    if (!mapping.temperaments.has(iv)) throw new Error("Unhandled - chord temperament not yet loaded");
    const ivset = mapping.lattice.properIntervalSet, { n, d } = iv;
    if (n !== Common.comp(nd) || d !== Common.comp(dd)) throw new Error("Unhandled - comma / interval mismatch");
    return new Chord({ keyboard, mapping, type, voicing,
      internalIntervals: internalIntervalsRaw.map(interp => interp.map(ivs => ivs.map(iv => ivset.getRatio(...iv)))) })
  }
  #keyboard; #mapping; temperament; type; adicity
  #temperedIntervals; #internalTemperedIntervals; #intervals; #internalIntervals
  #interpretation; subchords; superchords
  harmonics; #harmonicIntervals; isSubHarm; #inversion
  voicing
  ord
  constructor ({ keyboard, mapping, type, harmonics, bass, isSubHarm = false, internalIntervals, voicing, ord }) {
    if (!(Keyboard.prototype.isPrototypeOf(keyboard))) throw new Error("Chord error: must provide Keyboard object");
    if (!(HarmonicMapping.prototype.isPrototypeOf(mapping))) throw new Error("Chord error: must provide HarmonicMapping object");
    this.#keyboard = keyboard;
    this.#mapping = mapping;
    if (typeof type !== "string" && !Chord.types.includes(type)) throw new Error("Chord error: unknown type");
    this.type = type;
    switch (type) {
      // Harmonic chords temper the unison
      case "harmonic series":
      if (typeof bass !== "number" || !harmonics.includes(bass) || !("length" in harmonics) || !(harmonics.length > 1) ||
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
        mapping.lattice.properIntervalSet.getRatio(harmonics[(i + j) % len], 1).withOctave(i + j >= len).fraction));
      this.temperament = mapping.temperaments.get(mapping.commas.getRatio(1, 1)) // Unify
      break
    case "essentially tempered":
      // TODO test iv membership in lattice.intervalSet?
      if (!("length" in internalIntervals) || !(internalIntervals.length > 0) ||
        internalIntervals.slice(1).reduce(([len, b], ivs) => b || ivs.length !== len, [ internalIntervals[0].length, false ])[1] ||
        internalIntervals.some(interp => !("length" in interp) || !(interp.length > 1) ||
          interp.some((ivs, _, ar) => !("length" in ivs) || ivs.length !== ar.length ||
            !ivs.every(iv => Interval.prototype.isPrototypeOf(iv)))))
        throw new Error("Chord error: malformed interval data");
      this.adicity = internalIntervals[0].length;
      this.voicing = voicing ?? Array(this.adicity).fill(0);
      this.#interpretation = 0;
      this.#inversion = 0;
      const
        { temperament } = mapping, // Can a chord ever be created when the temperament is different? Refactor this
        internalTemperedIntervals = this.#internalTemperedIntervals = internalIntervals[0]
          .map(ivs => ivs.map(({ fraction: [n, d] }) => temperament.getTemperedInterval(n, d)));
      this.temperament = temperament;
      
      this.#internalIntervals = internalIntervals;
      this.#intervals = [ this.#internalIntervals[0].map(ivs => ivs[1]) ];
      const intervals = this.#intervals[0]
      
      this.ord = ord ?? [ intervals.length, ...intervals
        .map(({ fraction: [n, d] }, i) => {
          const v = 2 ** (Common.bigLog2(n) - Common.bigLog2(d));
          return i ? 2 - v : v
        }) ];
      this.#temperedIntervals = internalTemperedIntervals.map(ivs => ivs[1]);

      // Check if symmetric - move to chordgen
      this.inverse = this;
      // Levenshtein neighbour graph
      this.subchords = new Set();
      this.superchords = new Set();

      this.#genNames()
    }
  }
  // TODO verify
  addInterpretation (chord) {
    this.#internalIntervals = this.#internalIntervals.concat(chord.#internalIntervals);
    this.#intervals = this.#intervals.concat(chord.#intervals);
    this.#names = this.#names.concat(chord.#names);
  }
  get interpretation () { return this.#interpretation }
  set interpretation (i) { this.#interpretation = Common.mod(i, this.#internalIntervals.length) }
  get interpretations () { return this.#internalIntervals.length }
  set interpretations (_) {}

  get inversion () { return this.#inversion }
  set inversion (i) { this.#inversion = Common.mod(i, this.adicity) }

  get intervals () {
    const
      inv = this.#inversion, { type } = this,
      ivs = type === "harmonic series" ? this.#harmonicIntervals :
        type === "essentially tempered" ? this.#intervals[this.#interpretation] : []
    return ivs.toSpliced(0, inv).concat(ivs.toSpliced(inv))
  }
  set intervals (_) {}

  get internalIntervals () {
    const { properIntervalSet } = this.#mapping.lattice;
    return this.type === "harmonic series" ?
      this.#internalIntervals[this.#interpretation][this.#inversion].map(iv => properIntervalSet.getRatio(...iv)) :
      this.type === "essentially tempered" ? this.#internalIntervals[this.#interpretation][this.#inversion].slice() : []
  }
  set internalIntervals (_) {}

  get temperedIntervals () {
    if (this.type === "harmonic series") return null;
    const inv = this.#inversion, ivs = this.#temperedIntervals;
    return ivs.toSpliced(0, inv).concat(ivs.toSpliced(inv))
  }
  set temperedIntervals (_) {}

  get internalTemperedIntervals () { return this.#internalTemperedIntervals[this.#inversion].slice() }
  set internalTemperedIntervals (_) {}

  #names
  #genNames () {
    if (this.type === "harmonic series") return;
    const
      { temperament } = this, { intervalSet, lattice } = this.#mapping, { harmonicList } = lattice,
      harms = new Set(temperament.hdecomp.map(([h]) => BigInt(h))).add(1n), interps = this.#internalIntervals,
      tonalities = interps.map(interp => interp.map(ivs => {
        const [ n, d ] = ivs[1].splitDecomp, [ [ ov, ol, op ], [ uv, ul, up ] ] = ivs.slice(2).reduce((brs, { n, d }, i) => {
          const ix = i + 2;
          return brs.map((sidebrs, s) => {
            const hVal = Number(s ? d : n), hNum = hVal === 1 ? [] : harmonicList.get(hVal)?.primeDecomp, h = [ hNum, [] ];
            return hNum ? sidebrs.reduce((acc, [ lixs, rixs, llcm, rlcm ]) => {
              const newLlcm = Common.splitLCM(llcm, h), newRlcm = Common.splitLCM(rlcm, h);
              if (lixs.size === 0 || harms.has(Common.comp(newLlcm[0]))) acc.push([ new Set(lixs).add(ix), rixs, newLlcm, rlcm ]);
              if (rixs.size === 0 || harms.has(Common.comp(newRlcm[0]))) acc.push([ lixs, new Set(rixs).add(ix), llcm, newRlcm ]);
              return acc
            }, []) : []
          })
        }, [ [ [ new Set([1]), new Set(), [ n, [] ], [[], []] ] ], [ [ new Set([1]), new Set(), [ d, [] ], [[], []] ] ] ])
          .map((candidates, s) => candidates
            .reduce(([ acc, len ], candidate) => {
              const [ lixs, rixs ] = candidate, thisLen = Math.max(lixs.length, rixs.length);
              return thisLen < len ? acc : thisLen > len ? [ [candidate], thisLen ] : [ acc.concat([candidate]), len ]
            }, [[], 0])[0]
            .reduce(([v, len, a], [ lixs, rixs, llcm, rlcm ]) => {
              const
                thisLen = Math.max(lixs.size, rixs.size),
                livs = ivs.filter((_, i) => !i || lixs.has(i)), rivs = ivs.filter((_, i) => !i || rixs.has(i)),
                m = Common.bigMax([
                  ...(livs.length > 2 ? livs : livs.slice(0, 1)).map(({ splitDecomp: dec }) => Common.comp(Common.splitMult(s ? dec : dec.toReversed(), llcm)[0])),
                  ...(rivs.length > 2 ? rivs : rivs.slice(0, 1)).map(({ splitDecomp: dec }) => Common.comp(Common.splitMult(s ? dec : dec.toReversed(), rlcm)[0]))
                ]);
              const inLat = harmonicList.has(Number(m)), hasHarms = thisLen !== 1;
              return inLat && thisLen > len ? [ m, thisLen, [[ livs, rivs ]] ] : inLat && thisLen < len ? [v, len, a] :
                hasHarms && m < v ? [ m, len, [[ livs, rivs ]] ] : hasHarms && m > v ? [v, len, a] : [ v, len, a.concat([[ livs, rivs ]]) ]
            }, [ Infinity, 0, [] ]));
        return [ ol < ul ? 1 : ol > ul ? -1 : ov > uv ? 1 : ov < uv ? -1 : 0, op, up ]
      })),
      names = interps.map((interp, inv) => {
        const interpNames = interp.map((ivs, int) => {
          const
            [ q, op, up ] = tonalities[inv][int], ns = { built: new Set(), default: ivs.map(iv => iv.noteSpelling.letter).join(" ") },
            genNames = (chs, q) => chs.map(([ livs, rivs ]) => {
              const { 2: single = [], 0: harm = [] } = Common.groupBy([ livs, rivs ], ivs => ivs.length <= 2 ? ivs.length : 0)
              if (!harm.length) return [];
              const
                harmParts = harm.map(bin => {
                  const
                    splitSubch = bin.map(({ splitDecomp }) => splitDecomp), [ nDec, dDec ] = Common.splitLCM(...splitSubch.slice(1)).with(q, []),
                    root = intervalSet.addRatio(Common.comp(nDec), (q ? 3n : 1n) * Common.comp(dDec)),
                    harmSeq = splitSubch.map(frac => Common.splitMult(frac, [dDec, nDec]).map(hDec => Number(Common.comp(hDec))))
                      .reduce((acc, frac) => {
                        let n = frac[q], ln = Math.log2(n), lf = Math.log2(acc.at(-1) ?? 1);
                        if (q) {
                          if (ln > lf) acc = acc.map(v => v * 2 ** Math.ceil(ln - lf));
                          else n *= 2 ** Math.max(0, Math.floor(lf - ln))
                        } else {
                          if (lf > ln) n *= 2 ** Math.ceil(lf - ln);
                          else acc = acc.map(v => v * 2 ** Math.max(0, Math.floor(ln - lf)))
                        }
                        return acc.concat([n])
                      }, []);
                  return root.noteSpelling[q ? "romanlow" : "roman"] + " " + harmSeq.join(":")
                }),
                addPart = single.map(([, iv]) => " add" + iv.noteSpelling.number); // length in [0, 1]
              return [ harmParts.join(" / ") + addPart.join("") ]
            }).flat();
          q !== -1 && genNames(up, 0).forEach(n => ns.built.add(n));
          q !== 1 && genNames(op, 1).forEach(n => ns.built.add(n));
          return ns
        });
        return interpNames.map(ns => ns.built.size === 0 ? new Set([ ns.default ]) : ns.built)
      });
    this.#names = names
  }
  get chordName () {
    if (this.type === "essentially tempered") return this.#names[this.#interpretation][this.#inversion]
  }

  #inverse
  get inverse () { return this.#inverse }
  set inverse (chord) {
    const { adicity } = this;
    if (adicity !== chord.adicity) return false;
    const { inversion } = chord, { intervals } = chord.withInversion(0, true);
    if (this.#intervals.every(interp => interp.some((iv, i) => iv !== intervals[i ? adicity - i : 0]))) return false;
    this.#inverse = chord.withInversion(inversion, true)
  }

  get #repr () {
    const { type, harmonics, voicing } = this;
    let opts = { type, inversion: this.#inversion, voicing }
    if (type === "harmonic series") Object.assign(opts, { harmonics, bass: harmonics[0], isSubHarm: this.isSubHarm });
    else if (type === "essentially tempered") opts.internalIntervals = this.#internalIntervals;
    return opts
  }
  set #repr (_) {}

  toString () {
    const { internalIntervals, ...opts } = this.#repr;
    if (internalIntervals) opts.internalIntervalsRaw = internalIntervals.map(interps => interps.map(ivs => ivs.map(iv => iv.fraction.map(String))));
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
    throw new Error("stop");
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



export { HarmonicMapping, Temperament, TemperedInterval, TemperedIntervalSet, Chord }