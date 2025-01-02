import Common from "./common.js";



// Finds multiplicative decompositions of rational numbers using a given set of divisors
class HarmonicLattice { // is commas on the lattice??

  // Static
  static #isPrime (pdec) {
    let sum = 0;
    for (const rad of pdec.values()) sum += rad;
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

  params = []; index = []; indexPrimes = []; primes = []; harmonicList = new Map(); verify = () => true
  properIntervalSet; ready = false
  constructor ({ harmsRaw }) {
    this.properIntervalSet = new IntervalSet();

    const
    //  { maxError } = scale,
      decs = Common.decomp(...harmsRaw).map((pdec, i) => [ harmsRaw[i], pdec ]),
      { true: primeDecs = [], false: compositeDecs = [] } = Common.groupBy(
        decs, ([, a]) => HarmonicLattice.#isPrime(a)),
      { true: simpleDecs = [], false: residueDecs = [] } = Common.groupBy(
        compositeDecs.map(([ h, pdec ]) => [ h, [...pdec].filter(([p]) => !~primeDecs.findIndex(([q]) => q === p)) ]),
        ([ , pp ]) => pp.length === 0, ([p]) => compositeDecs.find(([q]) => q === p)),
      ps = [ ...residueDecs.reduce((acc, [, pdec]) => {
        for (const [p] of pdec) acc.add(p);
        return acc
      }, new Set()).values() ].sort((a, b) => a > b),
      { true: residuePrimeDecs = [], false: simplePrimeDecs = [] } = Common.groupBy(
        primeDecs, ([p]) => ps.includes(p)),
      residue = residuePrimeDecs.concat(residueDecs);
      
    this.indexPrimes = ps;
    this.primes = simplePrimeDecs.map(([h]) => h);

    simplePrimeDecs.forEach(([h]) => this.harmonicList.set(h, new Harmonic({ lattice: this, order: h,
      countingFn: (...params) => params[ simplePrimeDecs.findIndex(([p]) => p === h) ] })));
    simpleDecs.forEach(([h, hdec]) => {
      // const
      //   just = Math.log2(h) % 1,
      //   steps = [ ...hdec ].reduce((acc, [p, rad]) => acc + hmap.get(p) * rad, 0) % edo,
      //   error = (steps / edo - just) * 1200;
      // if (Math.abs(error) >= maxError || steps + edo * maxError / 1200 < 1 ||
      //   steps - edo * maxError / 1200 > edo - 1) hmap.delete(i);
      // else
      this.harmonicList.set(h, new Harmonic({ lattice: this, order: h }))
    });

    if (residue.length) {
      let system, best = 0, dims = -1;
      const cols = ps.length;
      for (const hs of HarmonicLattice.#subsets(residue)) { // TODO: memoise?
        const mat = [], rows = hs.length;
        for (const [, pdec] of hs) mat.push(ps.map(p => pdec.get(p) ?? 0));
        if (rows < cols) mat.splice(Infinity, Infinity, ...Array(cols - rows).fill().map(() => mat.at(-1).slice()));
        if (rows > cols) mat.forEach((row, i) => row.splice(Infinity, Infinity, ...(i < cols ? Array(rows - cols).fill(0) :
          Array(rows - cols).fill(0).with(i - cols, -1))));
        const { inv, det } = HarmonicLattice.#invDet(mat, hs, ps);
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
      for (const [, pdec] of hs) mat.push(ps.map(p => pdec.get(p) ?? 0));
      if (rows > cols) mat.forEach((row, i) => row.splice(Infinity, Infinity, ...(i < cols ? Array(rows - cols).fill(0) :
        Array(rows - cols).fill(0).with(i - cols, -1))));

      // TODO: Can I use det to exclude harmonics before running the counting function?
      const { mods, inv, det, lcm, verify } = HarmonicLattice.#invDet(mat, hs, ps);

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

      inv.forEach(([h, vec]) => this.harmonicList.set(h, new Harmonic({ lattice: this, order: h,
        countingFn: (...params) => {
          const rawNum = hs.reduce((a, _, i) => a + (params[i] ?? 0) * vec[i] * (mods[i]?.[1] ?? 1), 0);
          return rawNum % lcm ? null : rawNum / lcm // Null means failure
        } }), true));
      residue.filter(([d]) => !~inv.findIndex(([h]) => h === d)) // Does this ever delete hmap keys?
        .forEach(([h, dec]) => {
          // if (~residueDecs.findIndex(([p]) => p === h)) {
          //   const
          //     just = Math.log2(h) % 1,
          //     primeVec = this.indexPrimes.map(p => dec.get(p) ?? 0),
          //     steps = this.index.reduce(
          //       (count, h) => count + hmap.get(h) * this.harmonicList.get(h).countingFn(...primeVec),
          //       this.primes.reduce((count, p) => count + hmap.get(p) * (dec.get(p) ?? 0), 0)) % edo,
          //     error = (steps / edo - just) * 1200;
          //   if (Math.abs(error) >= maxError || steps + edo * maxError / 1200 < 1 ||
          //     steps - edo * maxError / 1200 > edo - 1) {
          //     hmap.delete(i); // ??
          //     return
          //   }
          // }
          this.harmonicList.set(h, new Harmonic({ lattice: this, order: h }))
      })
    }

    const withUnison = [1].concat(harmsRaw);
    for (const n of withUnison) for (const d of withUnison) {
      this.properIntervalSet.addRatio(n, d);
      if (d === 1 && n !== 1) this.harmonicList.get(n).withQuality("harmonic", true)
    }
    // this.ready = true
  }

  decomp (n, d) { //Null is failure
    n = BigInt(n);
    const pdec = Common.decompBig(n)[0], dec = [];
    if (d) {
      d = BigInt(d);
      for (const [p, rad] of Common.decompBig(d)[0]) if (pdec.has(p)) {
        const nrad = pdec.get(p);
        if (nrad === rad) pdec.delete(p);
        else pdec.set(p, nrad - rad)
      } else pdec.set(p, -rad)
    }
    const { index, indexPrimes, primes, harmonicList, verify } = this;
    for (const p of primes) {
      if (!pdec.has(p)) continue;
      else dec.push([ p, pdec.get(p) ]);
      pdec.delete(p)
    }
    const primeVec = indexPrimes.map(p => pdec.get(p) ?? 0);
    for (const [p] of pdec) if (!indexPrimes.includes(p)) return null;
    if (!verify(...primeVec)) return null;
    return index.reduce((fn, h) => (...params) => {
      const acc = fn(...params);
      if (acc === null) return null;
      const res = harmonicList.get(h).countingFn(...primeVec, ...params);
      return res === null ? null : res === 0 ? acc : acc.concat([[ h, res ]])
    }, () => dec)
  }
}



class Harmonic {
  // countingFn counts the number of this harmonic required to form the given product, in this lattice
  #lattice; order; isBasis; countingFn = null; decomp; primeDecomp
  isSubHarm = false; label
  constructor ({ lattice, order, countingFn, isSubHarm = false }) {
    if (!(HarmonicLattice.prototype.isPrototypeOf(lattice))) throw new Error("Harmonic error: must provide HarmonicLattice object");
    this.#lattice = lattice;
    this.order = order;
    this.isSubHarm = isSubHarm;
    this.primeDecomp = [ ...Common.decomp(order)[0] ];
    if (order === 1) { // Unison
      this.isBasis = false;
      this.decomp = () => []
    } else {
      const
        { /*nonHarmonics,*/ index, primes } = lattice;
        // doErr = () => { throw new Error("Harmonic not in mapping") };
      if (lattice.ready) {
        let decomp = mapping.decomp(order); // lattice.decomp
        // if (nonHarmonics.has(order) || decomp === null) doErr();
        this.isBasis = false;
        this.decomp = decomp
      } else {
        if (this.isBasis = primes.concat(index).includes(order)) this.countingFn = countingFn;
        else this.decomp = lattice.decomp(order)()
      }
    }
  }
  withQuality (q, mutate = false) {
    if (!["harmonic", "subharmonic"].includes(q)) return;
    const lattice = this.#lattice, { order } = this, isSubHarm = q === "subharmonic";
    if (mutate) {
      this.isSubHarm = isSubHarm;
      this.label = isSubHarm ?
        lattice.properIntervalSet.getRatio(1, order).noteSpelling.romanlow :
        lattice.properIntervalSet.getRatio(order, 1).noteSpelling.roman;
      return this
    } else return new Harmonic({
      lattice: this.#lattice, order: this.order, countingFn: this.countingFn, isSubHarm
    }).withQuality(q, true)
  }
}



class IntervalSet {
  #rawMap = new Map() // Map([ denominator, Map([ numerator, interval ]) ])
  constructor ({ intervalSet, intervalList = [] } = {}) {
    if (intervalSet) for (const interval of intervalSet) this.add(interval);
    else for (const [ n, d ] of intervalList) this.addRatio(n, d)
  }
  add (interval) {
    const { n, d } = interval, dMap = this.#rawMap.get(d) ?? this.#rawMap.set(d, new Map()).get(d);
    return (dMap.has(n) ? dMap : dMap.set(n, interval)).get(n)
  }
  addRatio (n, d) {
    n = BigInt(n); d = BigInt(d);
    return this.add(new Interval({ intervalSet: this, n, d }))
    // return this.add(new Interval({ intervalSet: this, n: Number(n), d: Number(d) }))
  }
  has (interval) {
    const { n, d } = interval;
    return Boolean(this.#rawMap.get(d)?.has(n))
  }
  hasRatio (n, d) {
    n = BigInt(n); d = BigInt(d);
    const c = Common.gcd(n, d);
    return this.#rawMap.get(Common.non2(d / c))?.has(Common.non2(n / c)) ?? false
  }
  get (interval) { // TODO remove?
    const { n, d } = interval;
    return this.#rawMap.get(d)?.get(n)
  }
  getRatio (n, d) {
    n = BigInt(n); d = BigInt(d);
    const
      c = Common.gcd(n, d), _n = Common.non2(d / c), _d = Common.non2(n / c),
      iv = this.#rawMap.get(_n)?.get(_d);
    return iv?.withOctave(Math.floor(Common.bigLog2(n) - Common.bigLog2(d)))
  }
  * [ Symbol.iterator ] () { for (const s of this.#rawMap.values()) for (const iv of s.values()) yield iv }
}



class Interval {
  #intervalSet; n; d; octave; fraction; decomp; noteSpelling
  octaveAdjust; splitDecomp
  constructor ({ intervalSet, n, d }) {
    if (!(IntervalSet.prototype.isPrototypeOf(intervalSet))) throw new Error("Interval error: must provide IntervalSet object");
    if (typeof n !== "bigint" || typeof d !== "bigint") throw new Error("Interval error: numerator and denominator type must be BigInt");
    const c = Common.gcd(n, d);
    n = n / c;
    d = d / c;
    if (intervalSet.hasRatio(n, d)) return intervalSet.getRatio(n, d).withOctave(0); // TODO remove withOctave here
    this.#intervalSet = intervalSet;
    this.n = n = Common.non2(n);
    this.d = d = Common.non2(d);
    this.octave = Math.floor(Common.bigLog2(n) - Common.bigLog2(d));
    const octave = this.octave = BigInt(this.octave);
    this.octaveAdjust = octave;
    const fraction = this.fraction = [ octave < 0 ? n << -octave : n, octave > 0 ? d << octave : d ];

    const pdec = Common.decompBig(n).concat([ new Map() ]);
    if (d) {
      for (const [ p, rad ] of Common.decompBig(d)[0]) if (pdec[0].has(p)) {
        const nrad = pdec[0].get(p);
        if (nrad <= rad) pdec[0].delete(p);
        if (nrad > rad) pdec[0].set(p, nrad - rad);
        else if (nrad < rad) pdec[1].set(p, rad - nrad);
      } else pdec[1].set(p, rad)
    }
    this.splitDecomp = pdec.map(m => [ ...m ].map(v => v.map(Number)).sort(([a], [b]) => a > b));
    this.decomp = this.splitDecomp.reduce((n, d) => n.concat(d.map(([ p, rad ]) => [p, -rad])))
      .sort(([a], [b]) => a > b);
    this.noteSpelling = { ...Common.noteFromFactors(this.splitDecomp), fraction: `<sup>${fraction[0]}</sup>⁄<sub>${fraction[1]}</sub>` }
  }
  withOctave (o, mutate = false) {
    const
      octave = this.octaveAdjust = this.octave - BigInt(o),
      { n, d } = this;
    this.fraction = [ octave < 0 ? n << -octave : n, octave > 0 ? d << octave : d ];
    return this
  }
  inverse () { return this.#intervalSet.addRatio(this.d, this.n).withOctave(0) }
}



export { HarmonicLattice, Harmonic, IntervalSet, Interval }