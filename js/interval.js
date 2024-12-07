import Common from "./common.js";

class IntervalSet {
  stepsBasis; edo; #rawMap // Map([ denominator, Map([ numerator, interval ]) ])
  constructor ({ stepsBasis, edo, intervalSet, intervalList = [] }) {
    this.stepsBasis = stepsBasis;
    this.edo = edo;
    this.#rawMap = new Map();
    if (intervalSet) for (const interval of intervalSet) this.add(interval);
    else for (const [ n, d ] of intervalList) this.addRatio(n, d)
  }
  add (interval) {
    const { n, d } = interval, dMap = this.#rawMap.get(d) ?? this.#rawMap.set(d, new Map()).get(d);
    return (dMap.has(n) ? dMap : dMap.set(n, interval)).get(n)
  }
  addRatio (n, d) {
    return this.add(new Interval({ intervalSet: this, n: Number(n), d: Number(d) }))
  }
  has (interval) {
    const { n, d } = interval;
    return Boolean(this.#rawMap.get(d)?.has(n))
  }
  hasRatio (n, d) {
    const c = Common.gcd(n, d);
    return Boolean(this.#rawMap.get(Common.non2(d / c))?.has(Common.non2(n / c)))
  }
  get (interval) {
    const { n, d } = interval;
    return this.#rawMap.get(d)?.get(n)
  }
  getRatio (n, d) {
    const c = Common.gcd(n, d), iv = this.#rawMap.get(Common.non2(d / c))?.get(Common.non2(n / c));
    return iv?.withOctave(Math.floor(Math.log2(n / d)))
  }
  * [ Symbol.iterator ] () { for (const [ , s ] of this.#rawMap) for (const [ , iv ] of s) yield iv }
}

class Interval {
  #intervalSet; n; d; octave; fraction; decomp; noteSpelling
  octaveAdjust; splitDecomp
  constructor ({ intervalSet, n, d}) {
    if (!(IntervalSet.prototype.isPrototypeOf(intervalSet))) throw new Error("Interval error: must provide IntervalSet object");
    const c = Common.gcd(n, d);
    n = n / c;
    d = d / c;
    if (intervalSet.hasRatio(n, d)) return intervalSet.getRatio(n, d).withOctave(0); // TODO remove withOctave here
    this.#intervalSet = intervalSet;
    this.n = Common.non2(n);
    this.d = Common.non2(d);
    const
      isBig = typeof n === "bigint",
      log2 = isBig ? Common.bigLog2 : Math.log2,
      decomp = Common[isBig ? "decompBig" : "decomp"];
    this.octave = Math.floor(log2(this.n) - log2(this.d));
    const octave = this.octave = isBig ? BigInt(this.octave) : this.octave;
    this.octaveAdjust = octave;
    this.fraction = [ octave < 0 ? n << -octave : n, octave > 0 ? d << octave : d ];
    // this.decomp = mapping.decomp(n, d)(...params); // TODO: BigInt

    const pdec = decomp(n).concat([ new Map() ]);
    if (d) {
      for (const [ p, rad ] of decomp(d)[0]) if (pdec[0].has(p)) {
        const nrad = pdec[0].get(p);
        if (nrad <= rad) pdec[0].delete(p);
        if (nrad > rad) pdec[0].set(p, nrad - rad);
        else if (nrad < rad) pdec[1].set(p, rad - nrad);
      } else pdec[1].set(p, rad)
    }
    this.splitDecomp = pdec.map(m => [ ...m ].sort(([a], [b]) => a > b));
    this.decomp = this.splitDecomp.reduce((n, d) => n.concat(d.map(([ p, rad ]) => [p, -rad])))
      .sort(([a], [b]) => a > b);
    this.noteSpelling = Common.noteFromFactors(this.splitDecomp)
  }
  withOctave (o, mutate = false) {
    const
      octave = this.octaveAdjust = this.octave - o,
      { n, d } = this;
    this.fraction = [ octave < 0 ? n << -octave : n, octave > 0 ? d << octave : d ];
    return this
  }
  steps () {
    const { stepsBasis, edo } = this.#intervalSet;
    return this.decomp.reduce((acc, [p, rad]) => acc + stepsBasis.get(p) * rad, 0) - Number(this.octaveAdjust) * edo
  }
  inverse () { return this.#intervalSet.addRatio(this.d, this.n) }
}

export { IntervalSet, Interval }