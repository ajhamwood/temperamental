import { Common, Iter, MultiSet, Index } from "./common.js";



// A scale is a necklace of k symbols chosen from an alphabet of n symbols,
//   with zero or more linear constraints on the value of the symbols

class Scale {

  // Static data & methods

  static #wordChars = "XYZWVUTSRQ";
  static get wordChars () { return Scale.#wordChars } static set wordChars (_) {}
  static #patChars = "BCHLMnpstw";
  static get patChars () { return Scale.#patChars } static set patChars (_) {}
  static #patOrder = [3, 7, 4, 8, 2, 5, 9, 0, 6, 1]; // Nonstandard order, has a more even distribution.
  static get patOrder () { return Scale.#patOrder.slice() } static set patOrder (_) {}
  static #accidChar = [["d", "A"], ["s", "S"], ["n", "W"]]
  static get accidChar () { return Scale.#accidChar.map(p => p.slice()) } static set accidChar (_) {}

  // Step symbol comparators
  static charCmp = (c0, c1) => {
    const i0 = new RegExp(c0).exec(this.#patChars)?.index, i1 = new RegExp(c1).exec(this.#patChars)?.index;
    if (i0 === undefined || i1 === undefined) return null; // Not comparable
    else return i0 > i1 ? -1 : i0 < i1 ? 1 : 0
  }
  static wordCharCmp = (c0, c1) => {
    const i0 = new RegExp(c0).exec(this.#wordChars)?.index, i1 = new RegExp(c1).exec(this.#wordChars)?.index;
    if (i0 === undefined || i1 === undefined) return null; // Not comparable
    else return i0 > i1 ? -1 : i0 < i1 ? 1 : 0
  }

  static wordInMode (str, mode = 0) { return str.slice(mode) + str.slice(0, mode) }
  // Find relative mode of two words, uncurried for partial application
  static findMode = word0 => {
    const sq = Array(word0.length).keys().map(i => Scale.wordInMode(word0, i)).toArray();
    return word1 => word0.length === word1.length ? sq.indexOf(word1) : -1
  }
  // Find rotation and mode of scale string with lowest lex order
  static primeLex = (w, chars) => {
    const
      isq = Array(w.length).keys().map(i => {
        const word = Scale.wordInMode(w, i);
        return [ word.split("").map(c => chars.indexOf(c)), word, i ]
      }).toArray(),
      [ , word, mode ] = isq.sort(([w0], [w1]) => w0 > w1)[0];
    return { word, mode }
  }

  static normaliseWord (str) {
    let symbols = [], remain = str, w = "", prev = str.length;
    while (remain.length) {
      const c = remain[0]
      remain = remain.replaceAll(remain[0], "")
      symbols.push([c, prev - (prev = remain.length)]);
    }
    if (symbols.length > Scale.#wordChars.length) return null;
    symbols = symbols.sort(([, a], [, b]) => a < b).map(([c]) => c);
    for (let i = 0; i < str.length; i++) w += Scale.#wordChars[symbols.indexOf(str[i])];
    const { word, mode } = Scale.primeLex(w, Scale.#wordChars);
    return { word, mode, renaming: symbols.reduce((m, c, i) => m.set(c, Scale.#wordChars[i]), new Map()) }
  }
  static renameSteps (ms, renaming) {
    return MultiSet.from(new Map(ms.keys().map(k => [renaming.get(k), ms.count(k)])))
  }
  static invertNormaliseWord ({ word, mode = 0, renaming }) {
    const inv = new Map(renaming.entries().map(([k, v]) => [v, k]));
    return Scale.wordInMode(word.split("").map(c => inv.get(c) ?? c).join(""), word.length - mode)
  }
  static normalisePattern (str) {
    let pcs = new Set(Scale.#patChars), syms = new Set(str), ord = [], res = "";
    if (syms.difference(pcs).size) return null;
    for (let c of Scale.#patChars) if (syms.has(c)) ord.push(c);
    const canon = Scale.#patOrder.slice(0, syms.size).sort();
    for (let c of str) res += Scale.#patChars[canon[ord.indexOf(c)]];
    return res
  }

  static wordToGenericIvsInMode (str) {
    return Array(str.length).fill(0).map((_, j) => ({
      degree: j,
      ivs: Array(Math.floor(str.length)).fill(0).map((_, i) => i + j + 1 > str.length ?
        str.slice(j) + str.slice(0, i + j + 1 - str.length) : str.slice(j, j + i + 1))
    }))
  }
  static wordToGenericIvs (str) {
    return Array(str.length).fill(0).map((_, i) =>
      Common.group(Array(str.length).fill(0).map((_, j) => ({
        degree: j,
        iv: new MultiSet((i + j + 1 > str.length ?
          str.slice(j) + str.slice(0, i + j + 1 - str.length) : str.slice(j, j + i + 1)).split(""))
      })), ({ iv: a }, { iv: b }) => a.equal(b))
      .map(ivs => ivs.reduce(({ iv, degrees }, { iv: iv0, degree }) =>
        ({ iv: iv ?? iv0, degrees: degrees.concat(degree) }), { iv: null, degrees: [] })))
  }

  static equalMapping (m0, m1) {
    if (m0.size !== m1.size) return null;
    return Boolean(Iter.genMaps(new Map(Scale.wordChars.split("").slice(0, m0.size).map(x => [x])))
      .find(ren => Common.mapCompose(ren, m1).entries().every(([c, m]) => m0.get(c).equal(m))))
  }
  static gensToMapping (gens) { return gens.reduce((m, g, i) => m.set(Scale.wordChars[i], g), new Map()) }

  static mappingToRanks (word, mapping) {
    return word.split("").reduce((ar, c, i) => ar.concat(i ? ar.at(-1).plus(mapping.get(c)) : mapping.get(c)), [new MultiSet()])
  }
  static ranksToMapping (ranks) {
    const [ b, w, m ] = ranks.slice(1).reduce(([b, word, mapping], ms, i) => {
      if (b) return [b];
      const span = ms.minus(ranks[i]);
      if (span === null) return [true];
      const j = mapping.findIndex(([, m]) => span.equal(m));
      if (!~j) mapping.push([Scale.wordChars[mapping.length], span]);
      word += (mapping[j] ?? mapping.at(-1))[0];
      return [false, word, mapping]
    }, [false, "", []]);
    if (b) return;
    const { word, renaming, mode } = Scale.normaliseWord(w);
    return { word: Scale.wordInMode(word, -mode), mapping: Common.mapCompose(renaming, new Map(m)) }
  }
  static multisetImage (ms, mapping) {
    return ms.repr.entries()
      .reduce((m, [c, n]) => m.plus(mapping.get(c).scalarMultiply(n)), new MultiSet())
  }
  static compositionToInterval (comp) {
    return MultiSet.from(new Map(comp.repr.entries().reduce(([c, r], [k, n]) => {
      for (let i = 0; i < n; i++) r.push([Scale.wordChars[c++], k]);
      return [c, r]
    }, [0, []])[1]))
  }
  static edoEmbedding (steps) {
    return new Map(steps.map((v, i) => [ Scale.wordChars[i], Scale.compositionToInterval(new MultiSet([v])) ]))
  }

  static wordsWithGenerators (fn, ms) {
    const
      { word, renaming } = Scale.normaliseWord([...ms].join("")),
      comp = new MultiSet(new MultiSet(word.split("")).repr.values());
    return fn(comp).map(word => Scale.invertNormaliseWord({ word, renaming }))
  }
  // No pattern version because pattern generators are not interchangeable
  static scalesWithGenerators (fn, ms, sv) {
    const
      { word, renaming } = Scale.normaliseWord([...ms].join("")),
      comp = new MultiSet(new MultiSet(word.split("")).repr.values());
    return fn(comp, sv).map(({ word, mappings }) => ({ word, mappings: mappings
      .map(m => new Map(m.entries().map(([k, v]) => [ k, Scale.renameSteps(v, renaming) ])))
    }))
  }



  // Scale generators

  static genByComposition (comp) { return Iter.genAllNecklaces(comp, Scale.#wordChars) }
  static genAllCompositions (arity, variety) {
    return new Map(Iter.partitions(arity, variety)
      .map(comp => [ comp, Scale.genByComposition(comp) ]))
  }
  // All billiard necklaces for the given word composition
  // TODO not seqPerms... compute n-dim epsilon for each region around vector axis
  static genBilliards (composition) {
    const
      comp = composition.values().toArray(),
      t = Array(comp.length).fill(.5), counter = Array(comp.length).fill(0),
      arity = Common.sum(comp), steps = [], e = Math.sqrt(Number.EPSILON);
    let n = 0;
    while (n < arity - 1) {
      const [is, d] = t.reduce(([is, v], x, j) => {
        const k = x / comp[j];
        return Math.abs(k - v) < e ? [is.concat(j), v] : k < v ? [[j], k] : [is, v]
      }, [[], 1]);
      t.forEach((v, j) => t[j] = is.includes(j) ? 1 : v - d * comp[j]);
      is.forEach(i => counter[i]++);
      steps.push(is);
      n += is.length
    }
    const last = comp.findIndex((x, i) => x !== counter[i]);
    ~last && steps.push([last]);
    return Common.quotient(
      Iter.seqPerms(steps).map(ar => ar.map(v => Scale.#wordChars[v]).join("")).toArray(),
      (w0, w1) => {
        const check = Scale.findMode(w0);
        return ~check(w1) || ~check(w1.split("").toReversed().join(""))
      }
    )
  }
  static genAllBilliards (arity, variety) {
    return new Map(Iter.partitions(arity, variety)
      .map(comp => [ comp, Scale.genBilliards(comp) ]))
  }

  static genPatternsByComposition (comp) {
    const
      s = comp.repr.entries().reduce(([m, cum], [k, c]) => [ m.set(k, Scale.#wordChars
        .slice(cum, cum + c).split("")), cum + c ], [ new Map(), 0 ])[0],
      sets = () => new Map(s.entries().map(([k, v]) => [k, v.slice()])),
      chars = Scale.normalisePattern(Scale.#patChars.slice(-comp.size));
    return Iter.genMultiPerms(comp).flatMap(ar => {
      const mapping = ar.reduce(([m, cs], k, i) =>
        [ m.set(cs.get(k).shift(), chars[i]), cs ], [ new Map(), sets() ])[0];
      return Iter.genAllNecklaces(comp, Scale.#wordChars).map(word =>
        word.split("").map(c => mapping.get(c)).join(""))
    })
  }
  static genAllPatterns (arity, variety) {
    return new Map(Iter.partitions(arity, variety).filter(comp => comp.size === variety)
      .map(comp => [ comp, Scale.genPatternsByComposition(comp) ]))
  }
  static genBilliardPatterns (comp) {
    const
      s = comp.repr.entries().reduce(([m, cum], [k, c]) => [ m.set(k, Scale.#wordChars
        .slice(cum, cum + c).split("")), cum + c ], [ new Map(), 0 ])[0],
      sets = () => new Map(s.entries().map(([k, v]) => [k, v.slice()])),
      chars = Scale.normalisePattern(Scale.#patChars.slice(-comp.size));
    return Iter.genMultiPerms(comp).flatMap(ar => {
      const mapping = ar.reduce(([m, cs], k, i) =>
        [ m.set(cs.get(k).shift(), chars[i]), cs ], [ new Map(), sets() ])[0];
      return Scale.genBilliards(comp).map(word =>
        word.split("").map(c => mapping.get(c)).join(""))
    })
  }
  static genAllBilliardPatterns (arity, variety) {
    return new Map(Iter.partitions(arity, variety).filter(comp => comp.size === variety)
      .map(comp => [ comp, Scale.genBilliardPatterns(comp) ]))
  }

  static * genAllScalesByComposition (comp, sv = comp?.size) {
    yield * Iter.genGensByComp(comp, sv, Scale.wordChars)
      .flatMap(gens => Iter.genDecompositions(new MultiSet([...comp].flatMap((n, i) => Scale.wordChars[i].repeat(n).split(""))), gens)
        .flatMap(m => Common.quotient(Iter.genAllNecklaces(m, Scale.wordChars).map(w => Scale.normaliseWord(w).word).toArray())
          .map(word => ({ word, mappings: Iter.genMaps(new MultiSet(word.split("")).repr, m).toArray() }))))
  }
  static * genBilliardScalesByCompositionRaw (comp, sv = comp?.size) {
    yield * Iter.genGensByComp(comp, sv, Scale.wordChars)
      .flatMap(gens => Iter.genDecompositions(new MultiSet([...comp].flatMap((n, i) => Scale.wordChars[i].repeat(n).split(""))), gens)
        .flatMap(comp => Scale.genBilliards(new MultiSet(comp.values().toArray().sort((a, b) => b - a)))
          .map(word => ({ word, comp, mappings: Iter.genMaps(new MultiSet(word.split("")).repr, comp).toArray() }))))
  }
  static * genBilliardScalesByComposition (comp, sv = comp?.size) {
    yield * Index.quotient(
      new Index({ address: ({ word, mapping }) => [ word, mapping ], done: ($0, $1, i) => i === 1, cmp: (a, b, i) => i ? Common.mapEq(a, b) : a === b }),
      Scale.genBilliardScalesByCompositionRaw(comp, sv).flatMap(({ word, comp, mappings }) => mappings.map(mapping => ({ word, comp, mapping }))),
      ({ word, comp }) => Iter.genMaps(new MultiSet(word.split("")).repr, comp).map(mapping => ({ word, mapping })).toArray())
  }



  // Constructor

  constructor ({ word, pattern, embedding, constraints, mode }) {
    if (embedding) this.#setEmbedding({ embedding, word, constraints });
    else if (pattern) this.#setPattern({ pattern, constraints });
    else if (word) this.#setWord({ word, constraints });
    else throw new Error("Scale error: must provide string as either word or pattern");
    if (parseInt(mode) === mode) this.mode = mode;

    return this
  }
  #repr () {
    const opt = {};
    opt.word = this.#word;
    if (this.#pattern) opt.pattern = this.#pattern;
    if (!this.intervals.constraints.isEmpty) opt.constraints = this.intervals.constraints;
    if (this.#mode !== undefined) opt.mode = this.#mode;
    return opt
  }
  clone () { return new Scale(this.#repr()) }



  // Accessors

  #word; #wordInMode
  get word () { return this.#wordInMode ?? (this.mode = this.primeMode, this.#wordInMode) }
  set word (_) {}
  // TODO subPO -> most in-edges
  #primeMode
  get primeMode () { return this.#primeMode ??= Common.mod(Scale.wordToGenericIvsInMode(this.#word)
    .sort(({ ivs: as }, { ivs: bs }) => {
      const
        // aCmp = as.map(a => bs.reduce((n, b) => n + (this.intervals.cmpg(this.intervals.getWord(a), this.intervals.getWord(b)) === 1), 0)),
        // bCmp = bs.map(b => as.reduce((n, a) => n + (this.intervals.cmpg(this.intervals.getWord(b), this.intervals.getWord(a)) === 1), 0));
        aCmp = as.map(a => bs.reduce((n, b) => n + (StepInterval.cmpCons(this.intervals.getWordIv(a).value, this.intervals.getWordIv(b).value, this.intervals.constraints) === 1), 0)),
        bCmp = bs.map(b => as.reduce((n, a) => n + (StepInterval.cmpCons(this.intervals.getWordIv(b).value, this.intervals.getWordIv(a).value, this.intervals.constraints) === 1), 0));
      return Common.arrCmp(aCmp, bCmp)
    })[0].degree + 1, this.modeCount) }
  set primeMode (_) {}

  #pattern; #patternInMode
  // get pattern () { return this.#pattern ? this.#patternInMode ?? (this.mode = this.primeMode, this.#patternInMode) : null }
  get pattern () { return this.intervals.isStepTotalOrder ?
    (this.#pattern ??= this.#word.split("").reduce((s, c) => s + this.patternDict.get(c), ""), this.#patternInMode) ??
      (this.mode = this.#mode ?? this.primeMode, this.#patternInMode) : null
  }
  set pattern (_) {}
  #patternDict
  get patternDict () { return this.intervals.isStepTotalOrder && (this.#patternDict ??= this.#genPatternDict()) }
  set patternDict (_) {}
  #genPatternDict () {
    const
      steps = this.getGenericIntervalClass(0),
      chars = Scale.normalisePattern(Scale.#patChars.slice(-steps.length));
    return this.#intervals.generic.values().filter(giv => steps.some(iv => giv.has(iv))).toArray()
      .reduce((m, giv, i) => {
        const eqs = giv.values().filter(iv => steps.includes(iv)).toArray();
        if (eqs.length === 1) return m.set([...eqs[0].value.keys()][0], chars.at(-i - 1));
        else for (let j = 0; j < eqs.length; j++) m.set([...eqs[j].value.keys()][0], chars.at(-i - 1) + String.fromCodePoint(0x2080 + j));
        return m
      }, new Map())
  }

  #embedding; #ranksInMode; #embeddingScale; #embeddingImage; #embeddingPreimage
  get embedding () { if (this.#embedding) return new Map(this.#embedding) }
  set embedding (_) {}
  get ranks () { return this.#ranksInMode ?? (this.mode = this.primeMode, this.#ranksInMode) }
  set ranks (_) {}
  get embeddingScale () { if (this.#embedding) return this.#embeddingScale }
  set embeddingScale (_) {}
  getEmbeddingImage (iv) {
    if (!this.#embedding) return;
    const { intervals } = this;
    if (typeof iv === "string") iv = new MultiSet(iv.split(""))
    iv = intervals.values().find(iv0 => iv0.value.equal(iv) || iv0.value === iv) ?? iv;
    if (!this.#embeddingImage) {
      this.#embeddingImage = new Map();
      for (const iv of intervals) {
        const imIv = this.embeddingScale.intervals.getBagIv(Scale.multisetImage(iv.value, this.#embedding));
        this.#embeddingImage.set(iv, imIv)
      }
    }
    return this.#embeddingImage.get(iv)
  }
  getEmbeddingPreimage (iv) {
    if (!this.#embedding) return;
    const { intervals } = this.embeddingScale;
    if (typeof iv === "string") iv = new MultiSet(iv.split(""));
    iv = intervals.values().find(iv0 => iv0.value.equal(iv) || iv0.value === iv) ?? iv;
    if (!this.#embeddingPreimage) {
      this.#embeddingPreimage = new Map();
      this.getEmbeddingImage();
      for (const iv of intervals) {
        const preimIv = new Set(this.#embeddingImage.entries().flatMap(([preimIv, imIv]) => imIv.equal(iv) ? [preimIv] : []));
        this.#embeddingPreimage.set(iv, preimIv)
      }
    }
    return this.#embeddingPreimage.get(iv)
  }

  #mode; #givsInMode; #ivRanks
  set mode (mode) {
    mode = Common.mod(mode, this.modeCount);
    if (isNaN(mode)) throw new Error("Scale error: bad mode value");
    this.#mode = mode;
    this.#wordInMode = Scale.wordInMode(this.#word, mode);
    if (this.#pattern) this.#patternInMode = Scale.wordInMode(this.#pattern, mode);
    if (this.#intervals) this.#givsInMode = Scale.wordToGenericIvsInMode(this.#word)[mode].ivs.map(str => this.intervals.getWord(str));
    if (this.#embedding) this.#ranksInMode = Scale.mappingToRanks(this.#wordInMode, this.#embedding)
  }
  get mode () { return this.#mode ?? (this.mode = this.primeMode) }
  get genericIvs () { return this.#intervals && this.#mode ? this.#givsInMode.slice() : (this.intervals, this.mode, this.#givsInMode.slice()) }
  set genericIvs (_) {}
  getIvRanks (iv) {
    iv = this.intervals.getWord(iv) ?? this.intervals.get(iv) ?? iv;
    if (!this.#ivRanks) {
      const { mode } = this;
      this.#ivRanks = new Map();
      for (let i = 0; i < this.modeCount; i++) {
        this.mode = i;
        for (const iv of this.#givsInMode)
          this.#ivRanks.set(iv, this.#ivRanks.get(iv) ?? new Set()).get(iv).add(this.mode);
      }
      this.mode = mode;
    }
    return new Set(this.#ivRanks.get(iv).values().map(i => Common.mod(i - this.mode, this.modeCount)).toArray().sort((a, b) => a - b))
  }

  #arity; get arity () { return this.#arity } set arity (_) {}
  #composition;
  get composition () { return MultiSet.from(this.#composition ??=
    new MultiSet(Common.group(this.#word.split("")).map(ar => ar.length))) }
  set composition (_) {}
  #variety;
  get variety () { return this.composition.size }
  set variety (_) {}
  #modeCount;
  get modeCount () { return this.#modeCount ??= Scale.findMode(this.#word)(Scale.wordInMode(this.#word, -1)) + 1 }
  set modeCount (_) {}

  #intervals; #genICs
  getGenericIntervalClass (n) { return (this.#genICs ?? this.#createIntervalStore().genICs)[n] }
  get intervals () { return this.#intervals ?? this.#createIntervalStore().intervals }
  set intervals (_) {}
  #isBalanced; get isBalanced () { return this.#isBalanced ?? this.#createIntervalStore().isBalanced } set isBalanced (_) {}

  #isDeepScale
  get isDeepScale () { return this.#isDeepScale ??= Math.floor((this.intervals.size + 1) / 2) ===
    new Set(this.intervals.generic.values().map(giv => giv.values()
      .reduce((s, iv) => (iv.degrees.forEach(d => s.add(d)), s), new Set()).size)).size }
  set isDeepScale (_) {}

  #gIvNames; #rankNames; #rothenberg
  getNames (iv) {
    if (!StepInterval.prototype.isPrototypeOf(iv)) return null;
    return (this.#gIvNames ?? this.#computePatternData().gIvNames).get(this.intervals.get(iv)).values()
      .map(({ rank, accid }) => accid + Common.ordinal(rank) +
        this.arity.toString().split("").map(n => String.fromCodePoint(0x2080 + parseInt(n))).join("")).toArray() }
  getRankNames (rank) {
    if (rank !== parseInt(rank)) return null;
    return Array.from((this.#rankNames ?? this.#computePatternData().rankNames)[rank])
      .map(({ rank, accid }) => accid + Common.ordinal(rank) +
        this.arity.toString().split("").map(n => String.fromCodePoint(0x2080 + parseInt(n))).join("")) }
  // TODO rothenberg, lumma stability on rank scales
  #computeRothenberg = (mins, maxes, strict) =>
    maxes.reduce((b, max, i) => b && mins.slice(i + 1).every(min => Common.pairwiseCmp(max, min, strict ?
      ((a, b) => [...a][0].store.cmpg(a, b) === -1) : ((a, b) => [...a][0].store.cmpg(a, b) < 1))), true) &&
    mins.reduce((b, min, i) => b && maxes.slice(0, i).every(max => Common.pairwiseCmp(min, max, strict ?
      ((a, b) => [...a][0].store.cmpg(a, b) === 1) : ((a, b) => [...a][0].store.cmpg(a, b) > -1))), true)
  get rothenberg () { return this.#rothenberg ?? this.#computePatternData().rothenberg }
  set rothenberg (_) {}



  // Instance data

  #constraints
  #setWord ({ word, constraints, mode = 0 }) {
    this.#constraints = constraints;
    this.#arity = word.length;

    let m; ({ word, mode: m } = Scale.normaliseWord(word));
    if (word === null) throw new Error("Scale error: word has too many unique symbols");
    this.#word = word;
    this.mode = mode - m
  }

  #setPattern ({ pattern, constraints, mode = 0 }) {
    pattern = Scale.normalisePattern(pattern);
    if (pattern === null) throw new Error("Scale error: pattern contains unrecognised step names");
    const
      { word, renaming, mode: m } = Scale.normaliseWord(pattern),
      cons = new Constraints(), is = Scale.#patOrder.slice(0, renaming.size).sort((a, b) => a - b);
    for (const [ patChar, wordChar ] of renaming) {
      const i = Scale.#patChars.indexOf(patChar), r = is.indexOf(i);
      if (i > is[0]) cons.insertLt([ new MultiSet([ wordChar ]), new MultiSet([ renaming.get(Scale.#patChars[ is[r - 1] ]) ]) ])
    }
    this.#setWord({ word, constraints: constraints?.combine(cons) ?? cons, mode: mode - m })
  }
  #computePatternData = () => {
    const
      { arity, intervals } = this, gicMaxes = [], gicMins = [], gicTOSubsets = [],
      baseGIvs = Scale.wordToGenericIvsInMode(this.#word)[this.primeMode].ivs.map(str => intervals.getWord(str));
    for (let i = 0; i < arity; i++) {
      // Needs: embedding ordering, base intervals
      let tOThis;
      if (this.#embedding) {
        const { tOSubsets } = this.embeddingScale.intervals.substore([...new Set(this.getGenericIntervalClass(i).map(iv => this.getEmbeddingImage(iv)))]);
        tOThis = tOSubsets.map(ss => new Set([...ss].map(([iv]) => this.embeddingScale.intervals.getBag(iv.value))))
        gicTOSubsets.push(tOSubsets.map(ss => new Set([...ss].flatMap(([iv]) => this.getEmbeddingPreimage(this.embeddingScale.intervals.getBagIv(iv.value))
          .values().flatMap(iv => this.getGenericIntervalClass(i).includes(iv) ? [intervals.get(iv)] : []).toArray()))))
      } else {
        const { tOSubsets } = intervals.substore(this.getGenericIntervalClass(i));
        tOThis = tOSubsets.map(ss => new Set([...ss].map(([iv]) => intervals.getBag(iv.value))))
        gicTOSubsets.push(tOThis);
      }
      gicMaxes.push(Array.from(tOThis.at(-1)));
      gicMins.push(Array.from(tOThis[0]));
    }
    const 
      rothFn = () => this.#rothenberg = this.#computeRothenberg(gicMins, gicMaxes, true) ? 1 :
        this.#computeRothenberg(gicMins, gicMaxes, false) ? 0 : -1,
      nameFn = () => {
        const rankNames = this.#rankNames = [], gIvNames = this.#gIvNames = new Map();
        intervals.generic.values().forEach(giv => gIvNames.set(giv, new Set()));
        if (this.#embedding && this.rothenberg >= 0) {
          for (let i = 0; i < this.embeddingScale.arity; i++) this.#rankNames[i] = new Set();
          const
            min = Math.min(...gicMins[0].map(giv => [...giv][0].value.size)),
            max = Math.max(...gicMaxes.at(-1).map(giv => [...giv][0].value.size));
          if (min > 0) {
            this.#rankNames[0].add({ rank: 1, accid: "" });
            this.#concatAccid([], { rank: 1, accid: "A" }, 1, 1, false, Array(Math.ceil((min - 1) / 2)).fill(0).map((_, i) => i + 1));
          }
          for (let i = 0; i < arity - 1; i++) {
            const
              // MultiSet.size for now, TODO embeddingScale.intervals.cmp/iv.store.cmp
              curMin = Math.min(...gicMins[i].map(giv => [...giv][0].value.size)),
              lower = curMin - Math.max(0, Math.floor((curMin - (i === 0 ? 0 :
                Math.max(...gicMaxes[i - 1].map(giv => [...giv][0].value.size))) - 1) / 2)),
              curMax = Math.max(...gicMaxes[i].map(giv => [...giv][0].value.size)),
              upper = curMax + Math.ceil(((i === arity - 2 ? this.embeddingScale.arity - 1 :
                Math.min(...gicMins[i + 1].map(giv => [...giv][0].value.size))) - curMax - 1) / 2);
            this.#concatAccid(gicTOSubsets[i], { rank: i + 2, accid: "" }, 0, 0, baseGIvs[i],
              Array(upper - lower + 1).fill(0).map((_, i) => i + lower))
          }
          if (max < this.embeddingScale.arity - 1) {
            this.#concatAccid([], { rank: arity + 1, accid: "d" }, 1, 0, false,
              Array(Math.ceil((this.embeddingScale.arity - max - 1) / 2)).fill(0)
                .map((_, i) => this.embeddingScale.arity - i - 1).reverse());
          }
          this.#gIvNames.get([...gicTOSubsets.at(-1)[0]][0]).add({ rank: arity + 1, accid: "" })
        }
        else for (let i = 0; i < arity; i++)
          this.#concatAccid(gicTOSubsets[i], { rank: i + 2, accid: "" }, 0, 0, baseGIvs[i]);
        return { gIvNames, rankNames }
      };
    return (this.#computePatternData = () => ({
      get rothenberg () { return rothFn() },
      get gIvNames () { return nameFn().gIvNames },
      get rankNames () { return nameFn().rankNames }
    }))()
  }
  // Interval name by recursive splitting of ordering, relative to scale
  #concatAccid (ar, name, level, bias, init, ranks) {
    if (ar.length === 0 && !ranks?.length) return;
    const
      si = init ? ar.findIndex(givs => givs.has(init)) :
        ar.length % 2 === 0 ? Math.max(0, ar.length / 2 + bias - 1) : (ar.length - 1) / 2,
      left = ar.slice(0, si), right = ar.slice(si + 1), leftRanks = [], rightRanks = [];
    let ri;
    if (ranks?.length) {
      ri = ar.length ?
        ranks.findIndex(r => ar[si].values().find(giv => r === this.getEmbeddingImage([...giv][0]).value.size)) :
        ranks.length % 2 === 0 ? ranks.length / 2 + bias - 1 : (ranks.length - 1) / 2;
      leftRanks.splice(0, 0, ...ranks.slice(0, ri));
      rightRanks.splice(0, 0, ...ranks.slice(ri + 1));
    }
    this.#concatAccid(left, Object.assign({}, name, { accid: (Scale.#accidChar[level]?.[0] ?? "-") + name.accid }), level + 1, bias, false, leftRanks);
    if (ar.length) if (ar[si].size > 1) Array.from(ar[si]).forEach((iv, j) => this.#gIvNames
      .get(iv).add(Object.assign({}, name, { accid: `(${Scale.#wordChars[j]})` + name.accid })));
    else this.#gIvNames.get([...ar[si]][0]).add(name);
    if (ranks?.length) this.#rankNames[ranks[ri]].add(name);
    this.#concatAccid(right, Object.assign({}, name, { accid: (Scale.#accidChar[level]?.[1] ?? "+") + name.accid }), level + 1, 1 - bias, false, rightRanks)
  }

  #setEmbedding ({ embedding, word, constraints }) {
    if (!Map.prototype.isPrototypeOf(embedding) || !embedding.entries().every(([c, m]) => ~Scale.wordChars.indexOf(c) &&
      MultiSet.prototype.isPrototypeOf(m) && m.repr.keys().every(mc => ~Scale.wordChars.indexOf(mc))))
      throw new Error("Scale error: embedding must be a Map from word chars to MultiSets of word chars");
    
    const { word: w, renaming, mode } = Scale.normaliseWord(word.split("").flatMap(c => [...embedding.get(c)]).join(""));
    embedding = new Map(embedding.entries()
      .map(([k, v]) => [ k, MultiSet.from(new Map(v.repr.entries().map(([c, n]) => [ renaming.get(c), n ]))) ]));
    this.#embedding = embedding;

    const
      embeddingScale = this.#embeddingScale = ScaleStore.get(w)?.scale ?? new Scale({ word: w }),
      gens = embedding.entries().map(([c, m]) => [...embeddingScale.intervals.getBag(m)][0]),
      store = embeddingScale.intervals.substore(gens);
    if (store.isTotalOrder) {
      const
        chars = Scale.normalisePattern(Scale.#patChars.slice(-embedding.size)),
        mapping = new Map([...store].map((iv, i) => [ embedding.entries().find(([, k]) => iv.value.equal(k))[0], chars.at(-i - 1) ]));
      this.#setPattern({ pattern: word.split("").map(c => mapping.get(c)).join(""), constraints, mode: -mode })
    } else this.#setWord({ word, constraints, mode: -mode });
    ScaleStore.addDescendant(this)
  }

  #createIntervalStore () {
    const
      gics = Scale.wordToGenericIvs(this.#word),
      isBalanced = this.#isBalanced = gics.every(ar => ar.length <= this.composition.size),
      ivs = new Map(), { arity } = this;
    for (let i = 0; i < gics.length; i++) for (const { iv, degrees: ds } of gics[i]) {
      const mbGiv = ivs.keys().find(iv1 => StepInterval.cmp(iv, iv1) === 0);
      if (mbGiv) {
        const { gic, degrees } = ivs.get(mbGiv);
        gic.add(i);
        for (const d of ds) degrees.add(d)
      } else ivs.set(iv, { gic: new Set([i]), degrees: new Set(ds.map(n => n % arity)) })
    }
    // Where is interval gic and degree set stored?
    const store = this.#intervals = new IntervalStore({ scale: this, constraints: this.#constraints });
    this.#constraints = undefined;
    for (const [ interval, { gic, degrees } ] of ivs) ivs.set(interval, new StepInterval({ store, interval, gic, degrees }));
    const genICs = this.#genICs = gics.map((gic, i) => gic.map(({ iv }) => ivs.entries().find(([iv1]) => iv.equal(iv1))[1]));
    for (const iv of Common.quotient(genICs.flat(), (a, b) => a.equal(b))) store.add(iv);
    store.finalise();
    if (this.#mode !== undefined) this.mode = this.#mode;
    return { genICs, intervals: store, isBalanced }
  }



  // Refinement (instance -> instance, mutators)

  withPattern (stepOrder) {
    let mapping;
    if (Array.prototype.isPrototypeOf(stepOrder)) {
      if (stepOrder.length < this.variety || !Common.zipCmp(stepOrder.toSorted(), Array(stepOrder.length).fill(0).map((_, i) => i))) return null;
      const chars = Scale.normalisePattern(Scale.#patChars.slice(-this.variety));
      mapping = stepOrder.reduce((m, n, i) => m.set(Scale.#wordChars[i], chars[n]), new Map());
    } else {
      if (!Map.prototype.isPrototypeOf(stepOrder) || stepOrder.entries().some(([k, v]) =>
        !Scale.#wordChars.includes(k) || !Scale.#patChars.includes(v))) return null;
      mapping = stepOrder
    }
    const pattern = this.#word.split("").map(c => Scale.#patChars[stepOrder.indexOf(Scale.#wordChars.indexOf(c))]).join("");
    return new Scale({ pattern, constraints: this.intervals.constraints.clone() })
  }
  // TODO use constraints
  genAllPatterns () {
    return Iter.genUniquePerms(Array(this.variety).keys().toArray()).map(ar => this.withPattern(ar))
  }

  withConstraint ({ eq, lt }) {
    if (!this.intervals.incomparables.some(inc => Constraints.symEqual(inc, eq ?? lt))) return null;
    const { eqs, lts } = this.intervals.constraints;
    return new Scale({ word: this.#word, pattern: this.#pattern,
      constraints: new Constraints({
        eqs: eqs?.map(([lhs, rhs]) => [ MultiSet.from(lhs),MultiSet.from(rhs) ]),
        lts: lts?.map(([lhs, rhs]) => [ MultiSet.from(lhs), MultiSet.from(rhs) ])
      }).insertEq(eq).insertLt(lt) })
  }

  allAncestors (sv = this.variety) {
    const
      ivs = Array.from(this.intervals.generic), { mode, arity, modeCount } = this, patterns = [],
      // modeMap: [unique [outerMode, innerMode]]
      rec = (mapping, mode, offset, pos) => {
        if (offset === arity) {
          const m = mapping.entries().toArray().sort(([a], [b]) => b - a);
          if (pos >= mapping.size) {
            const newMapping = m.map(([ivIx]) => ivIx);
            let i = 0, ix, word = "";
            while ((ix = m.findIndex(([, poss]) => poss[0] === i)) !== -1) {
              m[ix][1].shift();
              word += Scale.wordChars[ix];
              i++
            }
            const wMode = Scale.findMode([...word].reverse().join(""));
            for (const { word, mapping, modeMap } of patterns) {
              if (!Common.zipCmp(mapping, newMapping)) continue;
              const ix = wMode([...word].reverse().join(""));
              if (!~ix) continue;
              return modeMap.push([ mode, ix ])
            }
            patterns.push({ modeMap: [[ mode, 0 ]], mapping: newMapping, word })
          }
          return
        }
        let i = 1;
        while (offset + i <= arity) {
          this.mode = mode + offset;
          const
            ivIx = ivs.indexOf(this.genericIvs[i - 1]),
            m = new Map(mapping.entries().map(([k, v]) => [k, v.slice()]));
          if (~ivIx && (m.has(ivIx) || m.size < sv)) {
            m.set(ivIx, (m.get(ivIx) ?? []).concat(pos));
            rec(m, mode, offset + i, pos + 1)
          }
          i++
        }
      };
    this.mode = 0;
    const { word } = this, { mode: offset = 0 } = ScaleStore.getMode(word) ?? {};
    for (let i = 0; i < modeCount; i++) {
      rec(new Map(), i, 0, 0);
      this.mode = i + 1
    }
    if (mode) this.mode = mode;
    return patterns.map(({ word: w, modeMap, mapping: m }) => {
      const { word: wr, renaming, mode: mo } = Scale.normaliseWord(w);
      if (word === wr) return;
      return {
        word: wr,
        mapping: renaming.entries().reduce((ar, [from, to]) => ar.with(Scale.wordChars.indexOf(to),
          [...ivs[m[Scale.wordChars.indexOf(from)]]][0].value), Array(renaming.size)),
        modeMap: modeMap.map(([o, i]) => [ Common.mod(o - offset, modeCount), Common.mod(i - mo, wr.length) ]).sort()
      }
    }).filter(Boolean).sort(({ word: w0 }, { word: w1 }) => w1.length - w0.length).values();
  }

  // // TODO: genGensByComp -> billiards -> filter by inclusion, collect modes
  // billiardAncestors () {}

  // // TODO: iterate over outs the mappings which can still assign each gen to a different step,
  // //       yielding when all equal
  // ancestorsByGenerators (gens) {
  //   const v = ScaleStore.get(this.#word);
  //   if (v) return this.#ancestorsByGenerators(v, gens)
  // }
  // #ancestorsByGenerators (v, gens) {}

  // Terrible...
  genDescendentsByGenerators (m) {
    const mapping = new Map(m.entries().map(([k, v]) => [k, Scale.wordsWithGenerators(Scale.genBilliards, v)]));
    return Index.quotient(
      new Index({ address: x => x, done: (_, v, i) => i === v.length - 1 }),
      Iter.cartProd(this.#word.split("").map(c => Common.quotient(
        mapping.get(c).flatMap(w => Array(w.length).values().map(i => Scale.wordInMode(w, i)))))).map(ars => [].concat(...ars)),
      ar => Array(ar.length).keys().map(i => ar.slice(i).concat(ar.slice(0, i)))
    ).map(ar => ar.join(""))
  }

  withEmbedding (embedding) { return new Scale({ ...this.#repr(), embedding }) }

}



class StepInterval {
  // TODO matrices...
  static cmp (iv0, iv1) {
    if (!StepInterval.prototype.isPrototypeOf(iv0) || !StepInterval.prototype.isPrototypeOf(iv1) ||
      iv0.store !== iv1.store) return null;
    const { constraints } = iv0.store;
    return StepInterval.cmpCons(iv0.value, iv1.value, constraints)
  }
  // TODO goes in Constraints?
  static cmpCons (ms0, ms1, cons) {
    const { eqs, lts } = cons;
    let d0 = ms0.minusSat(ms1), d1 = ms1.minusSat(ms0), i = 0;
    while (i < eqs?.length && d0.size && d1.size) {
      const [ e0, e1 ] = eqs[i];
      if (e0.minusSat(d0).size === 0 && e1.minusSat(d1).size === 0) {
        d0 = d0.minusSat(e0);
        d1 = d1.minusSat(e1)
      } else if (e1.minusSat(d0).size === 0 && e0.minusSat(d1).size === 0) {
        d0 = d0.minusSat(e1);
        d1 = d1.minusSat(e0)
      } else i++
    }
    if (d0.size === 0 && d1.size === 0) return 0;
    i = 0;
    let ord = 0;
    while (i < lts?.length && d0.size && d1.size) {
      const [ l0, l1 ] = lts[i];
      if (l0.minusSat(d0).size === 0 && l1.minusSat(d1).size === 0) {
        if (ord === 1) return null;
        ord = -1;
        d0 = d0.minusSat(l0);
        d1 = d1.minusSat(l1)
      } else if (l0.minusSat(d1).size === 0 && l1.minusSat(d0).size === 0) {
        if (ord === -1) return null;
        ord = 1;
        d0 = d0.minusSat(l1);
        d1 = d1.minusSat(l0)
      } else i++
    }
    return d0.size === 0 && d1.size === 0 ? ord :
      ord !== -1 && d1.size === 0 ? 1 :
      ord !== 1 && d0.size === 0 ? -1 : null
  }
  static multiSetToString (m, patternDict) {
    m = patternDict ? new Map(m.entries().map(([k, v]) => [ patternDict.get(k), v ])) : m;
    return Array.from(m.entries()).sort(([a], [b]) => Scale.charCmp(b, a) || Scale.wordCharCmp(b, a))
      .reduce((a, [k, v]) => a + v.length + k, "")
  }

  #store; #value; #strRep; #gIC; #degrees
  constructor ({ store, interval, gic, degrees }) {
    if (!IntervalStore.prototype.isPrototypeOf(store)) throw new Error("StepInterval error: store must be IntervalStore object");
    this.#store = store;
    const chars = Scale.wordChars.slice(0, store.scale.composition.size);
    if (!MultiSet.prototype.isPrototypeOf(interval) || interval.keys().find(char => !chars.includes(char)))
      throw new Error("StepInterval error: must be a MultiSet of allowed characters");
    this.#value = interval;
    if (gic !== undefined && !Set.prototype.isPrototypeOf(gic) && gic.values().some(n => parseInt(n) !== n || n < 0))
      throw new Error("StepInterval error: generic interval class must be given as a Set of positive integers");
    this.#gIC = gic;
    if (degrees !== undefined && !Set.prototype.isPrototypeOf(degrees) || degrees.values().some(n => parseInt(n) !== n || n < 0))
      throw new Error("StepInterval error: degree positions must be a Set of positive integers");
    this.#degrees = degrees
  }
  get value () { return this.#value }
  set value (_) {}
  get store () { return this.#store }
  set store (_) {}
  withStore (store) {
    if (!IntervalStore.prototype.isPrototypeOf(store)) throw new Error("StepInterval error: store must be IntervalStore object");
    return new StepInterval({ store, interval: this.#value, gic: this.#gIC, degrees: this.#degrees })
  }
  get degrees () { return this.#degrees }
  set degrees (_) {}
  get genericInterval () { return this.#store.get(this) }
  set genericInterval (_) {}
  get genericIntervalClass () { return new Set(this.#gIC.values().map(n => this.#store.scale.getGenericIntervalClass(n))) }
  set genericIntervalClass (_) {}
  get names () { return this.#store.scale.getNames(this) }
  set names (_) {}

  equal (iv) { return this.#value.equal(iv.value) }
  toString () { return this.#strRep ??= StepInterval.multiSetToString(this.#value, this.#store.scale.patternDict) }
}



class IntervalStore {

  // Constructor

  constructor ({ scale, ivs, constraints }) {
    if (!Scale.prototype.isPrototypeOf(scale)) throw new Error("IntervalStore error: scale must be Scale object");
    this.#scale = scale;
    if (constraints != null) {
      if (!Constraints.prototype.isPrototypeOf(constraints))
        throw new Error("IntervalStore error: constraints must be Constraints object");
      this.#constraints = constraints;
    }
    if (typeof ivs?.[Symbol.iterator] === "function") {
      if (ivs.values().some(iv => !StepInterval.prototype.isPrototypeOf(iv)))
        throw new Error("StepIntervalPO error: must provide an Iterable of StepIntervals");
      ivs.forEach(iv => this.add(iv));
    }
  }
  [Symbol.iterator] = () => this.#ivs[Symbol.iterator]()
  values = this[Symbol.iterator];
  get generic () { return new Set(this.#vertices) }
  set generic (_) {}
  get size () { return this.#ivs.size }
  set size (_) {}
  get uniques () { return this.#vertices.size }
  set uniques (_) {}

  #scale
  get scale () { return this.#scale }
  set scale (_) {}

  #constraints = new Constraints()
  get constraints () { return this.#constraints }
  set constraints (_) {}



  // Instance methods

  // Partial order graph
  // TODO vertices as repr, givs = Map(repr -> Set(iv))
  #ivs = new Set(); #vertices = new Set(); #edges = new Map()
  add (iv0) {
    this.#ivs.add(iv0);
    const mbGIv = this.#vertices.values().find(iv1 => StepInterval.cmp(iv0, iv1) === 0);
    if (mbGIv === undefined) {
      const s0 = new Set([iv0]), val = { in: new Set(), out: new Set() };
      this.#edges.set(s0, val);
      this.#vertices.add(s0);
      this.#vertices.values().forEach(s1 => {
        const [iv1] = s1, c = StepInterval.cmp(iv0, iv1);
        if (c === null || c === 0 || this.cmp(iv0, iv1) !== null) return;
        const
          [lhs, rhs] = [[s1, s0], [s0, s1]][(c + 1) / 2],
          { out: lhOuts } = this.#edges.get(lhs), { in: rhIns } = this.#edges.get(rhs)
        lhOuts.add(rhs);
        rhIns.add(lhs);
        for (const lhOut of lhOuts)
          if (this.cmpg(rhs, lhOut) === 1) {
            lhOuts.delete(lhOut);
            this.#edges.get(lhOut).in.delete(lhs);
          }
        for (const rhIn of rhIns)
          if (this.cmpg(rhIn, lhs) === 1) {
            rhIns.delete(rhIn);
            this.#edges.get(rhIn).out.delete(rhs)
          }
      });
    } else mbGIv.add(iv0);
  }
  cmp (iv0, iv1) {
    if (iv0?.store !== this || iv1?.store !== this) return null;
    if (this.#vertices.values().find(s => s.has(iv0))?.has(iv1)) return 0;
    if (this.#hasPath(iv0, iv1, new Set())) return 1;
    if (this.#hasPath(iv1, iv0, new Set())) return -1;
    return null
  }
  // Compare with generic interval
  cmpg ([iv0] = [], [iv1] = []) {
    if (iv0 && iv1) return this.cmp(iv0, iv1);
    else return null
  }
  #hasPath (iv0, iv1, visited) {
    if (this.#vertices.values().find(s => s.has(iv0))?.has(iv1)) return true;
    visited.add(iv0);
    for (const [neighbour] of this.#edges.entries().find(([k]) => k.has(iv0))?.[1].out ?? [])
      if (!visited.has(neighbour) && this.#hasPath(neighbour, iv1, visited)) return true;
    return false
  }

  // Compute incomparables
  #finalised = false
  finalise () {
    if (this.#finalised) return;
    for (const o of this.#edges.values()) o.inc = new Set();
    const vl = Array.from(this.#vertices);
    for (let i = 0; i < vl.length; i++)
      for (let j = i + 1; j < vl.length; j++)
        if (this.cmpg(vl[i], vl[j]) === null) {
          this.#edges.get(vl[i]).inc.add(vl[j]);
          this.#edges.get(vl[j]).inc.add(vl[i]);
        }
    const ord = this.#topOrder();
    this.#ivs = new Set(Iterator.concat(...ord));
    this.#vertices = new Set(ord);
    this.#edges = new Map(ord.map(giv => [giv, this.#edges.get(giv)]));
    this.#finalised = true;
    return this
  }
  // TODO on scale?
  #isStepTotalOrder
  get isStepTotalOrder () {
    const root = this.#scale.intervals;
    if (root.#isStepTotalOrder === undefined) {
      const givs = new Set(this.#scale.getGenericIntervalClass(0));
      return root.#isStepTotalOrder = givs.values().every(giv => new Set(Iterator.concat(...root.#edges.get(root.get(giv)).inc)).intersection(givs).size === 0)
    } else return root.#isStepTotalOrder
  }
  set isStepTotalOrder (_) {}
  #isTotalOrder
  get isTotalOrder () { return this.#isTotalOrder ??= this.#edges.values().every(({ inc }) => inc.size === 0) }
  set isTotalOrder (_) {}

  #min = new Set(); get min () { return new Set(this.#min) } set min (_) {}
  #max = new Set(); get max () { return new Set(this.#max) } set max (_) {}
  #topOrder () {
    const outDeg = new Map(this.#edges.keys().map(s => [ s, { value: 0 } ])), queue = [], ord = [];
    this.#max.clear();
    this.#min.clear();
    this.#edges.entries().forEach(([v, { in: ins, out: outs }]) => {
      if (ins.size === 0) this.#max.add(v);
      if (outs.size === 0) this.#min.add(v);
      outDeg.get(v).value = outs.size
    })
    for (const s of this.#edges.keys()) if (outDeg.get(s).value === 0) queue.push(s);
    while (queue.length > 0) {
      const cur = queue.shift();
      ord.push(cur);
      for (const next of this.#edges.get(cur).in)
        if (--outDeg.get(next).value === 0) queue.push(next);
    }
    if (ord.length !== this.#edges.size) throw new Error("IntervalStore error: found cycle");
    return ord
  }

  // Accessors
  get (iv) { return this.#vertices.values().find(s => s.has(iv)) }
  has (iv) { return Boolean(~this.#vertices.values().toArray().findIndex(s => s.has(iv))) }
  getBag (m) { return this.#vertices.values().find(s => ~Array.from(s).findIndex(iv => iv.value.equal(m))) }
  hasBag (m) { return Boolean(~this.#vertices.values().toArray().findIndex(s => ~Array.from(s).findIndex(iv => iv.value.equal(m)))) }
  getWord (str) { return this.getBag(new MultiSet(str.split(""))) }
  hasWord (str) { return this.hasBag(new MultiSet(str.split(""))) }

  getIv (iv) { return this.#ivs.values().find(iv0 => iv0.equal(iv)) }
  hasIv (iv) { return Boolean(~this.#ivs.values().toArray().findIndex(iv0 => iv0.equal(iv))) }
  getBagIv (m) { return this.#ivs.values().find(iv0 => iv0.value.equal(m)) }
  hasBagIv (m) { return Boolean(~this.#ivs.values().toArray().findIndex(iv0 => iv0.value.equal(m))) }
  getWordIv (str) { return this.getBagIv(new MultiSet(str.split(""))) }
  hasWordIv (str) { return this.hasBagIv(new MultiSet(str.split(""))) }

  // returns a new partial ordering on the given ivs
  substore (ivs) {
    const store = new IntervalStore({ scale: this.#scale, constraints: this.#constraints });
    ivs.forEach(iv => store.add(iv.withStore(store)));
    return store.finalise()
  }
  toConstraints () {
    const eqs = [], lts = [];
    for (const [v, { out }] of this.#edges) {
      const va = Array.from(v);
      for (let i = 1; i < v.size; i++) eqs.push([va[i - 1], va[i]]);
      for (const [iv] of out) lts.push([iv.value, va[0].value])
    }
    return new Constraints({ eqs, lts })
  }

  // Compute totally-ordered subsets (what is the correct name?)
  #tOSubsets
  get tOSubsets () { return (this.#tOSubsets ?? this.#genTOSubsets()).map(ss => new Set(ss)) }
  set tOSubsets (_) {}
  #genTOSubsets () {
    return this.#tOSubsets = Array.from(this.#edges.entries()).reduce(({ result, state }, [v, { inc }], i) => {
      if (inc.size === 0) return {
        result: state.size ? result.concat(state, new Set([v])) : result.concat(new Set([v])),
        state: new Set()
      };
      else if (i === this.#edges.size - 1)
        return { result: state.size ? result.concat(state.add(v)) : result.concat(new Set([v])) };
      else return { result, state: state.add(v) }
    }, { result: [], state: new Set() }).result
  }

  // Generates all pairs of reduced incomparable intervals
  #incomparables
  #genIncs () {
    const incomparableSets = this.tOSubsets.filter(s => s.size !== 0), pairs = [], cons = this.#constraints;
    for (const givs of incomparableSets) {
      const subset = Array.from(givs);
      for (let i = 0; i < subset.length; i++) {
        const s0 = subset[i];
        for (let j = i + 1; j < subset.length; j++) {
          const s1 = subset[j];
          for (const iv0 of s0) for (const iv1 of s1) {
            let lhs = iv0.value.minusSat(iv1.value), rhs = iv1.value.minusSat(iv0.value), g = Common.gcd(lhs.gcd, rhs.gcd);
            lhs = lhs.scalarMultiply(1 / g);
            rhs = rhs.scalarMultiply(1 / g);
            //
            if (lhs.size === 0 || rhs.size === 0 ||
              pairs.some(([m0, m1]) => (m0.equal(lhs) && m1.equal(rhs)) || (m1.equal(lhs) && m0.equal(rhs))) ||
              this.cmpg(this.getBag(lhs), this.getBag(rhs)) !== null) continue;
            if (Scale.charCmp(lhs.keys().toArray().sort(Scale.charCmp)[0], rhs.keys().toArray().sort(Scale.charCmp)[0]) === 1)
              pairs.push([rhs, lhs]);
            else pairs.push([lhs, rhs]);
          }
        }
      }
    }
    return this.#incomparables = pairs
  }
  get incomparables () { return (this.#incomparables ?? this.#genIncs()).map(([lhs, rhs]) => [ MultiSet.from(lhs), MultiSet.from(rhs) ]) }
  set incomparables (_) {}
  // Only constraints listed in incomparables may be applied?

  // Concrete scales

  #concreteRanges;
  get concreteRanges () { return new Map(this.#concreteRanges ??= this.#genConcreteRanges()) }
  set concreteRanges (_) {}
  #genConcreteRanges () {
    const [[ { value: oct } ]] = this.max, result = new Map();
    for (const iv of this.#ivs) {
      let min = 1, max = 0;
      for (const c of Scale.wordChars.slice(0, this.#scale.variety)) {
        const v = (iv.value.repr.get(c) ?? 0) / oct.repr.get(c);
        if (v < min) min = v;
        if (v > max) max = v
      }
      result.set(iv, [min, max])
    }
    return result
  }
  solveForHarmonics (harms) { return this.solve(harms.map(h => Common.mod(Math.log2(h), 1))) }
  solve (target) {
    const
      { variety } = this.#scale,
      fixed = Iter.genUniqueCombs(Scale.wordChars.slice(0, variety), Math.min(target.length, variety)).toArray();
    console.log(fixed)
  }

}



// Global scale store
class ScaleStore {

  static eqGraph (g0, g1) {
    const s1 = new Set(g1.keys());
    for (const [ k, { in: ins } ] of g0) {
      s1.delete(k);
      if (!Common.bagEq(ins, g1.get(k))) return false;
    }
    return s1.size === 0
  }

  static data = new Map(); static #vertices = []
  static * [Symbol.iterator] () { yield * ScaleStore.#vertices.values().map(({ str }) => str) }

  // Edges go towards ancestor scale, indexed by mapping
  // graph vertices must be referentially equal to mapping elements
  static #addData ({ sOut, sIn, mapping, ...edgeData }) {
    const { str: str0, scale: sc0 } = sOut, { str: str1 } = sIn;
    if (str0.length <= str1.length) return null;
    const
      { data } = ScaleStore,
      s0 = ScaleStore.get(str0) ?? (ScaleStore.#vertices.push(sOut = { str: str0 }), sOut),
      s1 = ScaleStore.get(str1) ?? (ScaleStore.#vertices.push(sIn = { str: str1 }), sIn);
    s0.scale ??= sc0;
    if (ScaleStore.#cmp(s0, s1).some(m => ScaleStore.#indexEq(m, mapping))) return data;
    const
      s0Val = data.get(s0) ?? { out: new Map(), in: new Map() },
      s1Val = data.get(s1) ?? { out: new Map(), in: new Map() };
    data.set(s0, s0Val); data.set(s1, s1Val);
    s0Val.out.set(s1, (s0Val.out.get(s1) ?? []).concat([ { mapping, ...edgeData } ]));
    s1Val.in.set(s0, (s1Val.in.get(s0) ?? []).concat([ { mapping, ...edgeData } ]));
    for (const [ outV, ds ] of s0Val.out) if (outV !== s0) for (let i = 0; i < ds.length; i++) {
      const
        { mapping: m } = ds[i],
        i1 = ScaleStore.#cmp(s1, outV).findIndex(m0 =>
          ScaleStore.#indexEq(ScaleStore.#indexCompose(mapping, m0), m) ||
          ScaleStore.#indexEq(m0, ScaleStore.#indexCompose(mapping, m)));
      if (~i1) {
        ds.splice(i, 1);
        if (ds.length === 0) s0Val.out.delete(outV);
        const v1 = data.get(outV), ds1 = v1.in.get(s0);
        ds1.splice(i1, 1);
        if (ds1.length === 0) v1.in.delete(s0)
      }
    }
    for (const [ inV, ds ] of s1Val.in) if (inV !== s1) for (let i = 0; i < ds.length; i++) {
      const
        { mapping: m } = ds,
        i0 = ScaleStore.#cmp(inV, s0).findIndex(m0 =>
          ScaleStore.#indexEq(m0, ScaleStore.#indexCompose(m, mapping)) ||
          ScaleStore.#indexEq(ScaleStore.#indexCompose(m0, mapping), m));
      if (~i0) {
        ds.splice(i, 1);
        if (ds.length === 0) s1Val.in.delete(inV);
        const v0 = data.get(inV), ds0 = v0.out.get(s1);
        ds0.splice(i0, 1);
        if (ds0.length === 0) v0.out.delete(s1)
      }}
    return data
  }
  static #markCached (v) { if (v) v.cached = true }

  // Collects all mappings which transform first scale word into second
  static cmp (str0, str1) {
    const s0 = ScaleStore.get(str0), s1 = ScaleStore.get(str1);
    if (s0 === undefined || s1 === undefined) return;
    if (str0.length < str1.length) return [];
    return ScaleStore.#cmp(s0, s1)
  }
  static #cmp (s0, s1) { return ScaleStore.#cmpHelper(s0, s1, [null], new Map()).filter(Boolean) }
  static #cmpHelper (s0, s1, mappings, visited) {
    if (s0 === s1) return mappings;
    const s = visited.get(s0) ?? [];
    visited.set(s0, s.concat(mappings = mappings.filter(m0 => !s.some(m1 => ScaleStore.#indexEq(m0, m1)))));
    let nextMappings = [];
    for (const [ next, data ] of ScaleStore.data.get(s0)?.out ?? []) {
      const comps = Iter.cartProd([ mappings, data.map(({ mapping }) => mapping) ])
        .map(([ m0, m1 ]) => ScaleStore.#indexCompose(m0, m1)).toArray();
      nextMappings = nextMappings.concat(ScaleStore.#cmpHelper(next, s1, comps, visited))
    }
    return Common.quotient(nextMappings, ScaleStore.#indexEq)
  }

  static get (str) {
    const eq = Scale.findMode(str);
    return ScaleStore.#vertices.find(({ str }) => ~eq(str))
  }
  static getMode (str) {
    const eq = Scale.findMode(str), index = ScaleStore.#vertices.find(({ str }) => ~eq(str));
    return index && { index, mode: eq(index.str) }
  }

  static #indexEq (i0, i1) {
    if (i0 == null || i1 == null) return false;
    for (const ms0 of i0) {
      const i = i1.findIndex(ms1 => ms0.equal(ms1));
      if (!~i) return false;
      else i1 = i1.toSpliced(i, 1)
    }
    return i1.length === 0
  }
  // returns interval list r0⨟r1 where r1's character set agrees with r0's dimension
  // r0, r1: [ MultiSet(char) ]
  static #indexCompose (i0, i1) {
    if (i0 == null) return i1;
    if (i1 == null) return i0;
    if (i1.some(ms => ms.keys().some(c => !Scale.wordChars.includes(c))) ||
      i0.length !== i1.reduce((a, b) => a.union(b), new MultiSet()).repr.size) return null;
    return i1.map(ms => new MultiSet(ms.repr.entries().flatMap(([c, k]) =>
      [ ...i0[Scale.wordChars.indexOf(c)].scalarMultiply(k) ]).toArray()))
  }

  // Collects all transformations of first scale into second.
  static transforms (str0, str1) {
    if (str0 == null || str1 == null) return;
    const
      { index: i0, mode: o0 } = ScaleStore.getMode(str0), { index: i1, mode: o1 } = ScaleStore.getMode(str1),
      pre = Array(str0.length).keys().map(i => [i, Common.mod(i - o0, str0.length)]).toArray(),
      post = Array(str1.length).keys().map(i => [i, Common.mod(i + o1, str1.length)]).toArray();
    return this.#transforms(i0, i1, [ { modeMap: pre } ], new Map()).filter(Boolean)
      .map(d => ScaleStore.#transformCompose(d, { modeMap: post }))
  }
  // data: [ { mapping, modeMap } ]
  static #transforms (i0, i1, data, visited) {
    if (i0 === i1) return data;
    const s = visited.get(i0) ?? [];
    visited.set(i0, s.concat(data = data.filter(d => d && !s.some(({ mapping }) => ScaleStore.#indexEq(d.mapping, mapping)))));
    let nextData = [];
    for (const [ next, ds ] of ScaleStore.data.get(i0)?.out?? []) {
      const comps = Iter.cartProd([ data, ds ]).map(([ d0, d1 ]) => ScaleStore.#transformCompose(d0, d1)).toArray();
      nextData = nextData.concat(ScaleStore.#transforms(next, i1, comps, visited))
    }
    return Common.quotient(nextData, ({ mapping: m0 }, { mapping: m1 }) => ScaleStore.#indexEq(m0, m1))
  }
  // returns interval list r0⨟r1 where r1's character set agrees with r0's dimension
  // d0, d1: { mapping: [ MultiSet(char) ], modeMap: [[outerMode, innerMode]] }
  static #transformCompose (d0, d1) {
    if (d0 == null) return d1;
    if (d1 == null) return d0;
    const
      { mapping: m0, modeMap: o0 } = d0, { mapping: m1, modeMap: o1 } = d1,
      prev = Map.groupBy(o0, ([, b]) => b), next = Map.groupBy(o1, ([a]) => a),
      modeMap = Common.quotient(next.entries().flatMap(([m0, m1s]) => (prev.get(m0) ?? [])
        .flatMap(m => m1s.map(([, m1]) => m.with(1, m1)))).toArray(), Common.zipCmp).sort();
    return { mapping: ScaleStore.#indexCompose(m0, m1), modeMap }
  }

  // Caching
  // Generates scales
  // TODO incorporate Scale generators
  // TODO return substore?
  static allAncestors (sc, sv) {
    if (typeof sc === "string") sc = ScaleStore.get(sc).scale ?? new Scale({ word: sc });
    if (parseInt(sv) !== sv) sv = sc.variety;
    const v = ScaleStore.get(sc.word);
    if (v?.cached) return ScaleStore.#allAncestors(sc.word, sc.word, new Map([[ v, [] ]]));
    const result = sc.allAncestors(sv).toArray();
    for (const { word: wr, mapping, modeMap } of result)
      ScaleStore.#addData({ sOut: { str: sc.word, scale: sc }, sIn: { str: wr }, mapping, modeMap })
    ScaleStore.#markCached(ScaleStore.get(sc.word));
    return result
  }
  static * #allAncestors (strInit, strV, visited) {
    const v = ScaleStore.get(strV),
      { in: _, out } = ScaleStore.data.get(v) ?? {},
      s = visited.get(strV) ?? [], newPaths = [];
    for (const { mapping, ...edgeData } of ScaleStore.transforms(strInit, strV))
      if (!s.some(m => ScaleStore.#indexEq(m, mapping))) {
        newPaths.push(mapping);
        if (mapping) yield { word: strV, mapping, ...edgeData }
      }
    visited.set(strV, Common.quotient(s.concat(newPaths), ScaleStore.#indexEq));
    for (const [ { str } ] of out) yield * ScaleStore.#allAncestors(strInit, str, visited)
  }
  static addDescendant (sc, ranks) {
    if (typeof sc === "string") sc = ScaleStore.get(w)?.scale ?? new Scale({ word: sc });
    else if (typeof ranks === "undefined") ({ ranks } = sc);
    if (!ranks) return null;
    const { word, mapping } = Scale.ranksToMapping(ranks);
    if (!~Scale.findMode(word, sc.word)) return null;
    const scale = sc.embedding ? sc : sc.withEmbedding(mapping), { embeddingScale } = scale, modeMap = [];
    for (let i = 0; i < embeddingScale.modeCount; i++)
      for (let j = 0; j < scale.modeCount; j++) {
        embeddingScale.mode = i;
        scale.mode = j;
        if (scale.word.split("").every(c => {
          const k = embeddingScale.genericIvs.indexOf(embeddingScale.intervals.getBag(mapping.get(c)));
          if (!~k) return false;
          embeddingScale.mode += k + 1;
          return true;
        })) modeMap.push([i, j])
      }
    // TODO unify mapping representations...
    ScaleStore.#addData({ sOut: { str: embeddingScale.word, scale: embeddingScale }, sIn: { str: word, scale: sc }, modeMap,
      mapping: mapping.entries().reduce((ar, [c, m]) => ar.with(Scale.wordChars.indexOf(c), m), Array(mapping.size)) })
    return { inner: word, outer: embeddingScale.word, mapping, modeMap };
  }
  // Dangerous for now...
  static cacheAll () {
    const vs = ScaleStore.data.keys().filter(({ cached }) => !cached).toArray()
      .sort(({ str: str0 }, { str: str1 }) => str0.length - str1.length);
    for (const { str } of vs) ScaleStore.allAncestors(str);
    if (ScaleStore.data.keys().filter(({ cached }) => !cached).toArray().length !== vs.length) ScaleStore.cacheAll()
  }

  // Generates strings
  static listAncestors (str) {
    const v = ScaleStore.get(str);
    if (v) return ScaleStore.#listAncestors(v, new Set())
  }
  static * #listAncestors (v, visited) {
    visited.add(v.str);
    yield v.str;
    const { out } = ScaleStore.data.get(v);
    for (const [ { str } ] of out) if (!visited.has(str))
      yield * ScaleStore.#listAncestors(ScaleStore.get(str), visited)
  }

  // // TODO
  // static subgraphBetween (s0, s1) {}

  static ancestorsByIv (str, iv) {
    const v = ScaleStore.get(str);
    if (typeof iv === "string") iv = new MultiSet(iv.split(""));
    if (v) return ScaleStore.#ancestorsByIv(str, v, iv, new Map([[ v, [] ]]))
  }
  static * #ancestorsByIv (strInit, v, iv, visited) {
    const { in: _, out } = ScaleStore.data.get(v);
    for (const [vOut] of out){
      const { cached, str } = vOut;
      for (const { mapping, ...edgeData } of ScaleStore.transforms(strInit, str))
        if (!visited.get(vOut)?.some(m => ScaleStore.#indexEq(m, mapping))) {
          let rec = false;
          for (const m of mapping) {
            if (m.symmetricDifference(iv).size === 0) {
              const s = visited.get(vOut) ?? [];
              visited.set(vOut, Common.quotient(s.concat([mapping]), ScaleStore.#indexEq));
              yield { mapping, str, ...edgeData }
            }
            if (m.minusSat(iv).size === 0) rec = true
          }
          if (rec) yield * ScaleStore.#ancestorsByIv(strInit, vOut, iv, visited)
        }
    }
  }

}



// Represents constraints on intervals
class Constraints {

  // Total order on n elements
  static totalOrder (n) {
    const chars = Scale.wordChars;
    if (parseInt(n) !== n || !Common.between(1, chars.length, n)) return null;
    const lts = Array(n - 1).keys().map(i => [ new MultiSet([ chars[i + 1] ]), new MultiSet([ chars[i] ]) ]).toArray();
    return new Constraints({ lts })
  }
  static symEqOperands ([lhs0, rhs0], [lhs1, rhs1]) {
    return (lhs0.symmetricDifference(lhs1).size === 0 && rhs0.symmetricDifference(rhs1).size === 0) ||
      (lhs0.symmetricDifference(rhs1).size === 0 && rhs0.symmetricDifference(lhs1).size === 0)
  }
  static eqOperands ([lhs0, rhs0], [lhs1, rhs1]) {
    return (lhs0.symmetricDifference(lhs1).size === 0 && rhs0.symmetricDifference(rhs1).size === 0)
  }
  static equal (c0, c1) {
    if (!Constraints.prototype.isPrototypeOf(c0) || !Constraints.prototype.isPrototypeOf(c1)) return false;
    const { eqs: eqs0, lts: lts0 } = c0, { eqs: eqs1, lts: lts1 } = c1;
    if (eqs0.length !== eqs1.length || lts0.length !== lts1.length ||
      eqs0.some((eq, i) => !Constraints.symEqOperands(eq, eqs1[i])) || lts0.some((lt, i) => !Constraints.eqOperands(lt, lts1[i])))
      return false;
    return true
  }
  static pretty ({ eqs, lts, inc }, patternDict) {
    return [
      eqs?.map(pair => pair.map(m => StepInterval.multiSetToString(m, patternDict)).join("=")).join(", "),
      lts?.map(pair => pair.map(m => StepInterval.multiSetToString(m, patternDict)).join("<")).join(", "),
      inc?.map(pair => pair.map(m => StepInterval.multiSetToString(m, patternDict)).join("~")).join(", ")
    ].filter(Boolean).join(", ")
  }

  constructor ({ eqs, lts } = {}) {
    if (typeof eqs?.[Symbol.iterator] === "function") {
      if (eqs.some(eq => !Array.prototype.isPrototypeOf(eq) || eq.length !== 2 ||
        !MultiSet.prototype.isPrototypeOf(eq[0]) || !MultiSet.prototype.isPrototypeOf(eq[1])))
        throw new Error("Constraints error: malformed eqs");
      this.#eqs = eqs;
    }
    if (typeof lts?.[Symbol.iterator] === "function") {
      if (lts.some(lt => !Array.prototype.isPrototypeOf(lt) || lt.length !== 2 ||
        !MultiSet.prototype.isPrototypeOf(lt[0]) || !MultiSet.prototype.isPrototypeOf(lt[1])))
        throw new Error("Constraints error: malformed eqs");
      this.#lts = lts
    }
  }
  clone () { return new Constraints({ eqs: this.eqs, lts: this.lts }) }
  #eqs;
  get eqs () { return this.#eqs?.map(([lhs, rhs]) => [ MultiSet.from(lhs), MultiSet.from(rhs) ]) }
  set eqs (_) {}
  #lts;
  get lts () { return this.#lts?.map(([lhs, rhs]) => [ MultiSet.from(lhs), MultiSet.from(rhs) ]) }
  set lts (_) {}
  get isEmpty () { return !(this.#eqs?.length || this.#lts?.length) }
  set isEmpty (_) {}

  insertEq ([lhs, rhs] = []) {
    if (!MultiSet.prototype.isPrototypeOf(lhs) || !MultiSet.prototype.isPrototypeOf(rhs)) return this;
    this.#eqs ?
      ~this.#eqs.findIndex(c => Constraints.eqOperands(c, [lhs, rhs])) || this.#eqs.push([lhs, rhs]) :
      (this.#eqs = [[lhs, rhs]]);
    return this
  }
  insertLt ([lhs, rhs] = []) {
    if (!MultiSet.prototype.isPrototypeOf(lhs) || !MultiSet.prototype.isPrototypeOf(rhs)) return this;
    this.#lts ?
      ~this.#lts.findIndex(c => Constraints.eqOperands(c, [lhs, rhs])) || this.#lts.push([lhs, rhs]) :
      (this.#lts = [[lhs, rhs]]);
    return this
  }
  combine (cons) {
    if (!Constraints.prototype.isPrototypeOf(cons)) return false;
    this.#eqs?.concat([cons.#eqs]) ?? (this.#eqs = cons.#eqs);
    this.#lts?.concat([cons.#lts]) ?? (this.#lts = cons.#lts)
    return this
  }
  // Uses referential equality
  substitute (sub) {
    return new Constraints({
      eqs: this.#eqs?.map(eq => eq.map(o => {
        const i = sub.indexOf(o);
        return ~i ? new MultiSet([ Scale.wordChars[i] ]) : o
      })),
      lts: this.#lts?.map(lt => lt.map(o => {
        const i = sub.indexOf(o);
        return ~i ? new MultiSet([ Scale.wordChars[i] ]) : o
      }))
    })
  }

}



export { Scale, StepInterval, IntervalStore, ScaleStore, Constraints }