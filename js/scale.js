import { Common, MultiSet } from "./common.js";
import { HarmonicLattice, Interval } from "./interval.js";
import { Keyboard } from "./keyboard.js";
import { HarmonicMapping } from "./mapping.js";


// Represents scales at varying levels of concretion/abstraction, with generating functions
class Scale {

  // Static

  static #wordChars = "XYZWVUTSRQ";
  static #patChars = "BCHLMnpstw";
  static #patOrder = [3, 7, 4, 8, 2, 5, 9, 0, 6, 1]; //Nonstandard order, has a more even distribution.
  static #levelChar = [["d", "A"], ["s", "S"], ["n", "W"]]
  static charCmp = (c0, c1) => {
    const i0 = new RegExp(c0).exec(this.#patChars)?.index, i1 = new RegExp(c1).exec(this.#patChars)?.index;
    if (i0 === undefined || i1 === undefined) return null; // Not comparable
    else return i0 > i1 ? -1 : i0 < i1 ? 1 : 0
  }
  // TODO: eg XYY -> XXY (lower index = most frequent)
  static normalisePermutation (str) {
    let symbols = "", remain = str, newStr = "";
    while (remain.length) {
      symbols += remain[0];
      remain = remain.replaceAll(remain[0], "")
    }
    if (symbols.length > Scale.#wordChars.length) return null;
    for (let i = 0; i < str.length; i++)
      newStr += Scale.#wordChars[symbols.indexOf(str[i])];
    return newStr
  }
  static normalisePattern (str) {
    let pcs = new Set(Scale.#patChars), syms = new Set(str), ord = [], res = "";
    if (syms.difference(pcs).size) return null;
    for (let c of Scale.#patChars) if (syms.has(c)) ord.push(c);
    const canon = Scale.#patOrder.slice(0, syms.size).sort();
    for (let c of str) res += Scale.#patChars[canon[ord.indexOf(c)]];
    return res
  }
  static ranksToPattern (ranks) {
    const ivs = ranks.slice(1).map((r, i) => r - ranks[i]), stepSizes = Array.from(new Set(ivs)).sort((a, b) => b - a);
    return Scale.normalisePattern(ivs.map(steps => Scale.#patChars[stepSizes.indexOf(steps)]))
  }
  static ranksToMapping (ar) {
    const steps = Array.from(ar.slice(1).reduce((s, r, i) => s.add(r - ar[i]), new Set())).sort((a, b) => b - a);
    return new Map(this.normalisePattern(this.#patChars.slice(0, steps.length)).split("")
      .map((c, i) => [c, steps[i]]))
  }
  static ranksInMode (ranks, mode) {
    if (mode === 0) return ranks;
    const edo = ranks.at(-1);
    return ranks.slice(mode).concat(ranks.slice(1, mode).map(x => x + edo)).map(x => x - ranks[mode]).concat(edo)
  }
  static ranksToGenericIvs (ranks) {
    return Array(Math.floor((ranks.length - 1) / 2)).fill(0).map((_, i) =>
      Common.group(Array(ranks.length).fill(0).map((_, j) => ({
        degree: j,
        iv: j + i + 2 >= ranks.length ?
          ranks[j + i + 2 - ranks.length] + ranks.at(-1) - ranks[j] : ranks[j + i + 1] - ranks[j]
      })), ({ iv: a }, { iv: b }) => a === b)
      .map(ivs => ivs.reduce(({ iv, degrees }, { iv: iv0, degree }) =>
        ({ iv: iv ?? iv0, degrees: degrees.concat(degree) }), { iv: null, degrees: [] })))
  }
  static mixedWordToGenericIvsInMode (str) {
    return Array(str.length).fill(0).map((_, j) => ({
      degree: j,
      ivs: Array(Math.floor(str.length / 2)).fill(0).map((_, i) => i + j + 1 > str.length ?
        str.slice(j) + str.slice(0, i + j + 1 - str.length) : str.slice(j, j + i + 1))
    }))
  }
  static mixedWordToGenericIvs (str) {
    return Array(Math.floor(str.length / 2)).fill(0).map((_, i) =>
      Common.group(Array(str.length).fill(0).map((_, j) => ({
        degree: j,
        iv: new MultiSet((i + j + 1 > str.length ?
          str.slice(j) + str.slice(0, i + j + 1 - str.length) : str.slice(j, j + i + 1)).split(""))
      })), ({ iv: a }, { iv: b }) => a.equal(b))
      .map(ivs => ivs.reduce(({ iv, degrees }, { iv: iv0, degree }) =>
        ({ iv: iv ?? iv0, degrees: degrees.concat(degree) }), { iv: null, degrees: [] })))
  }

  // TODO: orthogonality predicate (matrix stuff)
  static eqIndependence (eq, eqs) {}


  // All ordered compositions satisfying the edo and list of step sizes
  static genStepCompositions = (edo, steps) => function * () {
    const rec = (gen, x) => function * (...as) {
      const max = as.reduce((ac, [{}, x], i) => ac - x * steps[i], edo) / x;
      for (let y = 1; y <= max; y++) yield * gen(...as, [x, y])
    };
    let gen = function * (...as) {
      const z = as.reduce((ac, [{}, x], i) => ac - x * steps[i], edo) / steps.at(-1);
      if (z === Math.floor(z) && z) yield [ ...as, [steps.at(-1), z] ]
    };
    for (const s of steps.toReversed().slice(1)) gen = rec(gen, s);
    yield * gen().map(v => new Map(v))
  }()
  
  // All permutations with the given composition
  static * genAllPermutations (comp) {
    const
      c = comp.values().toArray(),
      ar = c.flatMap((n, i) => Array(n).fill(i)),
      mapping = {
        MultiSet: ar => ({ comp, word: ar.reduce((a, i) => a + Scale.#wordChars[i], "") }),
        Map: (() => {
          const
            pchs = this.normalisePattern(Scale.#patChars.slice(0, comp.size)),
            kvs = comp.entries()
              .map(([s, c], i) => [s, c, i]).toArray()
              .sort(([a], [b]) => b - a)
              .reduce((m, [s,, i], t) => m.set(i,
                [ Scale.#wordChars[t], pchs[t], s ]), new Map());
          return ar => ({ comp, ...ar.reduce(({ word, pattern, ranks }, i) => {
            const [w, p, s] = kvs.get(i);
            return { word: word + w, pattern: pattern + p, ranks: ranks.concat(ranks.at(-1) + s) }
          }, { word: "", pattern: "", ranks: [0] }) })
        })()
      }[comp.constructor.name];
    yield mapping(ar);
    while (true) {
      let i = ar.length - 2;
      while (i >= 0 && (ar[i] >= ar[i + 1])) i--;
      if (i < 0) return;
      let j = ar.length - 1;
      while (ar[j] <= ar[i]) j--;
      [ ar[i], ar[j] ] = [ ar[j], ar[i] ];
      let start = i + 1, end = ar.length - 1;
      while (start < end) {
        [ ar[start], ar[end] ] = [ ar[end], ar[start] ];
        end--; start++
      }
      yield mapping(ar)
    }
  }

  // The most balanced word for the given composition
  static genBilliardPattern (composition) {
    const
      comp = composition.values().toArray(),
      t = Array(comp.length).fill(.5 + Number.EPSILON), counter = Array(comp.length).fill(0),
      k = comp.reduce((a, b) => a + b, -1), steps = [];
    for (let n = 0; n < k; n++) {
      const i = t.reduce(([i, v], x, j) => {
          const k = comp[j] / x;
          return k > v ? [j, k] : [i, v]
        }, [-1, 1])[0],
        d = t[i] / comp[i];
      t.forEach((v, j) => t[j] = i === j ? 1 : v - d * comp[j]);
      counter[i]++;
      steps.push(i)
    }
    steps.push(comp.findIndex((x, i) => x !== counter[i]));
    const word = steps.map(i => Scale.#wordChars[i]).join("");
    if (MultiSet.prototype.isPrototypeOf(composition)) return { word };
    else if (Map.prototype.isPrototypeOf(composition)) {
      const
        keys = composition.keys().toArray(),
        ranks = steps.reduce((a, i) => a.concat(a.at(-1) + keys[i]), [0]);
      return { word, ranks, pattern: Scale.ranksToPattern(ranks) }
    }
  }

  // All possible step sizes for a given edo and scale step variety
  static * #genStepSizePerms (edo, sv) {
    const counter = Array(sv).fill(0).map((_, i) => i + 1);
    let pos = sv - 1, s;
    while ((s = Common.sum(counter)) <= edo && pos == 0 || pos > 0) {
      if (s > edo) pos--;
      else {
        yield counter.slice();
        pos = sv - 1;
      }
      counter[pos]++;
      counter.slice(pos + 1).forEach((_, i) => counter[pos + 1 + i] = counter[pos + i] + 1)
    }
  }
  // Infinite list of sv unique numbers, in ascending order of sum then lex-order
  static * genStepSizePermStream (sv) {
    let i = sv * (sv + 1) / 2;
    while (true) yield * Scale.#genStepSizeHelper(sv, i++)
  }
  static * #genStepSizeHelper (sv, i) {
    let j = 0;
    if (sv === 1) yield [i];
    else while (i > ++j * sv)
      for (const ns of Scale.#genStepSizeHelper(sv - 1, i - j * sv))
        yield [j].concat(ns.map(n => n + j))
  }
  // All permutations of array elements, ignoring equality
  static * genUniquePerms (array, choose = array.length) {
    if (choose === 0 || array.length === 0) yield [];
    else for (let i = 0; i < array.length; i++)
      yield * Scale.genUniquePerms(array.toSpliced(i, 1), choose - 1).map(ar => [array[i]].concat(ar))
  }
  // All combinations of array elements, ignoring equality
  static * genUniqueCombs (array, choose = array.length, i = 0) {
    if (choose === 0 || array.length === 0) yield [];
    else for (; i <= array.length - choose; i++)
      yield * Scale.genUniqueCombs(array, choose - 1, i + 1).map(ar => [array[i]].concat(ar))
  }

  static * genIvMappingsFromComposition (comp) {
    const ord = Array.from(comp).sort((a, b) => b - a);
    let results = [], newRes = [];
    for (const steps of Scale.genStepSizePermStream(comp.size)) {
      const iter = [[new Map(), new Set(steps)]], min = ord.reduce((a, c, i) => a + steps[i] * c, 0);
      ({ true: results = [], false: newRes = [] } = Common.groupBy(results, ({ edo }) => edo < min))
      yield * results.sort((({ edo: edo0 }, { edo: edo1 }) => edo0 - edo1));
      for (const [k, v] of comp.entries())
        for (const [m, s] of iter.splice(0))
          for (const comb of Scale.genUniqueCombs(Array.from(s), v.length)) {
            const m0 = new Map(m), s0 = new Set(s);
            for (const step of comb) {
              m0.set(step, k);
              s0.delete(step)
            }
            iter.push([m0, s0]);
          }
      results = newRes.concat(iter.map(([m]) => ({ mapping: m, edo: m.entries().reduce((a, [s, c]) => a + s * c, 0) })))
    }
  }
  static * genIvMappingsFromPatCharCounts (counts) {
    const chars = Scale.normalisePattern(Scale.#patChars.slice(0, counts.length));
    let curSum = counts.length * (counts.length + 1) / 2, results = [], newRes = [];
    for (const steps of Scale.genStepSizePermStream(counts.length)) {
      const newSum = Common.sum(steps), edo = steps.reduce((a, s, i) => a + s * counts[i], 0);
      if (curSum < newSum) {
        const
          ss = steps.map(n => 1 / n), k = Common.sum(ss),
          min = ss.reduce((a, n, i) => a + counts[i] * Math.floor(newSum * n / k), 0);
        if (edo > 210) return;
        ({ true: results = [], false: newRes = [] } = Common.groupBy(results, ({ edo }) => edo < min));
        yield * results.sort((({ edo: edo0 }, { edo: edo1 }) => edo0 - edo1));
        results = newRes;
        curSum = newSum
      }
      const mapping = new Map(steps.toReversed().map((k, i) => [chars[i], k]));
      results.push({ mapping, edo })
    }
  }

  // All possible scales for the given edo and scale step variety
  static * genAllScales (edo, sv) {
    yield * Scale.#genStepSizePerms(edo, sv)
      .flatMap(steps => Scale.genStepCompositions(edo, steps)
        .flatMap(comp => Scale.genAllPermutations(comp)))
  }

  // All possible balanced scales for the given edo and scale step variety
  static * genBilliardScales (edo, sv) {
    yield * Scale.#genStepSizePerms(edo, sv)
      .flatMap(steps => Scale.genStepCompositions(edo, steps)
        .map(comp => ({ comp, ...Scale.genBilliardPattern(comp) })))
  }
  
  // TODO expose subcomputations for pruning, worker balancing etc
  static * genConstrainedScales (gen, { arity = null, maxVariety = null, rothenberg = null } = {}) {
    gen = gen.map(({ ranks, ivs, ...rest }) => ({ ...rest, ranks, ivs: ivs ?? Scale.ranksToGenericIvs(ranks)
     }));
    if (arity !== null) gen = gen.filter(({ ranks }) => ranks.length - 1 === arity);
    if (maxVariety !== null) gen = gen.filter(({ ivs }) => ivs.every(ivl => ivl.length <= maxVariety));
    if (rothenberg !== null) gen = rothenberg ?
      gen.filter(({ ivs }) => ivs.every((ivl, i) => !i || ivl.every(({ iv: iv0 }) => ivs[i - 1].every(({ iv: iv1 }) => iv0 > iv1)))) :
      gen.filter(({ ivs }) => ivs.every((ivl, i) => !i || ivl.every(({ iv: iv0 }) => ivs[i - 1].every(({ iv: iv1 }) => iv0 >= iv1))));
    yield * gen
  }
  // TODO (gen, { eqs }) => ({ ...results, eqs }), don't initialise Scale objects
  static filterApplyEqs (gen, eqs) {}

  static scaleCoverage (gen, mapping) {
    const ranks = Object.entries(Common.groupBy(mapping.properIntervals[Symbol.iterator]()
      .map(iv => [ mapping.steps(iv), iv ]).toArray(),
      ([s]) => s, ([{}, iv]) => iv))
      .map(([k, v]) => [ parseInt(k), v ]);
    return function * (...harmsRaw) {
      const lat = new HarmonicLattice({ harmsRaw });
      // TODO Not correct in general, need to take exotic temperaments into account
      const ranks_ = ranks.map(([s, enh]) => [ s, enh.filter(iv => lat.decomp(...iv.fraction)) ])
        .filter(([{}, enh]) => enh.length);
      yield * Scale.genConstrainedScales(gen).map(({ comp, ranks, ivs }) => {
        let m = 0;
        const coverage = [], l = ranks.length;
        do {
          const rs = Scale.ranksInMode(ranks, m);
          coverage.push(ranks_.filter(([s]) => rs.includes(s)).length);
        } while (!(l % m++) && !Common.arrEq(ranks, Array(Math.floor(l / m)).fill(ranks.slice(0, m)).flat()));
        return { arity: ranks.length - 1, max: Math.max(...coverage), coverage, comp, ranks, ivs }
      })
    }
  }



  // Instance

  #keyboard; #mapping; arity; #composition; #equations; #word; #pattern; #mode; #ranks;
  #ivPO; #genICs; #ivNames = new Map()
  // Optional: keyboard, mapping, word, equations, pattern, mode, ranks
  constructor ({ keyboard, mapping, composition, equations, word, pattern, mode, ranks }) {
    if (keyboard) {
      if (!Keyboard.prototype.isPrototypeOf(keyboard)) throw new Error("Scale error: keyboard must be Keyboard object");
      this.#keyboard = keyboard;
    }
    if (mapping) {
      if (!HarmonicMapping.prototype.isPrototypeOf(mapping)) throw new Error("Scale error: mapping must be HarmonicMapping object");
      this.#mapping = mapping
    }
    // TODO allow overdetermination + validation, mode specification by necklace splice point
    if (ranks) this.ranks = ranks;
    else if (pattern) this.pattern = pattern;
    else if (word) this.word = word;
    else if (composition) this.composition = composition;
    else throw new Error("Scale error: must at least provide scale composition");
    if (this.#word) this.#genIntervalData();
    if (mode) this.mode = mode;
    if (equations) this.equations = equations;
  }
  clone () {
    const opt = {};
    if (this.#keyboard) opt.keyboard = this.#keyboard;
    if (this.#mapping) opt.mapping = this.#mapping;
    if (this.#ranks) opt.ranks = this.#ranks;
    else if (this.#pattern) opt.pattern = this.#pattern;
    else if (this.#word) opt.word = this.#word;
    else opt.composition = this.#composition;
    if (this.#mode) opt.mode = this.#mode;
    if (this.#equations) opt.equations = this.#equations;
    return new Scale(opt)
  }



  //Validation

  set keyboard (kb) { if (Keyboard.prototype.isPrototypeOf(kb)) return this.#keyboard = kb }
  get keyboard () { return this.#keyboard }
  set mapping (hm) { if (HarmonicMapping.prototype.isPrototypeOf(kb)) return this.#mapping = hm }
  get mapping () { return this.#mapping }

  // Set (abstract intervals counts) or Map (interval size-count pairs)
  // Remember to test implied edo when composition is a Map and being used in the context of a keyboard
  set composition (comp) {
    const mbEdo = this.#keyboard?.edo ?? 210;
    if (MultiSet.prototype.isPrototypeOf(comp)) {
      if (comp.keys().some(v => typeof v !== "number" || v < 1 || v > mbEdo || v !== Math.floor(v)))
        throw new Error("Scale error: malformed composition")
    }
    else if (Map.prototype.isPrototypeOf(comp)) {
      if (comp.entries().some(([k, v]) => typeof k !== "number" || typeof v !== "number" || k < 1 || v < 1 || k > mbEdo || v > mbEdo ||
        k !== Math.floor(k) || v !== Math.floor(v))) throw new Error("Scale error: malformed composition");
    } else throw new Error("Scale error: composition must be either a MultiSet or a Map")
    this.arity ??= comp.values().reduce((a, b) => a + b, 0);
    if (this.#keyboard && Map.prototype.isPrototypeOf(comp) && comp.entries().reduce((a, [k, v]) => a + k * v, 0) !== mbEdo)
      throw new Error("Scale error: malformed composition");
    this.#composition = comp;
    return this.composition
  }
  get composition () { return this.#composition }

  #wordInMode
  set word (word) {
    if (typeof word !== "string") throw new Error("Scale error: word must be a string");
    else if (this.arity !== undefined) {
      if (word.length !== this.arity) throw new Error("Scale error: word length must equal arity")
    } else this.arity ??= word.length;
    word = Scale.normalisePermutation(word);
    if (word === null) throw new Error("Scale error: word has too many unique symbols");
    const comp = new MultiSet(Common.group(word.split("")).map(ar => ar.length));
    if (this.composition) {
      if (MultiSet.prototype.isPrototypeOf(this.composition)) {
        if (this.composition.symmetricDifference(comp).size)
          throw new Error("Scale error: word does not match scale composition")
      } else if (Map.prototype.isPrototypeOf(this.composition)) {
        if (this.composition.size !== comp.size || this.composition.keys().some(v => !comp.has(v)))
          throw new Error("Scale error: word does not match scale composition");
      }
    } else this.composition = comp;
    this.#word = word;
    { // TODO This shit...
      let rep = this.arity;
      const
        ps = Common.decomp(rep)[0].entries()
          .reduce((m, [p, k]) => m.plus(new MultiSet([p]).scalarMultiply(k)),
            new MultiSet([2]).scalarMultiply(31 - Math.clz32(rep & -rep)));
      MultiSet.enumerateSubsets(ps).forEach(m => {
        const f = m.values().reduce((a, b) => a * b, 1);
        if (Common.quotient(word.match(new RegExp(`.{1,${f}}`, "g"))).length === 1 && f < rep) rep = f
      });
      this.#modeCount = rep
    }
    this.mode = this.#mode ?? 0;
    return this.word
  }
  get word () { return this.#word ? this.#wordInMode : null }

  #primeMode; #patternInMode
  set pattern (pattern) {
    if (typeof pattern !== "string") throw new Error("Scale error: pattern must be a string");
    else if (this.arity !== undefined) {
      if (pattern.length !== this.arity) throw new Error("Scale error: pattern length must equal arity");
    } else this.arity ??= pattern.length;
    pattern = Scale.normalisePattern(pattern);
    if (pattern === null) throw new Error("Scale error: pattern contains unrecognised step names");
    const word = Scale.normalisePermutation(pattern);
    if (this.#word) {
      if (this.#word !== word) throw new Error("Scale error: concrete pattern does not match abstract pattern")
    } else this.word = word;
    this.#pattern = pattern;
    this.mode = this.#mode ?? 0;
    return this.pattern
  }
  get pattern () { return this.#pattern ? this.#patternInMode : null }

   //TODO list of numbers or intervals
  #scaleInMode
  set ranks (ranks) {
    if (!Array.prototype.isPrototypeOf(ranks)) throw new Error("Scale error: ranks must be an array");
    const keyboard = this.#keyboard;
    let edo;
    if (keyboard) ({ edo } = keyboard);
    else if (!Common.between(1, 210, edo = parseInt(ranks.at(-1))))
      throw new Error("Scale error: malformed scale rank list");
    ranks = ranks.map(v => {
      const vv = parseInt(v);
      return vv === edo ? edo : Common.mod(vv, edo)
    });
    if (ranks[0] !== 0 || ranks.at(-1) !== edo || ranks.some((v, i) => i > 0 && v <= ranks[i - 1]))
      throw new Error("Scale error: malformed scale rank list")
    this.arity ??= ranks.length - 1;
    const pattern = Scale.ranksToPattern(ranks);
    if (this.#pattern) {
      if (this.#pattern !== pattern) throw new Error("Scale error: rank list does not match scale pattern")
    } else this.pattern = pattern;
    this.#ranks = ranks;
    this.#primeMode ??= Common.mod(Array(this.arity).fill(0)
      .map((_, i) => [Scale.ranksInMode(ranks, i).map(r => ranks.at(-1) - r), i]).sort().at(-1)[1] + 1, this.#modeCount);
    this.mode = this.#primeMode;
    return this.ranks
  }
  get ranks () { return this.#ranks ? this.#scaleInMode : null }

  #genIntervalData () {
    let gics;
    const mode = this.#primeMode ?? 0, { arity } = this;
    if (this.#ranks) gics = Scale.ranksToGenericIvs(this.ranks);
    else if (this.#word) gics = Scale.mixedWordToGenericIvs(this.pattern ?? this.word);
    this.#genICs = gics.map((gic, i) => gic.map(({ iv, degrees }) =>
      new StepInterval({ scale: this, iv, gic: i, degrees: degrees.map(n => (n + mode) % arity) })));
    this.#ivPO = new StepIntervalPO({ scale: this, ivs: Common.quotient(this.#genICs.flat(), (a, b) => a.equal(b)) });
    if (this.#pattern && !this.#ranks) this.mode = this.#primeMode = Common.mod(Scale.mixedWordToGenericIvsInMode(this.#pattern)
      .sort(({ ivs: as }, { ivs: bs }) => as.toReversed().reduce(({ ord, done = false }, str, i) => {
        if (done) return { ord, done };
        switch (this.#ivPO.cmp(this.#ivPO.getWord(str), this.#ivPO.getWord(bs[bs.length - i - 1]))) {
          case 1: return ord > -1 ? { ord: 1 } : { done: true, ord: -1 };
          case 0: return { ord };
          case -1: return ord < 1 ? { ord: -1 } : { done: true, ord: 1 };
          default: return { done: true, ord }
        }
      }, { ord: 0 }).ord)[0].degree + Math.ceil(this.arity / 2) + 1, this.#modeCount);

    if (this.#pattern) {
      const gicMaxes = [], gicMins = []
      const
        { intervals } = this,
        baseIvs = this.#ranks ? Scale.ranksInMode(this.#ranks, this.#primeMode).map(rank => intervals.getRank(rank)).filter(Boolean) :
          Scale.mixedWordToGenericIvsInMode(this.#pattern)[this.#primeMode].ivs.map(word => intervals.getWord(word));
      Array.from(this.#ivPO).forEach(iv => this.#ivNames.set(iv, new Set()));
      for (let i = 0; i < this.#genICs.length; i++) {
        const gic = this.#genICs[i], { tOSubsets, cmp } = this.#ivPO.getSubPO(gic);
        this.#concatAccid(tOSubsets, { rank: i + 2, accid: "" }, 0, 0, baseIvs[i]);
        gicMaxes.push(Array.from(tOSubsets.at(-1)));
        gicMins.push(Array.from(tOSubsets[0]))
      }
      this.#rothenberg = this.#computeRothenberg(gicMins, gicMaxes, true) ? 1 :
        this.#computeRothenberg(gicMins, gicMaxes, false) ? 0 : -1
    }
    const givs = Array.from(this.#ivPO);
    this.#deepScale = givs.length === Common.group(givs.map(giv => giv.values()
      .reduce((s, iv) => (iv.degrees.forEach(d => s.add(d)), s), new Set()).size)).length
  }
  getGenericIntervalClass (n) { return this.#genICs[n] }

  // Interval name by recursive splitting of ordering
  // TODO not stable under constraint application - leave space for incomparable intervals to be given names
  #concatAccid (ar, name, level, bias, init) {
    if (ar.length === 0) return;
    const
      si = init ? ar.findIndex(ss => ss.has(init)) : ar.length % 2 === 0 ? ar.length / 2 + bias - 1 : (ar.length - 1) / 2,
      left = ar.slice(0, si), right = ar.slice(si + 1);
    this.#concatAccid(left, Object.assign({}, name, { accid: (Scale.#levelChar[level]?.[0] ?? "-") + name.accid }), level + 1, 1);
    if (ar[si].size > 1) Array.from(ar[si]).forEach((iv, j) => this.#ivNames
      .get(iv).add(Object.assign({}, name, { accid: `(${Scale.#wordChars[j]})` + name.accid })));
    else this.#ivNames.get(ar[si].values().next().value).add(name);
    this.#concatAccid(right, Object.assign({}, name, { accid: (Scale.#levelChar[level]?.[1] ?? "+") + name.accid }), level + 1, 0)
  }
  getNames (iv) {
    const { rank, accid } = this.#ivNames.get(this.#ivPO.get(iv));
    return accid + Common.ordinal(rank) +
      this.arity.toString().split("").map(n => String.fromCodePoint(0x2080 + parseInt(n))).join("")
  }

  // TODO rothenberg, lumma stability on rank scales
  #rothenberg
  #computeRothenberg = (mins, maxes, strict) =>
    maxes.reduce((b, max, i) => b && mins.slice(i + 1).every(min => Common.pairwiseCmp(max, min, strict ?
      ((a, b) => this.#ivPO.cmp(a, b) === -1) : ((a, b) => this.#ivPO.cmp(a, b) < 1))), true) &&
    mins.reduce((b, min, i) => b && maxes.slice(0, i).every(max => Common.pairwiseCmp(min, max, strict ?
      ((a, b) => this.#ivPO.cmp(a, b) === 1) : ((a, b) => this.#ivPO.cmp(a, b) > -1))), true)
  get rothenberg () { return this.#rothenberg }
  set rothenberg (_) {}
  #deepScale
  get deepScale () { return this.#deepScale }
  set deepScale (_) {}

  #modeCount
  set mode (mode) {
    if (!this.#word) throw new Error("Scale error: mode requires an abstract scale pattern");
    mode = Common.mod(parseInt(mode), this.#modeCount);
    if (isNaN(mode)) throw new Error("Scale error: bad mode value");
    this.#mode = mode;
    const ranks = this.#ranks, pattern = this.#pattern, word = this.#word;
    if (ranks) this.#scaleInMode = Scale.ranksInMode(ranks, mode);
    if (pattern) this.#patternInMode = pattern.slice(mode) + pattern.slice(0, mode);
    if (word) this.#wordInMode = word.slice(mode) + word.slice(0, mode);
    return mode
  }

  get mode () { return this.#mode }

  // TODO use renaming from earlier if required
  set equations (eqs) {
    if (!Array.prototype.isPrototypeOf(eqs)) throw new Error("Scale error: equations must be an array");
    for (const eq of eqs) {
      if (!Array.prototype.isPrototypeOf(eq) || eq.length !== 2 || eq.some(s => !MultiSet.prototype.isPrototypeOf(s)))
        throw new Error("Scale error: equation must be 2 MultiSets");
      const [lhs, rhs] = eq, mixedChars = Scale.#wordChars + Scale.#patChars;
      if (lhs.plus(rhs).keys().some(k => !mixedChars.includes(k)))
        throw new Error("Scale error: equation must equate known step labels");
    }
    this.#equations = eqs
  }
  get equations () { return this.#equations }

  // TODO: use equations
  get intervals () { return this.#ivPO }
  set intervals (_) {}


  // Generation

  genSymmetricScale () {
    if (!this.#composition) throw new Error("Scale error: requires scale composition");
    const { word, ranks } = Scale.genBilliardPattern(this.#composition), newScale = this.clone();
    if (ranks) newScale.ranks = ranks;
    else if (word) newScale.word = word;
    return newScale
  }
  * genAllPermutations () {
    if (!this.#composition) throw new Error("Scale error: requires scale composition");
    yield * Scale.genAllPermutations(this.#composition)
  }
  setPattern (stepOrder) {
    if (!this.#word) throw new Error("Scale error: requires abstract scale pattern");
    if (!Array.prototype.isPrototypeOf(stepOrder) || stepOrder.length < Common.group(this.#word.split("")).length ||
      !Common.arrEq(stepOrder.sort(), Array(stepOrder.length).fill(0).map((_, i) => i))) return null;
    // More efficient to invert stepOrder, but eh
    const newScale = this.clone();
    newScale.pattern = this.#word.split("").map(c => Scale.#patChars[stepOrder.indexOf(Scale.#wordChars.indexOf(c))]).join("");
    return newScale
  }
  // Infinite list of step size mappings ordered by scale edo
  // TODO I could probably do better...
  * genStepSizeMappingsStream () {
    if (this.#pattern) {
      const givCounts = new MultiSet(this.#pattern.split("")).entries().toArray()
        .sort(([k0], [k1]) => Scale.charCmp(k0, k1)).map(([, v]) => v.length);
      yield * Scale.genIvMappingsFromPatCharCounts(givCounts);
    } else if (MultiSet.prototype.isPrototypeOf(this.#composition)) {
      const gen = Scale.genIvMappingsFromComposition(this.#composition);
      if (this.#word) {
        const givCounts = new MultiSet(this.#word.split("")).entries()
          .reduce((m, [k, v]) => m.concat([[k, v.length]]), []);
        yield * gen.map(({ mapping, edo }) => {
          const m = new Map();
          for (const [s, n0] of mapping) m.set(givCounts.find(([, n1]) => n0 === n1)[0], s);
          return { mapping: m, edo }
        })
      } else yield * gen
    }
  }
  // Constrain mappings to the keyboard edo
  genAllStepSizeMappings () {
    if (!this.#keyboard) throw new Error("Scale error: requires keyboard");
    const { edo } = this.#keyboard, gen = this.genStepSizeMappingsStream();
    let value;
    while (({ value } = gen.next()).value?.edo < edo);
    const result = value?.edo === edo ? [value] : [];
    while (({ value } = gen.next()).value?.edo === edo) result.push(value);
    return result.map(({ mapping }) => mapping)
  }

  setStepSizes (ivMap) {
    if (!this.#word) throw new Error("Scale error: requires scale word");
    const mbEdo = this.#keyboard?.edo ?? 210;
    if (!Map.prototype.isPrototypeOf(ivMap) || ivMap.entries().some(([k, v]) =>
      (!this.#pattern && this.#word && !Scale.#wordChars.includes(k)) || (this.#pattern && !Scale.#patChars.includes(k)) ||
      parseInt(v) !== v || !Common.between(0, mbEdo, v))) return null;
    const newScale = this.clone();
    const v = (this.#pattern ?? this.#word).split("")
      .map(c => ivMap.get(c)).reduce((ar, v) => ar.concat([ ar.at(-1) + v ]), [0]);
    newScale.ranks = v;
    if (this.#keyboard && this.#keyboard.edo !== newScale.ranks.at(-1))
      throw new Error("Scale error: mismatch between ranks and keyboard")
    return newScale
  }



  // Equations

  // TODD: returns a new scale with the given equations applied, or null
  applyEquations (eqs) {}



  // Expression

  // TODO toggle scale highlighting
  #speed = 500
  set speed (v) {
    const s = parseInt(v)
    this.#speed = isNaN(s) ? this.#speed : s;
  }
  get speed () { return this.#speed }
  play (id) {
    if (this.ranks === null) throw new Error("Scale error: requires concrete scale rank list");
    // TODO play at which octave? Play by notes?
    const
      keyboard = this.#keyboard, { edo, hexGrid } = this.#keyboard,
      { orientation: [ g0, h0 ] } = hexGrid, ms = this.#speed;
    return this.ranks.reduce((p, rank) => p.then(Common.wait(ms)).then(b => {
      b && keyboard.stop(id);
      if (rank === edo) keyboard.play(g0, h0, id);
      else {
        const [ g, h ] = keyboard.tuning.getKey(rank).home.coord;
        keyboard.play(g, h, id);
      }
      return true
    }), Promise.resolve(false)).then(Common.wait(ms)).then(() => keyboard.stop(id))
  }
}



class StepInterval {
  // TODO factor through equations - computationally expensive
  static cmp (iv0, iv1) {
    if (iv0.scale !== iv1.scale) return null;
    if (iv0.scale.ranks && iv1.scale.ranks)
      return iv0.value === iv1.value ? 0 : iv0.value > iv1.value ? 1 : -1;
    const scale = iv0.scale, siv0 = iv0.value, siv1 = iv1.value;
    // For now...
    if (siv0.size > siv1.size) return 1;
    else if (siv1.size > siv0.size) return -1;
    const
      d0 = Array.from(siv0.minus(siv1)).sort((a, b) => a - b),
      d1 = Array.from(siv1.minus(siv0)).sort((a, b) => a - b);
    return d0.reduce((ord, char, i) => { switch (ord) {
      case 0: return Scale.charCmp(char, d1[i]);
      case 1: return Scale.charCmp(char, d1[i]) > -1 ? 1 : null;
      case -1: return Scale.charCmp(char, d1[i]) < 1 ? -1 : null;
      default: return null
    } }, 0)
  }
  static multiSetToString (m) {
    return Array.from(m.entries()).sort(([a], [b]) => Scale.charCmp(b, a))
      .reduce((a, [k, v]) => a + v.length + k, "")
  }
  #scale; #value; po; #strRep; #gIC; #degrees
  constructor ({ scale, iv, gic, degrees }) {
    if (!Scale.prototype.isPrototypeOf(scale)) throw new Error("StepInterval error: scale must be Scale object");
    this.#scale = scale;
    const chars = (scale.pattern ?? scale.word).split("");
    if (scale.ranks) {
      if (typeof iv !== "number" || iv < 0 || iv > scale.ranks.at(-1) || iv !== Math.floor(iv))
        throw new Error("StepInterval error: must be an allowed step size");
      this.#strRep = String(iv)
    } else if (scale.word) {
      if (!MultiSet.prototype.isPrototypeOf(iv) || iv.keys().find(char => !chars.includes(char)))
        throw new Error("StepInterval error: must be a MultiSet of allowed characters");
      this.#strRep = StepInterval.multiSetToString(iv)
    }
    this.#value = iv;
    if (gic !== undefined && typeof gic !== "number")
      throw new Error("StepInterval error: generic interval class must be given as a number");
    this.#gIC = gic;
    if (degrees !== undefined && (typeof degrees[Symbol.iterator] !== "function" || degrees.values().some(n => typeof n !== "number")))
      throw new Error("StepInterval error: degree positions must be an Iterable of Numbers");
    this.#degrees = degrees
  }
  get scale () { return this.#scale }
  set scale (_) {}
  get value () { return this.#value }
  set value (_) {}
  get degrees () { return this.#degrees }
  set degrees (_) {}
  get genericInterval () { return this.#scale.intervals.get(this) }
  set genericInterval (_) {}
  get genericIntervalClass () { return this.#scale.getGenericIntervalClass(this.#gIC) }
  set genericIntervalClass (_) {}

  equal (iv) {
    if (!this.#scale.ranks ^ !iv.scale.ranks) return false;
    if (this.#scale.ranks) return this.#value === iv.value;
    else return this.#value.equal(iv.value)
  }

  toString () { return this.#strRep }
}



// Partial ordering on generic intervals. Edges point in descending order.
class StepIntervalPO {
  static fromPattern (pattern) {}

  #scale; #vertices = new Set(); #edges = new Map() // Map(iv -> Set(iv))
  min = new Set(); max = new Set(); tOSubsets = []; #eqs = []
  // TODO accept gics, compute second po with gic ordering
  constructor ({ scale, ivs = [] }) {
    if (!Scale.prototype.isPrototypeOf(scale)) throw new Error("StepIntervalPO error: scale must be Scale object");
    this.#scale = scale;
    if (typeof ivs[Symbol.iterator] !== "function" || ivs.values().some(iv => !StepInterval.prototype.isPrototypeOf(iv)))
      throw new Error("StepIntervalPO error: must provide an Iterable of StepIntervals");
    ivs.forEach(iv => this.add(iv));
    this.#genIncomparables();
    const ord = this.#topOrder();
    this.#vertices = new Set(ord);
    this.#edges = new Map(ord.map(giv => [giv, this.#edges.get(giv)]));
    this.tOSubsets = this.#genTOSubsets();
    if (this.#scale.word && !this.#scale.ranks) this.#genEquations();
  }
  [Symbol.iterator] = () => this.#vertices[Symbol.iterator]()

  add (iv0) {
    const mbGIv = this.#vertices.values().find(iv1 => StepInterval.cmp(iv0, iv1) === 0);
    if (mbGIv === undefined) {
      const s0 = new Set([iv0]), val = { in: new Set(), out: new Set() };
      this.#edges.set(s0, val);
      this.#vertices.add(s0);
      this.#vertices.values().forEach(s1 => {
        const [iv1] = s1, c = StepInterval.cmp(iv0, iv1);
        if (c === null || c === 0 || this.cmp(s0, s1) !== null) return;
        const
          [lhs, rhs] = [[s1, s0], [s0, s1]][(c + 1) / 2],
          { out: lhOuts } = this.#edges.get(lhs), { in: rhIns } = this.#edges.get(rhs)
        lhOuts.add(rhs);
        rhIns.add(lhs);
        for (const lhOut of lhOuts)
          if (this.cmp(rhs, lhOut) === 1) {
          lhOuts.delete(lhOut);
          this.#edges.get(lhOut).in.delete(lhs);
        }
        for (const rhIn of rhIns)
          if (this.cmp(rhIn, lhs) === 1) {
          rhIns.delete(rhIn);
          this.#edges.get(rhIn).out.delete(rhs)
        }
      });
    } else mbGIv.add(iv0);
    iv0.po = this
  }
  // Depth-first search - computationally cheap once the matrix math has been completed
  cmp ([iv0], [iv1]) {
    if (iv0.scale !== this.#scale || iv1.scale !== this.#scale) return null;
    if (this.#vertices.values().find(s => s.has(iv0))?.has(iv1)) return 0;
    if (this.#hasPath(iv0, iv1, new Set())) return 1;
    if (this.#hasPath(iv1, iv0, new Set())) return -1;
    return null
  }
  #hasPath (iv0, iv1, visited) {
    if (this.#vertices.values().find(s => s.has(iv0))?.has(iv1)) return true;
    visited.add(iv0);
    for (const [neighbour] of this.#edges.entries().find(([k]) => k.has(iv0))?.[1].out ?? [])
      if (!visited.has(neighbour) && this.#hasPath(neighbour, iv1, visited)) return true;
    return false
  }
  // Symbol.dispose?
  #genIncomparables () {
    for (const o of this.#edges.values()) o.inc = new Set();
    const vl = Array.from(this.#vertices);
    for (let i = 0; i < vl.length; i++)
      for (let j = i + 1; j < vl.length; j++)
        if (this.cmp(vl[i], vl[j]) === null) {
          this.#edges.get(vl[i]).inc.add(vl[j]);
          this.#edges.get(vl[j]).inc.add(vl[i]);
        }
  }

  // TODO: handle cycles for rothenberg-improper scales?
  #topOrder (edges = this.#edges) {
    const outDeg = new Map(edges.keys().map(s => [ s, { value: 0 } ])), queue = [], ord = [];
    this.max.clear();
    this.min.clear();
    edges.entries().forEach(([v, { in: ins, out: outs }]) => {
      if (ins.size === 0) this.max.add(v);
      if (outs.size === 0) this.min.add(v);
      outDeg.get(v).value = outs.size
    })
    for (const s of edges.keys()) if (outDeg.get(s).value === 0) queue.push(s);
    while (queue.length > 0) {
      const cur = queue.shift();
      ord.push(cur);
      for (const next of edges.get(cur).in)
        if (--outDeg.get(next).value === 0) queue.push(next);
    }
    if (ord.length !== edges.size) throw new Error("StepIntervalPO error: found cycle");
    return ord
  }
  // Show by generic interval
  toString () { return this.#vertices.values().map(s => "[ " + Array.from(s).join("; ") + " ]")
    .reduce((a, b) => a + ", " + b) }
  
  get scale () { return this.#scale }
  set scale (_) {}
  get (iv0) { return this.#vertices.values().find(s => ~Array.from(s).findIndex(iv1 => iv0.equal(iv1))) }
  has (iv0) { return !!~this.#vertices.values().toArray().findIndex(s => ~Array.from(s).findIndex(iv1 => iv0.equal(iv1))) }
  getWord (str) {
    if (!this.#scale.word) return;
    const m = new MultiSet(str.split(""));
    return this.#vertices.values().find(s => ~Array.from(s).findIndex(iv => iv.value.equal(m)));
  }
  hasWord (str) {
    if (!this.#scale.word) return;
    const m = new MultiSet(str.split(""));
    return !!~this.#vertices.values().toArray().findIndex(s => ~Array.from(s).findIndex(iv => iv.value.equal(m)));
  }
  getRank (rank) {
    if (!this.#scale.ranks) return;
    return this.#vertices.values().find(s => ~Array.from(s).findIndex(iv => iv.value === rank));
  }
  hasRank (rank) {
    if (!this.#scale.ranks) return;
    return !!~this.#vertices.values().toArray().findIndex(s => ~Array.from(s).findIndex(iv => iv.value === rank));
  }
  // returns a comparator just on the PO subset containing the given intervals, and the greatest total ordering
  getSubPO (ivs) {
    let vertices = new Set(), edges = new Map();
    for (const iv of ivs) vertices.add(this.get(iv));
    for (const giv of vertices) {
      const { in: ins, out: outs, inc: incs } = this.#edges.get(giv);
      edges.set(giv, {
        in: ins.intersection(vertices),
        out: outs.intersection(vertices),
        inc: incs.intersection(vertices)
      });
    }
    const ord = this.#topOrder(edges);
    vertices = new Set(ord);
    edges = new Map(ord.map(giv => [giv, edges.get(giv)]));
    const hasPath = (s0, s1, visited) => {
      if (s0 === s1) return true;
      visited.add(s0);
      for (const neighbour of edges.get(s0)?.out ?? [])
        if (!visited.has(neighbour) && hasPath(neighbour, s1, visited)) return true;
      return false
    };
    return { tOSubsets: this.#genTOSubsets(edges), cmp (iv0, iv1) {
      const s0 = vertices.values().find(s => s.has(iv0)), s1 = vertices.values().find(s => s.has(iv1));
      if (!s0 || !s1) return null;
      if (s0.has(iv1)) return 0;
      if (hasPath(s0, s1, new Set())) return 1;
      if (hasPath(s1, s0, new Set())) return -1;
      return null
    } }
  }
  // find by predicate on generic interval, ord: 1 => look above, -1 => look below
  find (pred, ord, giv) {
    if (ord === 1) {
      ord = "in";
      giv ??= this.max.values().next().value
    } else if (ord === -1) {
      ord = "out"
      giv ??= this.min.values().next().value
    }
    const queue = Array.from(this.#edges.get(giv)[ord]), visited = new Set();
    while (queue.length > 0) {
      const cur = queue.shift();
      visited.add(cur);
      if (pred(cur)) return cur;
      else this.#edges.get(cur)[ord].forEach(v => visited.has(v) || queue.push(v))
    }
  }

  #genTOSubsets (edges = this.#edges) {
    return Array.from(edges.entries()).reduce(({ result, state }, [v, { inc }], i) => {
      if (inc.size === 0) return {
        result: state.size ? result.concat(state, new Set([v])) : result.concat(new Set([v])),
        state: new Set()
      };
      else if (i === edges.size - 1)
        return { result: state.size ? result.concat(state.add(v)) : result.concat(new Set([v])) };
      else return { result, state: state.add(v) }
    }, { result: [], state: new Set() }).result
  }
  // TODO non-arity-preserving equations such as L=Ms
  #eqChoices
  #genEquations () {
    const incomparableSets = this.tOSubsets.filter(s => s.size !== 0), eqs = [];
    for (const givs of incomparableSets) {
      const subset = Array.from(givs);
      for (let i = 0; i < subset.length; i++) {
        const s0 = subset[i], [iv0] = s0;
        for (let j = i + 1; j < subset.length; j++) {
          // For now...
          const s1 = subset[j], [iv1] = s1;
          let lhs = iv0.value.minus(iv1.value), rhs = iv1.value.minus(iv0.value), g = Common.gcd(lhs.gcd, rhs.gcd);
          lhs = lhs.scalarMultiply(1 / g);
          rhs = rhs.scalarMultiply(1 / g);
          if (lhs.size === 0 || rhs.size === 0 ||
            eqs.some(([m0, m1]) => (m0.equal(lhs) && m1.equal(rhs)) || (m1.equal(lhs) && m0.equal(rhs)))) continue;
          if (Scale.charCmp(lhs.keys().toArray().sort(Scale.charCmp)[0], rhs.keys().toArray().sort(Scale.charCmp)[0]) === 1)
            eqs.push([rhs, lhs]);
          else eqs.push([lhs, rhs]);
        }
      }
    }
    this.#eqChoices = eqs;
  }
  get eqs () { return this.#eqs.slice() }
  set eqs (_) {}

  // TODO: constrain this PO with the given equations
  applyEquations (eqs) {}
  // TODO: minimal set of equations which determines a total ordering between
  //   generic intervals
  eqsForTO () {}
  // TODO: minimal set of equations which determines a total ordering between
  //   generic interval classes (may be incomparable within gic)
  eqsForGICwiseTO (gics) {}
  // TODO: minimal set of equations which determines given value of rothenberg propriety on scale
  // "wlog choices"
  eqsForRothenberg (gics, rothenberg) {}
  // TODO: returns [-1,0,1,null] for LT,EQ,GT,not comparable
  rothenberg (gics) {}
  isTotalOrder () { return this.#edges.values().every(({ inc }) => inc.size === 0) }
}



export { Scale, StepInterval, StepIntervalPO }