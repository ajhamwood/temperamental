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
  static wordCharCmp = (c0, c1) => {
    const i0 = new RegExp(c0).exec(this.#wordChars)?.index, i1 = new RegExp(c1).exec(this.#wordChars)?.index;
    if (i0 === undefined || i1 === undefined) return null; // Not comparable
    else return i0 > i1 ? -1 : i0 < i1 ? 1 : 0
  }
  static findMode = str0 => {
    const sq = Array(str0.length).fill(0).map((_, i) => str0.slice(i) + str0.slice(0, i));
    return str1 => str0.length === str1.length ? sq.indexOf(str1) : -1 }
  static findRanksMode = ar0 => {
    const sq = Array(ar0.length).fill(0).map((_, i) => ar0.slice(i).concat(ar0.slice(0, i)));
    return ar1 => ar0.length === ar1.length ? sq.findIndex(ar => Common.arrEq(ar, ar1)) : -1 }
  static normalisePermutation (str) {
    let symbols = [], remain = str, newStr = "", prev = str.length;
    while (remain.length) {
      const c = remain[0]
      remain = remain.replaceAll(remain[0], "")
      symbols.push([c, prev - (prev = remain.length)]);
    }
    if (symbols.length > Scale.#wordChars.length) return null;
    symbols = symbols.sort(([, a], [, b]) => a < b).map(([c]) => c);
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
    return Array(Math.floor(ranks.length - 2)).fill(0).map((_, i) =>
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
      ivs: Array(Math.floor(str.length - 1)).fill(0).map((_, i) => i + j + 1 > str.length ?
        str.slice(j) + str.slice(0, i + j + 1 - str.length) : str.slice(j, j + i + 1))
    }))
  }
  static mixedWordToGenericIvs (str) {
    return Array(Math.floor(str.length - 1)).fill(0).map((_, i) =>
      Common.group(Array(str.length).fill(0).map((_, j) => ({
        degree: j,
        iv: new MultiSet((i + j + 1 > str.length ?
          str.slice(j) + str.slice(0, i + j + 1 - str.length) : str.slice(j, j + i + 1)).split(""))
      })), ({ iv: a }, { iv: b }) => a.equal(b))
      .map(ivs => ivs.reduce(({ iv, degrees }, { iv: iv0, degree }) =>
        ({ iv: iv ?? iv0, degrees: degrees.concat(degree) }), { iv: null, degrees: [] })))
  }
  static applyMappingToWord (str, m) {
    return str.split("").reduce((ar, c) => ar !== null && m.has(c) ? ar.concat(ar.at(-1) + m.get(c)) : null, [0])
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

  // All billiard patterns for the given word composition, quotient rotations and mirrors
  static genBilliardPattern (composition) {
    const
      comp = composition.values().toArray(),
      t = Array(comp.length).fill(.5), counter = Array(comp.length).fill(0),
      arity = comp.reduce((a, b) => a + b, 0), steps = [], e = Math.sqrt(Number.EPSILON);
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
    const
      compsRaw = Scale.seqPerms(steps).toArray(),
      rots = new Map(compsRaw.map(cs => [cs, cs.map((_, i) => Scale.ranksInMode(cs, i)).flatMap(ar => [ar, ar.toReversed()])])),
      comps = Common.group(compsRaw, (ar0, ar1) => ~rots.get(ar0).findIndex(r0 => Common.arrEq(r0, ar1))).map(([ar]) => ar),
      words = comps.map(rs => rs.map(i => Scale.#wordChars[i]).join(""));
    if (MultiSet.prototype.isPrototypeOf(composition)) return words.map(word => ({ word }));
    else if (Map.prototype.isPrototypeOf(composition)) {
      const keys = composition.keys().toArray();
      return comps.map((c, i) => {
        const ranks = c.reduce((a, i) => a.concat(a.at(-1) + keys[i]), [0]);
        return { word: words[i], ranks, pattern: Scale.ranksToPattern(ranks) }
      })
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
  static * cartProd (array) {
    if (array.length === 0) yield [];
    else if (array.length === 1) yield array[0].map(el => [el]);
    else {
      const [ a0, ...rest ] = array;
      for (let i = 0; i < a0.length; i++)
        yield * Scale.cartProd(rest).flatMap(ars => ars.map(ar => [a0[i]].concat(ar)))
    }
  }
  static * seqPerms (array) {
    if (array.length === 0) yield [];
    else {
      const [ a0, ...rest ] = array;
      yield * Scale.genUniquePerms(a0).flatMap(ar0 => Scale.seqPerms(rest).map(ar1 => ar0.concat(ar1)))
    }
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

  // Infinite list of step size mappings ordered by scale edo
  // TODO I could probably do better...
  static * genStepSizeMappingsStream ({ pattern, composition }) {
    if (pattern) {
      const givCounts = new MultiSet(pattern.split("")).entries().toArray()
        .sort(([k0], [k1]) => Scale.charCmp(k0, k1)).map(([, v]) => v.length);
      yield * Scale.genIvMappingsFromPatCharCounts(givCounts);
    } else if (MultiSet.prototype.isPrototypeOf(composition)) {
      const gen = Scale.genIvMappingsFromComposition(composition);
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
        .flatMap(comp => Scale.genBilliardPattern(comp).map(result => ({ comp, ...result }))))
  }
  
  // TODO expose subcomputations for pruning, worker balancing etc
  // maxVariety === sv => balanced
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



  // Global data

  // data: Map(vertex -> { (in, out): Map(vertex -> [{ mapping, modeMap }]) })
  // vertex: { str, ordered: boolean }
  // mapping: { rules: [ MultiSet(char) ], ordered: boolean }
  // TODO non-TO scales
  static data = new Map()
  static #graphVertices = [];
  static #getWord (s) {
    const eq = Scale.findMode(s);
    return Scale.#graphVertices.find(({ str }) => ~eq(str))
  }
  static #getWordWithOffset (s) {
    const eq = Scale.findMode(s), vertex = Scale.#graphVertices.find(({ str }) => ~eq(str));
    return vertex && { vertex, o: eq(vertex.str) }
  }
  static modeOffset (s) {
    const eq = Scale.findMode(s), w = Scale.#graphVertices.find(({ str }) => ~eq(str))?.str, o = w && eq(w);
    return o ?? 0
  }
  static #markCached (v) { if (v) v.cached = true }

  // Edges go towards ancestor scale, indexed by mapping
  static addData ({ sOut, sIn, mapping, ...edgeData }) {
    // Maybe we need addVertex after all...
    const { str: str0, ordered: o0, ...outData } = sOut, { str: str1, ordered: o1, ...inData } = sIn;
    if (str0.length <= str1.length) return null;
    const
      { data } = Scale,
      s0 = Scale.#getWord(str0) ?? (Scale.#graphVertices.push(sOut = { str: str0, ordered: o0 }), sOut),
      s1 = Scale.#getWord(str1) ?? (Scale.#graphVertices.push(sIn = { str: str1, ordered: o1 }), sIn);
    if (Scale.#getConnected(s0, s1).some(m => Scale.equalScaleMappings(m, mapping))) return data;
    const
      s0Val = data.get(s0) ?? { out: new Map(), in: new Map(), ...outData },
      s1Val = data.get(s1) ?? { out: new Map(), in: new Map(), ...inData };
    data.set(s0, s0Val);
    data.set(s1, s1Val);
    s0Val.out.set(s1, (s0Val.out.get(s1) ?? []).concat([{ mapping, ...edgeData }]));
    s1Val.in.set(s0, (s1Val.in.get(s0) ?? []).concat([{ mapping, ...edgeData }]));
    for (const [ outV, ds ] of s0Val.out) if (outV !== s0) for (const { mapping: m } of ds)
      if (Scale.#getConnected(s1, outV).some(m0 =>
        Scale.composeScaleMappings(mapping, m0).some(m1 => Scale.equalScaleMappings(m1, m)) ||
        Scale.composeScaleMappings(mapping, m).some(m1 => Scale.equalScaleMappings(m0, m1)))) {
        s0Val.out.delete(outV);
        data.get(outV).in.delete(s0)
      }
    for (const [ inV, ds ] of s1Val.in) if (inV !== s1) for (const { mapping: m } of ds)
      if (Scale.#getConnected(inV, s0).some(m0 =>
        Scale.composeScaleMappings(m, mapping).some(m1 => Scale.equalScaleMappings(m0, m1)) ||
        Scale.composeScaleMappings(m0, mapping).some(m1 => Scale.equalScaleMappings(m1, m)))) {
        s1Val.in.delete(inV);
        data.get(inV).out.delete(s1)
      }
    return data
  }

  static cmpScales (str0, str1) {
    const s0 = Scale.#getWord(str0), s1 = Scale.#getWord(str1);
    if (s0 === undefined || s1 === undefined) return;
    return Scale.#getConnected(s0, s1)
  }
  // Collects all connected scales and their mapping
  static #getConnected (s0, s1) { return this.#connectedHelper(s0, s1, [null], new Map()).filter(Boolean) }
  // visited: Map(vertex -> [{ mapping, modeMap }]) - mappings are all out of the s0 applied to getConnected
  static #connectedHelper(s0, s1, mappings, visited) {
    if (s0 === s1) return mappings;
    const s = visited.get(s0) ?? [];
    visited.set(s0, s.concat(mappings = mappings.filter(m0 => !s.some(m1 => Scale.equalScaleMappings(m0, m1)))));
    let nextMappings = [];
    for (const [next, data] of Scale.data.get(s0)?.out ?? []) {
      const comps = Scale.cartProd([mappings, data.map(({ mapping }) => mapping)])
        .flatMap(([m0, m1]) => Scale.composeScaleMappings(m0, m1)).toArray();
      nextMappings = nextMappings.concat(Scale.#connectedHelper(next, s1, comps, visited))
    }
    return Common.group(nextMappings, Scale.equalScaleMappings).map(([m]) => m)
  }

  // TODO function which returns path arrays, or general iterator
  // Collects all connected scales and their associated data
  static paths (str0, str1) {
    const { vertex: s0, o: o0 } = Scale.#getWordWithOffset(str0), { vertex: s1, o: o1 } = Scale.#getWordWithOffset(str1);
    if (s0 == null || s1 == null) return;
    const
      pre = Array(s0.str.length).keys().map(i => [i, Common.mod(i + o0, s0.str.length)]).toArray(),
      post = Array(s1.str.length).keys().map(i => [i, Common.mod(i + o1, s1.str.length)]).toArray();
    return this.#pathHelper(s0, s1, [{ modeMap: pre }], new Map()).filter(Boolean)
      .flatMap(d => Scale.#composeScaleEntries(d, { modeMap: post }))
  }
  // data: [{ mapping, modeMap }]
  static #pathHelper (s0, s1, data, visited) {
    if (s0 === s1) return data;
    const s = visited.get(s0) ?? [];
    visited.set(s0, s.concat(data = data.filter(d => d && !s.some(({ mapping }) => Scale.equalScaleMappings(d.mapping, mapping)))));
    let nextData = [];
    for (const [next, ds] of Scale.data.get(s0)?.out ?? []) {
      const comps = Scale.cartProd([data, ds]).flatMap(([d0, d1]) => Scale.#composeScaleEntries(d0, d1)).toArray();
      nextData = nextData.concat(Scale.#pathHelper(next, s1, comps, visited))
    }
    return Common.group(nextData, ({ mapping: m0 }, { mapping: m1 }) => Scale.equalScaleMappings(m0, m1)).map(([d]) => d)
  }

  // returns list m0⨟m1 where m1's character set agrees with m0's ordered status
  // if m0 is ordered, returns one composition. if m1 is unordered, return all possible compositions
  static composeScaleMappings (m0, m1) {
    if (m0 == null) return [m1];
    if (m1 == null) return [m0];
    if (m1.rules.some(m0.ordered ? 
      ms => ms.keys().some(c => !Scale.#patChars.includes(c)) :
      ms => ms.keys().some(c => !Scale.#wordChars.includes(c)))) return [];
    if (m0.rules.length !== m1.rules.reduce((a, b) => a.union(b), new MultiSet()).repr.length) return [];
    // TODO: This could be avoided with a scale mapping class
    const charOrd = [...m1.rules.reduce((a, b) => a.union(new Set(b.keys())), new Set())].sort((a, b) => Scale.charCmp(b, a));
    return (m0.ordered ? [m0.rules] : Scale.genUniquePerms(m0.rules).toArray())
      .map(mleft => ({ ordered: m1.ordered,
        rules: m1.rules.map(ms => new MultiSet(ms.repr.flatMap(([c, k]) => [...mleft[charOrd.indexOf(c)].scalarMultiply(k)])))
      }))
  }
  static equalScaleMappings ({ ordered: o0, rules: r0 } = {}, { ordered: o1, rules: r1 } = {}) {
    if (o0 !== o1) return false;
    if (o0) return r0.every((ms, i) => ms.equal(r1[i]));
    else {
      const [b, rem] = r0.reduce(([b, rRem], ms0) => {
        if (!b) return [false];
        const i = rRem.findIndex(ms1 => ms1.equal(ms0));
        return ~i ? [true, rRem.toSpliced(i, 1)] : [false]
      }, [true, r1]);
      return b && rem.length === 0
    }
  }

  // TODO compose constraints (lts)
  static #composeScaleEntries (d0, d1) {
    const { mapping: m1, modeMap: o1 } = d1;
    if (d0 == null) return [d1];
    if (d1 == null) return [d0];
    const
      { mapping: m0, modeMap: o0 } = d0,
      prev = Map.groupBy(o0, ([, b]) => b), next = Map.groupBy(o1, ([a]) => a),
      modeMap = Common.quotient(next.entries().flatMap(([m0, m1s]) => (prev.get(m0) ?? [])
        .flatMap(m => m1s.map(([, m1]) => m.with(1, m1)))).toArray(), Common.arrEq).sort();
    return Scale.composeScaleMappings(m0, m1).map(m => ({ mapping: m, modeMap }))
  }

  // returns all ancestor scales which contain the given interval
  // iv: Multiset (later, step size for ranks?)
  static getAncestorsByIv (str, iv) {
    const v = Scale.#getWord(str);
    if (v) return Scale.#getAncestorsByIv(str, v, iv, new Map([[v, [{ ordered: v.ordered, rules: [] }]]]))
  }
  static * #getAncestorsByIv (strInit, v, iv, visited) {
    const { out, in: _, ...scaleData } = Scale.data.get(v);
    for (const [vOut] of out) {
      const { cached, ...ret } = vOut;
      for (const { mapping, ...edgeData } of Scale.paths(strInit, vOut.str))
        if (!visited.get(vOut)?.some(m => Scale.equalScaleMappings(m, mapping))) {
          let rec = false;
          for (const m of mapping.rules) {
            if (m.symmetricDifference(iv).size === 0) {
              const s = visited.get(vOut) ?? [];
              visited.set(vOut, Common.quotient(s.concat(mapping), Scale.equalScaleMappings));
              yield { mapping, ...ret, ...scaleData, ...edgeData };
            }
            if (m.minus(iv).size === 0) rec = true
          }
          if (rec) yield * Scale.#getAncestorsByIv(strInit, vOut, iv, visited)
        }
    }
  }

  // Caching
  static ancestors (str) {
    const v = Scale.#getWord(str);
    if (v?.cached) return Scale.#ancestors(v, v, new Map([[v, [{ ordered: v.ordered, rules: [] }]]]))
  }
  static * #ancestors (vinit, v, visited) {
    const { in:_, out, ...scaleData } = Scale.data.get(v) ?? {};
    const s = visited.get(v) ?? [], newPaths = [];
    for (const { mapping, modeMap } of Scale.paths(vinit.str, v.str)){
      if (!visited.get(v)?.some(m => Scale.equalScaleMappings(m, mapping))) {
        newPaths.push(mapping);
        yield { [v.ordered ? "pattern" : "word"]: v.str, isOrdered: v.ordered,
          ...(mapping ? { mapping } : {}), modeMap, ...scaleData };
        }}
    visited.set(v, Common.quotient(s.concat(newPaths), Scale.equalScaleMappings));
    for (const [ { str } ] of out) yield * Scale.#ancestors(vinit, Scale.#getWord(str), visited)
  }
  static ancestorScales (str) {
    const v = Scale.#getWord(str);
    if (v?.cached) return Scale.#ancestorScales(v, new Set())
  }
  static * #ancestorScales (v, visited) {
    visited.add(v.str);
    yield v.str;
    const { out } = Scale.data.get(v);
    for (const [ { str } ] of out) if (!visited.has(str)) yield * Scale.#ancestorScales(Scale.#getWord(str), visited)
  }
  // Dangerous for now...
  static cacheAllScales () {
    const vs = Scale.data.keys().filter(({ cached }) => !cached).toArray().sort(({ str: s0 }, { str: s1 }) => s0.length - s1.length);
    for (const { str, ordered } of vs)
      new Scale(ordered ? { pattern: str } : { word: str }).genAncestorScales()
  }



  // Instance

  #keyboard; #mapping; arity; #composition; #equations; #word; #pattern; #mode; #ranks;
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
    // Mode behaviour: not definable for composition scale, no default for word scale,
    //   default is primeMode for pattern scale+
    if (mode !== undefined || this.#primeMode !== undefined) this.mode = mode ?? this.#primeMode;
    if (equations) this.equations = equations;
    this.#initialised = true;
  }
  #initialised
  get initialised () { return this.#initialised }
  set initialised (_) {}
  clone () {
    const opt = {};
    if (this.#keyboard) opt.keyboard = this.#keyboard;
    if (this.#mapping) opt.mapping = this.#mapping;
    if (this.#ranks) opt.ranks = this.#ranks;
    else if (this.#pattern) opt.pattern = this.#pattern;
    else if (this.#word) opt.word = this.#word;
    else opt.composition = this.#composition;
    if (this.#mode !== undefined) opt.mode = this.#mode;
    if (this.#equations) opt.equations = this.#equations;
    return new Scale(opt)
  }



  //Validation

  set keyboard (kb) { if (Keyboard.prototype.isPrototypeOf(kb)) return this.#keyboard = kb }
  get keyboard () { return this.#keyboard }
  set mapping (hm) { if (HarmonicMapping.prototype.isPrototypeOf(kb)) return this.#mapping = hm }
  get mapping () { return this.#mapping }

  // MultiSet (abstract intervals counts) or Map (interval size-count pairs)
  // Remember to test implied edo when composition is a Map and being used in the context of a keyboard
  set composition (comp) {
    const mbEdo = this.#keyboard?.edo ?? 210;
    if (MultiSet.prototype.isPrototypeOf(comp)) {
      if (comp.keys().some(v => parseInt(v) !== v || !Common.between(1, mbEdo, v))) throw new Error("Scale error: malformed composition")
    } else if (Map.prototype.isPrototypeOf(comp)) {
      if (comp.entries().some(([k, v]) => parseInt(k) !== k || parseInt(v) !== v || !Common.between(1, mbEdo, k) || !Common.between(1, mbEdo, v)))
        throw new Error("Scale error: malformed composition");
    } else throw new Error("Scale error: composition must be either a MultiSet or a Map")
    this.arity ??= comp.values().reduce((a, b) => a + b, 0);
    if (this.#keyboard && Map.prototype.isPrototypeOf(comp) && comp.entries().reduce((a, [k, v]) => a + k * v, 0) !== mbEdo)
      throw new Error("Scale error: malformed composition");
    this.#composition = comp;
    return this.composition
  }
  get composition () { return this.#composition }

  #wordInMode; isBalanced
  set word (word) {
    if (this.#word) {
      const ix = Scale.findMode(this.#word)(word);
      return ~ix && (this.mode = ix);
    }
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
    this.#modeCount = Scale.findMode(word)(word.at(-1) + word.slice(0, -1)) + 1;
    // TODO affected by equations
    this.isBalanced = Scale.mixedWordToGenericIvs(word).every(ar => ar.length <= this.#composition.size)
    return this.word
  }
  get word () { return this.#word ? this.#wordInMode ?? this.#word : null }

  #primeMode; #patternInMode
  set pattern (pattern) {
    if (this.#pattern) {
      const ix = Scale.findMode(this.#pattern)(pattern);
      return ~ix && (this.mode = ix);
    }
    let init = false;
    if (this.#initialised) {
      this.#initialised = false;
      init = true
    }
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
    const { intervals } = this;
    this.#primeMode = Common.mod(Scale.mixedWordToGenericIvsInMode(this.#pattern)
      .sort(({ ivs: as }, { ivs: bs }) => as.toReversed().reduce(({ ord, done = false }, str, i) => {
        if (done) return { ord, done };
        switch (intervals.cmp(intervals.getWord(str), intervals.getWord(bs[bs.length - i - 1]))) {
          case 1: return ord > -1 ? { ord: 1 } : { done: true, ord: -1 };
          case 0: return { ord };
          case -1: return ord < 1 ? { ord: -1 } : { done: true, ord: 1 };
          default: return { done: true, ord }
        }
      }, { ord: 0 }).ord)[0].degree + 1, this.#modeCount);
    if (init) {
      this.#genIvData();
      this.mode = this.#primeMode ?? this.#mode;
      this.#initialised = true
    }
    return this.pattern
  }
  get pattern () { return this.#pattern ? this.#patternInMode ?? this.#pattern : null }

   //TODO list of numbers or intervals
  #ranksInMode
  set ranks (ranks) {
    if (this.#ranks) {
      const ix = Scale.findRanksMode(this.#ranks)(ranks);
      return ~ix && (this.mode = ix);
    }
    let init = false;
    if (this.#initialised) {
      this.#initialised = false;
      init = true
    }
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
    if (init) {
      this.#genIvPO();
      this.#genIvData();
      this.mode = this.#mode ?? this.#primeMode;
      this.#initialised = true
    }
    return this.ranks
  }
  get ranks () { return this.#ranks ? this.#ranksInMode ?? this.#ranks : null }



  // Data

  #intervals; #genICs
  getGenericIntervalClass (n) { return (this.#genICs ?? (this.#genIvPO().genICs))[n] }
  get intervals () { return this.#intervals ?? (this.#genIvPO()).intervals }
  set intervals (_) {}
  #genIvPO () {
    let gics;
    if (this.#ranks) gics = Scale.ranksToGenericIvs(this.ranks);
    else if (this.#word) gics = Scale.mixedWordToGenericIvs(this.pattern ?? this.word);
    else return {};
    const { genICs, intervals } = StepIntervalPO.create({ scale: this, gics });
    this.#genICs = genICs;
    this.#intervals = intervals;
    return { intervals, genICs }
  }

  #isDeepScale
  get isDeepScale () { return this.#isDeepScale ??= this.intervals.size === Common.group(this.intervals.values().map(giv => giv.values()
    .reduce((s, iv) => (iv.degrees.forEach(d => s.add(d)), s), new Set()).size).toArray()).length }
  set isDeepScale (_) {}

  #ivNames; #rankNames; #rothenberg
  getNames (iv) {
    if (!StepInterval.prototype.isPrototypeOf(iv)) return null;
    return (this.#ivNames ??= this.#genIvData().ivNames).get(this.intervals.get(iv)).values()
      .map(({ rank, accid }) => accid + Common.ordinal(rank) +
        this.arity.toString().split("").map(n => String.fromCodePoint(0x2080 + parseInt(n))).join("")).toArray().join("; ") }
  getRankNames (rank) {
    if (this.#ranks) return Array.from((this.#rankNames ??= this.#genIvData().rankNames).get(rank)).map(({ rank, accid }) => accid + Common.ordinal(rank) +
      this.arity.toString().split("").map(n => String.fromCodePoint(0x2080 + parseInt(n))).join("")) }
  // TODO rothenberg, lumma stability on rank scales
  #computeRothenberg = (mins, maxes, strict) =>
    maxes.reduce((b, max, i) => b && mins.slice(i + 1).every(min => Common.pairwiseCmp(max, min, strict ?
      ((a, b) => this.intervals.cmp(a, b) === -1) : ((a, b) => this.intervals.cmp(a, b) < 1))), true) &&
    mins.reduce((b, min, i) => b && maxes.slice(0, i).every(max => Common.pairwiseCmp(min, max, strict ?
      ((a, b) => this.intervals.cmp(a, b) === 1) : ((a, b) => this.intervals.cmp(a, b) > -1))), true)
  get rothenberg () { return this.#rothenberg ??= this.#genIvData().rothenberg }
  set rothenberg (_) {}

  #genIvData () {
    const
      { arity, intervals } = this, gicMaxes = [], gicMins = [], gicTOSubsets = [], ivNames = this.#ivNames = new Map(),
      baseIvs = this.#ranks ? Scale.ranksInMode(this.#ranks, this.#primeMode).map(rank => intervals.getRank(rank)).filter(Boolean) :
        Scale.mixedWordToGenericIvsInMode(this.#pattern)[this.#primeMode].ivs.map(word => intervals.getWord(word));
    intervals.values().forEach(giv => ivNames.set(giv, new Set()));
    for (let i = 0; i < arity - 1; i++) {
      const
        { tOSubsets } = intervals.getSubPO(this.getGenericIntervalClass(i)),
        tOThis = tOSubsets.map(ss => new Set([...ss].map(([iv]) => intervals.get(iv))));
      gicTOSubsets.push(tOThis);
      gicMaxes.push(Array.from(tOThis.at(-1)));
      gicMins.push(Array.from(tOThis[0]))
    }
    const
      rothenberg = this.#rothenberg = this.#computeRothenberg(gicMins, gicMaxes, true) ? 1 :
        this.#computeRothenberg(gicMins, gicMaxes, false) ? 0 : -1,
      rankNames = this.#rankNames = new Map(), result = { ivNames, rothenberg, rankNames };
    if (this.#ranks && rothenberg >= 0) {
      for (let i = 0; i < this.#ranks.at(-1); i++) this.#rankNames.set(i, new Set());
      const min = [...gicMins[0][0]][0].value, max = [...gicMaxes.at(-1)[0]][0].value;
      if (min > 0) {
        this.#rankNames.get(0).add({ rank: 1, accid: "" });
        this.#concatAccid([], { rank: 1, accid: "A" }, 1, 1, false, Array(Math.ceil((min - 1) / 2)).fill(0).map((_, i) => i + 1));
      }
      for (let i = 0; i < arity - 1; i++) {
        const
          curMin = [...gicMins[i][0]][0].value,
          lower = curMin - Math.max(0, Math.floor((curMin - (i === 0 ? 0 : [...gicMaxes[i - 1][0]][0].value) - 1) / 2)),
          curMax = [...gicMaxes[i][0]][0].value,
          upper = curMax + Math.ceil(((i === arity - 2 ? this.#ranks.at(-1) - 1 : [...gicMins[i + 1][0]][0].value) - curMax - 1) / 2);
        this.#concatAccid(gicTOSubsets[i], { rank: i + 2, accid: "" }, 0, 0, baseIvs[i],
          Array(upper - lower + 1).fill(0).map((_, i) => i + lower))
      }
      if (max < this.#ranks.at(-1) - 1) {
        this.#concatAccid([], { rank: arity + 1, accid: "d" }, 1, 0, false,
          Array(Math.ceil((this.#ranks.at(-1) - max - 1) / 2)).fill(0).map((_, i) => this.#ranks.at(-1) - i - 1).reverse());
      }
    }
    else for (let i = 0; i < arity - 1; i++)
      this.#concatAccid(gicTOSubsets[i], { rank: i + 2, accid: "" }, 0, 0, baseIvs[i]);
    return result
  }
  // Interval name by recursive splitting of ordering, relative to scale
  #concatAccid (ar, name, level, bias, init, ranks) {
    if (ar.length === 0 && !ranks?.length) return;
    const
      si = init ? ar.findIndex(ss => ss.has(init)) : ar.length % 2 === 0 ? Math.max(0, ar.length / 2 + bias - 1) : (ar.length - 1) / 2,
      left = ar.slice(0, si), right = ar.slice(si + 1), leftRanks = [], rightRanks = [];
    let ri;
    if (ranks?.length) {
      ri = ar.length ? ranks.indexOf([...[...ar[si]][0]][0].value) : ranks.length % 2 === 0 ? ranks.length / 2 + bias - 1 : (ranks.length - 1) / 2;
      leftRanks.splice(0, 0, ...ranks.slice(0, ri));
      rightRanks.splice(0, 0, ...ranks.slice(ri + 1));
    }
    this.#concatAccid(left, Object.assign({}, name, { accid: (Scale.#levelChar[level]?.[0] ?? "-") + name.accid }), level + 1, bias, false, leftRanks);
    if (ar.length) if (ar[si].size > 1) Array.from(ar[si]).forEach((iv, j) => this.#ivNames
      .get(iv).add(Object.assign({}, name, { accid: `(${Scale.#wordChars[j]})` + name.accid })));
    else this.#ivNames.get([...ar[si]][0]).add(name);
    if (ranks?.length) this.#rankNames.get(ranks[ri]).add(name)
    this.#concatAccid(right, Object.assign({}, name, { accid: (Scale.#levelChar[level]?.[1] ?? "+") + name.accid }), level + 1, 1 - bias, false, rightRanks)
  }

  #modeCount; #intervalsInMode
  set mode (mode) {
    if (!this.#word) throw new Error("Scale error: mode requires an abstract scale pattern");
    mode = Common.mod(parseInt(mode), this.#modeCount);
    if (isNaN(mode)) throw new Error("Scale error: bad mode value");
    this.#mode = mode;
    const ranks = this.#ranks, pattern = this.#pattern, word = this.#word;
    if (ranks) this.#ranksInMode = Scale.ranksInMode(ranks, mode);
    if (pattern) this.#patternInMode = pattern.slice(mode) + pattern.slice(0, mode);
    if (word) {
      this.#wordInMode = word.slice(mode) + word.slice(0, mode);
      if (ranks) this.#intervalsInMode = this.#ranksInMode.slice(1, -1).map(r => this.intervals.getRank(r));
      else this.#intervalsInMode = Scale.mixedWordToGenericIvsInMode(pattern ?? word)[mode].ivs.map(str => this.intervals.getWord(str));
    }
    return mode
  }
  get mode () { return this.#mode }
  get primeMode () { return this.#primeMode }
  set primeMode (_) {}
  getInterval (n) { return this.#mode === undefined ? undefined : this.#intervalsInMode[n - 2]}

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



  // Generation

  // Doesn't include inverted scales
  genSymmetricScales ({ mode } = {}) {
    if (!this.#composition) throw new Error("Scale error: requires scale composition");
    return Scale.genBilliardPattern(this.#composition).map(({ word, ranks }) => {
      const newScale = this.clone();
      if (ranks) newScale.ranks = ranks;
      else if (word) newScale.word = word;
      if (mode !== undefined) newScale.mode = mode;
      return newScale
    })
  }
  * genAllPermutations () {
    if (!this.#composition) throw new Error("Scale error: requires scale composition");
    yield * Scale.genAllPermutations(this.#composition)
  }
  // Converts word scale to pattern scale by assigning word symbols the given descending order
  setPattern (stepOrder) {
    if (!this.#word) throw new Error("Scale error: requires abstract scale pattern");
    if (!Array.prototype.isPrototypeOf(stepOrder) || stepOrder.length < this.#composition.keys().toArray().length ||
      !Common.arrEq(stepOrder.toSorted(), Array(stepOrder.length).fill(0).map((_, i) => i))) return null;
    const newScale = this.clone();
    newScale.pattern = this.#word.split("").map(c => Scale.#patChars[stepOrder.indexOf(Scale.#wordChars.indexOf(c))]).join("");
    return newScale
  }
  // Skips all mappings except the keyboard edo
  genAllStepSizeMappings () {
    if (!this.#keyboard) throw new Error("Scale error: requires keyboard");
    const
      { edo } = this.#keyboard,
      gen = Scale.genStepSizeMappingsStream({ pattern: this.#pattern, composition: this.#composition });
    let value;
    while (({ value } = gen.next()).value?.edo < edo);
    const result = value?.edo === edo ? [value] : [];
    while (({ value } = gen.next()).value?.edo === edo) result.push(value);
    return result.map(({ mapping }) => mapping)
  }
  setStepSizes (ivSizes) {
    if (!this.#word) throw new Error("Scale error: requires scale word");
    const mbEdo = this.#keyboard?.edo ?? 210, newScale = this.clone();
    if (this.#pattern) {
      if (typeof ivSizes[Symbol.iterator] !== "function" || ivSizes.values().some(v => parseInt(v) !== v)) return null;
      ivSizes.sort((a, b) => b - a);
      const chars = new MultiSet(this.#pattern.split("")).keys().toArray().sort((a, b) => Scale.charCmp(b, a));
      newScale.ranks = this.#pattern.split("").reduce((ar, c) => ar.concat([ ar.at(-1) + ivSizes[chars.indexOf(c)] ]), [0])
    } else {
      if (!Map.prototype.isPrototypeOf(ivSizes) || ivSizes.entries().some(([k, v]) =>
       !Scale.#wordChars.includes(k) || parseInt(v) !== v || !Common.between(0, mbEdo, v))) return null;
      newScale.ranks = this.#word.split("").map(c => ivSizes.get(c)).reduce((ar, v) => ar.concat([ ar.at(-1) + v ]), [0])
    }
    if (this.#keyboard && this.#keyboard.edo !== newScale.ranks.at(-1))
      throw new Error("Scale error: mismatch between ranks and keyboard");
    return newScale
  }
  // All scales on this keyboard that fit the current constraints
  * genAllConcreteScales () {}

  genAncestorScales (sv = this.#composition.size) {
    if (!this.#word) return;
    const vertex = Scale.#getWord(this.#pattern ?? this.#word);
    if (vertex?.cached) return Scale.ancestors(vertex.str).toArray();

    const
      ivs = Array.from(this.intervals),
      // modeMap: [unique [outerMode, innerMode]]
      rec = (mapping, mode, offset, pos) => {
        if (offset === this.arity) {
          const m = mapping.entries().toArray().sort(([a], [b]) => a < b);
          if (pos >= m.length) {
            let i = 0, ix, word = "";
            while ((ix = m.findIndex(([, poss]) => poss[0] === i)) >= 0) {
              m[ix][1].shift();
              word += Scale.#wordChars[ix];
              i++
            }
            const strMode = Scale.findMode([...word].reverse().join(""));
            for (const { word, mapping, modeMap } of patterns) {
              if (!Common.arrEq(mapping, m.map(([ix]) => ix))) continue;
              const ix = strMode([...word].reverse().join(""));
              if (!~ix) continue;
              modeMap.push([mode, ix]);
              return 
            }
            patterns.push({ modeMap: [[mode, 0]], mapping: m.map(([ivIx]) => ivIx), word })
          }
          return
        }
        let i = 1;
        while (offset + i <= this.arity) {
          this.mode = mode + offset;
          const
            ivIx = ivs.indexOf(this.getInterval(i + 1)),
            m = new Map(mapping.entries().map(([k, v]) => [k, v.slice()]));
          if (~ivIx && (m.has(ivIx) || m.size < sv)) {
            m.set(ivIx, (m.get(ivIx) ?? []).concat(pos));
            rec(m, mode, offset + i, pos + 1);
          }
          i++
        }
      },
      mode = this.mode, patterns = [];
    this.mode = 0;
    const o = Boolean(this.pattern), thisStr = o ? this.pattern : this.word, offset = Scale.modeOffset(thisStr);
    for (let i = 0; i < this.#modeCount; i++) {
      rec(new Map(), i, 0, 0);
      this.mode++
    }
    if (mode) this.mode = mode;
    const { true: ordered = [], false: unordered = [] } = Common.groupBy(patterns.map(({ modeMap, mapping: m, word }) => {
      const
        isBalanced = Scale.mixedWordToGenericIvs(word).every(ar => ar.length <= m.length),
        mapping = m.map(n => ivs[n]),
        po = this.intervals.getSubPO(mapping.reduce((a, b) => a.union(b), new Set())),
        topOrd = [...po].map(([iv]) => iv).reverse(),
        pattern = Scale.normalisePattern(word.split("")
          .map(c => Scale.#patChars[topOrd.indexOf([...mapping[Scale.#wordChars.indexOf(c)]][0])]).join(""));
      Scale.addData({
        sOut: { str: thisStr, ordered: o, isBalanced: this.isBalanced },
        sIn: { str: po.isTotalOrder ? pattern : word, ordered: po.isTotalOrder, isBalanced },
        mapping: { rules: mapping.map(si => [...si][0].value), ordered: po.isTotalOrder },
        modeMap: modeMap.map(([o, i]) => [ Common.mod(o - offset, this.#modeCount), i ]).sort(),
        lts: po.graph
      });
      return po.isTotalOrder ?
        { modeMap, mapping, isBalanced, isOrdered: true, pattern } :
        { modeMap, mapping, isBalanced, isOrdered: false, word, lts: po.graph }
    }), ({ isOrdered }) => isOrdered);
    Scale.#markCached(Scale.#getWord(thisStr));
    return ordered.sort(({ pattern: p0 }, { pattern: p1 }) => p1.length - p0.length)
      .concat(unordered.sort(({ word: w0 }, { word: w1 }) => w1.length - w0.length))
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



// TODO remove scale => ordered: boolean; po: StepIntervalPO|null
class StepInterval {
  // Simple equality
  static cmp (iv0, iv1) {
    if (StepInterval.prototype.isPrototypeOf(iv0)) iv0 = iv0.value;
    if (StepInterval.prototype.isPrototypeOf(iv1)) iv1 = iv1.value;
    if (iv0.constructor.name !== iv1.constructor.name ||
      iv0.constructor.name !== "Number" && iv0.constructor.name !== "MultiSet") return null;
    if (typeof iv0 === "number") return iv0 === iv1 ? 0 : iv0 > iv1 ? 1 : -1;
    if (iv0.size > iv1.size) return 1;
    else if (iv1.size > iv0.size) return -1;
    const
      d0 = Array.from(iv0.minus(iv1)).sort((a, b) => a - b),
      d1 = Array.from(iv1.minus(iv0)).sort((a, b) => a - b);
    return d0.reduce((ord, char, i) => { switch (ord) {
      case 0: return Scale.charCmp(char, d1[i]);
      case 1: return Scale.charCmp(char, d1[i]) > -1 ? 1 : null;
      case -1: return Scale.charCmp(char, d1[i]) < 1 ? -1 : null;
      default: return null
    } }, 0)
  }
  static multiSetToString (m) {
    return Array.from(m.entries()).sort(([a], [b]) => Scale.charCmp(b, a) || Scale.wordCharCmp(b, a))
      .reduce((a, [k, v]) => a + v.length + k, "")
  }
  #scale; #value; po; #strRep; #gIC; #degrees
  constructor ({ scale, iv, gic, degrees }) {
    if (!Scale.prototype.isPrototypeOf(scale)) throw new Error("StepInterval error: scale must be Scale object");
    this.#scale = scale;
    const chars = (scale.pattern ?? scale.word).split("");
    if (scale.ranks) {
      if (parseInt(iv) !== iv || !Common.between(0, scale.ranks.at(-1), iv)) throw new Error("StepInterval error: must be an allowed step size");
      this.#strRep = String(iv)
    } else if (scale.word) {
      if (!MultiSet.prototype.isPrototypeOf(iv) || iv.keys().find(char => !chars.includes(char)))
        throw new Error("StepInterval error: must be a MultiSet of allowed characters");
      this.#strRep = StepInterval.multiSetToString(iv)
    }
    this.#value = iv;
    if (gic !== undefined && !Set.prototype.isPrototypeOf(gic) && gic.values().some(n => parseInt(n) !== n || n < 0))
      throw new Error("StepInterval error: generic interval class must be given as a Set of positive integers");
    this.#gIC = gic;
    if (degrees !== undefined && !Set.prototype.isPrototypeOf(degrees) || degrees.values().some(n => parseInt(n) !== n || n < 0))
      throw new Error("StepInterval error: degree positions must be a Set of positive integers");
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
  applyMapping (m) {
    if (typeof this.#value === "number") return;
    if (m.values().every(v => typeof v === "number"))
      return this.#value.entries().reduce((n, [c, v]) => n !== null && m.has(c) ? n + v.length * m.get(c) : null, 0);
    else return MultiSet.from(new Map(this.#value.entries().reduce((ar, [c, v]) => ar !== null && m.has(c) ? ar.concat([[m.get(c), v.length]]) : null, [])))
  }

  toString () { return this.#strRep }
}



// TODO remove scale => ordered: boolean; octave: str|ranks?
// Necklace class?
// Partial ordering on generic intervals. Edges point in descending order.
class StepIntervalPO {
  // Interval set by simple equality
  static create ({ scale, gics }) {
    if (typeof gics[Symbol.iterator] !== "function" || gics.values().some(gic => typeof gics[Symbol.iterator] !== "function" ||
      gic.values().some(obj => typeof obj?.degrees[Symbol.iterator] !== "function" ||
        !(typeof obj?.iv === "number" || MultiSet.prototype.isPrototypeOf(obj?.iv)))))
      throw new Error("StepIntervalPO error: generic interval class array malformed");
    const ivs = new Map(), { arity, primeMode } = scale, mode = primeMode ?? 0;
    for (let i = 0; i < gics.length; i++) for (const { iv, degrees: ds } of gics[i]) {
      const mbGiv = ivs.keys().find(iv1 => StepInterval.cmp(iv, iv1) === 0);
      if (mbGiv) {
        const { gic, degrees } = ivs.get(mbGiv);
        gic.add(i);
        for (const d of ds) degrees.add(d)
      } else ivs.set(iv, { gic: new Set([i]), degrees: new Set(ds.map(n => (n + mode) % arity)) })
    }
    for (const [ iv, { gic, degrees } ] of ivs) ivs.set(iv, new StepInterval({ scale, iv, gic, degrees }));
    const
      genICs = gics.map((gic, i) => gic.map(({ iv }) => ivs.entries().find(([iv1]) => StepInterval.cmp(iv, iv1) === 0)[1])),
      intervals = new StepIntervalPO({ scale, ivs: Common.quotient(genICs.flat(), (a, b) => a.equal(b)) });
    return { genICs, intervals }
  }

  #scale; #vertices = new Set(); #edges = new Map() // Map(iv -> Set(iv))
  min = new Set(); max = new Set(); #eqs = []
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
    if (this.#scale.word && !this.#scale.ranks) this.#genEquations();
  }
  [Symbol.iterator] = () => this.#vertices[Symbol.iterator]()
  values = this[Symbol.iterator]
  get size () { return this.#vertices.size }
  set size (_) {}

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
  cmp ([iv0] = [], [iv1] = []) {
    if (iv0?.scale !== this.#scale || iv1?.scale !== this.#scale) return null;
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
  getWord (str) { return this.getBag(new MultiSet(str.split(""))) }
  hasWord (str) { return this.hasBag(new MultiSet(str.split(""))) }
  getRank (rank) {
    if (!this.#scale.ranks) return;
    return this.#vertices.values().find(s => ~Array.from(s).findIndex(iv => iv.value === rank));
  }
  hasRank (rank) {
    if (!this.#scale.ranks) return false;
    return Boolean(~this.#vertices.values().toArray().findIndex(s => ~Array.from(s).findIndex(iv => iv.value === rank)));
  }
  getBag (m) {
    if (!this.#scale.word) return;
    return this.#vertices.values().find(s => ~Array.from(s).findIndex(iv => iv.value.equal(m)));
  }
  hasBag (m) {
    if (!this.#scale.word) return false;
    return Boolean(~this.#vertices.values().toArray().findIndex(s => ~Array.from(s).findIndex(iv => iv.value.equal(m))));
  }
  // returns a new partial ordering on the given ivs
  getSubPO (ivs) { return new StepIntervalPO({ scale: this.#scale, ivs }) }
  // returns po graph as ordered pairs of vertices where lhs < rhs
  get graph () {
    const result = []
    for (const [giv0, { in: ins }] of this.#edges) for (const giv1 of ins) result.push([giv0, giv1]);
    return result
  }
  set graph (_) {}
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

  #tOSubsets
  get tOSubsets () { return this.#tOSubsets ??= this.#genTOSubsets() }
  set tOSubsets (_) {}
  #genTOSubsets () {
    return Array.from(this.#edges.entries()).reduce(({ result, state }, [v, { inc }], i) => {
      if (inc.size === 0) return {
        result: state.size ? result.concat(state, new Set([v])) : result.concat(new Set([v])),
        state: new Set()
      };
      else if (i === this.#edges.size - 1)
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
            eqs.some(([m0, m1]) => (m0.equal(lhs) && m1.equal(rhs)) || (m1.equal(lhs) && m0.equal(rhs))) ||
            this.cmp(this.getBag(lhs), this.getBag(rhs)) !== null) continue;
          if (Scale.charCmp(lhs.keys().toArray().sort(Scale.charCmp)[0], rhs.keys().toArray().sort(Scale.charCmp)[0]) === 1)
            eqs.push([rhs, lhs]);
          else eqs.push([lhs, rhs]);
        }
      }
    }
    this.#eqChoices = eqs;
  }
  showEqChoices () { return this.#eqChoices.map(eq => eq.map(StepInterval.multiSetToString).join(" = ")).join("; ") }
  get eqs () { return this.#eqs.slice() }
  set eqs (_) {}

  // TODO: constrain this PO with the given equations
  // updates to partial order and computing enharmonic intervals are done here
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
  get isTotalOrder () { return this.#edges.values().every(({ inc }) => inc.size === 0) }
  set isTotalOrder (_) {}
}

class ScaleConstraints {
  #scale
  constructor ({ scale, eqs, lts }) {
    if (!Scale.prototype.isPrototypeOf(scale)) throw new Error("ScaleConstraints error: scale must be Scale object");
    this.#scale = scale;
  }
}



export { Scale, StepInterval, StepIntervalPO }