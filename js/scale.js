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
    return Array(Math.floor(ranks.length / 2)).fill(0).map(({}, i) =>
      Common.group(Array(ranks.length).fill(0).map(({}, j) => j + i + 2 >= ranks.length ?
      ranks[j + i + 2 - ranks.length] + ranks.at(-1) - ranks[j] : ranks[j + i + 1] - ranks[j])).map(ar => ar[0]))
  }

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
      t = Array(comp.length).fill(.5), counter = Array(comp.length).fill(0),
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
    const counter = Array(sv).fill(0).map(({}, i) => i + 1);
    let pos = sv - 1, s;
    while ((s = Common.sum(counter)) <= edo && pos == 0 || pos > 0) {
      if (s > edo) pos--;
      else {
        yield counter.slice();
        pos = sv - 1;
      }
      counter[pos]++;
      counter.slice(pos + 1).forEach(({}, i) => counter[pos + 1 + i] = counter[pos + i] + 1)
    }
  }

  // All possible balanced scales for the given edo and scale step variety,
  // with optional constraints on maximum interval variety and rothenberg propriety
  static * genBilliardScales (edo, sv) {
    yield * Scale.#genStepSizePerms(edo, sv)
      .flatMap(steps => Scale.genStepCompositions(edo, steps)
        .map(comp => ({ comp, ...Scale.genBilliardPattern(comp) })))
  }
  static * genAllScales (edo, sv) {
    yield * Scale.#genStepSizePerms(edo, sv)
      .flatMap(steps => Scale.genStepCompositions(edo, steps)
        .flatMap(comp => Scale.genAllPermutations(comp)))
  }

  // TODO expose subcomputations for pruning!
  static * genConstrainedScales (gen, { arity = null, maxVariety = null, rothenberg = null } = {}) {
    gen = gen.map(({ comp, ranks, ivs }) => ({ comp, ranks, ivs: ivs ?? Scale.ranksToGenericIvs(ranks) }));
    if (arity !== null) gen = gen.filter(({ ranks }) => ranks.length - 1 === arity);
    if (maxVariety !== null) gen = gen.filter(({ ivs }) => ivs.every(ivl => ivl.length <= maxVariety));
    if (rothenberg !== null) gen = rothenberg ?
      gen.filter(({ ivs }) => ivs.every((ivl, i) => !i || ivl.every(iv0 => ivs[i - 1].every(iv1 => iv0 > iv1)))) :
      gen.filter(({ ivs }) => ivs.every((ivl, i) => !i || ivl.every(iv0 => ivs[i - 1].every(iv1 => iv0 >= iv1))));
    yield * gen
  }

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

  #keyboard; #mapping; arity; #composition; #equations; #word; #pattern; #mode; #ranks
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
    if (ranks) this.ranks = ranks;
    else if (pattern) this.pattern = pattern;
    else if (word) this.word = word;
    else if (composition) this.composition = composition;
    else throw new Error("Scale error: must at least provide scale composition");
    if (mode) this.mode = mode;

    if (equations) { //TODO format?
      this.#equations = equations
    }
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

  #patternInMode
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
  #primeMode; #scaleInMode
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
    this.#primeMode = Array(this.arity).fill(0)
      .map(({}, i) => [Scale.ranksInMode(ranks, i).toReversed(), i]).sort().at(-1)[1];
    const pattern = Scale.ranksToPattern(ranks);
    if (this.#pattern) {
      if (this.#pattern !== pattern) throw new Error("Scale error: rank list does not match scale pattern")
    } else this.pattern = pattern;
    this.#ranks = ranks;
    this.mode = this.#primeMode;
    return this.ranks
  }
  get ranks () { return this.#ranks ? this.#scaleInMode : null }

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
      !Common.arrEq(stepOrder.sort(), Array(stepOrder.length).fill(0).map(({}, i) => i))) return null;
    // More efficient to invert stepOrder, but eh
    const newScale = this.clone();
    newScale.pattern = this.#word.split("").map(c => Scale.#patChars[stepOrder.indexOf(Scale.#wordChars.indexOf(c))]).join("");
    return newScale
  }
  setStepSizes (ivMap) {
    if (!this.#word) throw new Error("Scale error: requires scale word");
    const mbEdo = this.#keyboard?.edo ?? 210;
    if (!Map.prototype.isPrototypeOf(ivMap) || ivMap.entries().some(([k, v]) =>
      (this.#word && !Scale.#wordChars.includes(k)) || (this.#pattern && !Scale.#patChars.includes(k)) ||
      parseInt(v) !== v || !Common.between(0, mbEdo, v))) return null;
    const newScale = this.clone();
    const v = (this.#pattern ?? this.#word).split("")
      .map(c => ivMap.get(c)).reduce((ar, v) => ar.concat([ ar.at(-1) + v ]), [0]);
    newScale.ranks = v;
    if (this.#keyboard && this.#keyboard.edo !== newScale.ranks.at(-1))
      throw new Error("Scale error: mismatch between ranks and keyboard")
    return newScale
  }

  // TODO toggle scale highlighting
  #speed = 500
  set speed (v) {
    const s = parseInt(v)
    this.#speed = isNaN(s) ? this.#speed : s;
  }
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



export { Scale }