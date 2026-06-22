import Common from "./common.js";
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
  static ranksInMode (ranks, mode) {
    if (mode === 0) return ranks;
    const edo = ranks.at(-1);
    return ranks.slice(mode).concat(ranks.slice(1, mode).map(x => x + edo)).map(x => x - ranks[mode]).concat(edo)
  }

  // All ordered compositions satisfying the edo and list of step sizes
  // TODO you can do better...
  static genStepCompositions (edo, steps) {
    const res = [];
    steps.slice(0, -1).reduceRight(
      (fn, x) => (...as) => {
        const max = as.reduce((ac, [{}, x], i) => ac - x * steps[i], edo) / x;
        for (let y = 1; y <= max; y++) fn(...as, [x, y])
      },
      (...as) => {
        const z = as.reduce((ac, [{}, x], i) => ac - x * steps[i], edo) / steps.at(-1);
        if (z === Math.floor(z) && z) res.push([ ...as, [steps.at(-1), z] ])
      }
    )();
    return res.map(v => new Map(v))
  }
  
  // All permutations with the given composition
  // TODO return { words, patterns, rankss } for Set/Map
  static * genAllPermutations (composition) {
    const
      comp = composition.values().toArray(),
      ar = comp.flatMap((n, i) => Array(n).fill(i));
    yield ar.map(i => chars[i]).join("");
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
      yield ar.map(i => Scale.#wordChars[i]).join("")
    }
  }

  // The most balanced word for the given composition
  static genBilliardPattern (composition) {
    const
      comp = composition.entries().toArray(),
      t = Array(comp.length).fill(.5), counter = Array(comp.length).fill(0),
      k = comp.reduce((a, [{}, b]) => a + b, -1), steps = [];
    for (let n = 0; n < k; n++) {
      const i = t.reduce(([i, v], x, j) => {
          const k = comp[j][1] / x;
          return k > v ? [j, k] : [i, v]
        }, [-1, 1])[0],
        d = t[i] / comp[i][1];
      t.forEach((v, j) => t[j] = i === j ? 1 : v - d * comp[j][1]);
      counter[i]++;
      steps.push(i)
    }
    steps.push(comp.findIndex(([{}, x], i) => x !== counter[i]));
    const word = steps.map(i => Scale.#wordChars[i]).join("");
    if (Set.prototype.isPrototypeOf(composition)) return { word };
    else if (Map.prototype.isPrototypeOf(composition)) {
      const ranks = steps.reduce((a, i) => a.concat(a.at(-1) + comp[i][0]), [0]);
      return { word, ranks, pattern: Scale.ranksToPattern(ranks) }
    }
  }

  // All possible step sizes for a given edo and scale step variety
  static #genStepSizePerms (edo, sv) {
    const counter = Array(sv).fill(0).map(({}, i) => i + 1), res = [];
    let pos = sv - 1, s;
    while ((s = Common.sum(counter)) <= edo && pos == 0 || pos > 0) {
      if (s > edo) pos--;
      else {
        res.push(counter.slice());
        pos = sv - 1;
      }
      counter[pos]++;
      counter.slice(pos + 1).forEach(({}, i) => counter[pos + 1 + i] = counter[pos + i] + 1)
    }
    return res
  }

  // All possible balanced scales for the given edo and scale step variety,
  // with optional constraints on maximum interval variety and rothenberg propriety
  // TODO factor out constraint filtering for use with arbitrary scale generators
  static genBilliardScales (edo, sv, { maxVariety = null, rothenberg = null } = {}) {
    let rawScales = Scale.#genStepSizePerms(edo, sv).flatMap(steps => Scale.genStepCompositions(edo, steps)
      .map(comp => {
        const { ranks } = Scale.genBilliardPattern(comp);
        return ({ steps, ranks, ivs:  Array(Math.floor(ranks.length / 2)).fill(0).map(({}, i) =>
          Common.group(Array(ranks.length).fill(0).map(({}, j) => j + i + 2 >= ranks.length ?
          ranks[j + i + 2 - ranks.length] + edo - ranks[j] : ranks[j + i + 1] - ranks[j])).map(ar => ar[0])) })
      }));
    if (maxVariety !== null) rawScales = rawScales
      .filter(({ ivs }) => ivs.every(ivl => ivl.length <= maxVariety));
    if (rothenberg !== null) rawScales = rothenberg ?
      rawScales.filter(({ ivs }) => ivs.every((ivl, i) => !i || ivl.every(iv0 => ivs[i - 1].every(iv1 => iv0 > iv1)))) :
      rawScales.filter(({ ivs }) => ivs.every((ivl, i) => !i || ivl.every(iv0 => ivs[i - 1].every(iv1 => iv0 >= iv1))));
    return rawScales
  }

  // TODO take scale generator param
  static scaleCoverage (edo, sv, mapping, options) {
    const
      scales = Common.groupBy(Scale.genBilliardScales(edo, sv, options), ({ ranks }) => ranks.length - 1),
      ranks = Object.entries(Common.groupBy(mapping.properIntervals[Symbol.iterator]()
        .map(iv => [ mapping.steps(iv), iv ]).toArray(),
        ([s]) => s, ([{}, iv]) => iv))
        .map(([k, v]) => [ parseInt(k), v ]);
    // TODO return minimal sets of scale modes which cover harmsRaw/ best covers per number of modes
    return (...harmsRaw) => {
      const lat = new HarmonicLattice({ harmsRaw });
      // TODO Not correct in general, need to take exotic temperaments into account
      const ranks_ = ranks.map(([s, enh]) => [ s, enh.filter(iv => lat.decomp(...iv.fraction)) ])
        .filter(([{}, enh]) => enh.length);
      return Object.values(scales).flat().map(({ steps, ranks, ivs }) => {
        let mrs = ranks.slice();
        const ivCounts = [];
        for (let mode = 0; mode < ranks.length; mode++) {
          const ivl = ranks_.filter(([s, enh]) => mrs.includes(s));
          ivCounts.push(ivl);
          mrs = mrs.slice(1).map(v => v - mrs[1]).concat(edo)
        }
        const max = ivCounts.reduce((a, ar) => a > ar.length ? a : ar.length, 0);
        return { arity: ranks.length - 1, max, ivCounts, steps, ranks, ivs }
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
    if (Set.prototype.isPrototypeOf(comp)) {
      if (comp.values().some(v => typeof v !== "number" || v < 1 || v > mbEdo || v !== Math.floor(v)))
        throw new Error("Scale error: malformed composition")
    }
    else if (Map.prototype.isPrototypeOf(comp)) {
      if (comp.entries().some(([k, v]) => typeof k !== "number" || typeof v !== "number" || k < 1 || v < 1 || k > mbEdo || v > mbEdo ||
        k !== Math.floor(k) || v !== Math.floor(v))) throw new Error("Scale error: malformed composition");
    } else throw new Error("Scale error: composition must be either a Set or a Map")
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
    const comp = new Set(Common.group(word.split("")).map(ar => ar.length));
    if (this.composition) {
      if (Set.prototype.isPrototypeOf(this.composition)) {
        if (this.composition.symmetricDifference(comp).size)
          throw new Error("Scale error: word does not match scale composition")
      } else if (Map.prototype.isPrototypeOf(this.composition)) {
        if (this.composition.size !== comp.size || this.composition.keys().some(v => !comp.has(v)))
          throw new Error("Scale error: word does not match scale composition");
      }
    } else this.composition = comp;
    this.#word = word;
    this.mode = this.mode ?? 0;
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
    this.mode = this.mode ?? 0;
    return this.pattern
  }
  get pattern () { return this.#pattern ? this.#patternInMode : null }

   //TODO list of numbers or intervals
  #scaleInMode
  set ranks (ranks) {
    const keyboard = this.#keyboard;
    if (!keyboard) throw new Error("Scale error: must provide keyboard with concrete rank list");
    const { edo } = keyboard;
    if (!Array.prototype.isPrototypeOf(ranks)) throw new Error("Scale error: ranks must be an array");
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
    this.mode = this.mode ?? 0;
    return this.ranks
  }
  get ranks () { return this.#ranks ? this.#scaleInMode : null }

  // TODO some scales have fewer modes than their arity!
  set mode (mode) {
    if (!this.#word) throw new Error("Scale error: mode requires an abstract scale pattern");
    mode = Common.mod(parseInt(mode), this.arity);
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
  // TODO select a scale among all permutations?
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
    if (!(this.#word || this.#pattern) || !this.#keyboard) throw new Error("Scale error: requires scale pattern and keyboard");
    const { edo } = this.#keyboard
    if (!Map.prototype.isPrototypeOf(ivMap) || ivMap.entries().some(([k, v]) =>
      (this.#word && !Scale.#wordChars.includes(k)) || (this.#pattern && !Scale.#patChars.includes(k)) ||
      parseInt(v) !== v || !Common.between(0, edo, v))) return null;
    const newScale = this.clone();
    newScale.ranks = (this.#pattern ?? this.#word).split("")
      .map(c => ivMap.get(c)).reduce((ar, v) => ar.concat([ ar.at(-1) + v ]), [0]);
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
    // TODO play at which octave?
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