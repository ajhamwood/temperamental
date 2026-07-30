class Common {

  static #allPrimes = [ 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47 ]
  static #allPrimesBig = this.#allPrimes.map(BigInt)

  static wait = ms => v => new Promise(r => setTimeout(() => r(v), ms))
  // static debounce = (wm => key => {
  //   const { b, p } = wm.get(key) ?? wm.set(key, { b: true, p: Promise.resolve() }).get(key);
  //   if (b) {

  //   }
  // })(new WeapMap())
  
  static between = (min, max, val) => val <= max && val >= min
  static clamp = (min, max, val) => (max >= min && Number(val) === val) ? Math.max(min, Math.min(max, val)) : undefined
  static lerp = (a, b, t) => a * (1 - t) + b * t
  static mod = (n, m) => ((n % m) + m) % m
  static non2 = h => h / (h & (~--h))
  static gcd = (a, b) => !b ? a : this.gcd(b, a % b)
  static lcm = (a, b) => a * b / this.gcd(a, b)
  static gcdExt = (a, b) => {
    let x0 = 1, y0 = 0, x1 = 0, y1 = 1;
    while (b !== 0) {
      const q = Math.floor(a / b), r = a % b;
      [a, b, x0, y0, x1, y1] = [b, r, x1, y1, x0 - q * x1, y0 - q * y1]
    }
    return { gcd: a, solution: [x0, y0] }
  }
  static sum = ar => ar.reduce((a, b) => a + b, 0)
  static bigMax = ar => ar.reduce((a, b) => a > b ? a : b)
  static maxBy = (ar, fn = x => x) => ar.reduce(([x, a, b], y) => (b = fn(y)) <= a ? [x, a] : [y, b], [,])[0]
  static minBy = (ar, fn = x => x) => ar.reduce(([x, a, b], y) => (b = fn(y)) >= a ? [x, a] : [y, b], [,])[0]
  static LTE = (a1, a2) => [a1, a2].sort()[1].every((v, i) => v === a2[i])
  static arrCmp = (ar0, ar1) => { for (let i = 0; i < ar0.length; i++)
    if (ar0[i] !== ar1[i]) return Math.sign(ar0[i] - ar1[i]); return Math.sign(ar0.length - ar1.length) }
  static pairwiseCmp = (a1, a2, cmp = (a, b) => a === b) => a1.every(i1 => a2.every(i2 => cmp(i1, i2)))
  static zipCmp = (a1, a2, cmp = (a, b) => a === b) => a1.length === a2.length && a1.every((v, i) => cmp(v, a2[i]))
  static bagEq = (a1, a2, cmp = (a, b) => a === b) => a1.length === a2.length && a1.reduce(([ b, rem ], v) => {
    if (!b) return [ false ];
    const i = rem.findIndex(u => cmp(u, v));
    return ~i ? [ true, rem.toSpliced(i, 1) ] : [ false ]
  }, [ true, a2 ])[0]
  static groupBy = (ar, groupFn = x => x, mapFn = x => x) => ar.reduce((a, v) => {
    const k = groupFn(v);
    a[k] = (a[k] ?? []).concat([mapFn(v)]);
    return a
  }, {})
  static mapBy = (ar, groupFn = x => x, mapFn = x => x) => ar.reduce((a, v) => {
    const k = groupFn(v);
    return a.set(k, (a.get(k) ?? []).concat([mapFn(v)]))
  }, new Map())
  static group = (ar, cmp = (a, b) => a === b) => ar.reduce((a, v) => {
    const i = a.findIndex(vs => cmp(vs[0], v));  // quadratic in cmp
    return ~i ? a.with(i, a[i].concat([v])) : a.concat([[v]])
  }, [])
  static quotient = (ar, cmp = (a, b) => a === b) => ar.reduce((a, v) =>
    ~a.findIndex(v0 => cmp(v0, v)) ? a : a.concat([v]), [])
  static mapCompose = (m0, m1) => new Map(m1.entries().map(([k, v]) => [m0.get(k), v]))
  
  static decomp = (...iv) => iv.map(r => { // use 2s?
    const raw = [], res = new Map();
    let ivh = this.non2(r), i = 1;
    while (ivh !== 1) {
      const p = this.#allPrimes[i];
      if (this.gcd(ivh, p) === 1) i++;
      else { raw.push(p); ivh /= p }
    }
    for (const [ k, v ] of this.mapBy(raw)) res.set(parseInt(k), v.length)
    return res
  })
  static comp = ar => ar.reduce((n, [p, rad]) => n * BigInt(p) ** BigInt(rad), 1n)
  static splitMult = (a, b) => {
    const acc = b.map(side => side.map(f => f.slice()));
    for (let side = 0; side <= 1; side++) for (const [p, rad] of a[side]) {
      const i = acc[side].findIndex(([q]) => p === q),
            j = acc[1 - side].findIndex(([q]) => p === q);
      if (~i) acc[side][i][1] += rad;
      else if (~j) {
        const r = rad - acc[1 - side][j][1];
        if (r > 0) {
          acc[side].push([p, r]);
          acc[1 - side].splice(j, 1)
        } else if (r === 0) acc[1 - side].splice(j, 1);
        else if (r < 0) acc[1 - side][j][1] = -r
      } else acc[side].push([p, rad]);
    }
    return acc
  }
  static splitLCM = (...ns) => ns.reduce((acc, val) => acc.map((m, i) => val[i]
    .reduce((acc, [p, rad]) => acc.get(p) > rad ? acc : acc.set(p, rad), m)),
    [new Map(), new Map()]).map(m => [ ...m ])
  // static splitGCD = (n, ...ns) => ns.map(nn => nn.map(side => new Map(side)))
  //   .reduce((acc, ms) => acc.map((side, i) => side.reduce((acc, [p, rad]) =>
  //     ms[i].get(p) >= rad ? acc.concat([[p, rad]]) : acc, [])), n)
  static bigLog2 = x => {
    const str = x.toString(16), d = str.slice(0, 13);
    return Math.log2(parseInt(d, 16) / 16 ** d.length) + 4 * str.length
  }
  static decompBig = (...iv) => iv.map(r => { // use 2s?
    const raw = [], res = new Map();
    let ivh = this.non2(r), i = 1;
    while (ivh !== 1n) {
      const p = this.#allPrimesBig[i];
      if (this.gcd(ivh, p) === 1n) i++;
      else { raw.push(p); ivh /= p }
    }
    for (const [ k, v ] of this.mapBy(raw)) res.set(parseInt(k), v.length)
    return res
  })

  static tenneyNorm = m => Math.sqrt(m.entries().reduce((acc, [b, v]) => acc + (b * v) ** 2, 0))
  static weilNorm = (m, k = 1) => Math.sqrt(this.tenneyNorm(m) ** 2 + (k * m.entries().reduce((acc, [b, v]) => acc + b * v, 0)) ** 2)

  static colourMix = (hc1, hc2, t) => {
    if (![hc1, hc2].every(hc => hc.match(/#\p{Hex_Digit}{6,8}/ug))) return null;
    const [r1, g1, b1, a1] = hc1.slice(1).match(/.{2}/g).map(s => parseInt(s, 16));
    const [r2, g2, b2, a2] = hc2.slice(1).match(/.{2}/g).map(s => parseInt(s, 16));
    return "#" + [[r1, r2], [g1, g2], [b1, b2]].reduce((a, [l, r]) => a + Math.round(Common.lerp(l, r, t)).toString(16).padStart(2, "0"), "")
      .concat(a1 && a2 ? [[a1, a2]] : [])
  }

  static scaleVolume = value => value && 10 ** (2 * (value / 100 - 1))
  static ordinal = (() => {
    const rule = new Intl.PluralRules("en-AU", { type: "ordinal" }),
          suf = new Map([ ["one", "st"], ["two", "nd"], ["few", "rd"], ["other", "th"] ]);
    return n => `${n}${suf.get(rule.select(n))}`
  })()

  static steps ({ edo, stepsBasis, iv, params = [], decomp }) {
    return decomp(...iv.fraction)(...params).reduce((acc, [h, r]) => acc + stepsBasis.get(h) * r, edo * -Number(iv.octave))
  }

  static noteFromFactors = (() => {  // Any way to generalise? Use u/e26c and u/e26d ?
    const degree = [["F", "IV", 4], ["C", "I", 1], ["G", "V", 5], ["D", "II", 2],
            ["A", "VI", 6], ["E", "III", 3], ["B", "VII", 7]]
            .reduce((acc, vals, i) => ({ ...acc, [i - 1]: vals }), {}),
          hejiRatios = {
            5: [[[3, 4]], [[5, 1]]],
            7: [[], [[3, 2], [7, 1]]],
            11: [[[3, 1], [11, 1]], []],
            13: [[[3, 3]], [[13, 1]]],
            17: [[[3, 7]], [[17, 1]]],
            19: [[[3, 3], [19, 1]], []],
            23: [[[23, 1]], [[3, 6]]],
            29: [[[3, 2], [29, 1]], []],
            31: [[], [[31, 1]]],
            37: [[[37, 1]], [[3, 2]]],
            41: [[[41, 1]], [[3, 4]]],
            43: [[[3, 1], [43, 1]], []],
            47: [[[47, 1]], [[3, 6]]],
            53: [[[3, 3]], [[53, 1]]]
          };
    return factors => {
      const accid = {};
      factors = structuredClone(factors);
      const
        { mod, bigLog2, comp } = Common,
        logHigh = mod((bigLog2(comp(factors[0])) - bigLog2(comp(factors[1]))), 1) > .5;

      // Factorise out commas
      structuredClone(factors).forEach((d, i) => {
        d.forEach(([p, rad]) => {
          if (p === 3) return;
          const tone = hejiRatios[p].findIndex(side => ~side.findIndex(([q]) => p === q));
          accid[p] = (1 - 2 * (i ^ tone)) * rad;
          hejiRatios[p].forEach((side, j) => side.forEach(([q, qrad]) => {
            const targetSide = i ^ j ^ !tone, k = factors[targetSide].findIndex(([r]) => q === r);
            ~k ? (factors[targetSide][k][1] += qrad * rad) : factors[targetSide].push([q, qrad * rad])
          }))
        })
      });

      // Normalise to Pythagorean key
      factors[1].forEach(([p, rad], i, dc1) => {
        const j = factors[0].findIndex(([q]) => p === q);
        if (!~j) return;
        const qrad = factors[0][j][1];
        if (rad > qrad) factors[1][i][1] -= qrad;
        else factors[1][i] = [];
        if (rad < qrad) factors[0][j][1] -= rad;
        else factors[0].splice(j, 1);
      });
      factors[1] = factors[1].filter(ar => ar.length);

      // Build string
      const tone = factors.findIndex(d => d.length),
            fifths = (1 - 2 * tone) * (~tone ? factors[tone][0][1] : 0),
            sharps = Math.floor((fifths + 1) / 7);
      let acstring = "", pref5 = () => "", prefNo5 = "";
      if (sharps < -2) {
        pref5 = n => ["", String.fromCodePoint(0xe2c1 + n), String.fromCodePoint(0xe2c0 + n)][(sharps === -3) - sharps % 3];
        prefNo5 = ["", String.fromCodePoint(0xe260), String.fromCodePoint(0xe264)][-sharps % 3];
        acstring = sharps === -3 && (5 in accid) ? String.fromCodePoint(0xe264) : String.fromCodePoint(0xe266).repeat(Math.floor(-sharps / 3))
      } else if (sharps > 2) {
        pref5 = n => sharps % 2 ? String.fromCodePoint(0xe2c3 + n) : String.fromCodePoint(0xe2c4 + n);
        prefNo5 = sharps % 2 ? String.fromCodePoint(0xe265) : String.fromCodePoint(0xe263).repeat(2);
        acstring = String.fromCodePoint(0xe263).repeat(Math.floor((sharps - 1) / 2) - !(5 in accid))
      } else {
        pref5 = n => String.fromCodePoint(0xe2c0 + n + (sharps + 2) % 5);
        prefNo5 = sharps === 0 ? "" : String.fromCodePoint(0xe260 + (sharps + 6) % 5)
      }
      if (5 in accid) {
        const arr = accid[5];
        if (Math.abs(arr) <= 3) {
          const arrowsOffset = 5 * (arr > 0 ? 2 * arr - 1 : -2 - 2 * arr);
          acstring += pref5(arrowsOffset);
        } else {
          const arrowsOffset = 5 * (arr > 0 ? 2 * (arr % 3) - 1 : 2 * (-arr % 3) - 2);
          acstring += (arrowsOffset < 0 ? "" : pref5(arrowsOffset)) + String.fromCodePoint(0xe2d6 + 5 * (arr > 0)).repeat(Math.floor(Math.abs(arr) / 3))
        }
      } else acstring = prefNo5 + acstring;
      if (7 in accid) {
        const sep = accid[7];
        acstring += String.fromCodePoint(0xe2e0 + (sep > 0)).repeat(Math.floor((Math.abs(sep) - 1) / 2)) + 
          String.fromCodePoint(0xe2de + (sep > 0) + 2 * Math.abs((sep + 1) % 2));
      }
      Object.keys(hejiRatios).slice(2).forEach((p, i) => {
        const cp = i < 5 ? 0xe2e2 + 2 * i : i === 5 ? 0xee50 : i === 6 ? 0xe2ec : i === 11 ? 0xe2f7 : 0xee44 + 2 * i;
        acstring += accid[p] > 0 ? String.fromCodePoint(cp + 1).repeat(accid[p]) : String.fromCodePoint(cp).repeat(-accid[p])
      });
      const
        [ key, roman, num ] = degree[ mod(fifths + 1, 7) - 1 ],
        revac = acstring.split("").reverse().join(""),
        oct = fifths / 12,
        numAdj = oct > 0 ? -(oct >= 8 - num) : oct < 0 ? + (oct <= 1 - num) : 0,
        baseIvNum = num - 2 * (numAdj < 0) + 7 * ((num === 1 && logHigh) || numAdj);
      return {
        accid: { "3": fifths, ...accid },
        number: revac + (numAdj < 0 ? `(${baseIvNum})` : baseIvNum),
        degree: revac + (numAdj < 0 ? `(${baseIvNum}\u0302)` : baseIvNum + "\u0302"),
        ordinal: revac + (numAdj < 0 ? `(${this.ordinal(baseIvNum)})` : this.ordinal(baseIvNum)),
        roman: revac + roman,
        romanlow: revac + roman.toLowerCase(),
        letter: key + acstring
      };
    }
  })()

  static cacheAside = ({ setup, cacheGen, fresh }) => {
    const ready = setup();
    let cacheDone = false, value;
    return async function * (params) {
      await ready;
      let freshGen = fresh({ retrieve: cacheDone, params });
      while (true) {
        if (cacheDone) {
          if (({ value } = await freshGen.next()).done) return;
          else yield { source: "worker", value }
        } else {
          ({ done: cacheDone, value } = await cacheGen.next());
          if (cacheDone) freshGen = fresh({ retrieve: true, params });
          else yield { source: "cache", value }
        }
      }
    }
  }
}



class Iter {
  // Generator convenience methods

  // All ways to partition a number into (up to k) smaller numbers
  static partitions = (v, max, cuml) => {
    const rec = (n, as) => n >= v ?
      cuml ? as.toReversed().map(a => Iterator.concat(...a)) : Iterator.concat(...as[0]) :
      rec(n + 1, [ as.map((ps, i) => ps.slice(0, i + 1)
        .flatMap(ms => ms.filter(m => !max || m.size < max)
          .map(m => ((m = MultiSet.from(m)).insert(i + 1), m)))) ].concat(as))
    return rec(0, [[[ new MultiSet() ]]])
  }

  // TODO replace in chordworker.js
  static genAllNecklaces (comp, chars) {
    const
      total = Common.sum(comp.values()),
      ns = comp.values().map((k, i) => k - !i).toArray(),
      word = Array(total).fill(0);
    function * necklaces (t, p) {
      if (t > total && total % p === 0)
        yield word.reduce((s, n) => s + chars[n], "");
      else for (let i = word[t - p - 1]; i < comp.size; i++) if (ns[i] > 0) {
        word[t - 1] = i;
        ns[i]--;
        if (i === word[t - p - 1]) yield * necklaces(t + 1, p);
        else yield * necklaces(t + 1, t);
        ns[i]++
      }
    }
    return necklaces(2, 1)
  }

  // All ways to split a MultiSet into the given set of smaller MultiSets
  static * genDecompositions (ms, gens) {
    const rec = (gen, m) => function * (...as) {
      const max = as.reduce((ac, [{}, x], i) => ac.minus(gens[i].scalarMultiply(x)), ms).divSat(m);
      for (let y = 1; y <= max; y++) yield * gen(...as, [m, y])
    };
    let gen = function * (...as) {
      const z = as.reduce((ac, [{}, x], i) => ac.minus(gens[i].scalarMultiply(x)), ms).divide(gens.at(-1));
      if (z && z === Math.floor(z)) yield [ ...as, [ gens.at(-1), z ] ]
    };
    for (const g of gens.toReversed().slice(1)) gen = rec(gen, g);
    yield * gen().map(v => new Map(v))
  }
  // All the sets of MultiSets which cleanly divide a given composition
  static * genGensByComp (comp, sv = comp.size, chars) {
    const
      cs = [...comp], bijs = Iter.bijections(cs, cs).toArray(),
      index = new Index({ address: x => x, done: ($0, v, i) => i === v.length - 1, cmp: Common.zipCmp }),
      combs = Iter.cartProd(cs.map(n => Array(n + 1).keys().toArray())).map((ar, i) => [i, ar]).toArray();
    function * rec (a, v, j) {
      if (Common.sum(a) === 0 && v >= 0) yield [];
      else if (v < 0) return;
      for (const [ k, ar ] of combs.slice(j)) {
        const max0 = Math.min(...a.map((n, i) => ar[i] ? Math.floor(n / ar[i]) : Infinity));
        for (let i = 1; i <= max0; i++)
          yield * rec(a.map((n, h) => n - i * ar[h]), v - 1, k + 1).map(ars => [ar].concat(ars))
      }
    }
    yield * Index.quotient(
      index, rec(cs, sv, 1).filter(ars => ars.some(ar => Common.sum(ar) !== 1)),
      ars => bijs.map(bij => ars.map(ar => Iter.reorder(ar, bij)).toSorted())
    ).map(ars => ars.map(gen => new MultiSet(gen.flatMap((n, i) => chars[i].repeat(n).split("")))))
  }

  // All permutations of unique array elements, ignoring equality
  static * genUniquePerms (array, choose = array.length) {
    if (choose === 0 || array.length === 0) yield [];
    else for (let i = 0; i < array.length; i++)
      yield * Iter.genUniquePerms(array.toSpliced(i, 1), choose - 1).map(ar => [array[i]].concat(ar))
  }
  // All combinations of unique array elements, ignoring equality
  static * genUniqueCombs (array, choose, i = 0) {
    if (choose === 0 || array.length === 0) yield [];
    else for (; i <= array.length - choose; i++)
      yield * Iter.genUniqueCombs(array, choose - 1, i + 1).map(ar => [array[i]].concat(ar))
  }
  // All combinations of possibly non-unique array elements, ignoring equality
  static * genCombs (array, choose, i = 0) {
    if (choose === 0 || array.length === 0) yield [];
    else for (; i < array.length; i++)
      yield * Iter.genCombs(array, choose - 1, i).map(ar => [array[i]].concat(ar))
  }
  static * cartPower (array, choose) {
    if (choose === 0) yield [];
    else for (let i = 0; i < array.length; i++)
      yield * Iter.cartPower(array, choose - 1).map(ar => [array[i]].concat(ar))
  }
  // Cartesian product of series of arrays
  static * cartProd (array) {
    if (array.length === 0) yield [];
    else if (array.length === 1) yield * array[0].map(el => el == null ? [] : [el]);
    else {
      const [ a0, ...rest ] = array;
      for (let i = 0; i < a0.length; i++)
        yield * Iter.cartProd(rest).map(ar => a0[i] == null ? ar : [a0[i]].concat(ar))
    }
  }
  // Sequences of all permutations of the series of arrays
  static * seqPerms (array) {
    if (array.length === 0) yield [];
    else {
      const [ a0, ...rest ] = array;
      yield * Iter.genUniquePerms(a0).flatMap(ar0 => Iter.seqPerms(rest).map(ar1 => ar0.concat(ar1)))
    }
  }
  // All permutations of MultiSet elements
  static * genMultiPerms (ms) {
    if (ms.size === 0) yield [];
    else for (const k of ms.keys()) {
      const subMs = MultiSet.from(ms);
      subMs.delete(k);
      yield * Iter.genMultiPerms(subMs).map(ar => ar.concat([k]))
    }
  }
  // All total orders on a DAG
  // graph: Map(any -> { in: [any] })
  static * genTotalOrders (graph, inDeg = new Map(graph.entries().map(([k, { in: ins }]) => [k, ins.length]))) {
    if (graph.size === 0) yield [];
    for (const v of graph.keys()) {
      if (inDeg.get(v) !== 0) continue;
      const
        m = new Map(graph),
        d = new Map(inDeg.entries().map(([k, n]) => [ k, n - (graph.get(k)?.in.includes(v) ?? 0) ]));
      m.delete(v);
      yield * Iter.genTotalOrders(m, d).map(ar => [v].concat(ar))
    }
  }
  // All the ways two Maps can pair keys having the same value
  static genMaps (m0, m1 = m0) {
    const
      a0 = m0.entries().toArray().sort(([, a], [, b]) => a > b),
      a1 = m1.entries().toArray().sort(([, a], [, b]) => a > b);
    if (!Common.zipCmp(a0, a1, ([, a], [, b]) => a === b)) return null;
    const gs = Map.groupBy(m0.keys(), k => m0.get(k));
    return Iter.seqPerms(gs.entries().toArray().sort(([a], [b]) => a > b).map(([, ar]) => ar))
      .map(cs => new Map(cs.map((c, i) => [c, a1[i][0]])))
  }

  static * bijections (a0, a1, cmp = (a, b) => a === b, ar = []) {
    if (ar.length === 0 && a0.length !== a1.length) return;
    if (a0.length === 0) yield ar;
    for (let j = 0; j < a1.length; j++) if (!ar.includes(j) && cmp(a0[0], a1[j]))
      yield * Iter.bijections(a0.slice(1), a1, cmp, ar.concat([j]))
  }
  static reorder (ar, bij) {
    if (ar.length !== bij.length && Common.zipCmp(bij.toSorted((a, b) => a - b), Array(bij.length).keys().toArray())) return;
    return bij.reduce((ac, j, i) => ac.with(j, ar[i]), Array(ar.length).fill(0))
  }
  
}



class MultiSet {
  static * #subhelp (ar) {
    if (ar.length === 0) yield [];
    else for (let i = 0; i <= ar[0][1]; i++)
      yield * this.#subhelp(ar.slice(1)).map(br => br.concat([[ar[0][0], i]]))
  }
  // Iter?
  static * enumerateSubsets (m) {
    yield * this.#subhelp(m.#keys.entries().toArray()).map(ar => new MultiSet().attach(ar))
  }
  static from (m) {
    if (MultiSet.prototype.isPrototypeOf(m)) return new MultiSet().attach(structuredClone(m.#keys));
    if (!Map.prototype.isPrototypeOf(m)) return false;
    const ms = new MultiSet();
    ms.#keys = m;
    return ms
  }

  #keys = new Map()
  constructor (ar = []) {
    const g = Common.group(ar);
    for (const a of g) this.#keys.set(a[0], a.length)
  }
  attach (m) {
    this.#keys = m;
    return this
  }
  get repr () { return new Map(this.#keys) }
  set repr (_) {}

  * [Symbol.iterator] () { for (const [k, v] of this.#keys) for (let i = 0; i < v; i++) yield k }
  get [Symbol.toStringTag] () { return "MultiSet" }
  * keys () { yield * this.#keys.keys() }
  * values () { yield * this[Symbol.iterator]() }
  * entries () { yield * this.#keys.entries().map(([k, v]) => [k, Array(v).fill(k)]) }

  get size () { return this.#keys.values().reduce((a, b) => a + b, 0) }
  set size (_) {}
  get uniques () { return this.#keys.size }
  set uniques (_) {}

  insert (v) {
    let k = 1;
    if (this.#keys.has(v)) this.#keys.set(v, k += this.#keys.get(v));
    else this.#keys.set(v, 1);
    return k
  }
  delete (v) {
    if (this.#keys.has(v)) {
      const k = this.#keys.get(v);
      if (k === 1) this.#keys.delete(v);
      else this.#keys.set(v, k - 1);
      return true
    } else return false
  }
  has (v) { return this.#keys.has(v) }
  count (v) { return this.#keys.get(v) ?? 0 }
  union (ms) {
    if (!MultiSet.prototype.isPrototypeOf(ms)) return null;
    const r = new Map(this.#keys);
    for (const [k, v] of ms.#keys) r.set(k, r.has(k) ? Math.max(v, r.get(k)) : v);
    return MultiSet.from(r)
  }
  intersection (ms) {
    if (!MultiSet.prototype.isPrototypeOf(ms)) return null;
    const r = new Map();
    for (const [k, v] of ms.#keys)
      if (this.#keys.has(k)) r.set(k, Math.min(this.#keys.get(k), v));
    return MultiSet.from(r)
  }
  plus (ms) {
    if (!MultiSet.prototype.isPrototypeOf(ms)) return null;
    const r = new Map(this.#keys);
    for (const [k, v] of ms.#keys) r.set(k, (r.get(k) ?? 0) + v);
    return MultiSet.from(r)
  }
  minus (ms) {
    if (!MultiSet.prototype.isPrototypeOf(ms)) return null;
    const r = new Map(this.#keys);
    for (const [k, v] of ms.#keys)
      if (r.has(k)) {
        const v0 = r.get(k);
        if (v0 > v) r.set(k, v0 - v);
        else if (v0 === v) r.delete(k);
        else return null
      } else return null;
    return MultiSet.from(r)
  }
  minusSat (ms) {
    if (!MultiSet.prototype.isPrototypeOf(ms)) return null;
    const r = new Map(this.#keys);
    for (const [k, v] of ms.#keys)
      if (r.has(k)) {
        const v0 = r.get(k);
        if (v0 > v) r.set(k, v0 - v);
        else r.delete(k)
      }
    return MultiSet.from(r)
  }
  symmetricDifference (ms) {
    if (!MultiSet.prototype.isPrototypeOf(ms)) return null;
    const r = new Map(this.#keys);
    for (const [k, v] of ms.#keys) {
      if (r.has(k)) {
        const v0 = r.get(k);
        if (v0 !== v) r.set(k, Math.abs(v0 - v));
        else r.delete(k)
      } else r.set(k, v)
    }
    return MultiSet.from(r)
  }
  scalarMultiply (n) {
    const r = new Map()
    if (n !== 0) for (const [k, v] of this.#keys) {
      const nv = n * v;
      if (nv !== Math.floor(nv)) return null;
      r.set(k, nv);
    }
    return MultiSet.from(r)
  }
  divide (ms) {
    if (this.#keys.size !== ms.#keys.size) return NaN;
    let n, d;
    for (const [k, n0] of this.#keys) {
      if (!ms.#keys.has(k)) return NaN;
      const d0 = ms.#keys.get(k);
      if (n === undefined) {
        const g = Common.gcd(n0, d0);
        n = n0 / g;
        d = d0 / g;
      } else if (n * d0 !== d * n0) return NaN
    }
    return n / d
  }
  divSat (ms) {
    let n = Infinity;
    const d = ms.gcd || 0;
    for (const [k, d0] of ms.#keys) {
      if (!this.#keys.has(k)) return 0;
      n = Math.min(n, Math.floor(this.#keys.get(k) * d / d0))
    }
    return n / d
  }
  get gcd () { return this.#keys.size ? this.#keys.values().reduce(Common.gcd) : NaN }
  set gcd (_) {}
  equal (m) {
    if (!MultiSet.prototype.isPrototypeOf(m) || this.#keys.size !== m.#keys.size) return false;
    for (const [k, v] of this.#keys) if (!m.#keys.has(k) || m.#keys.get(k) !== v) return false;
    return true
  }
}



class Setoid {
  #values = []; #eq
  constructor (eq = (a, b) => a === b) { this.#eq = eq }
  from (s) {
    if (Setoid.prototype.isPrototypeOf(s) && s.#eq !== this.#eq)
      return new Setoid(this.#eq).attach(structuredClone(s.#values));
    if (typeof s[Symbol.iterator] !== "function") return false;
    const r = new Setoid(this.#eq);
    for (const a of s) r.insert(a);
    return r
  }
  attach (s) {
    this.#values = s;
    return this
  }
  get repr () { return this.#values.slice() }
  set repr (_) {}

  * [Symbol.iterator] () { yield * this.#values.values() }
  get [Symbol.toStringTag] () { return "Setoid" }
  * keys () { yield * this[Symbol.iterator]() }
  * values () { yield * this[Symbol.iterator]() }
  * entries () { yield * this.#values.values.map(a => [a, a]) }

  get size () { return this.#values.length }
  set size (_) {}
  get cmp () { return this.#eq }
  set cmp (_) {}

  insert (a) {
    const i = this.#values.findIndex(b => this.#eq(a, b));
    if (~i) this.#values.splice(i, 1);
    this.#values.push(a);
    return Boolean(~i)
  }
  delete (a) {
    const i = this.#values.findIndex(b => this.#eq(a, b));
    if (~i) this.#values.splice(i, 1);
    return Boolean(~i)
  }
  has (a) { return Boolean(~this.#values.findIndex(b => this.#eq(a, b))) }
  union (s) {
    if (!Setoid.prototype.isPrototypeOf(s) || s.#eq !== this.#eq) return null;
    const r = this.#values.slice();
    for (const a of s.#values)
      if (!~r.findIndex(b => this.#eq(a, b))) r.push(a);
    return s.from(r)
  }
  intersection (s) {
    if (!Setoid.prototype.isPrototypeOf(s) || s.#eq !== this.#eq) return null;
    const r = [];
    for (const a of this.#values)
      if (~s.#values.findIndex(b => this.#eq(a, b))) r.push(a);
    return s.from(r)
  }
  minus (s) {
    if (!Setoid.prototype.isPrototypeOf(s) || s.#eq !== this.#eq) return null;
    const r = this.#values.slice();
    for (const a of s.#values) {
      const i = r.findIndex(b => this.#eq(a, b));
      if (~i) r.splice(i, 1)
    }
    return s.from(r)
  }
  symmetricDifference (s) {
    if (!Setoid.prototype.isPrototypeOf(s) || s.#eq !== this.#eq) return null;
    const r = this.#values.slice();
    for (const a of s.#values) {
      const i = r.findIndex(b => this.#eq(a, b));
      if (~i) r.splice(i, 1);
      else r.push(a)
    }
    return s.from(r)
  }
  equal (s) {
    if (!Setoid.prototype.isPrototypeOf(s) || s.#eq !== this.#eq ||
      this.#values.length !== s.#values.length) return false;
    for (const a of this.#values) if (!~s.#values.findIndex(b => this.#eq(a, b))) return false;
    return true
  }
}



// Not for storage of Map objects...
class Index {
  static quotient = (index, gen, equiv = x => [x]) => (gen.forEach(v0 =>
    equiv(v0).some(v1 => index.has(v1)) || index.insert(v0)), [...index])
  static group = (index, gen, equiv = x => [x], comb = (a, b) => b) => 
    (gen.forEach(v0 => comb(index.get(equiv(v0).find(v1 => index.has(v1))), v0)), [...index])

  #rawMap = new Map(); #addrFn; #doneFn; #cmpFn
  constructor ({ address, done, cmp }) {
    this.#addrFn = address ?? (x => [x]);
    this.#doneFn = done ?? (() => true)
    this.#cmpFn = cmp
  }

  [Symbol.iterator] = this.values
  keys () { return this.entries().map(([k]) => k) }
  values () { return this.entries().map(([{}, v]) => v) }
  entries () {
    const self = this, gen = function * (m, i, path) {
      if (Map.prototype.isPrototypeOf(m)) for (const [k, v] of m)
        if (self.#doneFn(k, v, i, path)) yield [self.pathOf(v), v];
        else yield * gen(v, i + 1, path.concat(k));
      else yield [self.pathOf(m), m]
    }
    return gen(this.#rawMap, 0, [])
  }

  pathOf (item) { return this.#addrFn(item) }
  #pathValueOf (v, m) { return this.#cmpFn ? m.keys().find(v0 => v0 === null ? false : this.#cmpFn(v, v0)) ?? v : v }

  insert (item) {
    const path = this.#addrFn(item);
    let focus = this.#rawMap;
    for (let i = 0; i < path.length; i++) {
      const key = this.#pathValueOf(path[i], focus);
      if (!focus.has(key)) {
        focus.set(key, item);
        return item
      }
      const split = focus.get(key);
      if (Map.prototype.isPrototypeOf(split)) {
        if (i === path.length) split.set(null, item);
        else focus = split;
      } else {
        const splitPath = this.#addrFn(split);
        if (Common.zipCmp(path, splitPath, this.#cmpFn)) {
          focus.set(key, item);
          return item
        } else focus.set(key, focus = new Map([[
          i === splitPath.length - 1 ? null : splitPath[i + 1], split
        ]]));
      }
    }
    focus.set(null, item);
    return item
  }
  insertFrom (iter) {
    iter.values().forEach(this.insert);
    return this
  }
  delete (item) { return this.deletePath(...this.#addrFn(item)) }
  get (item) { return this.getPath(...this.#addrFn(item)) }
  has (item) { return this.hasPath(...this.#addrFn(item)) }
  clear () { this.#rawMap.clear() }

  deletePath (...path) {
    const spine = [];
    let focus = this.#rawMap, i = 0;
    for (; i < path.length; i++) {
      spine.push(focus);
      const key = this.#pathValueOf(path[i], focus);
      if (!focus.has(key)) return false;
      const newFocus = focus.get(key);
      if (!Map.prototype.isPrototypeOf(newFocus)) {
        if (Common.zipCmp(path, this.pathOf(newFocus), this.#cmpFn)) {
          focus.delete(key);
          break
        } else return false
      } else {
        if (i === path.length - 1 && newFocus.has(null)) newFocus.delete(null);
        focus = newFocus
      }
    }
    while (i > 0 && (focus = spine[i--] ?? focus).size < 2) {
      if (focus.size === 0) spine[i].delete(path[i]);
      else if (focus.size === 1) spine[i].set(path[i], focus.values().find(() => true));
      i--
    }
    return true
  }
  getPath (...path) {
    let focus = this.#rawMap;
    for (let i = 0; i <= path.length; i++) {
      const key = i === path.length ? null : this.#pathValueOf(path[i], focus);
      if (!focus.has?.(key)) return;
      focus = focus.get(key);
      if (!Map.prototype.isPrototypeOf(focus))
        if (Common.zipCmp(path, this.pathOf(focus), this.#cmpFn) || i === path.length) return focus;
        else return
    }
    return focus
  }
  hasPath (...path) {
    let focus = this.#rawMap;
    for (let i = 0; i <= path.length; i++) {
      const key = i === path.length ? null : this.#pathValueOf(path[i], focus);
      if (!focus.has?.(key)) return false;
      focus = focus.get(key);
      if (!Map.prototype.isPrototypeOf(focus))
        if (Common.zipCmp(path, this.pathOf(focus), this.#cmpFn) || i === path.length) return true;
        else return false
    }
    return true
  }
}



export { Common, Iter, MultiSet, Setoid, Index }