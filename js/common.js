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
  static sum = ar => ar.reduce((a, b) => a + b, 0)
  static bigMax = ar => ar.reduce((a, b) => a > b ? a : b)
  static LTE = (a1, a2) => [a1, a2].sort()[1].every((v, i) => v === a2[i])
  static arrEq = (a1, a2) => a1.length === a2.length && a1.every((v, i) => v === a2[i])
  static pairwiseCmp = (a1, a2, cmp = (a, b) => a === b) => a1.every(i1 => a2.every(i2 => cmp(i1, i2)))
  static bagEq = (a1, a2) => a1.length === a2.length && a1.reduce(([ b, rem ], v) => {
    if (!b) return [ false ];
    const i = rem.findIndex(u => u === v);
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
    ~a.findIndex(v0 => cmp(v0, v)) ? a : a.concat(v), [])
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



class MultiSet {
  static * #subhelp (ar) {
    if (ar.length === 0) yield [];
    else for (let i = 0; i <= ar[0][1]; i++)
      yield * this.#subhelp(ar.slice(1)).map(br => br.concat([[ar[0][0], i]]))
  }
  static * enumerateSubsets (m) {
    yield * this.#subhelp(m.#keys.entries().toArray()).map(ar => new MultiSet().#attachKeys(ar))
  }

  #keys = new Map()
  constructor (ar = []) {
    const g = Common.group(ar);
    for (const a of g) this.#keys.set(a[0], a.length)
  }
  #attachKeys (ar) {
    this.#keys = ar;
    return this
  }

  * [Symbol.iterator] () { for (const [k, v] of this.#keys) for (let i = 0; i < v; i++) yield k }
  get [Symbol.toStringTag] () { return "MultiSet" }
  * keys () { yield * this.#keys.keys() }
  values = this[Symbol.iterator];
  * entries () { yield * this.#keys.entries().map(([k, v]) => [k, Array(v).fill(k)]) }

  get size () { return this.#keys.values().reduce((a, b) => a + b, 0) }
  set size (_) {}

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
  union (ms) {
    if (!MultiSet.prototype.isPrototypeOf(ms)) return null;
    const r = new Map(this.#keys);
    for (const [k, v] of ms.#keys) r.set(k, r.has(k) ? Math.max(v, r.get(k)) : v);
    return new MultiSet().#attachKeys(r)
  }
  intersection (ms) {
    if (!MultiSet.prototype.isPrototypeOf(ms)) return null;
    const r = new Map();
    for (const [k, v] of ms.#keys)
      if (this.#keys.has(k)) r.set(k, Math.min(this.#keys.get(k), v));
    return new MultiSet().#attachKeys(r)
  }
  plus (ms) {
    if (!MultiSet.prototype.isPrototypeOf(ms)) return null;
    const r = new Map(this.#keys);
    for (const [k, v] of ms.#keys) r.set(k, (r.get(k) ?? 0) + v);
    return new MultiSet().#attachKeys(r)
  }
  minus (ms) {
    if (!MultiSet.prototype.isPrototypeOf(ms)) return null;
    const r = new Map(this.#keys);
    for (const [k, v] of ms.#keys)
      if (r.has(k)) {
        const v0 = r.get(k);
        if (v0 > v) r.set(k, v0 - v);
        else r.delete(k)
      }
    return new MultiSet().#attachKeys(r)
  }
  symmetricDifference (ms) {
    if (!MultiSet.prototype.isPrototypeOf(ms)) return null;
    const r = new Map();
    for (const [k, v] of ms.#keys)
      if (this.#keys.has(k)) {
        const v0 = this.#keys.get(k);
        if (v0 !== v) r.set(k, Math.abs(v0 - v));
      }
    return new MultiSet().#attachKeys(r)
  }
  scalarMultiply (n) {
    const r = new Map()
    if (n !== 0) for (const [k, v] of this.#keys) {
      const nv = n * v;
      if (nv !== Math.floor(nv)) return null;
      r.set(k, nv);
    }
    return new MultiSet().#attachKeys(r)
  }
  divide (m) {
    if (this.#keys.size !== m.#keys.size) return NaN;
    let n, d;
    for (const [k, n0] of this.#keys) {
      if (!m.#keys.has(k)) return NaN;
      const d0 = m.#keys.get(k);
      if (n === undefined) {
        const g = Common.gcd(n0, d0);
        n = n0 / g;
        d = d0 / g;
      } else if (n * d0 !== d * n0) return NaN
    }
    return n / d
  }
  get gcd () { return this.#keys.size ? this.#keys.values().reduce((a, b) => Common.gcd(a, b)) : NaN }
  set gcd (_) {}
  get unique () { return this.#keys.size }
  set unique (_) {}
  equal (m) {
    if (!MultiSet.prototype.isPrototypeOf(m) || this.#keys.size !== m.#keys.size) return false;
    for (const [k, v] of this.#keys) if (!m.#keys.has(k) || m.#keys.get(k) !== v) return false;
    return true
  }
}


// Not for storage of Map objects...
class Index {
  #rawMap = new Map(); #addrFn; #doneFn
  constructor ({ address, done }) {
    this.#addrFn = address ?? (x => [x]);
    this.#doneFn = done ?? (() => true)
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

  insert (item) {
    const path = this.#addrFn(item);
    let focus = this.#rawMap;
    for (let i = 0; i < path.length; i++) {
      const key = path[i];
      if (!focus.has(key)) {
        focus.set(key, item);
        return item
      }
      const split = focus.get(key);
      if (Map.prototype.isPrototypeOf(split)) {
        if (i === path.length - 1) split.set(null, item);
        else focus = split;
      } else {
        const splitPath = this.#addrFn(split);
        if (Common.arrEq(path, splitPath)) {
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
  has (item) { return item === this.hasPath(...this.#addrFn(item)) }
  clear () { this.#rawMap.clear() }

  deletePath (...path) {
    const spine = [];
    let focus = this.#rawMap, i = 0;
    for (; i < path.length; i++) {
      spine.push(focus);
      const key = path[i];
      if (!focus.has(key)) return false;
      const newFocus = focus.get(key);
      if (!Map.prototype.isPrototypeOf(newFocus)) {
        if (Common.arrEq(path, this.pathOf(newFocus))) {
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
      const key = i === path.length ? null : path[i];
      if (!focus.has?.(key)) return;
      focus = focus.get(key);
      if (!Map.prototype.isPrototypeOf(focus))
        if (Common.arrEq(path, this.pathOf(focus)) || i === path.length) return focus;
        else return
    }
    return focus
  }
  hasPath (...path) {
    let focus = this.#rawMap;
    for (let i = 0; i <= path.length; i++) {
      const key = i === path.length ? null : path[i];
      if (!focus.has?.(key)) return false;
      focus = focus.get(key);
      if (!Map.prototype.isPrototypeOf(focus))
        if (Common.arrEq(path, this.pathOf(focus)) || i === path.length) return true;
        else return false
    }
    return true
  }
}



export { Common, MultiSet, Index }