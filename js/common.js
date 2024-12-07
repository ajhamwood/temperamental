class Common {
  static #allPrimes = [ 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47 ]
  static #allPrimesBig = this.#allPrimes.map(BigInt)
  
  static between = (min, max, val) => val <= max && val >= min
  static clamp = (min, max, val) => (max >= min && Number(val) === val) ? Math.max(min, Math.min(max, val)) : undefined
  static lerp = (a, b, t) => a * (1 - t) + b * t
  static mod = (n, m) => ((n % m) + m) % m
  static non2 = h => h / (h & (~--h))
  static gcd = (a, b) => !b ? a : this.gcd(b, a % b)
  static LTE = (a1, a2) => [a1, a2].sort()[1].every((v, i) => v === a2[i])
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
  static comp = ar => ar.reduce((n, [p, rad]) => n * p ** rad, 1)
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

  static scaleVolume = value => value && 10 ** (2 * (value / 100 - 1))
  static ordinal = (() => {
    const rule = new Intl.PluralRules("en-AU", { type: "ordinal" }),
          suf = new Map([ ["one", "st"], ["two", "nd"], ["few", "rd"], ["other", "th"] ]);
    return n => `${n}${suf.get(rule.select(n))}`
  })()

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
export default Common