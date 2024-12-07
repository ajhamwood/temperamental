import Common from "./common.js";
import { IntervalSet } from "./interval.js";

class ChordWorker {
  edo; stepsBasis; hdecomp; ivSet; properIvSet; batchSize
  constructor ({ edo, stepsBasis, hdecomp, intervalList, batchSize }) {
    const
      ivSet = new IntervalSet({ edo, stepsBasis, intervalList }),
      properIvSet = new IntervalSet({ edo, stepsBasis, intervalList });
    Object.assign(this, { edo, stepsBasis, hdecomp, ivSet, properIvSet, batchSize })
  }

  #harmCombs = (dec, acc = [], cur = 0) => this.hdecomp
    .reduce((ar, [ n, primeDecomp ], i) => {
      if (cur > i) return ar;
      const
        newDec = primeDecomp.reduce((a, [ p, prad ]) => {
          if (a === null) return null;
          const rad = a.get(p);
          return rad >= prad ? rad === prad ? (a.delete(p), a) : a.set(p, rad - prad) : null
        }, new Map(dec));
      return newDec === null ? ar : ar.concat([[n, newDec, i]])
    }, [])
    .reduce((ar, [n, newDec, cur]) => ar.concat(newDec.size === 0 ?
      [ acc.concat([n]) ] : this.#harmCombs(newDec, acc.concat([n]), cur)), [])

  #enumStacks (ots, uts) {
    let flag = ots.flat().length > uts.flat().length;
    if (flag) ([ots, uts] = [uts, ots]);  // ots lesser than uts
    return ots.reduce((a, oharm) =>
      oharm.reduce((b, h, i) => 
        b.concat(a.map(([o, ivs]) => [
          i === oharm.length - 1 ? o : o.concat([ oharm.toSpliced(oharm.length - 1 - i) ]),
          ivs.concat(oharm.toSpliced(i + 1).map(h => [h, 1]))
        ])), a.map(([o, ivs]) => [ o.concat([oharm]), ivs ])),
      [[[], []]])
      .reduce((a, [o, ivs]) =>
        a.concat(o.reduce((b, oharm) => 
          b.reduce((c, [puts, pivs]) =>
            c.concat(puts.reduce((d, puharm, i) =>
              d.reduce((e, [pputs, ppivs, poharm]) => {
                const min = Math.max(0, poharm.length - pputs.slice(i + 1).flat().length)
                return e.concat(
                  poharm.slice(min, puharm.length)
                    .map((oh, k) => [
                      pputs.with(i, puharm.slice(min + k)),
                      ppivs.concat(Array(min + k).fill([oh, puharm[0]])),
                      poharm.slice(min + k)
                    ])
                    .concat([[
                      pputs.with(i, puharm.slice(poharm.length)),
                      ppivs.concat(poharm.toSpliced(puharm.length).fill([poharm[0], puharm[0]])),
                      poharm.slice(puharm.length)
                    ]])
                )
              }, []),
              [[puts, pivs, oharm]])),
            []),
          [[uts, ivs]])),
        [])
      .map(([puts, pivs]) => flag ?
        pivs.map(([u, o]) => [o, u]).concat(puts.flat().map(h => [h, 1])):
        pivs.concat(puts.flat().map(h => [1, h])))
  }

  #partitionComma (iv, { octaves = 1 } = {}) {
    const
      { edo, properIvSet } = this,
      [ nCombs, dCombs ] = iv.splitDecomp.map(side => side.length ?
        this.#harmCombs(new Map(side)).map(p => Common.group(p)) : [[]]);
    let acc = [];
    for (let otones of nCombs) for (let utones of dCombs)
      for (let partition of this.#enumStacks(otones, utones)) {
        const
          partIvs = partition.map(([n, d]) => properIvSet.getRatio(n, d).withOctave(0)),
          invIvs = partition.map(([d, n]) => properIvSet.getRatio(n, d).withOctave(0));
        if (partIvs.reduce((a, iv) => a + iv.steps(), 0) === octaves * edo) acc.push(partIvs);
        if (invIvs.reduce((a, iv) => a + iv.steps(), 0) === octaves * edo) acc.push(invIvs)
      }
    return acc
  }

  #enumChords = ivs => {  // Joe Sawada, A fast algorithm to generate necklaces with fixed content
    const
      ivClasses = Common.group(ivs),
      ns = ivClasses.map((kl, i) => kl.length - !i),
      word = ivs.slice().fill(0);
    function * necklaces (t, p) {
      if (t > ivs.length && ivs.length % p === 0) yield word.map(i => ivClasses[i][0]);
      else for (let i = word[t - p - 1]; i < ivClasses.length; i++) if (ns[i] > 0) {
        word[t - 1] = i;
        ns[i]--;
        if (i === word[t - p - 1]) yield * necklaces(t + 1, p);
        else yield * necklaces(t + 1, t);
        ns[i]++
      }
    }
    return necklaces(2, 1)
  }
  #basicStacks
  enharms (n, d) {
    const
      iv = this.ivSet.addRatio(n, d),
      { true: pairs = [], false: basicStacks = [] } = Common.groupBy(this.#partitionComma(iv), ivs => ivs.length === 2),
      enharms = pairs.reduce((m, [a, b]) => a === b ?  // Could be a map
        m.set(a, a.inverse()) : m.set(a, b.inverse()).set(b, a.inverse()), new Map());
    this.#basicStacks = basicStacks;
    return [...enharms].map(ivp => ivp.map(iv => iv.fraction))
  }
  chords (n, d) {
    const
      { ivSet, properIvSet } = this, iv = ivSet.addRatio(n, d),
      ivOrder = (a, b) => {
        const [ an, ad ] = a.fraction, [ bn, bd ] = b.fraction;
        return an * bd > ad * bn
      },
      harms = [1].concat(this.hdecomp.map(([h]) => h)
        .filter(h => Common.gcd(h, iv.n) > 1 || Common.gcd(h, iv.d) > 1)
        .sort((a, b) => Math.log2(a) % 1 < Math.log2(b) % 1)),

      stacks = this.#basicStacks.map(ivs => ivs.reduce((acc, iv) => {
        const
          ni = harms.indexOf(iv.n), di = harms.indexOf(iv.d),
          divs = ni > di ?
            harms.slice(ni + 1).concat(harms.toSpliced(di)) :
            harms.slice(ni + 1, di),
          ivPartitions = divs.reduce((acc, h) => acc.map(basePart => {
            const [ n, d ] = basePart.at(-1);
            return [ basePart, basePart.toSpliced(-1).concat([ [n, h], [h, d] ]) ]
          }).flat(), [[ iv.fraction ]])
          .map(ivs => ivs.map(([n, d]) => properIvSet.getRatio(n, d).withOctave(0)));
        return acc.map(pch => ivPartitions.map(ivpart => pch.concat(ivpart))).flat()
      }, [[]])).flat()
        .reduce((acc, ivs) => {
          ivs.sort((a, b) => ivOrder(b, a)); // Ascending order
          let low = 0, high = acc.length;
          while (low < high) {
            const mid = (low + high) >>> 1, checkIvs = acc[mid];
            if (checkIvs.length < ivs.length || (checkIvs.length === ivs.length &&
              checkIvs.reduce((b, iv, i) => {
                if (b !== null) return b;
                const [ an, ad ] = iv.fraction, [ bn, bd ] = ivs[i].fraction, l = an * bd, r =  ad * bn;
                return l < r ? true : l > r ? false : null
              }, null))) low = mid + 1;  // Lex order
            else high = mid
          }
          if (acc[low]?.every((iv, i) => iv === ivs[i])) return acc;
          return acc.toSpliced(low, 0, ivs)
        }, []),

      // chordIvs = new Set(stacks.flatMap(ivs => ivs)),
      equivs = Common.mapBy(stacks
        .flatMap(ivs => ivs.map((iv, i) => [ iv.inverse(), ivs.toSpliced(i, 1).sort(ivOrder) ]))
        .filter(([iv, ch], i, ar) => {
          if (i === 0) return true;
          const [ iv0, ch0 ] = ar[i - 1];
          return iv.n !== iv0.n || iv.d !== iv0.d || !ch.every((iv, i) => iv === ch0[i])
        }), ([a]) => a, ([ , b ]) => b),
      chords = stacks.map(ivs => [ ...this.#enumChords(ivs) ]).flat()
        .reduce((acc, ch) => {
          const intIvs = ch.map(iv => Array(ch.length - 1).with(0, iv));
          ch.forEach((iv, i) => intIvs[(i + 1) % ch.length][ch.length - 2] = iv.inverse());
          for (let j = 2; j <= ch.length / 2; j++) for (let i = 0; i < ch.length / (1 + (ch.length === j * 2)); i++) {
            const
              subchs = (i + j >= ch.length ?
                [ ch.slice(i).concat(ch.toSpliced(i + j - ch.length)), ch.slice(i + j - ch.length, i) ] :
                [ ch.slice(i, i + j), ch.slice(i + j).concat(ch.toSpliced(i)) ]).map(subch => subch.toSorted(ivOrder)),
              facts = subchs.map(subch => {
                const [ n, d ] = subch.reduce(([ ao, au ], iv) => [ ao * iv.n, au * iv.d ], [1, 1]);
                return ivSet.addRatio(n, d)
              }),
              natural = facts.reduce((res, fact, p) => res || (properIvSet.has(fact) &&
                ((n % fact.n && d % fact.d) || (n % fact.d && d % fact.n)) &&
                (p ? fact.inverse() : fact)), false),
              tempered = subchs.reduce((b, subch, p) => {
                if (b) return b;
                const entry = [ ...equivs ].find(([, ar]) => ~ar.findIndex(x => x.length === subch.length && x.every((iv, i) => iv === subch[i])));
                return entry && (p ? entry[0].inverse() : entry[0]);
              }, false);
            const equiv = natural || tempered;
            if (!equiv) return acc;
            intIvs[i][j - 1] = equiv;
            intIvs[(i + j) % ch.length][ch.length - 1 - j] = equiv.inverse()
          }
          return acc.concat([intIvs])
        }, []);
    return chords.map(intIvs => intIvs.map(ivs => ivs.map(iv => iv.fraction)))
  }

  #resolveEnharms; #promiseEnharms = new Promise(res => this.#resolveEnharms = res);
  get waitForEnharms () { return this.#promiseEnharms }
  set waitForEnharms (_) { return false }
  #resolveChords; #promiseChords = new Promise(res => this.#resolveChords = res);
  get waitForChords () { return this.#promiseChords }
  set waitForChords (_) { return false }
}

// self.onmessage = ({ data: { comma, ...params } }) => {
//   postMessage({ ...new ChordWorker(params).chords(...comma), done: true })
// }

var chordGen, comma;
self.onmessage = ({ data: { params, upperBound, retrieve, i } }) => {
  // postMessage({ ...new ChordWorker(chordParams).chords(...comma), done: true })
  if (params) {
    ({ comma } = params);
    delete params.comma;
    chordGen = new ChordWorker(params);
    postMessage({ enharmsRaw: chordGen.enharms(...comma) , i })
  } else if (upperBound !== undefined) {
    const { batchSize } = chordGen, batch = [];
    for (const value of chordGen.chords(...comma)) {
      const ord = [ value.length, [[ value[0][0] ]].concat(value.slice(1).reverse()).map(([ [n, d] ]) => n / d) ];
      if (Common.LTE(ord, upperBound)) continue;
      if (batch.length < batchSize) batch.push({ internalIntervalsRaw: value, ord });
      else postMessage({ batch: batch.splice(0), done: false, i })
    }
    postMessage({ batch, done: true, i });
  }
}