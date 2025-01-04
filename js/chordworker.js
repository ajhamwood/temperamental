import Common from "./common.js";
import { HarmonicLattice, IntervalSet } from "./interval.js";

class ChordWorker {
  edo; stepsBasis; hdecomp; ivSet; properIvSet; lattice; batchSize
  constructor ({ edo, stepsBasis, hdecomp, intervalList, batchSize }) {
    const
      ivSet = new IntervalSet({ intervalList }),
      properIvSet = new IntervalSet({ intervalList }),
      lattice = new HarmonicLattice({ harmsRaw: hdecomp.map(([h]) => h) });
    Object.assign(this, { edo, stepsBasis, hdecomp, ivSet, properIvSet, lattice, batchSize })
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

  chords ([ n, d ], stacks) {
    const
      { ivSet, properIvSet } = this, iv = ivSet.addRatio(n, d),
      ivOrder = (a, b) => {
        const [ an, ad ] = a.fraction, [ bn, bd ] = b.fraction;
        return an * bd > ad * bn
      },
      equivs = Common.mapBy(stacks
        .flatMap(ivs => ivs.map((iv, i) => [ iv.inverse(), ivs.toSpliced(i, 1).sort(ivOrder) ]))
        .filter(([iv, ch], i, ar) => {
          if (i === 0) return true;
          const [ iv0, ch0 ] = ar[i - 1];
          return iv.n !== iv0.n || iv.d !== iv0.d || ch.some((iv, i) => iv !== ch0[i])
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
                const [ n, d ] = subch.reduce(([ ao, au ], iv) => [ ao * iv.n, au * iv.d ], [1n, 1n]);
                return ivSet.addRatio(n, d)
              }),
              natural = facts.reduce((res, fact, p) => res || (properIvSet.hasRatio(fact.n, fact.d) &&
                ((n % fact.n === 0n && d % fact.d === 0n) || (n % fact.d === 0n && d % fact.n === 0n)) &&
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
}

var chordGen, identifier, comma, ps;
self.onmessage = ({ data: { params, stacks, upperBound, retrieve, i } }) => {
  if (params) {
    ({ identifier, comma, ...ps } = params);
    chordGen = new ChordWorker(ps);
  } else if (stacks !== undefined) {
    const { batchSize } = chordGen, batch = [];
    let count = 0;
    if (upperBound.get(i) !== null)
      for (const value of chordGen.chords(comma, stacks.map(ivs => ivs.map(iv => chordGen.properIvSet.getRatio(...iv))))) {
        const
          ord = [ value.length, ...value
            .map(([ [n, d] ], i) => {
              const v = 2 ** (Common.bigLog2(n) - Common.bigLog2(d));
              return i ? 2 - v : v
            }) ];
        if (upperBound.has(i) && Common.LTE(ord, upperBound.get(i))) continue;
        batch.push({ internalIntervalsRaw: value, ord });
        if (batch.length < batchSize) continue;
        postMessage({ batch: batch.splice(0), done: false, identifier, i, count });
        count++
      }
    postMessage({ batch, done: true, identifier, i, count });
  }
}