import Common from "./common.js";

class CommaWorker {
  #commaGen; curComma; #done = false
  primes; index; maxError; edo; limit; batchSize
  constructor({ primes, index, maxError, edo, limit, batchSize }) {
    Object.assign(this, { primes, index, maxError, edo, limit, batchSize });
    this.#commaGen = this.#commas()
  }
  * #mults () { // Not correct for indexed mappings
    const
      ps = [2].concat(this.primes, this.index).sort((a, b) => a > b),
      bps = ps.map(BigInt), list = [[ 1n, Array(ps.length).fill(0) ]];  // TODO: persist list
    let len = 1;
    while (true) {
      const [ k, d ] = list.splice(0, 1)[0];
      len--;
      for (let i = 0, low = 0; i < ps.length; i++) {
        const val = k * bps[i], dec = d.with(i, d[i] + 1);
        let high = len;
        while (low < high) {
          const mid = (low + high) >>> 1;
          if (list[mid][0] < val) low = mid + 1;
          else high = mid
        }
        if (list[low]?.[0] === val) continue;
        list.splice(low, 0, [ val, dec ]);
        len++
      }
      yield [ k, d ]
    }
  }

  #withPrimes (ar) {
    const ps = this.primes.concat(this.index);
    return ar.slice(1).reduce((acc, rad, i) => rad === 0 ? acc : acc.concat([[ ps[i], rad ]]), [])
  }

  * #commas () {
    let prev = [];
    // const lps = this.primes.concat([2], this.index).map(Math.log2).sort((a, b) => a > b); // Fix this...
    for (const [ n, nd ] of this.#mults()) {
      prev = prev.filter(([ d ]) => Common.bigLog2(n) - Common.bigLog2(d) < this.maxError / 400);
      for (const [ d, dd ] of prev) if (Common.gcd(n, d) === 1n) yield { n, d, nd: this.#withPrimes(nd), dd: this.#withPrimes(dd) };
      prev.push([ n, nd ])
    }
  }

  * takeCommas (upperBound) {
    if (this.curComma) {
      if (!this.#done) yield this.curComma;
      if (this.curComma.n > upperBound) {
        this.#done = true;
        return
      } else this.#done = false
    }
    if (!this.#done) while ((this.curComma = this.#commaGen.next().value).n <= upperBound) yield this.curComma
  }
}
var commaGen, firstRetrieve = true;
self.onmessage = ({ data: { params, upperBound, retrieve, i } }) => {
  if (params) commaGen = new CommaWorker(params);
  else if (upperBound !== undefined) {
    const { batchSize } = commaGen, batch = [];
    let count = 0;
    if (retrieve && firstRetrieve) { // Always advance signal before retrieval
      batch.push(commaGen.curComma);
      firstRetrieve = false
    }
    for (const value of commaGen.takeCommas(upperBound)) {
      if (!retrieve) continue;
      batch.push(value);
      if (batch.length < batchSize) continue;
      postMessage({ batch: batch.splice(0), done: false, i, count });
      count++
    }
    postMessage({ batch, done: true, i, count })
  }
}