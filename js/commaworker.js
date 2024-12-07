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
      ps = this.primes.concat([2], this.index).sort((a, b) => a > b),
      lps = ps.map(Math.log2), bps = ps.map(BigInt), list = [[ 1n, 0 ]];  // TODO: persist list
    let len = 1;
    while (true) {
      const [ k, l ] = list.splice(0, 1)[0];
      len--;
      for (let i = 0, low = 0; i < ps.length; i++) {
        const val = k * bps[i], log = l + lps[i];
        let high = len;
        while (low < high) {
          const mid = (low + high) >>> 1;
          if (list[mid][0] < val) low = mid + 1;
          else high = mid
        }
        if (list[low]?.[0] === val) continue;
        list.splice(low, 0, [ val, log ]);
        len++
      }
      yield [ k, l ]
    }
  }

  * #commas () {
    let prev = [];
    const lps = this.primes.concat([2], this.index).map(Math.log2).sort((a, b) => a > b); // Fix this...
    for (const [ n, ln ] of this.#mults()) {
      prev = prev.filter(([ , ld ]) => ln - ld < this.maxError / 400);
      for (const [ d, ld ] of prev) if (Common.gcd(n, d) === 1n) yield { n, d, ln, ld };
      prev.push([ n, ln ])
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
    if (retrieve && firstRetrieve) { // Always advance signal before retrieval
      batch.push(commaGen.curComma);
      firstRetrieve = false
    }
    for (const value of commaGen.takeCommas(upperBound)) {
      if (!retrieve) continue;
      else if (batch.length < batchSize) batch.push(value);
      else postMessage({ batch: batch.splice(0), done: false, i })
    }
    postMessage({ batch, done: true, i })
  }
}