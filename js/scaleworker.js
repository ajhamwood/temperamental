import $ from "./machine.js";
import { Common, Iter, MultiSet } from "./common.js";
import { Scale } from "./scale.js";



class ScaleWorkerContext {
  static batchSize = 50 // For now
  static #from = {
    MultiSet: ms => ms.repr.entries().toArray(),
    embedding: em => em.entries().map(([k, v]) => [k, ScaleWorkerContext.#from.MultiSet(v)]).toArray(),
    genericIvs: givs => givs.map(giv => giv.values().map(iv => ScaleWorkerContext.#from.MultiSet(iv.value)).toArray()),
    patternDict: p => p == null ? null : p.entries().toArray(),
    ranks: mss => mss == null ? null : mss.map(ms => ScaleWorkerContext.#from.MultiSet(ms))
  }
  static #to = {
    MultiSet: repr => MultiSet.from(new Map(repr)),
    embedding: m => new Map(m.map(([k, v]) => [k, ScaleWorkerContext.#to.MultiSet(v)])),
    genericIvs: givs => givs.map(giv => giv.map(ms => ScaleWorkerContext.#to.MultiSet(ms))),
    patternDict: p => new Map(p),
    ranks: mss => mss.map(ms => ScaleWorkerContext.#to.MultiSet(ms))
  }
  static #types = {
    composition: "MultiSet",
    embedding: "embedding",
    genericIvs: "genericIvs",
    patternDict: "patternDict",
    ranks: "ranks",
    embeddingScale: null, intervals: null
  }
  static from (type, value) { return type in ScaleWorkerContext.#types ?
    ScaleWorkerContext.#types[type] == null ? null : ScaleWorkerContext.#from[ScaleWorkerContext.#types[type]](value) : value }
  static to (type, value) { return type in ScaleWorkerContext.#types ?
    ScaleWorkerContext.#types[type] == null ? null : ScaleWorkerContext.#to[ScaleWorkerContext.#types[type]](value) : value }
}



var ScaleWorker, ScaleWorkerManager;

if (self instanceof (self.WorkerGlobalScope ?? class {}) ) {

  // Worker thread
  // TODO duty cycle?
  $.targets({ message ({ data: { initialise, batch, id, done } }) {
    if (initialise) {
      const { extract, filter, i } = initialise;
      self.id = i;
      self.scaleWorker = new ScaleWorker({ extract, filter })
    }
    if (batch) self.scaleWorker.enqueue({ batch, id });
    if (done) self.scaleWorker.finalise()
  }, error (e) { console.error(e.error) } });

  ScaleWorker = class extends ScaleWorkerContext {
    static available = 1
    static #rels = {
      Map: type => ({
        EQ: (a, b) => a?.size === b?.size && a.entries().every(([k, v]) => ScaleWorker.#rels[type].EQ(v, b.get(k))),
        NEQ: (a, b) => a?.size !== b?.size || a?.entries().some(([k, v]) => ScaleWorker.#rels[type].NEQ(v, b.get(k)))
      }),
      Set: type => ({
        EQ: (a, b) => a?.size === b?.size && a.values().every(v0 => b.values().some(v1 => this.#rels[type].EQ(v0, v1))),
        NEQ: (a, b) => a?.size !== b?.size || !a?.values().every(v0 => b.values().some(v1 => this.#rels[type].EQ(v0, v1))),
      }),
      Eq: {
        EQ: (a, b) => a?.equal(b),
        NEQ: (a, b) => !a?.equal(b)
      },
      composition: {
        EQ: (a, b) => a?.equal(b),
        NEQ: (a, b) => !a?.equal(b)
      },
      embedding: {
        EQ: (a, b) => this.#rels.Map("Eq").EQ(a, b),
        NEQ: (a, b) => this.#rels.Map("Eq").NEQ(a, b),
      },
      genericIvs: {
        EQ: (a, b) => Common.zipCmp(a, b, this.#rels.Set("Eq").EQ),
        NEQ: (a, b) => !Common.zipCmp(a, b, this.#rels.Set("Eq").EQ),
      },
      patternDict: {
        EQ: (a, b) => a == null && b == null || this.#rels.Map("default").EQ(a, b),
        NEQ: (a, b) => ((a == null) ^ (b == null)) || this.#rels.Map("default").NEQ(a, b),
      },
      ranks: {
        EQ: (a, b) => a == null && b == null || Common.zipCmp(a, b, this.#rels.Eq.EQ),
        NEQ: (a, b) => ((a == null) ^ (b == null)) || !Common.zipCmp(a, b, this.#rels.Eq.EQ),
      },
      default: {
        EQ: (a, b) => a === b,
        NEQ: (a, b) => a !== b,
        LTE: (a, b) => a <= b,
        GTE: (a, b) => a >= b
      }
    }
    static #getRel (prop, rel) {
      return prop in this.#rels ? this.#rels[prop][rel] : this.#rels.default[rel]
    }
    // eg { property: "word", operand: { constant: "XYXYX" }, rel: "EQ" }
    static #test ({ property, operand: { constant }, rel }) {
      const fn = this.#getRel(property, rel);
      if (constant != null) return scale => fn(scale[property], ScaleWorker.to(property, constant));
      else return scale => scale[property] != null
    }

    extract; filter
    constructor ({ extract, filter }) {
      super()
      if (!extract) throw new Error("ScaleWorker error: must provide property extraction set");
      this.#setExtract(extract);
      if (filter) this.#setFilter(filter);
      this.ready()
    }

    #setFilter (filter) {
      const fns = filter.map(mbOrs => Array.prototype.isPrototypeOf(mbOrs) ?
        mbOrs.map(v => ScaleWorker.#test(v)) : ScaleWorker.#test(mbOrs));
      this.filter = scale => fns.every(mbFns => Array.prototype.isPrototypeOf(mbFns) ?
        mbFns.some(fn => fn(scale)) : mbFns(scale))
    }
    #setExtract (extract) {
      const fns = extract.map(p => [p, v => ScaleWorker.from(p, v)]);
      this.extract = scale => fns.reduce((o, [p, fn]) => (o[p] = fn(scale[p]), o), {})
    }

    #resolvers = []; #promises = [ new Promise(r => this.#resolvers.push(r)) ]
    async * results () {
      let batch, id;
      while (!({ batch, id } = await this.#promises.shift()).done) {
        let deltaOut = 0;
        for (let i = 0; i < batch.length; i++) {
          const
            opts = batch[i],
            o = Object.entries(opts).reduce((o, [p, v]) => (o[p] = ScaleWorker.to(p, v), o), {}),
            scale = new Scale(o);
          let item;
          try {
            if (this.filter?.(scale) ?? true) {
              deltaOut++
              yield { item: this.extract(scale) }
            }
          } catch (e) {
            console.log("Error with opts:", opts);
            console.error(e)
          }
        }
        postMessage({ id, deltaIn: batch.length, deltaOut });
      }
    }
    enqueue ({ batch, id }) {
      let res;
      this.#promises.push(new Promise(r => res = r));
      this.#resolvers.push(res);
      this.#resolvers.shift()(batch ? { batch, id, done: false } : { done: true });
    }
    finalise () { this.enqueue({}) }
    async ready () {
      const batch = [], r = this.results();
      let value;
      do {
        batch.splice(0);
        while (!({ value } = await r.next()).done) {
          batch.push(value.item);
          if (batch.length >= ScaleWorker.batchSize) break
        }
        postMessage({ batch });
      } while (value && !value.done)
    }
  }

} else {

  // Main thread
  ScaleWorkerManager = class extends ScaleWorkerContext {
    // TODO global WorkerPool:
    //      queue resource requests at the global pool and distribute using flex model (basis/ratio)
    static pool = []
    static #maxWorkers = navigator.hardwareConcurrency
    static available = this.#maxWorkers

    workers = []; active = []; id = 0; available; gen; options
    constructor ({ count, gen, options }) {
      super();
      if (ScaleWorkerManager.available <= 0) return {};
      const available = Math.min(Math.floor(Common.between(0, 1 - Number.EPSILON, count) ?
        count * navigator.hardwareConcurrency : count), ScaleWorkerManager.available);
      Object.assign(this, { available, gen, options });
    }

    // Unordered!
    #started = false; #sent = false; #resolver; #promise = new Promise(r => this.#resolver = r)
    async start () {
      const
        self = this, { workers, active, available, gen, options: { filter, extract } } = this,
        totIn = Array(available).fill(0), totOut = Array(available).fill(0);
      filter?.forEach(f => "operand" in f && "constant" in f.operand &&
        (f.operand.constant = ScaleWorkerManager.from(f.property, f.operand.constant)));
      for (let i = 0; i < available; i++) {
        const
          worker = new Worker(new URL("./scaleworker.js", import.meta.url), { name: this.name, type: "module" }),
          batch = await Array.fromAsync(this.getBatch(gen));
        workers.push(worker);
        $.targets({ message ({ data: { batch, deltaIn, deltaOut, id } }) {
          if (batch) {
            self.#resolver({ batch, done: self.#sent && !active.some(ar => ar.length) })
            self.#promise = new Promise(r => self.#resolver = r)
          } else {
            self.active[i].splice(self.active[i].indexOf(id), 1);
            totIn[i] += deltaIn;
            totOut[i] += deltaOut
            if (self.#started && !self.#sent) self.run(i)
          }
        } }, worker);
        worker.postMessage({ initialise: { extract, filter, i }, batch, id: this.id++ });
        active.push([i]);
        ScaleWorkerManager.available--;
        this.available--;
        if (batch.length < ScaleWorkerManager.batchSize) {
          for (const w of workers) w.postMessage({ done: true });
          this.#started = this.#sent = true;
          return this.#results()
        }
      }
      this.#started = true;
      for (let i = 0; i < available; i++) if (await this.run(i)) break;
      return this.#results()
    }
    async * getBatch (gen) {
      for await (const item of Iter.takeAsync(Iter.yieldEach(gen), ScaleWorkerManager.batchSize))
        yield Object.entries(item).reduce((o, [p, v]) => (o[p] = ScaleWorkerManager.from(p, v), o), {})
    }
    async run (i) {
      const { workers, active, gen } = this, batch = await Array.fromAsync(this.getBatch(gen));
      if (batch.length !== 0) {
        workers[i].postMessage({ batch, id: this.id });
        active[i].push(this.id++)
      }
      if (batch.length !== ScaleWorkerManager.batchSize) {
        for (const w of workers) w.postMessage({ done: true });
        return this.#sent = true;
      }
    }
    pause () {}
    resume () {}
    async * #results () {
      if (!this.#started) return;
      let batch, done;
      do yield * ({ done } = await this.#promise).batch
        .map(item => Object.entries(item).reduce((o, [p, v]) => (o[p] = ScaleWorkerManager.to(p, v), o), {}));
      while (!done);
      this.#finalise()
    }
    #finalise () {
      this.#started = false;
      this.#sent = false;
      const { workers } = this;
      for (const w of workers) w.terminate();
      ScaleWorkerManager.available += workers.length
    }
  }

}



export { ScaleWorker, ScaleWorkerManager }