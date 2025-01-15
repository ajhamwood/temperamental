import Common from "./common.js";
import { app } from "./main.js";
import { IntervalSet } from "./interval.js";
import { Keyboard } from "./keyboard.js";



// Keyboard grid

class HexGrid { // TODO: set w, h, theta within HexGrid
  #keyboard
  w = 0; h = 0; c; unit; r; octLen
  gstep; hstep; orientations; displayKeyNames; theta = 0
  #orientation
  #hexes = new Map(); #edges; #notes
  #activeClasses = new Map() // Map([classname, Map([hex, Set(id)])])
  #bgImgCache

  constructor ({ keyboard, gstep, hstep, unit, orientation, displayKeyNames = true }) {
    if (!(Keyboard.prototype.isPrototypeOf(keyboard))) throw new Error("HexGrid error: must provide Keyboard object");
    this.#keyboard = keyboard;
    if (typeof gstep !== "number" || gstep < 1 || gstep > app.maxEdo || gstep % 1 ||
      typeof hstep !== "number" || hstep < 1 || hstep > app.maxEdo || hstep % 1) throw new Error("Keyboard error: bad grid steps");
    if (typeof unit !== "number" || unit < 5 || unit > 1e4) throw new Error("Keyboard error: bad button size");
    if (!("length" in orientation) || orientation.length !== 2 || orientation.some(v => v < 0 || v > app.maxEdo || v % 1) ||
      orientation[0] * gstep + orientation[1] * hstep !== keyboard.edo) throw new Error("Keyboard error: bad orientation");
    this.gstep = gstep;
    this.hstep = hstep;
    this.genOrientations();
    this.orientation = orientation;
    this.displayKeyNames = Boolean(displayKeyNames);
    this.unit = unit;
    this.r = this.unit * 2
  }

  #newHex (g, h, isGhost) {
    const row = this.#hexes.get(g) ?? this.#hexes.set(g, new Map()).get(g),
          hex = new HexButton({ keyboard: this.#keyboard, hexGrid: this, g, h, isGhost });
    row.set(h, hex);
    return hex
  }

  getHex (g, h) { return this.#hexes.get(g)?.get(h) }
  hasHex (g, h) { return this.#hexes.get(g)?.has(h) ?? false }

  coordToSteps (g, h) { return g * this.gstep + h * this.hstep }
  coordToRank (g, h) { return Common.mod(this.coordToSteps(g, h), this.#keyboard.edo) }
  coordToOctave (g, h) { return Math.floor(this.coordToSteps(g, h) / this.#keyboard.edo) }

  * [Symbol.iterator] () { for (const row of this.#hexes.values()) for (const hex of row.values()) yield hex }

  addToActiveClass (name, hex, id) {
    const activeClasses = this.#activeClasses, activeHexes = activeClasses.get(name) ?? new Map();
    activeClasses.set(name, activeHexes.set(hex, (activeHexes.get(hex) ?? new Set()).add(id)))
  }
  removeFromActiveClasses (hex, id) {
    for (const [ name, activeHexes ] of this.#activeClasses) {
      const ids = activeHexes.get(hex);
      if (!ids) return;
      ids.delete(id);
      if (ids.size === 0) activeHexes.delete(hex)
      if (activeHexes.size === 0) this.#activeClasses.delete(name)
    }
  }
  clearActiveClasses () { this.#activeClasses.clear() }

  genOrientations () {
    const { gstep, hstep } = this, { edo } = this.#keyboard, res = [];
    for (let y = 0; y <= edo / hstep; y++) {
      const x = (edo - hstep * y) / gstep;
      if (x === Math.floor(x)) res.push ([ x, y ])
    }
    this.orientations = res;
  }
  get orientation () { return this.#orientation }
  set orientation ([g, h]) {
    this.#orientation = [ g, h ];
    const { unit, w } = this, x = (2 * g + h) * Math.sqrt(3) / 2, y = h * 1.5;
    this.theta = Math.atan(y / x)
  }
  setLattice ({ gstep, hstep }) {
    Object.assign(this, { gstep, hstep });
    this.genOrientations();
    const
      { orientations } = this,
      orientation = orientations.find(([g, h]) => g + h === 7) || orientations[0];
    if (!orientation) return false;
    this.orientation = orientation;
    return true
  }

  updateGrid (force) {
    if (this.#notes && !force) return;
    const
      { gstep, hstep, c, w, octLen, orientation: [ g, h ] } = this,
      { edo } = this.#keyboard;

    // Central line
    this.#hexes = new Map();
    this.#edges = new Set([this.#newHex(0, 0, false)]);
    this.#notes = new Set([0]);
    let left = .5, right = .5, focus = [ [0, 0], [0, 0] ];
    for (let i = 1; i <= g + h; i++) {
      if (left / i <= h / (g + h)) { left++; focus[0][1]++ } else focus[0][0]++;
      if (right / i < h / (g + h)) { right++; focus[1][1]++ } else focus[1][0]++;
      this.#edges.add(this.#newHex(...focus[0], false));
      this.#notes.add(this.coordToSteps(focus[0][0], focus[0][1]));
      if (focus[0].every((v, i) => v === focus[1][i])) continue
      this.#edges.add(this.#newHex(...focus[1], false));
      this.#notes.add(this.coordToSteps(focus[1][0], focus[1][1]))
    }

    // One octave
    const dev = coord => Math.abs(this.h / 2 - HexButton.centre(...coord, this)[1]);
    this.fillGrid({
      candidate: (g0, h0) => Common.between(w / 2 - c, w / 2 - c + octLen, HexButton.centre(g0, h0, this)[0]) &&
        !this.#notes.has(this.coordToRank(g0, h0)),
      filter: hexes => Common.group(hexes, ([a, b], [c, d]) => this.coordToRank(a - c, b - d) === 0)
        .map(enhs => enhs.sort((a, b) => dev(a) > dev(b))[0]),
      isGhost: () => false
    });

    // Two octaves
    this.#notes = new Set();
    this.fillGrid({
      candidate: (g0, h0) => Common.between(w / 2 - c, w / 2 - c + octLen, HexButton.centre(g0, h0, this)[0]) &&
        !this.#notes.has(this.coordToRank(g0, h0)),
      filter: hexes => Common.group(hexes, ([a, b], [c, d]) => this.coordToRank(a - c, b - d) === 0)
        .filter(([[g0, h0]]) => !this.#notes.has(this.coordToRank(g0, h0)))
        .map(enhs => enhs.sort((a, b) => dev(a) > dev(b))[0]),
      isGhost: () => true
    });

    // Fill to sides
    const home = [ ...this ];
    this.fillGrid({
      candidate: (g0, h0) => {
        const homeEquiv = ~home.findIndex(hex => {
                const [ baseG, baseH ] = hex.coord;
                return (baseG - g0) * h === (baseH - h0) * g // require gcd(g, h) === 1
              });
        return homeEquiv && HexButton.vertices(g0, h0, this).some(([ px, py ]) =>
          px > 0 && px < this.w && py > 0 && py < this.h)
      },
      isGhost: (g0, h0) => home.find(hex => {
        const [ baseG, baseH ] = hex.coord;
        return (baseG - g0) * h === (baseH - h0) * g
      }).isGhost
    });

    // Notes
    for (const hex of this) if (!hex.isGhost) {
      const { octave, rank } = hex, note = this.#keyboard.scale.addNote({ octave, rank });
      if (octave === 0) note.key.home = hex
    }
  }

  async fillGrid ({ candidate, filter = x => x, isGhost }) {
    let viewEdges = new Set([ ...this.#edges ]);
    while (viewEdges.size > 0) {
      let newViewEdges = new Map(), removeViewEdges = new Set(), newNotes = new Set();
      for (const hex of viewEdges) {
        let remove = true;
        for (const [g, h] of hex.neighbours()) {
          const thisHex = this.getHex(g, h);
          if (thisHex) { if (viewEdges.has(thisHex)) removeViewEdges.add(thisHex) }
          else if (candidate(g, h)) {
            newViewEdges.get(g)?.add(h) ?? newViewEdges.set(g, new Set([h]));
            newNotes.add(this.coordToRank(g, h));
          } else remove = false;
        }
        removeViewEdges.add(hex)
        if (remove) this.#edges.delete(hex)
      }
      filter([ ...(function * () {
        for (const [g, s] of newViewEdges) for (const h of s) yield [g, h]
      })() ]).forEach(([g, h]) => {
        const nextHex = this.#newHex(g, h, isGhost(g, h));
        this.#edges.add(nextHex);
        viewEdges.add(nextHex)
      });
      removeViewEdges.forEach(hex => viewEdges.delete(hex));
      this.#notes = new Set([ ...this.#notes, ...newNotes ])
    }
  }

  rotate (x, y, rev = false) {
    const cx = this.w / 2, cy = this.h / 2, theta = rev ? -this.theta : this.theta,
          cos = Math.cos(theta), sin = Math.sin(theta);
    return [ cos * (x - cx) + sin * (y - cy) + cx, cos * (y - cy) - sin * (x - cx) + cy ]
  }

  getCoord (x, y) {
    const { r, w: width, h: height, c } = this;
    ([ x, y ] = this.rotate(x * 2 + c, y * 2, true));
    const a = (x - width / 2) / r / Math.sqrt(3) * 2,
          b = (y - height / 2) / r * 2,
          band = Math.floor(Math.floor((b + 1) / 3));
    if (((Math.floor(b % 3)) + 3) % 3 === 1) {
      const clampedA = ((a % 1) + 1) % 1, clampedB = ((b % 1) + 1) % 1,
            topLeft = clampedA + clampedB > 1, bottomLeft = clampedA < clampedB,
            h = 2 * Math.floor((b + 4) / 6), g = Math.floor((a - h) / 2);
      if (band % 2) return Math.floor(a) % 2 ? [ g + 1, h - !topLeft ] : [ g + !bottomLeft, h - !bottomLeft ];
      else return Math.floor(a) % 2 ? [ g + !bottomLeft, h + bottomLeft ] : [ g, h + topLeft ]
    } else return [ Math.floor((a - band + 1) / 2), band ]
  }

  // TODO urgent: needs BigInt Interval
  classifyKeys (force) {
    if (this.#notes && !force) return;
    const 
      { scale, edo } = this.#keyboard, { mapping } = scale,
      { intervalSet, lattice, rawHarmonicList } = mapping,
      { primes, indexPrimes, index, harmonicList } = lattice,
      bases = primes.map(p => [ p, p ])
        .concat(indexPrimes.map(p => [ p, index.find(h => harmonicList.get(h).primeDecomp.some(([q]) => q === p)) ]))
        .sort(([a], [b]) => a > b).map(([ , h ]) => intervalSet.getRatio(h, 1).withOctave(0));
    let i = edo - 1, full, prev, k = 0, result = Array(edo).fill(), prevResult,
        { properIntervals: ivset } = mapping, prevIvset;
    result[0] = [[[], []]];
    for (const basis of bases) {
      const [ pn, pd ] = basis.fraction.map(Number).map(Common.non2), pstep = mapping.steps(basis);
      prevIvset = new IntervalSet({ intervalSet: ivset });
      full = i;
      prev = null;
      while (i > 0 && (i !== prev || i === full) && rawHarmonicList.size) {
        full = null;
        prev = i;
        prevResult = structuredClone(result);
        for (const iv of prevIvset) {
          const [ n, d ] = iv.fraction.map(Number).map(Common.non2), step = mapping.steps(iv);
          let s = Common.mod(step + k * pstep, edo);
          if (prevResult[s] === undefined && mapping.decomp(n * pn ** k, d * pd ** k)()) {
            const newIv = intervalSet.addRatio(n * pn ** k, d * pd ** k);
            (result[s] ??= (i--, [])).push(newIv.splitDecomp);
            ivset.add(newIv)
          }
          s = Common.mod(step - k * pstep, edo);
          if (k > 0 && prevResult[s] === undefined && mapping.decomp(n * pd ** k, d * pn ** k)()) {
            const newIv = intervalSet.addRatio(n * pd ** k, d * pn ** k);
            (result[s] ??= (i--, [])).push(newIv.splitDecomp);
            ivset.add(newIv)
          }
        }
        k++
      }
      if (i <= 0) break;
      k = 1
    }
    for (const iv of ivset) mapping.intervalSet.add(iv);
    for (const key of scale) key.hexes.clear();
    for (const hex of this) {
      const
        { octave, rank } = hex, labels = [],
        scaleKey = scale.getKey(rank),
        note = scaleKey.addNote(octave);
      scaleKey.hexes.add(hex);
      hex.note = note;
      if (result[rank]) for (let i = 0, ivs = result[rank]; i < ivs.length; i++) {
        const { accid, ...labelStrings } = Common.noteFromFactors(ivs[i]);
        let keyClass = Common.between(6, 10, Common.mod(accid[3], 12)) ? "black" : "white";
        const ot = ivs[i][0].findLast(([p]) => p !== 3);
        if (ot) keyClass += ot[0] + "o";
        const ut = ivs[i][1].findLast(([p]) => p !== 3);
        if (ut) keyClass += ut[0] + "u";
        labels.push({ ...labelStrings, keyClass, interval: ivs[i] })
      }
      if (!scaleKey.labels.length) scaleKey.labels = labels
    }
  }

  redraw (force) {
    const { gridctx, canvas } = app.state(), { width, height } = canvas;
    this.updateGrid(force);
    this.classifyKeys(force);
    gridctx.fillStyle = "#000000";
    gridctx.fillRect(0, 0, width, height);
    for (const hex of this) hex.colour();  // Redraw by local hexes?
    canvas.toBlob(blob => {
      const url = URL.createObjectURL(new Blob([blob]));
      canvas.style.backgroundImage = `url('${url}'), url('${this.#bgImgCache ?? url}')`;
      this.#bgImgCache = url
    })
  }

  colour () {
    const { gridctx, canvas } = app.state(), { width, height } = canvas;
    gridctx.clearRect(0, 0, width, height);
    for (const [ name, activeHexes ] of this.#activeClasses)
      for (const hex of activeHexes.keys()) hex.colour({ bgColour: Keyboard.noteColours[name] })
  }
}



class HexButton {
  static #contrast = hc => {
    if (!hc.match(/#\p{Hex_Digit}{6,8}/ug)) return null;
    const [r, g, b, a] = hc.slice(1).match(/.{2}/g).map(s => parseInt(s, 16));
    return (r * .299 + g * .587 + b * .114 >= 32768 / ((a ?? 255) + 1) ? "#222222" : "#dddddd") + (a ? a.toString(16) : "")
  }

  static vertices (g, h, grid) {
    const { r, w, h: ht, c } = grid, x = w / 2, y = ht / 2, k = .5 * Math.sqrt(3),
          origin = [
            [ x, y - r ], [ x - r * k, y - r / 2 ], [ x - r * k, y + r / 2 ],
            [ x, y + r ], [ x + r * k, y + r / 2 ], [ x + r * k, y - r / 2 ]
          ];
    return origin.map(([ a, b ]) => {
      const [ rx, ry ] = grid.rotate(
              Math.floor(a + r * k * (h + 2 * g)),
              Math.floor(b + 1.5 * r * h)
            );
      return [ rx - c, ry ]
    })
  }
  static centre (g, h, grid) {
    const { r, w: width, h: height, c } = grid, k = .5 * Math.sqrt(3),
          [ rx, ry ] = grid.rotate(
            Math.floor(width / 2 + r * k * (h + 2 * g)),
            Math.floor(height / 2 + 1.5 * r * h)
          );
    return [ rx - c, ry ]
  }

  #keyboard; #hexGrid; #g; #h; #note; isGhost
  constructor ({ keyboard, hexGrid, g, h, isGhost = false }) {
    if (!(Keyboard.prototype.isPrototypeOf(keyboard))) throw new Error("HexButton error: must provide Keyboard object");
    this.#keyboard = keyboard;
    if (!(HexGrid.prototype.isPrototypeOf(hexGrid))) throw new Error("HexButton error: must provide HexGrid object");
    this.#hexGrid = hexGrid;
    this.#g = g;
    this.#h = h;
    this.isGhost = isGhost
  }
  vertices () { return HexButton.vertices(this.#g, this.#h, this.#hexGrid) }
  centre () { return HexButton.centre(this.#g, this.#h, this.#hexGrid) }

  neighbours () {
    const g = this.#g, h = this.#h;
    return [
      [ g - 1, h ], [ g, h - 1 ], [ g + 1, h - 1 ],
      [ g + 1, h ], [ g, h + 1 ], [ g - 1, h + 1 ]
    ]
  }

  get coord () { return [ this.#g, this.#h ] }
  get #steps () { return this.#hexGrid.coordToSteps(this.#g, this.#h) }
  get rank () { return Common.mod(this.#steps, this.#keyboard.edo) }
  get octave () { return Math.floor(this.#steps / this.#keyboard.edo) }
  set note (note) { this.#note = note }
  get note () { return this.#note }

  colour ({ bgColour, ctx } = {}) {
    ctx ??= app.state().gridctx;
    const
      { noteColours } = Keyboard, hexGrid = this.#hexGrid,
      [ colourBase, oharm, uharm ] = this.#note.key.label.keyClass
        ?.match(/(black|white)(?:(\d{1,2})o)?(?:(\d{1,2})u)?/)?.slice(1) ?? [],
      vertices = this.vertices(), { isGhost } = this,
      drawHex = c => {
        ctx.beginPath();
        ctx.moveTo(...vertices[5]);
        for (const [ x, y ] of vertices) ctx.lineTo(x, y);
        ctx.strokeStyle = isGhost ? c : "#dddddd";
        ctx.fillStyle = isGhost ? "#00000000" : c;
        ctx.lineWidth = isGhost ? 6 : 1;
        ctx.fill();
        ctx.stroke();
      }
    ctx.globalCompositeOperation = isGhost ? "lighten" : "source-over";
    if (bgColour) drawHex(bgColour);
    else if (colourBase) {
      const
        bc = noteColours[isGhost ? colourBase === "white" ? "black" : "white" : colourBase],
        oc = oharm ? Common.colourMix(bc, noteColours[oharm] ?? noteColours.default, .1) : null,
        uc = uharm ? Common.colourMix(bc, noteColours[uharm] ?? noteColours.default, .1) : null;
      if (oc && uc) {
        bgColour = Common.colourMix(oc, uc, .5);
        drawHex(Common.colourMix(oc, noteColours.white, .1));
        const [cx, cy] = this.centre();
        ctx.save();
        ctx.beginPath();
        ctx.arc(cx, cy, hexGrid.r, 0, Math.PI);
        ctx.closePath();
        ctx.clip();
        drawHex(Common.colourMix(uc, noteColours.black, .1));
        ctx.restore();
      } else drawHex(bgColour = (oc ? Common.colourMix(oc, noteColours.white, .1) : uc ?
        Common.colourMix(uc, noteColours.black, .1) : bc))
    } else drawHex(bgColour = noteColours.default);
    ctx.font = (isGhost ? "bold  " : "") + (.5 * hexGrid.r) + "px HEJI2, Ratafly";
    const [ x, y ] = this.centre(),
          label = hexGrid.displayKeyNames ? this.#note.key.label.letter ?? this.#note.key.label : this.#note.key.rank,
          { width } = ctx.measureText(label);
    ctx.fillStyle = isGhost ? bgColour : HexButton.#contrast(bgColour);
    ctx.fillText(label ?? this.rank, x - width / 2, y)
  }

}



export { HexGrid, HexButton }