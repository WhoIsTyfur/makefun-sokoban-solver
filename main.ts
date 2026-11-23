import * as fs from "node:fs";
import * as path from "node:path";

const IN = process.argv[2] || "/input", OUT = process.argv[3] || "/output";

function solveLevel(text: string): string {
  const lines = text.replace(/\r/g, "").split("\n").filter((l) => l.length > 0);
  const H = lines.length;
  const W = Math.max(...lines.map((l) => l.length));
  const N = W * H;
  const wall = new Uint8Array(N).fill(1);
  const goal = new Uint8Array(N);
  const box = new Uint8Array(N);
  let player = -1;
  for (let r = 0; r < H; r++) {
    for (let c = 0; c < W; c++) {
      const ch = lines[r][c] ?? "#";
      const i = r * W + c;
      if (ch === "#") continue;
      wall[i] = 0;
      if (ch === "." || ch === "*" || ch === "+") goal[i] = 1;
      if (ch === "$" || ch === "*") box[i] = 1;
      if (ch === "@" || ch === "+") player = i;
    }
  }
  const D = [-W, W, -1, 1];
  const L = ["u", "d", "l", "r"];
  const hallRow = Math.floor(player / W);
  const isHall = (i: number) => Math.floor(i / W) === hallRow;

  // rooms: components of open cells off the hallway row
  const comp = new Int32Array(N).fill(-1);
  const rooms: number[][] = [];
  for (let i = 0; i < N; i++) {
    if (wall[i] || isHall(i) || comp[i] >= 0) continue;
    const id = rooms.length, cells = [i];
    comp[i] = id;
    for (let k = 0; k < cells.length; k++) {
      for (const d of D) {
        const j = cells[k] + d;
        if (j < 0 || j >= N || wall[j] || isHall(j) || comp[j] >= 0) continue;
        comp[j] = id; cells.push(j);
      }
    }
    rooms.push(cells);
  }

  // full-board walk avoiding boxes
  function walk(from: number, to: number): string {
    if (from === to) return "";
    const prev = new Int32Array(N).fill(-1);
    prev[from] = from;
    const q = [from];
    for (let k = 0; k < q.length; k++) {
      const p = q[k];
      for (let d = 0; d < 4; d++) {
        const j = p + D[d];
        if (wall[j] || box[j] || prev[j] >= 0) continue;
        prev[j] = p; q.push(j);
        if (j === to) {
          let s = "", x = to;
          while (x !== from) { const y = prev[x]; s = L[D.indexOf(x - y)] + s; x = y; }
          return s;
        }
      }
    }
    throw new Error("no walk");
  }

  type Plan = { pushes: [number, number][]; exitOk: boolean; hall: number; door: number };
  const plans: Plan[] = [];

  for (const cells of rooms) {
    const inRoom = new Uint8Array(N);
    for (const c of cells) inRoom[c] = 1;
    let door = -1, hall = -1;
    for (const c of cells) for (const d of [-W, W]) if (!wall[c + d] && isHall(c + d)) { door = c; hall = c + d; }
    const boxes0 = cells.filter((c) => box[c]);
    if (boxes0.length === 0 || hall < 0) continue;
    const walkable = new Uint8Array(N);
    for (const c of cells) walkable[c] = 1;
    walkable[hall] = 1;
    // live squares by reverse pulls from goals
    const live = new Uint8Array(N);
    const lq: number[] = [];
    for (const c of cells) if (goal[c]) { live[c] = 1; lq.push(c); }
    for (let k = 0; k < lq.length; k++) {
      const x = lq[k];
      for (const d of D) {
        const y = x - d, p = x - 2 * d;
        if (inRoom[y] && walkable[p] && !live[y]) { live[y] = 1; lq.push(y); }
      }
    }
    const occ = new Uint8Array(N);
    const mark = new Int32Array(N);
    let stamp = 0;
    const reach = (bs: number[], start: number): number[] => {
      for (const b of bs) occ[b] = 1;
      stamp++;
      const q = [start]; mark[start] = stamp;
      for (let k = 0; k < q.length; k++) {
        for (const d of D) {
          const j = q[k] + d;
          if (walkable[j] && !occ[j] && mark[j] !== stamp) { mark[j] = stamp; q.push(j); }
        }
      }
      for (const b of bs) occ[b] = 0;
      return q;
    };
    const keyOf = (bs: number[], reg: number[]) => {
      let m = reg[0];
      for (const x of reg) if (x < m) m = x;
      return bs.join(",") + "|" + m;
    };
    const sBoxes: number[][] = [], sPlayer: number[] = [], sParent: number[] = [], sPush: [number, number][] = [];
    const seen = new Map<string, number>();
    const add = (bs: number[], pl: number, par: number, pu: [number, number]) => {
      const reg = reach(bs, pl);
      const k = keyOf(bs, reg);
      if (seen.has(k)) return;
      seen.set(k, sBoxes.length);
      sBoxes.push(bs); sPlayer.push(pl); sParent.push(par); sPush.push(pu);
    };
    const solved = (bs: number[]) => bs.every((b) => goal[b]);
    add(boxes0.slice().sort((a, b) => a - b), hall, -1, [0, 0]);
    let level = [0], found = -1, foundExit = -1;
    while (level.length && found < 0) {
      for (const s of level) {
        if (solved(sBoxes[s])) {
          if (found < 0) found = s;
          const reg = reach(sBoxes[s], sPlayer[s]);
          if (reg.includes(hall) && foundExit < 0) foundExit = s;
        }
      }
      if (found >= 0) break;
      const next: number[] = [];
      for (const s of level) {
        const bs = sBoxes[s];
        const reg = reach(bs, sPlayer[s]);
        for (const b of bs) occ[b] = 1;
        const moves: [number, number][] = [];
        for (const p of reg) {
          for (let d = 0; d < 4; d++) {
            const b = p + D[d], t = b + D[d];
            if (occ[b] && inRoom[t] && !occ[t] && live[t]) moves.push([b, d]);
          }
        }
        for (const b of bs) occ[b] = 0;
        for (const [b, d] of moves) {
          const nb = bs.map((x) => (x === b ? b + D[d] : x)).sort((x, y) => x - y);
          const before = sBoxes.length;
          add(nb, b, s, [b, d]);
          if (sBoxes.length > before) next.push(sBoxes.length - 1);
        }
      }
      level = next;
    }
    if (found < 0) continue;
    const end = foundExit >= 0 ? foundExit : found;
    const pushes: [number, number][] = [];
    for (let s = end; sParent[s] >= 0; s = sParent[s]) pushes.unshift(sPush[s]);
    plans.push({ pushes, exitOk: foundExit >= 0, hall, door });
  }

  // rooms whose finish leaves the door open go first
  plans.sort((a, b) => Number(b.exitOk) - Number(a.exitOk));
  let out = "";
  for (const pl of plans) {
    for (const [b, d] of pl.pushes) {
      out += walk(player, b - D[d]);
      out += L[d].toUpperCase();
      box[b] = 0; box[b + D[d]] = 1; player = b;
    }
  }
  return out;
}

const ids = fs.existsSync(IN) ? fs.readdirSync(IN).sort() : [];
for (const id of ids) {
  let ans = "";
  try { ans = solveLevel(fs.readFileSync(path.join(IN, id, "level.txt"), "utf8")); } catch { ans = ""; }
  fs.mkdirSync(path.join(OUT, id), { recursive: true });
  fs.writeFileSync(path.join(OUT, id, "solution.txt"), ans + "\n");
}
