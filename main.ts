// Push-optimal Sokoban solver: rooms are independent, each solved with A*
// over pushes (state = boxes + player region), then joined via the hallway.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const IN = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const DX = [0, 0, -1, 1], DY = [-1, 1, 0, 0], DL = ['u', 'd', 'l', 'r'];
const CAP = 400000;
const pc = (x: number): number => { let c = 0; while (x) { x &= x - 1; c++; } return c; };
function parse(t: string) {
  const r = t.split('\n').filter((x) => x.length > 0), h = r.length, w = Math.max(...r.map((x) => x.length));
  const wall = new Uint8Array(w * h).fill(1), goals: number[] = [], boxes: number[] = [];
  let player = -1;
  r.forEach((row, y) => { for (let x = 0; x < row.length; x++) { const ch = row[x]!, i = y * w + x; if (ch === '#') continue; wall[i] = 0; if ('.*+'.includes(ch)) goals.push(i); if ('$*'.includes(ch)) boxes.push(i); if ('@+'.includes(ch)) player = i; } });
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) if (x === 0 || y === 0 || x === w - 1 || y === h - 1) wall[y * w + x] = 1;
  boxes.sort((a, b) => a - b);
  return { w, h, wall, goals, boxes, player };
}
function bfs(w: number, h: number, from: number, ok: (i: number) => boolean): Int32Array {
  const par = new Int32Array(w * h).fill(-1), q = [from];
  par[from] = -2;
  for (let k = 0; k < q.length; k++) { const c = q[k]!, cx = c % w, cy = (c / w) | 0; for (let d = 0; d < 4; d++) { const nx = cx + DX[d]!, ny = cy + DY[d]!; if (nx < 0 || ny < 0 || nx >= w || ny >= h) continue; const n = ny * w + nx; if (par[n] !== -1 || !ok(n)) continue; par[n] = c; q.push(n); } }
  return par;
}
function path(w: number, h: number, from: number, to: number, ok: (i: number) => boolean): string | null {
  if (from === to) return '';
  const par = bfs(w, h, from, ok);
  if (par[to] === -1) return null;
  let s = '';
  for (let c = to; par[c] !== -2; c = par[c]!) { const p = par[c]!, dx = (c % w) - (p % w), dy = ((c / w) | 0) - ((p / w) | 0); s = (dx === 0 && dy === -1 ? 'u' : dx === 0 && dy === 1 ? 'd' : dx === -1 ? 'l' : 'r') + s; }
  return s;
}
function solveRoom(L: ReturnType<typeof parse>, room: { cells: number[]; boxes: number[]; goals: number[] }, starts: number[]) {
  const { w, h, wall } = L, n = room.boxes.length;
  if (n === 0) return { moves: '', start: starts[0]!, end: starts[0]!, pushes: 0 };
  if (n > room.goals.length) return null;
  const inRoom = new Uint8Array(w * h);
  for (const c of room.cells) inRoom[c] = 1;
  const goalSet = new Set(room.goals), startSet = new Set(starts);
  const play = (i: number): boolean => !wall[i] && (inRoom[i] === 1 || startSet.has(i));
  const live = new Uint8Array(w * h), lq = [...room.goals];
  for (const g of room.goals) live[g] = 1;
  for (let k = 0; k < lq.length; k++) { const c = lq[k]!; for (let d = 0; d < 4; d++) { const dd = DY[d]! * w + DX[d]!, p = c - dd, s = p - dd; if (p < 0 || s < 0 || !inRoom[p] || !play(s) || live[p]) continue; live[p] = 1; lq.push(p); } }
  const dist = new Map<number, Int32Array>();
  for (const a of room.cells) { const dd = new Int32Array(w * h).fill(-1); dd[a] = 0; const q = [a]; for (let k = 0; k < q.length; k++) { const c = q[k]!; for (let d = 0; d < 4; d++) { const m = c + DY[d]! * w + DX[d]!; if (!inRoom[m] || dd[m] !== -1) continue; dd[m] = dd[c]! + 1; q.push(m); } } dist.set(a, dd); }
  const heur = (bs: number[]): number => {
    const m = room.goals.length, INF = 1e9, dp = new Float64Array(1 << m).fill(INF);
    dp[0] = 0;
    for (let mask = 0; mask < (1 << m); mask++) { const k = pc(mask); if (k >= n || dp[mask] === INF) continue; for (let j = 0; j < m; j++) { if (mask & (1 << j)) continue; const d = dist.get(bs[k]!)![room.goals[j]!]!; if (d < 0) continue; const nm = mask | (1 << j); if (dp[mask]! + d < dp[nm]!) dp[nm] = dp[mask]! + d; } }
    let best = INF;
    for (let mask = 0; mask < (1 << m); mask++) if (pc(mask) === n && dp[mask]! < best) best = dp[mask]!;
    return best;
  };
  const frozenAt = (dest: number, bs: Set<number>): boolean => {
    const x = dest % w, y = (dest / w) | 0;
    for (let oy = -1; oy <= 0; oy++) for (let ox = -1; ox <= 0; ox++) { const bx = x + ox, by = y + oy; if (bx < 0 || by < 0 || bx + 1 >= w || by + 1 >= h) continue; const cs = [by * w + bx, by * w + bx + 1, (by + 1) * w + bx, (by + 1) * w + bx + 1]; let blocked = 0, bad = false; for (const c of cs) { if (wall[c]) { blocked++; continue; } if (bs.has(c)) { blocked++; if (!goalSet.has(c)) bad = true; } } if (blocked === 4 && bad) return true; }
    return false;
  };
  const regionMin = (player: number, bs: Set<number>): number => { const par = bfs(w, h, player, (i) => play(i) && !bs.has(i)); let mn = Infinity; for (let i = 0; i < w * h; i++) if (par[i] !== -1 && i < mn) mn = i; return mn; };
  const run = (start: number) => {
    type St = { boxes: number[]; player: number; region: number; g: number; f: number; parent: number; box: number; dir: number };
    const sts: St[] = [], heap: number[] = [], seen = new Map<string, number>();
    const keyOf = (bs: number[], r: number): string => bs.join(',') + '|' + r;
    const less = (a: number, b: number): boolean => sts[a]!.f !== sts[b]!.f ? sts[a]!.f < sts[b]!.f : sts[a]!.g !== sts[b]!.g ? sts[a]!.g > sts[b]!.g : a < b;
    const hpush = (i: number): void => { heap.push(i); for (let k = heap.length - 1; k > 0;) { const p = (k - 1) >> 1; if (!less(heap[k]!, heap[p]!)) break; [heap[k], heap[p]] = [heap[p]!, heap[k]!]; k = p; } };
    const hpop = (): number => { const top = heap[0]!, last = heap.pop()!; if (heap.length > 0) { heap[0] = last; for (let k = 0;;) { let c = 2 * k + 1; if (c >= heap.length) break; if (c + 1 < heap.length && less(heap[c + 1]!, heap[c]!)) c++; if (!less(heap[c]!, heap[k]!)) break; [heap[k], heap[c]] = [heap[c]!, heap[k]!]; k = c; } } return top; };
    const b0 = [...room.boxes].sort((a, b) => a - b), h0 = heur(b0);
    if (h0 >= 1e9) return null;
    sts.push({ boxes: b0, player: start, region: regionMin(start, new Set(b0)), g: 0, f: h0, parent: -1, box: -1, dir: -1 });
    seen.set(keyOf(b0, sts[0]!.region), 0);
    hpush(0);
    let expanded = 0;
    while (heap.length > 0) {
      const si = hpop(), s = sts[si]!;
      if (seen.get(keyOf(s.boxes, s.region))! < s.g) continue;
      const boxSet = new Set(s.boxes);
      if (s.boxes.every((b) => goalSet.has(b))) {
        const par = bfs(w, h, s.player, (i) => play(i) && !boxSet.has(i));
        let exit = -1, exitLen = Infinity;
        for (const e of starts) { if (par[e] === -1) continue; const pk = path(w, h, s.player, e, (i) => play(i) && !boxSet.has(i)); if (pk !== null && pk.length < exitLen) { exit = e; exitLen = pk.length; } }
        if (exit < 0) continue;
        const chain: St[] = [];
        for (let t = si; t >= 0; t = sts[t]!.parent) chain.push(sts[t]!);
        chain.reverse();
        let moves = '';
        for (let i = 1; i < chain.length; i++) { const prev = chain[i - 1]!, cur = chain[i]!, dd = DY[cur.dir]! * w + DX[cur.dir]!, stand = cur.box - dd, pb = new Set(prev.boxes); const wk = path(w, h, prev.player, stand, (x) => play(x) && !pb.has(x)); if (wk === null) return null; moves += wk + DL[cur.dir]!; }
        const gb = new Set(s.boxes), ex = path(w, h, s.player, exit, (x) => play(x) && !gb.has(x));
        if (ex === null) return null;
        return { moves: moves + ex, start, end: exit, pushes: s.g };
      }
      if (++expanded > CAP) return null;
      const par = bfs(w, h, s.player, (i) => play(i) && !boxSet.has(i));
      for (const b of s.boxes) for (let d = 0; d < 4; d++) {
        const dd = DY[d]! * w + DX[d]!, stand = b - dd, dest = b + dd;
        if (stand < 0 || par[stand] === -1) continue;
        if (!inRoom[dest] || boxSet.has(dest)) continue;
        const nb = [...s.boxes];
        nb[nb.indexOf(b)] = dest;
        nb.sort((a, b2) => a - b2);
        if (nb.some((x) => !live[x])) continue;
        const nbSet = new Set(nb);
        if (frozenAt(dest, nbSet)) continue;
        const hh = heur(nb);
        if (hh >= 1e9) continue;
        const r = regionMin(b, nbSet), k = keyOf(nb, r), prev = seen.get(k);
        if (prev !== undefined && prev <= s.g + 1) continue;
        seen.set(k, s.g + 1);
        sts.push({ boxes: nb, player: b, region: r, g: s.g + 1, f: s.g + 1 + hh, parent: si, box: b, dir: d });
        hpush(sts.length - 1);
      }
    }
    return null;
  };
  let best: ReturnType<typeof run> = null;
  for (const st of [...starts].sort((a, b) => a - b)) { const r = run(st); if (r && (!best || r.pushes < best.pushes)) best = r; }
  return best;
}
function solveLevel(text: string): string {
  const L = parse(text), { w, h, wall } = L, hy = (L.player / w) | 0;
  const comp = new Int32Array(w * h).fill(-1);
  const rooms: { cells: number[]; boxes: number[]; goals: number[] }[] = [];
  for (let i = 0; i < w * h; i++) {
    if (wall[i] || ((i / w) | 0) === hy || comp[i] !== -1) continue;
    const cells: number[] = [], q = [i];
    comp[i] = rooms.length;
    for (let k = 0; k < q.length; k++) { const c = q[k]!; cells.push(c); for (let d = 0; d < 4; d++) { const m = c + DY[d]! * w + DX[d]!; if (m < 0 || m >= w * h || wall[m] || ((m / w) | 0) === hy || comp[m] !== -1) continue; comp[m] = rooms.length; q.push(m); } }
    rooms.push({ cells, boxes: L.boxes.filter((b) => comp[b] === rooms.length), goals: L.goals.filter((g) => comp[g] === rooms.length) });
  }
  rooms.sort((a, b) => Math.min(...a.cells) - Math.min(...b.cells));
  let moves = '', cur = L.player;
  for (const room of rooms) {
    if (room.boxes.length === 0) continue;
    const starts: number[] = [], seenS = new Set<number>();
    for (const c of room.cells) for (let d = 0; d < 4; d++) { const m = c + DY[d]! * w + DX[d]!; if (((m / w) | 0) === hy && !wall[m] && !seenS.has(m)) { seenS.add(m); starts.push(m); } }
    starts.sort((a, b) => a - b);
    if (starts.length === 0) return '';
    const res = solveRoom(L, room, starts);
    if (!res) return '';
    const walk = path(w, h, cur, res.start, (i) => ((i / w) | 0) === hy && !wall[i]);
    if (walk === null) return '';
    moves += walk + res.moves;
    cur = res.end;
  }
  return moves;
}
for (const id of readdirSync(IN).sort()) {
  const moves = solveLevel(readFileSync(join(IN, id, 'level.txt'), 'utf8'));
  mkdirSync(join(OUT, id), { recursive: true });
  writeFileSync(join(OUT, id, 'solution.txt'), `${moves}\n`);
}
