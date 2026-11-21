// Push-optimal Sokoban solver, room by room: each room off the hallway is solved on its own by breadth-first search over pushes (state = boxes + player's reachable region); the optima add up. Pushes onto dead squares are pruned. Work is bounded by counted states, never the clock.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const IN = process.env.MAKEFUN_INPUT_DIR ?? '/input', OUT = process.env.MAKEFUN_OUTPUT_DIR ?? '/output', CAP = 2e6;
const D = [[0, -1, 'u', 'U'], [0, 1, 'd', 'D'], [-1, 0, 'l', 'L'], [1, 0, 'r', 'R']];
function A(t) {
const r = t.split('\n').filter((s) => s.length), h = r.length, w = Math.max(...r.map((s) => s.length)), n = w * h, W = new Uint8Array(n).fill(1), G = [], B = [];
let p = -1;
r.forEach((s, y) => { for (let x = 0; x < s.length; x++) { const c = s[x], i = y * w + x; if (c === '#') continue; W[i] = 0; if ('.*+'.includes(c)) G.push(i); if ('$*'.includes(c)) B.push(i); if ('@+'.includes(c)) p = i; } });
for (let i = 0; i < n; i++) { const x = i % w, y = (i / w) | 0; if (!x || !y || x === w - 1 || y === h - 1) W[i] = 1; }
return { w, W, G, B: B.sort((a, b) => a - b), p };
}
function V(L) {
const { w, W, G } = L, v = new Uint8Array(W.length), q = [];
for (const g of G) { v[g] = 1; q.push(g); }
for (let i = 0; i < q.length; i++) { const x = q[i]; for (const [a, b] of D) { const d = b * w + a, y = x - d; if (!W[y] && !W[y - d] && !v[y]) { v[y] = 1; q.push(y); } } }
return v;
}
function C(L, o, f, S, st, P, Q) {
const { w, W } = L, s = [f];
let l = f;
S[f] = st; P[f] = f;
while (s.length) { const p = s.pop(); if (p < l) l = p; for (const [a, b, m] of D) { const q = p + b * w + a; if (!W[q] && !o[q] && S[q] !== st) { S[q] = st; P[q] = p; Q[q] = m; s.push(q); } } }
return l;
}
function S(L) {
const { w, W, G } = L, n = W.length, g = new Uint8Array(n);
for (const x of G) g[x] = 1;
const v = V(L);
if (L.B.some((b) => !v[b])) return null;
const o = new Uint8Array(n), N = new Int32Array(n), M = new Int32Array(n), P = new Int32Array(n), Q = new Array(n);
let st = 0;
const dn = (bs) => bs.every((b) => g[b]), B = [L.B], Y = [L.p], PA = [-1], ix = new Map(), occ = (bs, z) => { for (const b of bs) o[b] = z; };
occ(L.B, 1); ix.set(L.B.join() + '|' + C(L, o, L.p, N, ++st, P, Q), 0); occ(L.B, 0);
let f = dn(L.B) ? 0 : -1;
for (let hd = 0; f < 0 && hd < B.length; hd++) {
const bx = B[hd];
occ(bx, 1); C(L, o, Y[hd], N, ++st, P, Q);
const hr = st;
for (let bi = 0; bi < bx.length && f < 0; bi++) {
const b = bx[bi];
for (const [a, e] of D) {
const d = e * w + a, t = b + d;
if (N[b - d] !== hr || W[t] || o[t] || !v[t]) continue;
const nx = bx.slice();
nx[bi] = t; nx.sort((x, y) => x - y);
o[b] = 0; o[t] = 1;
const lw = C(L, o, b, M, ++st, P, Q);
o[t] = 0; o[b] = 1;
const k = nx.join() + '|' + lw;
if (ix.has(k)) continue;
if (B.length >= CAP) return null;
ix.set(k, B.length); B.push(nx); Y.push(b); PA.push(hd);
if (dn(nx)) f = B.length - 1;
}
}
occ(bx, 0);
}
if (f < 0) return null;
const pt = [];
for (let s = f; s > 0; s = PA[s]) pt.push(s);
pt.reverse();
let mv = '', pl = L.p, bx = L.B;
for (const s of pt) {
const nb = B[s], fr = bx.find((b) => !nb.includes(b)), to = nb.find((b) => !bx.includes(b)), d = to - fr, dr = D.find(([a, e]) => e * w + a === d);
occ(bx, 1); C(L, o, pl, N, ++st, P, Q);
let wk = '';
for (let p = fr - d; p !== pl; p = P[p]) wk = Q[p] + wk;
mv += wk + dr[3];
occ(bx, 0); pl = fr; bx = nb;
}
return mv;
}
function E(L) {
const { w, W, G, B, p } = L, n = W.length, v = V(L), cut = new Uint8Array(n), row = ((p / w) | 0) * w;
for (let i = row; i < row + w; i++) if (!W[i] && !v[i]) cut[i] = 1;
if (B.some((b) => cut[b])) return null;
const pt = new Int32Array(n).fill(-1), R = [];
for (let s = 0; s < n; s++) {
if (W[s] || cut[s] || pt[s] >= 0) continue;
const q = [s];
pt[s] = R.length;
for (let i = 0; i < q.length; i++) for (const [a, b] of D) { const z = q[i] + b * w + a; if (!W[z] && !cut[z] && pt[z] < 0) { pt[z] = R.length; q.push(z); } }
R.push({ B: [], G: [] });
}
for (const b of B) R[pt[b]].B.push(b);
for (const g of G) if (pt[g] >= 0) R[pt[g]].G.push(g);
if (G.some((g) => pt[g] < 0) || R.some((r) => r.B.length !== r.G.length)) return null;
return R.filter((r) => r.B.length);
}
function F(L) {
const R = E(L);
if (R === null) return S(L);
let pl = L.p, mv = '';
const fl = R.map(() => false);
for (let i = 0; i < R.length; i++) {
const W = L.W.slice();
R.forEach((o, j) => { if (j !== i) for (const b of fl[j] ? o.G : o.B) W[b] = 1; });
const r = S({ w: L.w, W, G: R[i].G.slice().sort((a, b) => a - b), B: R[i].B.slice().sort((a, b) => a - b), p: pl });
if (r === null) return null;
mv += r;
for (const c of r.toLowerCase()) pl += c === 'u' ? -L.w : c === 'd' ? L.w : c === 'l' ? -1 : 1;
fl[i] = true;
}
return mv;
}
for (const id of readdirSync(IN).sort()) {
const r = F(A(readFileSync(join(IN, id, 'level.txt'), 'utf8')));
mkdirSync(join(OUT, id), { recursive: true });
writeFileSync(join(OUT, id, 'solution.txt'), r ?? '');
}
