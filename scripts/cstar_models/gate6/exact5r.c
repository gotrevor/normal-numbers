// Gate 6: {2,3,5} core certificate by a RUN-SUM ADVERSARY (no per-pair checks).
// Facts used, for every real parent cell in a base-3 bin with W3 > 0 (state s):
//   (G3) sum over its D-level leaves of w_l >= g3^D W3(parent), w_l = W3(leaf bin) * [leaf alive for {2,3}]
//        (gate-4 certificate with growth g3 = 181/100, exact3.c);
//   (Q)  for every run I = [i..j] of leaf paths, sum_{l in I} w_l <= Q[s][I] * sum_l w_l   (table, computed here
//        by box bounds: max over met bins / max(sum of min over met bins, g3^D W3)).
// Base 5 (phase PHI(s, i5, j5)): for a base-5 box, c_l = PHI(leaf bins met) if the leaf surely survives base 5,
// else 0.  Layer cake:  sum_l w_l c_l >= sum_k (c_k - c_{k-1}) (1 - sum_{runs of {c < c_k}} Q)^+ * sum_l w_l
//                                     >= g3^D W3(parent) * LC.
// So the weight W3 * PHI grows by g = 9/5 per level if  (g3/g)^D * LC >= PHI(parent) on every base-5 box.
typedef unsigned long size_t;
int printf(const char*, ...); int fflush(void*); void *malloc(size_t); void *calloc(size_t, size_t); void free(void*);
int atoi(const char*); int strcmp(const char*, const char*); double pow(double,double); double log2(double); double round(double); double fmax(double,double);
long long strtoll(const char*, char**, int); char *getenv(const char*);
typedef void FILE; FILE *fopen(const char*, const char*); char *fgets(char*, int, FILE*); int fprintf(FILE*, const char*, ...); int fclose(FILE*); void exit(int);
typedef unsigned long pthread_t; int pthread_create(pthread_t*, const void*, void*(*)(void*), void*); int pthread_join(pthread_t, void**);
#include "../sft449.h"
typedef __int128 Z;
typedef long long ll;
#define F 90
#define NP 64
static const Z ONE = (Z)1 << F;
static const int BASE[2] = {3, 5};
static Z dlo[2], dhi[2];
static int N3, M3, N5, M5, D, MAXB, NOWIN5;
static Z redge[2][64], xedge5[256];
static ll *W3, *PHI;   // W3[s*N3*M3 + i*M3 + j], PHI[s*N5*M5 + i*M5 + j]
static ll NUM, DEN; static long NB3, NB5;
typedef struct { Z xlo, xhi, rlo, rhi, zl, zr; } Bx;
static Z half(Z v) { if (v & 1) { printf("INEXACT HALF\n"); exit(1); } return v >> 1; }
static Z zmax(Z a, Z b) { return a > b ? a : b; }
static Z fl(Z v) { return v >> F; }
static long xbin(int k, Z v) { Z f = fl(v); v -= f * ONE;
  if (k == 0) return (long)f * N3 + (long)((v * N3) >> F);
  long i = 0; while (i < N5 - 1 && xedge5[i + 1] <= v) i++; return (long)f * N5 + i; }
static void rbins(int k, Z rlo, Z rhi, int *ja, int *jb) { int M = k ? M5 : M3; const Z *e = redge[k];
  int a = 0, b = M - 1; while (a < M - 1 && e[a + 1] < rlo) a++; while (b > 0 && e[b] > rhi) b--; *ja = a; *jb = b; }
typedef struct { int nx, nr; } Need;
typedef struct { ll w; int ia, ib, ja, jb; } Lf;  // value, met x-bins ia..ib (unwrapped, ib-ia < N), r-bins ja..jb
// min weight over the bins met by a leaf box of base k in SFT state s
static Lf leafmin(int k, int s, const Bx *c, Need *nd) {
  int Nx = k ? N5 : N3, Mx = k ? M5 : M3; const ll *Wt = k ? PHI : W3;
  Z f0 = fl(c->xlo); Z xlo = c->xlo - f0 * ONE, xhi = c->xhi - f0 * ONE;
  long ia = xbin(k, xlo), ib = xbin(k, xhi); if (ib - ia >= Nx) { ia = 0; ib = Nx - 1; }
  int ja, jb; rbins(k, c->rlo, c->rhi, &ja, &jb);
  long base = (long)s * Nx * Mx; ll m = -1, w0 = Wt[base + (ia % Nx) * Mx + ja];
  for (long x = ia; x <= ib; x++) for (int j = ja; j <= jb; j++) { ll v = Wt[base + (x % Nx) * Mx + j];
    if (v != w0) { if (x != ia) nd->nx = 1; if (j != ja) nd->nr = 1; } if (m < 0 || v < m) m = v; }
  Lf r = { m, (int)ia, (int)ib, ja, jb }; return r;
}
static int resolve(int k, Bx *c, Need *nd) {
  Z dl = dlo[k], dh = dhi[k]; (void)dl;
  if (!(k && NOWIN5)) for (Z A = fl(c->xlo) - 1; A <= fl(c->xhi + c->rhi) + 2; A++) {
    Z Ac = A * ONE;
    if (c->xhi + c->rhi < Ac - dh || c->xlo > Ac + dh) continue;
    nd->nx = 1;
    if (zmax(c->xlo, Ac - dh) <= (c->xhi < Ac + dh - c->rlo ? c->xhi : Ac + dh - c->rlo)) return 0;
    if (c->xlo <= Ac + dh && c->xhi >= Ac - dh) c->zl = zmax(c->zl, Ac + dh - c->xlo);
    if (c->xlo + c->rlo <= Ac + dh && c->xhi + c->rhi >= Ac - dh) c->zr = zmax(c->zr, c->xhi + c->rhi - (Ac - dh));
  }
  Z b = BASE[k], f0 = fl(c->xlo); c->xlo = b * (c->xlo - f0 * ONE); c->xhi = b * (c->xhi - f0 * ONE);
  c->rlo *= b; c->rhi *= b; if (c->zl >= 0) c->zl *= b; if (c->zr >= 0) c->zr *= b;
  return 1;
}
// per-path vector of base k below box c at state s, depth, path prefix pre; writes out[pre << (D-depth) ...]
static const Lf ZL = {0, 0, -1, 0, -1};
static void vgo(int k, int s, Bx c, int depth, int pre, Lf *out, Need *nd);
static void vkid(int k, int t, Bx cc, int res, int depth, int pre, Lf *out, Need *nd) {
  int lo = pre << (D - depth - 1), n = 1 << (D - depth - 1);
  if (res == 0) { vgo(k, t, cc, depth + 1, pre, out, nd); return; }
  if (res == 1) { if (resolve(k, &cc, nd)) vgo(k, t, cc, depth + 1, pre, out, nd); else for (int i = 0; i < n; i++) out[lo + i] = ZL; return; }
  nd->nr = 1;
  if (k == 1 && getenv("DBGAMB")) printf("AMB depth %d h/dlo [%.12f %.12f]\n", depth, (double)cc.rlo / (double)dlo[1], (double)cc.rhi / (double)dlo[1]);
  Lf tmp[NP]; Bx c2 = cc;
  vgo(k, t, cc, depth + 1, pre, out, nd);
  if (resolve(k, &c2, nd)) { vgo(k, t, c2, depth + 1, pre, tmp, nd);
    int Nx = k ? N5 : N3, Mx = k ? M5 : M3;
    for (int i = 0; i < n; i++) { Lf *o = &out[lo + i], *u = &tmp[lo + i];
      if (o->w == 0 || u->w == 0) { *o = ZL; continue; }
      if (u->w < o->w) o->w = u->w;
      if (o->ia != u->ia || o->ib != u->ib || o->ja != u->ja || o->jb != u->jb) { o->ia = 0; o->ib = Nx - 1; o->ja = 0; o->jb = Mx - 1; } } }
  else for (int i = 0; i < n; i++) out[lo + i] = ZL;
}
static void vgo(int k, int s, Bx c, int depth, int pre, Lf *out, Need *nd) {
  if (depth == D) { if (c.zl >= 0 || c.zr >= 0) { nd->nx = 1; out[pre] = ZL; } else { out[pre] = leafmin(k, s, &c, nd); if (out[pre].w == 0) out[pre] = ZL; } return; }
  for (int d = 0; d < 2; d++) {
    int t = T[s][d], cp = 2 * pre + d, lo = cp << (D - depth - 1), n = 1 << (D - depth - 1);
    if (t < 0) { for (int i = 0; i < n; i++) out[lo + i] = ZL; continue; }
    Z hlo = half(c.rlo), hhi = half(c.rhi);
    Bx cc; cc.xlo = d ? c.xlo + hlo : c.xlo; cc.xhi = d ? c.xhi + hhi : c.xhi; cc.rlo = hlo; cc.rhi = hhi;
    cc.zl = d ? (c.zl >= hlo ? c.zl - hlo : -1) : c.zl; cc.zr = d ? c.zr : (c.zr >= hlo ? c.zr - hlo : -1);
    if (cc.zl >= 0 && cc.zr >= 0 && cc.zl + cc.zr >= hlo) { nd->nx = 1; for (int i = 0; i < n; i++) out[lo + i] = ZL; continue; }
    int res = hhi <= 2 * dlo[k] ? 1 : ((k ? hlo >= 2 * dhi[k] : hlo > 2 * dhi[k]) ? 0 : 2);  // dlo < delta < dhi strictly
    vkid(k, t, cc, res, depth, cp, out, nd);
  }
}
// lazily refined box tree
typedef struct Node { Bx b; Lf v[NP]; Need nd; int lvl; struct Node *ch[2]; } Node;
static Node *mk(int k, int s, Bx b, int lvl) { Node *n = malloc(sizeof(Node)); n->b = b; n->lvl = lvl; n->ch[0] = n->ch[1] = 0;
  n->nd.nx = n->nd.nr = 0; vgo(k, s, b, 0, 0, n->v, &n->nd); return n; }
static int MAXB5, GEO5;
static int canSplitK(int k, Node *n) { return n->lvl < (k ? MAXB5 : MAXB) && (n->nd.nx || n->nd.nr); }
static void split(int k, int s, Node *n) {
  if (n->ch[0]) return;
  Bx a = n->b, b = n->b;
  if (n->nd.nx && (!n->nd.nr || n->lvl % 3 != 2)) { Z m = (a.xlo + a.xhi) / 2; a.xhi = m; b.xlo = m; }
  else { Z m = ((a.rlo + a.rhi) / 2) & ~(Z)0xFFFFF; a.rhi = m; b.rlo = m; }
  n->ch[0] = mk(k, s, a, n->lvl + 1); n->ch[1] = mk(k, s, b, n->lvl + 1);
}
static int worstNZ(int s, Node *n, int depth, Bx *wb) { int nz = 0; for (int p = 0; p < NP; p++) if (n->v[p].w) nz++;
  if (depth == 0 || !(n->nd.nx || n->nd.nr)) { *wb = n->b; return nz; }
  split(1, s, n); Bx b0, b1; int a = worstNZ(s, n->ch[0], depth - 1, &b0), b = worstNZ(s, n->ch[1], depth - 1, &b1);
  if (a <= b) { *wb = b0; return a; } *wb = b1; return b; }
static void freeTree(Node *n) { if (!n) return; freeTree(n->ch[0]); freeTree(n->ch[1]); free(n); }
static __thread long pairs;
static void freeTree(Node *n);
static void prune(Node *n, int keep) { if (!n || !n->ch[0]) return; if (n->lvl >= keep) { freeTree(n->ch[0]); freeTree(n->ch[1]); n->ch[0] = n->ch[1] = 0; return; } prune(n->ch[0], keep); prune(n->ch[1], keep); }
static int LS[S][NP];
static Bx box3(long r3) { int i = r3 / M3, j = r3 % M3; Bx c; c.xlo = ((Z)i << F) / N3; c.xhi = ((Z)(i + 1) << F) / N3;
  c.rlo = redge[0][j]; c.rhi = redge[0][j + 1]; c.zl = c.zr = -1; return c; }
static Bx box5(long r5) { int i = r5 / M5, j = r5 % M5; Bx c; c.xlo = xedge5[i]; c.xhi = xedge5[i + 1];
  c.rlo = redge[1][j]; c.rhi = redge[1][j + 1]; c.zl = c.zr = -1; return c; }
static int NT, QB; static long NEXTQ;
static double G3D, GD;   // g3^D, g^D
// ---- base 3 upper bounds: leaf max over met bins, nothing killed, ambiguous = max of both
static ll leafmax3(int s, const Bx *c, Need *nd) {
  Z f0 = fl(c->xlo); Z xlo = c->xlo - f0 * ONE, xhi = c->xhi - f0 * ONE;
  long ia = xbin(0, xlo), ib = xbin(0, xhi); if (ib - ia >= N3) { ia = 0; ib = N3 - 1; }
  int ja, jb; rbins(0, c->rlo, c->rhi, &ja, &jb);
  long base = (long)s * NB3; ll m = 0, w0 = W3[base + (ia % N3) * M3 + ja];
  for (long x = ia; x <= ib; x++) for (int j = ja; j <= jb; j++) { ll v = W3[base + (x % N3) * M3 + j];
    if (v != w0) { if (x != ia) nd->nx = 1; if (j != ja) nd->nr = 1; } if (v > m) m = v; }
  return m;
}
static void rescale(int k, Bx *c) { Z b = BASE[k], f0 = fl(c->xlo); c->xlo = b * (c->xlo - f0 * ONE); c->xhi = b * (c->xhi - f0 * ONE); c->rlo *= b; c->rhi *= b; }
static void hgo(int s, Bx c, int depth, int pre, ll *out, Need *nd) {
  if (depth == D) { out[pre] = leafmax3(s, &c, nd); return; }
  for (int d = 0; d < 2; d++) {
    int t = T[s][d], cp = 2 * pre + d, lo = cp << (D - depth - 1), n = 1 << (D - depth - 1);
    if (t < 0) { for (int i = 0; i < n; i++) out[lo + i] = 0; continue; }
    Z hlo = half(c.rlo), hhi = half(c.rhi);
    Bx cc = c; cc.xlo = d ? c.xlo + hlo : c.xlo; cc.xhi = d ? c.xhi + hhi : c.xhi; cc.rlo = hlo; cc.rhi = hhi;
    int res = hhi <= 2 * dlo[0] ? 1 : (hlo > 2 * dhi[0] ? 0 : 2);
    if (res == 0) hgo(t, cc, depth + 1, cp, out, nd);
    else if (res == 1) { rescale(0, &cc); hgo(t, cc, depth + 1, cp, out, nd); }
    else { nd->nr = 1; ll tmp[NP]; Bx c2 = cc; hgo(t, cc, depth + 1, cp, out, nd); rescale(0, &c2); hgo(t, c2, depth + 1, cp, tmp, nd);
      for (int i = 0; i < n; i++) if (tmp[lo + i] > out[lo + i]) out[lo + i] = tmp[lo + i]; }
  }
}
static double *QT; static int HIST; static long HCNT[20];   // QT[(s*NP + i)*NP + j], i <= j
static __thread double *QL;
static void qbox(int s, Bx b, int lvl, ll w3) {
  Lf lo[NP]; ll hi[NP]; Need n1 = {0, 0}, n2 = {0, 0};
  vgo(0, s, b, 0, 0, lo, &n1); hgo(s, b, 0, 0, hi, &n2);
  if (lvl < QB && (n1.nx || n1.nr || n2.nx || n2.nr)) {
    Bx a = b, c = b; int nx = n1.nx || n2.nx, nr = n1.nr || n2.nr;
    if (nx && (!nr || lvl % 3 != 2)) { Z m = (a.xlo + a.xhi) / 2; a.xhi = m; c.xlo = m; }
    else { Z m = ((a.rlo + a.rhi) / 2) & ~(Z)0xFFFFF; a.rhi = m; c.rlo = m; }
    qbox(s, a, lvl + 1, w3); qbox(s, c, lvl + 1, w3); return; }
  // share(I) = A/(A+B), A = sum_I w <= A_hi, B = sum_{not I} w >= B_lo, A+B >= g3^D W3: increasing in A, decreasing in B
  double prl[NP + 1], prh[NP + 1]; prl[0] = prh[0] = 0;
  for (int p = 0; p < NP; p++) { prl[p + 1] = prl[p] + (double)lo[p].w; prh[p + 1] = prh[p] + (double)hi[p]; }
  double c0 = G3D * (double)w3;
  for (int i = 0; i < NP; i++) for (int j = i; j < NP; j++) {
    double A = prh[j + 1] - prh[i], B = prl[NP] - (prl[j + 1] - prl[i]); double den = A + B; if (den < c0) den = c0;
    double r = den > 0 ? A / den : 0; double *q = &QL[(s * NP + i) * NP + j]; if (r > *q) *q = r; }
}
static void *qworker(void *pp) {
  double *loc = calloc(S * NP * NP, sizeof(double)); QL = loc;
  for (;;) { long q3 = __sync_fetch_and_add(&NEXTQ, 1); if (q3 >= S * NB3) break; ll w3 = W3[q3]; if (w3 <= 0) continue;
    if (HIST) { double *save = QL; QL = calloc(S * NP * NP, sizeof(double)); int s0 = q3 / NB3; qbox(s0, box3(q3 % NB3), 0, w3);
      double m1 = 0; for (int p = 0; p < NP; p++) if (QL[(s0 * NP + p) * NP + p] > m1) m1 = QL[(s0 * NP + p) * NP + p];
      int b = 0; while (b < 19 && m1 > (b + 1) * 0.05) b++; __sync_fetch_and_add(&HCNT[b], 1);
      for (long i = 0; i < S * NP * NP; i++) if (QL[i] > save[i]) save[i] = QL[i]; free(QL); QL = save; }
    else qbox(q3 / NB3, box3(q3 % NB3), 0, w3); }
  return loc;
}
// ---- base-5 check
static double layer(int s, const Lf *v) {
  double lv[NP]; int nl = 0; for (int p = 0; p < NP; p++) if (LS[s][p] >= 0) lv[nl++] = (double)v[p].w;
  // distinct levels ascending
  for (int a = 1; a < nl; a++) { double x = lv[a]; int b = a - 1; while (b >= 0 && lv[b] > x) { lv[b + 1] = lv[b]; b--; } lv[b + 1] = x; }
  double lc = 0, prev = 0;
  for (int k = 0; k < nl; k++) { double ck = lv[k]; if (ck <= prev) continue;
    // runs of {valid l : c_l < ck}, joined across invalid paths
    double sq = 0; int st = -1, last = -1;
    for (int p = 0; p <= NP; p++) {
      int in = p < NP && LS[s][p] >= 0 && (double)v[p].w < ck, inval = p < NP && LS[s][p] < 0;
      if (in) { if (st < 0) st = p; last = p; }
      else if (!inval && st >= 0) { sq += QT[(s * NP + st) * NP + last]; st = -1; }
    }
    double f = 1 - sq; if (f > 0) lc += (ck - prev) * f;
    prev = ck; }
  return lc;
}
static int MAXB5;
static __thread long boxes5;
static double bb5(int s, Bx b, int lvl, double target) {
  boxes5++;
  Lf v[NP]; Need nd = {0, 0}; vgo(1, s, b, 0, 0, v, &nd);
  double V = G3D / GD * layer(s, v);
  if (V >= target || lvl >= MAXB5 || !(nd.nx || nd.nr)) return V;
  Bx a = b, c = b;
  if (nd.nx && (!nd.nr || lvl % 3 != 2)) { Z m = (a.xlo + a.xhi) / 2; a.xhi = m; c.xlo = m; }
  else { Z m = ((a.rlo + a.rhi) / 2) & ~(Z)0xFFFFF; a.rhi = m; c.rlo = m; }
  double r0 = bb5(s, a, lvl + 1, target); if (r0 < target) return r0;
  double r1 = bb5(s, c, lvl + 1, target); return r0 < r1 ? r0 : r1;
}
static ll *NEWPHI; static long LOWERED; static double WORST;
static void *pworker(void *pp) { (void)pp; boxes5 = 0;
  for (;;) { long q5 = __sync_fetch_and_add(&NEXTQ, 1); if (q5 >= S * NB5) break; ll ph = PHI[q5]; if (ph <= 0) continue;
    double V = bb5(q5 / NB5, box5(q5 % NB5), 0, (double)ph * 1.000001);
    double r = V / (double)ph; if (r < WORST) WORST = r;
    if (V < (double)ph * 1.000001) { NEWPHI[q5] = (ll)(V * 0.99); __sync_fetch_and_add(&LOWERED, 1); } }
  return 0; }
static Z todyad(double v, int bits) { return (Z)(long long)round(v * pow(2, bits)) << (F - bits); }
int main(int argc, char **argv) {
  // usage: exact5r N3 M3 MODE5 D QB MAXB5 W3file g3num g3den IT THREADS [PHIout]
  N3 = atoi(argv[1]); M3 = atoi(argv[2]); int mode5 = atoi(argv[3]); D = atoi(argv[4]); QB = atoi(argv[5]); MAXB5 = atoi(argv[6]);
  double g3 = (double)atoi(argv[8]) / atoi(argv[9]); int IT = atoi(argv[10]); NT = atoi(argv[11]);
  G3D = pow(g3, D); GD = pow(1.8, D); NOWIN5 = getenv("NO5") != 0;
  double d3 = pow(3, -4.49); Z dm = todyad(d3, 60); dlo[0] = dm - ((Z)1 << (F - 50)); dhi[0] = dm + ((Z)1 << (F - 50));
  double d5 = pow(5, -4.49); Z dm5 = todyad(d5, 60); dlo[1] = dm5 - ((Z)1 << (F - 50)); dhi[1] = dm5 + ((Z)1 << (F - 50));
  { double U = log2(6); int M2 = (int)fmax(1, round(M3 * (U - 2) / (U - 1))), M1 = M3 - M2; double e[64]; int c = 0;
    for (int t = 0; t <= M1; t++) e[c++] = 1 + (double)t / M1; for (int t = 1; t <= M2; t++) e[c++] = 2 + (U - 2) * t / M2;
    for (int j = 0; j <= M3; j++) redge[0][j] = todyad(d3 * pow(2, e[j]), 40);
    redge[0][0] = 2 * dlo[0]; redge[0][M3] = 6 * dhi[0]; }
  { static const int TM[6] = {5, 3, 1, 6, 4, 2}, TJ[6] = {2, 1, 0, 2, 1, 0};
    const Z G = ((Z)1 << 20) - 1; int c = 0; redge[1][c++] = 2 * dlo[1];
    for (int t = 0; t < 6; t++) { Z p5 = 1; for (int u = 0; u < TJ[t]; u++) p5 *= 5;
      Z lo = ((2 * dlo[1]) << TM[t]) / p5, hi = (((2 * dhi[1]) << TM[t]) + p5 - 1) / p5;
      redge[1][c++] = lo & ~G; redge[1][c++] = (hi + G) & ~G; }
    redge[1][c] = 10 * dhi[1]; M5 = c; }
  { int c = 0, U = 1 << mode5; xedge5[c++] = 0; for (int u = 1; u < U; u++) xedge5[c++] = ((Z)u << F) / U; xedge5[c] = ONE; N5 = c; }
  NB3 = (long)N3 * M3; NB5 = (long)N5 * M5;
  for (int q = 0; q < S; q++) for (int p = 0; p < NP; p++) { int st = q; for (int d = D - 1; d >= 0 && st >= 0; d--) st = T[st][(p >> d) & 1]; LS[q][p] = st; }
  printf("N3 %d M3 %d N5 %d M5 %d D %d QB %d MAXB5 %d g3 %s/%s bins5 %ld threads %d%s\n", N3, M3, N5, M5, D, QB, MAXB5, argv[8], argv[9], S * NB5, NT, NOWIN5 ? " NO5" : ""); fflush(0);
  W3 = calloc(S * NB3, sizeof(ll)); PHI = calloc(S * NB5, sizeof(ll));
  { FILE *f = fopen(argv[7], "r"); char line[64]; long q = 0; while (q < S * NB3 && fgets(line, 64, f)) W3[q++] = strtoll(line, 0, 10);
    if (q != S * NB3) { printf("SHORT W3\n"); return 1; } }
  HIST = getenv("HIST") != 0;
  // Q table
  QT = calloc(S * NP * NP, sizeof(double));
  { pthread_t th[64]; NEXTQ = 0; for (int t = 0; t < NT; t++) pthread_create(&th[t], 0, qworker, 0);
    for (int t = 0; t < NT; t++) { void *r; pthread_join(th[t], &r); double *l = r; for (long i = 0; i < S * NP * NP; i++) if (l[i] > QT[i]) QT[i] = l[i]; free(l); } }
  { double q1 = 0, qall = 0; for (int s = 0; s < S; s++) { for (int p = 0; p < NP; p++) if (QT[(s * NP + p) * NP + p] > q1) q1 = QT[(s * NP + p) * NP + p];
      if (QT[(s * NP) * NP + NP - 1] > qall) qall = QT[(s * NP) * NP + NP - 1]; }
    if (HIST) for (int b = 0; b < 20; b++) printf("  bins with max single share in (%.2f,%.2f]: %ld\n", b * 0.05, (b + 1) * 0.05, HCNT[b]);
    printf("Q table: max single-path share %.4f, max full share %.4f\n", q1, qall);
    for (int L = 1; L <= 64; L *= 2) { double m = 0; for (int s = 0; s < S; s++) for (int i = 0; i + L <= NP; i++) { double v = QT[(s * NP + i) * NP + i + L - 1]; if (v > m) m = v; } printf("  max run share L=%d: %.4f\n", L, m); }
    fflush(0); }
  const ll PHI0 = 1LL << 30;
  for (long q = 0; q < S * NB5; q++) PHI[q] = PHI0;
  NEWPHI = malloc(S * NB5 * sizeof(ll));
  for (int it = 0; it < IT; it++) {
    for (long q = 0; q < S * NB5; q++) NEWPHI[q] = PHI[q];
    LOWERED = 0; WORST = 1e9; NEXTQ = 0; pthread_t th[64];
    for (int t = 0; t < NT; t++) pthread_create(&th[t], 0, pworker, 0);
    for (int t = 0; t < NT; t++) pthread_join(th[t], 0);
    long z = 0; ll mx = 0; for (long q = 0; q < S * NB5; q++) { PHI[q] = NEWPHI[q]; if (PHI[q] <= 0) { PHI[q] = 0; z++; } if (PHI[q] > mx) mx = PHI[q]; }
    printf("iter %d: lowered %ld, zeros %ld/%ld, worst %.5f, max phi %lld\n", it, LOWERED, z, S * NB5, WORST, mx); fflush(0);
    if (!LOWERED) { printf("RUN-SUM CERTIFICATE (float search) growth 9/5 from g3 %s/%s\n", argv[8], argv[9]);
      if (argc > 12) { FILE *o = fopen(argv[12], "w"); for (long q = 0; q < S * NB5; q++) fprintf(o, "%lld\n", PHI[q]); fclose(o); }
      return 0; }
    if (mx == 0) { printf("DEAD\n"); return 1; }
  }
  return 1;
}
