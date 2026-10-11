// Gate 6: EXACT joint {2,3,5} block certificate in PRODUCT form  W(s,i3,j3,i5,j5) = W3(s,i3,j3) * PHI(s,i5,j5).
// Semantics per base b in {3,5} exactly as exact3.c (fixed point 2^-90, delta_b enclosures, closed windows, strict
// zones, a leaf carrying a zone dies, ambiguous resolution = min over both interpretations), binary SFT sft449.h.
// Tensor lower bound: for a parent box3 x box5 and each binary path p of length D from state s,
//   a3[p] = (base-3 survives surely) * min W3 over the base-3 bins the leaf may meet   (0 if possibly killed)
//   b5[p] = (base-5 survives surely) * min PHI over the base-5 bins the leaf may meet
// and every real parent in the box has block value >= sum_p a3[p] b5[p] (the leaf bins met form a product set,
// weights are >= 0, and the true interpretation of every ambiguous test is one of the two taken).
// Certificate: every pair (bin3, bin5) with the same state s, refined by bisection of either side, satisfies
//   DEN * sum_p a3[p] b5[p] >= NUM * W3(bin3) PHI(bin5),  NUM/DEN = (9/5)^D.
// W3 is frozen (gate-4 integer weights certified at growth 181/100 by exact3.c); only PHI is iterated (lowered).
// usage: exact5t N3 M3 MODE5 M5 D MAXB W3file IT THREADS [PHIout]     |   exact5t N3 M3 MODE5 M5 D MAXB W3file check PHIfile THREADS
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
static ll NUM, DEN;
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
// min weight over the bins met by a leaf box of base k in SFT state s
static ll leafmin(int k, int s, const Bx *c, Need *nd) {
  int Nx = k ? N5 : N3, Mx = k ? M5 : M3; const ll *Wt = k ? PHI : W3;
  Z f0 = fl(c->xlo); Z xlo = c->xlo - f0 * ONE, xhi = c->xhi - f0 * ONE;
  long ia = xbin(k, xlo), ib = xbin(k, xhi); if (ib - ia >= Nx) { ia = 0; ib = Nx - 1; }
  int ja, jb; rbins(k, c->rlo, c->rhi, &ja, &jb);
  long base = (long)s * Nx * Mx; ll m = -1, w0 = Wt[base + (ia % Nx) * Mx + ja];
  for (long x = ia; x <= ib; x++) for (int j = ja; j <= jb; j++) { ll v = Wt[base + (x % Nx) * Mx + j];
    if (v != w0) { if (x != ia) nd->nx = 1; if (j != ja) nd->nr = 1; } if (m < 0 || v < m) m = v; }
  return m;
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
static void vgo(int k, int s, Bx c, int depth, int pre, ll *out, Need *nd);
static void vkid(int k, int t, Bx cc, int res, int depth, int pre, ll *out, Need *nd) {
  int lo = pre << (D - depth - 1), n = 1 << (D - depth - 1);
  if (res == 0) { vgo(k, t, cc, depth + 1, pre, out, nd); return; }
  if (res == 1) { if (resolve(k, &cc, nd)) vgo(k, t, cc, depth + 1, pre, out, nd); else for (int i = 0; i < n; i++) out[lo + i] = 0; return; }
  nd->nr = 1;
  ll tmp[NP]; Bx c2 = cc;
  vgo(k, t, cc, depth + 1, pre, out, nd);
  if (resolve(k, &c2, nd)) { vgo(k, t, c2, depth + 1, pre, tmp, nd); for (int i = 0; i < n; i++) if (tmp[lo + i] < out[lo + i]) out[lo + i] = tmp[lo + i]; }
  else for (int i = 0; i < n; i++) out[lo + i] = 0;
}
static void vgo(int k, int s, Bx c, int depth, int pre, ll *out, Need *nd) {
  if (depth == D) { if (c.zl >= 0 || c.zr >= 0) { nd->nx = 1; out[pre] = 0; } else out[pre] = leafmin(k, s, &c, nd); return; }
  for (int d = 0; d < 2; d++) {
    int t = T[s][d], cp = 2 * pre + d, lo = cp << (D - depth - 1), n = 1 << (D - depth - 1);
    if (t < 0) { for (int i = 0; i < n; i++) out[lo + i] = 0; continue; }
    Z hlo = half(c.rlo), hhi = half(c.rhi);
    Bx cc; cc.xlo = d ? c.xlo + hlo : c.xlo; cc.xhi = d ? c.xhi + hhi : c.xhi; cc.rlo = hlo; cc.rhi = hhi;
    cc.zl = d ? (c.zl >= hlo ? c.zl - hlo : -1) : c.zl; cc.zr = d ? c.zr : (c.zr >= hlo ? c.zr - hlo : -1);
    if (cc.zl >= 0 && cc.zr >= 0 && cc.zl + cc.zr >= hlo) { nd->nx = 1; for (int i = 0; i < n; i++) out[lo + i] = 0; continue; }
    int res = hhi <= 2 * dlo[k] ? 1 : (hlo > 2 * dhi[k] ? 0 : 2);
    vkid(k, t, cc, res, depth, cp, out, nd);
  }
}
// lazily refined box tree
typedef struct Node { Bx b; ll v[NP]; Need nd; int lvl; struct Node *ch[2]; } Node;
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
static int worstNZ(int s, Node *n, int depth, Bx *wb) { int nz = 0; for (int p = 0; p < NP; p++) if (n->v[p]) nz++;
  if (depth == 0 || !(n->nd.nx || n->nd.nr)) { *wb = n->b; return nz; }
  split(1, s, n); Bx b0, b1; int a = worstNZ(s, n->ch[0], depth - 1, &b0), b = worstNZ(s, n->ch[1], depth - 1, &b1);
  if (a <= b) { *wb = b0; return a; } *wb = b1; return b; }
static void freeTree(Node *n) { if (!n) return; freeTree(n->ch[0]); freeTree(n->ch[1]); free(n); }
static __thread long pairs;
// lower bound of the pair value, refining until it meets the target (or cannot)
static Z pairv(int s, Node *a, Node *b, Z target, int lvl) {
  pairs++;
  Z v = 0; for (int p = 0; p < NP; p++) v += (Z)a->v[p] * b->v[p];
  if ((Z)DEN * v >= (Z)NUM * target) return v;
  int sa = canSplitK(0, a), sb = canSplitK(1, b);
  if (!sa && !sb) return v;
  int pickB = sb && (!sa || b->lvl <= a->lvl);   // refine the coarser side
  Z r0, r1;
  if (pickB) { split(1, s, b); r0 = pairv(s, a, b->ch[0], target, lvl + 1); if ((Z)DEN * r0 < (Z)NUM * target) return r0; r1 = pairv(s, a, b->ch[1], target, lvl + 1); }
  else { split(0, s, a); r0 = pairv(s, a->ch[0], b, target, lvl + 1); if ((Z)DEN * r0 < (Z)NUM * target) return r0; r1 = pairv(s, a->ch[1], b, target, lvl + 1); }
  return r0 < r1 ? r0 : r1;
}
static Bx box3(long r3) { int i = r3 / M3, j = r3 % M3; Bx c; c.xlo = ((Z)i << F) / N3; c.xhi = ((Z)(i + 1) << F) / N3;
  c.rlo = redge[0][j]; c.rhi = redge[0][j + 1]; c.zl = c.zr = -1; return c; }
static Bx box5(long r5) { int i = r5 / M5, j = r5 % M5; Bx c; c.xlo = xedge5[i]; c.xhi = xedge5[i + 1];
  c.rlo = redge[1][j]; c.rhi = redge[1][j + 1]; c.zl = c.zr = -1; return c; }
static int NT, CHECK; static long NB3, NB5;
typedef struct { long lo, hi, fail, pairs; double worst; ll *newphi; long *zc; } Job;
static void *worker(void *pp) {
  Job *j = pp; j->fail = 0; j->worst = 1e9; pairs = 0;
  Node **T5 = calloc(S * NB5, sizeof(Node*));  // this thread's base-5 trees (lazily refined)
  for (long q5 = 0; q5 < S * NB5; q5++) if (PHI[q5] > 0) T5[q5] = mk(1, q5 / NB5, box5(q5 % NB5), 0);
  for (long q3 = j->lo; q3 < j->hi; q3++) {
    ll w3 = W3[q3]; if (w3 <= 0) continue;
    int s = q3 / NB3; Node *a = 0;
    for (long r5 = 0; r5 < NB5; r5++) { long q5 = s * NB5 + r5; ll ph = PHI[q5]; if (ph <= 0) continue;
      if (!a) a = mk(0, s, box3(q3 % NB3), 0);
      Z target = (Z)w3 * ph; Z v = pairv(s, a, T5[q5], target, 0);
      double r = (double)v * DEN / NUM / (double)target; if (r < j->worst) j->worst = r;
      if (v == 0 && j->zc) j->zc[q5]++;
      if ((Z)DEN * v < (Z)NUM * target) { j->fail++;
        if (CHECK) { if (j->fail < 5) printf("FAIL pair q3 %ld q5 %ld ratio %.6f\n", q3, q5, r); }
        else { ll np = (ll)((v * DEN * 99) / ((Z)NUM * w3 * 100)); if (np < j->newphi[q5]) j->newphi[q5] = np; } } }
    freeTree(a);
  }
  for (long q5 = 0; q5 < S * NB5; q5++) freeTree(T5[q5]); free(T5);
  j->pairs = pairs; return 0;
}
static Z todyad(double v, int bits) { return (Z)(long long)round(v * pow(2, bits)) << (F - bits); }
static void pz(const char *tag, Z v) { char t[64]; int n = 0; if (v == 0) t[n++] = '0'; while (v > 0) { t[n++] = (char)('0' + (int)(v % 10)); v /= 10; }
  printf("%s ", tag); for (int k = n - 1; k >= 0; k--) printf("%c", t[k]); printf("\n"); }
int main(int argc, char **argv) {
  N3 = atoi(argv[1]); M3 = atoi(argv[2]); int mode5 = atoi(argv[3]); M5 = atoi(argv[4]); D = atoi(argv[5]); MAXB = atoi(argv[6]);
  CHECK = !strcmp(argv[8], "check"); NT = atoi(argv[CHECK ? 10 : 9]); NOWIN5 = getenv("NO5") != 0;
  MAXB5 = getenv("MAXB5") ? atoi(getenv("MAXB5")) : MAXB; GEO5 = getenv("GEO5") ? atoi(getenv("GEO5")) : 0;
  if (D != 6) { printf("D must be 6 (NP = 64)\n"); return 1; }
  double d3 = pow(3, -4.49); Z dm = todyad(d3, 60); dlo[0] = dm - ((Z)1 << (F - 50)); dhi[0] = dm + ((Z)1 << (F - 50));
  double d5 = pow(5, -4.49); Z dm5 = todyad(d5, 60); dlo[1] = dm5 - ((Z)1 << (F - 50)); dhi[1] = dm5 + ((Z)1 << (F - 50));
  { double U = log2(6); int M2 = (int)fmax(1, round(M3 * (U - 2) / (U - 1))), M1 = M3 - M2; double e[64]; int c = 0;
    for (int t = 0; t <= M1; t++) e[c++] = 1 + (double)t / M1; for (int t = 1; t <= M2; t++) e[c++] = 2 + (U - 2) * t / M2;
    for (int j = 0; j <= M3; j++) redge[0][j] = todyad(d3 * pow(2, e[j]), 40);
    redge[0][0] = 2 * dlo[0]; redge[0][M3] = 6 * dhi[0]; }
  { double U = log2(10); for (int j = 0; j <= M5; j++) redge[1][j] = todyad(d5 * pow(2, 1 + (U - 1) * j / M5), 40);
    redge[1][0] = 2 * dlo[1]; redge[1][M5] = 10 * dhi[1]; }
  { int c = 0, U = 1 << mode5; xedge5[c++] = 0; for (int t = mode5 + GEO5; t > mode5; t--) xedge5[c++] = ONE >> t;
    for (int u = 1; u < U; u++) xedge5[c++] = ((Z)u << F) / U;
    for (int t = mode5 + 1; t <= mode5 + GEO5; t++) xedge5[c++] = ONE - (ONE >> t); xedge5[c] = ONE; N5 = c; }
  NB3 = (long)N3 * M3; NB5 = (long)N5 * M5;
  printf("GEO5 %d MAXB5 %d N3 %d M3 %d N5 %d M5 %d D %d MAXB %d bins3 %ld bins5 %ld pairs %ld threads %d%s\n", GEO5, MAXB5, N3, M3, N5, M5, D, MAXB, S * NB3, S * NB5, S * NB3 * NB5, NT, NOWIN5 ? " NO5" : "");
  pz("d5lo/2^90", dlo[1]); pz("d5hi/2^90", dhi[1]);
  for (int j = 0; j <= M5; j++) pz("redge5/2^90", redge[1][j]);
  for (int i = 0; i <= N5; i++) pz("xedge5/2^90", xedge5[i]);
  W3 = calloc(S * NB3, sizeof(ll)); PHI = calloc(S * NB5, sizeof(ll));
  { FILE *f = fopen(argv[7], "r"); char line[64]; long q = 0; while (q < S * NB3 && fgets(line, 64, f)) W3[q++] = strtoll(line, 0, 10);
    if (q != S * NB3) { printf("SHORT W3\n"); return 1; } }
  const ll PHI0 = 1LL << 20;
  if (CHECK) { FILE *f = fopen(argv[9], "r"); char line[64]; long q = 0; while (q < S * NB5 && fgets(line, 64, f)) PHI[q++] = strtoll(line, 0, 10);
    if (q != S * NB5) { printf("SHORT PHI\n"); return 1; } }
  else for (long q = 0; q < S * NB5; q++) PHI[q] = PHI0;
  NUM = 1; DEN = 1; for (int i = 0; i < D; i++) { NUM *= 9; DEN *= 5; }
  int IT = CHECK ? 1 : atoi(argv[8]);
  if (getenv("DBG5")) { for (long q5 = 0; q5 < S * NB5; q5 += atoi(getenv("DBG5"))) { Node *n = mk(1, q5 / NB5, box5(q5 % NB5), 0);
      int nz = 0, tot = 0; for (int p = 0; p < NP; p++) { if (n->v[p]) nz++; }
      ll a3[NP]; Need nd = {0,0}; Bx b3 = box3(0); (void)b3; (void)a3; (void)nd; (void)tot;
      Bx wb; int w = worstNZ(q5 / NB5, n, atoi(getenv("DEP")), &wb);
      printf("worst leaf-box nonzero %d at x [%.9f,%.9f] r/d [%.6f,%.6f]  ", w, (double)wb.xlo / (double)ONE, (double)wb.xhi / (double)ONE, (double)wb.rlo / (double)dlo[1], (double)wb.rhi / (double)dlo[1]);
      printf("q5 %ld s %ld i5 %ld j5 %ld nonzero %d nx %d nr %d\n", q5, q5 / NB5, (q5 % NB5) / M5, q5 % M5, nz, n->nd.nx, n->nd.nr); freeTree(n); }
    return 0; }
  for (int it = 0; it < IT; it++) {
    pthread_t th[64]; Job jb[64]; long Q3 = S * NB3, chunk = (Q3 + NT - 1) / NT;
    for (int t = 0; t < NT; t++) { jb[t].lo = t * chunk; jb[t].hi = (t + 1) * chunk < Q3 ? (t + 1) * chunk : Q3;
      jb[t].zc = calloc(S * NB5, sizeof(long)); jb[t].newphi = malloc(S * NB5 * sizeof(ll)); for (long q = 0; q < S * NB5; q++) jb[t].newphi[q] = PHI[q];
      pthread_create(&th[t], 0, worker, &jb[t]); }
    long fail = 0, pr = 0; double worst = 1e9;
    for (int t = 0; t < NT; t++) { pthread_join(th[t], 0); fail += jb[t].fail; pr += jb[t].pairs; if (jb[t].worst < worst) worst = jb[t].worst; }
    long low = 0, z = 0;
    if (!CHECK) for (long q = 0; q < S * NB5; q++) { ll m = PHI[q]; for (int t = 0; t < NT; t++) if (jb[t].newphi[q] < m) m = jb[t].newphi[q];
      if (m < 0) m = 0; if (m < PHI[q]) { PHI[q] = m; low++; } if (PHI[q] == 0) z++; }
    if (getenv("ZC")) { long tot = 0, nb = 0; for (long q = 0; q < S * NB5; q++) { long c = 0; for (int t = 0; t < NT; t++) c += jb[t].zc[q]; if (c) { nb++; tot += c; printf("zc q5 %ld count %ld\n", q, c); } }
      printf("zero-value pairs %ld over %ld base-5 bins\n", tot, nb); }
    for (int t = 0; t < NT; t++) { free(jb[t].newphi); free(jb[t].zc); }
    ll mx = 0; for (long q = 0; q < S * NB5; q++) if (PHI[q] > mx) mx = PHI[q];
    printf("%s %d: failing pairs %ld, phi lowered %ld, phi zeros %ld, worst %.5f, pair evals %ld, max phi %lld\n", CHECK ? "check" : "iter", it, fail, low, z, worst, pr, mx); fflush(0);
    if (CHECK) { printf("CHECK %s\n", fail ? "FAILED" : "PASSED"); return fail ? 1 : 0; }
    if (!fail) { printf("EXACT PRODUCT CERTIFICATE growth 9/5\n");
      if (argc > 10) { FILE *o = fopen(argv[10], "w"); for (long q = 0; q < S * NB5; q++) fprintf(o, "%lld\n", PHI[q]); fclose(o); }
      return 0; }
    if (mx == 0) { printf("DEAD\n"); return 1; }
  }
  return 1;
}
