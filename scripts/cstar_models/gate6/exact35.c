// Gate 6: EXACT joint {2,3,5} block checker, generalising exact3.c (gate 4) by one base-5 phase.
// Fixed-point integer arithmetic (__int128, denominator 2^90).  Per base b in {3,5}: the cell [x, x+rho] in
// pending-stage coordinates (x = b^n a / 2^k mod 1, rho = b^n / 2^k in (2 delta_b, 2b delta_b]); a child resolves
// its stage when rho/2 <= 2 delta_b and must then be DISJOINT from every closed window [A - delta_b, A + delta_b]
// (containment kills, partial overlap leaves an end-zone, a leaf carrying any zone is killed); ambiguous
// resolution (rho/2 within the enclosure of 2 delta_b) takes the min over both interpretations, per base.
// Binary part: SFT sft449.h (as gate 4).
// Bins: (s, i3, j3, i5, j5); base 3: x uniform N3, rho edges as exact3.c (M3); base 5: x edges E5 (dyadic,
// refined near the integers), rho edges geometric (M5).
// Certificate: for every bin, 5^D * (lower bound of sum over alive leaves of W[leaf bin]) >= 9^D * W[bin].
// usage: exact35 N3 M3 N5MODE M5 D MAXB W3file IT THREADS gnum gden [outfile]     (fixed point from W3 x 1)
//        exact35 N3 M3 N5MODE M5 D MAXB check Wfile THREADS                     (read-only check, growth 9/5)
typedef unsigned long size_t;
int printf(const char*, ...); int fflush(void*); void *malloc(size_t); void *calloc(size_t, size_t);
int atoi(const char*); int strcmp(const char*, const char*); double pow(double,double); double log2(double); double round(double); double fmax(double,double);
double floor(double); long strtol(const char*, char**, int); long atol(const char*); long long strtoll(const char*, char**, int);
typedef void FILE; FILE *fopen(const char*, const char*); char *fgets(char*, int, FILE*); int fprintf(FILE*, const char*, ...); int fclose(FILE*); void exit(int);
typedef unsigned long pthread_t; int pthread_create(pthread_t*, const void*, void*(*)(void*), void*); int pthread_join(pthread_t, void**);
#include "../sft449.h"
typedef __int128 Z;
#define F 90
static const Z ONE = (Z)1 << F;
typedef struct { Z xlo, xhi, rlo, rhi, zl, zr; } Bx;
static int BASE[2] = {3, 5};
static Z dlo[2], dhi[2]; static int NOWIN[2]; char *getenv(const char*);
static int N3, M3, N5, M5, D, MAXB;
static Z redge3[64], redge5[64], xedge5[256];
static long long *W;
static long NB3, NB5; // bins per state for base 3 (N3*M3), base 5 (N5*M5)
static __thread int needx[2], needr[2], kill5;
static __thread long boxes;
static Z half(Z v) { if (v & 1) { printf("INEXACT HALF\n"); exit(1); } return v >> 1; }
static Z zmax(Z a, Z b) { return a > b ? a : b; }
static Z fl(Z v) { return v >> F; }
// x-bin of v in [0, 2) for base 5 (extended: v >= 1 gives N5 + bin(v - 1)); floor ownership
static long xbin5(Z v) { Z f = fl(v); long o = (long)f * N5; v -= f * ONE; long i = 0; while (i < N5 - 1 && xedge5[i + 1] <= v) i++; return o + i; }
static void rbins(const Z *e, int M, Z rlo, Z rhi, int *ja, int *jb) {
  int a = 0, b = M - 1; while (a < M - 1 && e[a + 1] < rlo) a++; while (b > 0 && e[b] > rhi) b--; *ja = a; *jb = b; }
static long long leafmin(int s, const Bx *c) {
  Z x3lo = c[0].xlo, x3hi = c[0].xhi, f0 = fl(x3lo); x3lo -= f0 * ONE; x3hi -= f0 * ONE;
  long ia = (long)((x3lo * N3) >> F), ib = (long)((x3hi * N3) >> F); if (ib - ia >= N3) { ia = 0; ib = N3 - 1; }
  int ja, jb; rbins(redge3, M3, c[0].rlo, c[0].rhi, &ja, &jb);
  Z x5lo = c[1].xlo, x5hi = c[1].xhi, f5 = fl(x5lo); x5lo -= f5 * ONE; x5hi -= f5 * ONE;
  long ka = xbin5(x5lo), kb = xbin5(x5hi); if (kb - ka >= N5) { ka = 0; kb = N5 - 1; }
  int la, lb; rbins(redge5, M5, c[1].rlo, c[1].rhi, &la, &lb);
  // a dimension needs refinement only if the weights vary along its span
  long long m = -1; int vx3 = 0, vr3 = 0, vx5 = 0, vr5 = 0;
  for (long x = ia; x <= ib; x++) for (int j = ja; j <= jb; j++) {
    long base = ((long)s * NB3 + (x % N3) * M3 + j) * NB5;
    long base0 = ((long)s * NB3 + (ia % N3) * M3 + j) * NB5, basej = ((long)s * NB3 + (x % N3) * M3 + ja) * NB5;
    for (long y = ka; y <= kb; y++) for (int l = la; l <= lb; l++) {
      long r = (y % N5) * M5 + l; long long v = W[base + r]; if (m < 0 || v < m) m = v;
      if (v != W[base0 + r]) vx3 = 1; if (v != W[basej + r]) vr3 = 1;
      if (v != W[base + (ka % N5) * M5 + l]) vx5 = 1; if (v != W[base + (y % N5) * M5 + la]) vr5 = 1; } }
  if (vx3) needx[0] = 1; if (vr3) needr[0] = 1; if (vx5) needx[1] = 1; if (vr5) needr[1] = 1;
  return m;
}
// window test + rescale for base k; returns 0 if the child surely/possibly dies by containment
static int resolve(int k, Bx *c) {
  Z dl = dlo[k], dh = dhi[k];
  for (Z A = fl(c->xlo) - 1; A <= fl(c->xhi + c->rhi) + 2; A++) {
    Z Ac = A * ONE;
    if (NOWIN[k] || c->xhi + c->rhi < Ac - dh || c->xlo > Ac + dh) continue;
    needx[k] = 1;
    if (zmax(c->xlo, Ac - dh) <= (c->xhi < Ac + dh - c->rlo ? c->xhi : Ac + dh - c->rlo)) { if (k) kill5 = 1; return 0; }
    if (c->xlo <= Ac + dh && c->xhi >= Ac - dh) c->zl = zmax(c->zl, Ac + dh - c->xlo);
    if (c->xlo + c->rlo <= Ac + dh && c->xhi + c->rhi >= Ac - dh) c->zr = zmax(c->zr, c->xhi + c->rhi - (Ac - dh));
  }
  Z b = BASE[k], f0 = fl(c->xlo); c->xlo = b * (c->xlo - f0 * ONE); c->xhi = b * (c->xhi - f0 * ONE);
  c->rlo *= b; c->rhi *= b; if (c->zl >= 0) c->zl *= b; if (c->zr >= 0) c->zr *= b;
  return 1;
}
static long long go(int s, const Bx *c, int depth);
// child with interpretation mask: res[k] in {0 no, 1 yes, 2 ambiguous}; recursion over ambiguous bases
static long long kid(int t, Bx *cc, const int *res, int k, int depth) {
  if (k == 2) return go(t, cc, depth + 1);
  if (res[k] == 0) return kid(t, cc, res, k + 1, depth);
  if (res[k] == 1) { Bx save = cc[k]; long long v = resolve(k, &cc[k]) ? kid(t, cc, res, k + 1, depth) : 0; cc[k] = save; return v; }
  needr[k] = 1;
  Bx save = cc[k];
  long long a = kid(t, cc, res, k + 1, depth);
  cc[k] = save;
  long long b = resolve(k, &cc[k]) ? kid(t, cc, res, k + 1, depth) : 0;
  cc[k] = save;
  return a < b ? a : b;
}
static long long go(int s, const Bx *c, int depth) {
  if (depth == D) {
    for (int k = 0; k < 2; k++) if (c[k].zl >= 0 || c[k].zr >= 0) { needx[k] = 1; if (k) kill5 = 1; return 0; }
    return leafmin(s, c);
  }
  long long v = 0;
  for (int d = 0; d < 2; d++) {
    int t = T[s][d]; if (t < 0) continue;
    Bx cc[2]; int res[2], dead = 0;
    for (int k = 0; k < 2 && !dead; k++) {
      Z hlo = half(c[k].rlo), hhi = half(c[k].rhi);
      cc[k].xlo = d ? c[k].xlo + hlo : c[k].xlo; cc[k].xhi = d ? c[k].xhi + hhi : c[k].xhi;
      cc[k].rlo = hlo; cc[k].rhi = hhi;
      cc[k].zl = d ? (c[k].zl >= hlo ? c[k].zl - hlo : -1) : c[k].zl;
      cc[k].zr = d ? c[k].zr : (c[k].zr >= hlo ? c[k].zr - hlo : -1);
      if (cc[k].zl >= 0 && cc[k].zr >= 0 && cc[k].zl + cc[k].zr >= hlo) { needx[k] = 1; if (k) kill5 = 1; dead = 1; break; }
      Z two = 2 * dlo[k], twohi = 2 * dhi[k];
      res[k] = hhi <= two ? 1 : (hlo > twohi ? 0 : 2);
    }
    if (dead) continue;
    v += kid(t, cc, res, 0, depth);
  }
  return v;
}
static long long NUM, DEN;
// branch and bound over the 4 continuous coordinates
static long long bb(int s, Bx *c, int lvl, long long target) {
  boxes++; needx[0] = needx[1] = needr[0] = needr[1] = 0; kill5 = 0;
  long long v = go(s, c, 0);
  if ((__int128)DEN * v >= (__int128)NUM * target || lvl >= MAXB) return v;
  if (!(needx[0] | needx[1] | needr[0] | needr[1] | kill5)) return v;
  // priority: a possible base-5 kill -> split x5 (alternating with r5 if needed); else base 3 as exact3.c
  // (x, with rho every third level); else the base-5 leaf spans
  int dim;
  if (kill5) dim = (needr[1] && lvl % 3 == 2) ? 3 : 2;
  else if (needx[0] || needr[0]) dim = (needx[0] && (!needr[0] || lvl % 3 != 2)) ? 0 : 1;
  else dim = needx[1] ? 2 : 3;
  int k = dim / 2; Bx save = c[k]; long long a, b;
  if (dim % 2 == 0) { Z m = (c[k].xlo + c[k].xhi) / 2;
    c[k].xhi = m; a = bb(s, c, lvl + 1, target); c[k] = save;
    if ((__int128)DEN * a < (__int128)NUM * target) return a;
    c[k].xlo = m; b = bb(s, c, lvl + 1, target); c[k] = save; }
  else { Z m = ((c[k].rlo + c[k].rhi) / 2) & ~(Z)0xFFFFF;
    c[k].rhi = m; a = bb(s, c, lvl + 1, target); c[k] = save;
    if ((__int128)DEN * a < (__int128)NUM * target) return a;
    c[k].rlo = m; b = bb(s, c, lvl + 1, target); c[k] = save; }
  return a < b ? a : b;
}
static long long binValue(long q, long long target) {
  long s = q / (NB3 * NB5), r3 = (q / NB5) % NB3, r5 = q % NB5;
  int i3 = r3 / M3, j3 = r3 % M3, i5 = r5 / M5, j5 = r5 % M5;
  Bx c[2];
  c[0].xlo = ((Z)i3 << F) / N3; c[0].xhi = ((Z)(i3 + 1) << F) / N3; c[0].rlo = redge3[j3]; c[0].rhi = redge3[j3 + 1]; c[0].zl = c[0].zr = -1;
  c[1].xlo = xedge5[i5]; c[1].xhi = xedge5[i5 + 1]; c[1].rlo = redge5[j5]; c[1].rhi = redge5[j5 + 1]; c[1].zl = c[1].zr = -1;
  return bb((int)s, c, 0, target);
}
static Z todyad(double v, int bits) { return (Z)(long long)round(v * pow(2, bits)) << (F - bits); }
static long Q; static int CHECK, NT;
typedef struct { long lo, hi, low, fail; double worst; long boxes; } Job;
static void *worker(void *p) {
  Job *j = p; j->low = j->fail = 0; j->worst = 1e9; boxes = 0;
  for (long q = j->lo; q < j->hi; q++) { long long w = W[q]; if (w <= 0) continue;
    long long v = binValue(q, w);
    double r = (double)v * DEN / NUM / w; if (r < j->worst) j->worst = r;
    if ((__int128)DEN * v < (__int128)NUM * w) { if (CHECK) { j->fail++; if (j->fail < 5) printf("FAIL bin %ld\n", q); }
      else { W[q] = (long long)((__int128)v * DEN * 99 / (NUM * 100)); j->low++; } } }
  j->boxes = boxes; return 0;
}
static long pass(double *worst, long *bx, long *fail) {
  pthread_t th[64]; Job jb[64]; long chunk = (Q + NT - 1) / NT;
  for (int t = 0; t < NT; t++) { jb[t].lo = t * chunk; jb[t].hi = (t + 1) * chunk < Q ? (t + 1) * chunk : Q; pthread_create(&th[t], 0, worker, &jb[t]); }
  long low = 0; *worst = 1e9; *bx = 0; *fail = 0;
  for (int t = 0; t < NT; t++) { pthread_join(th[t], 0); low += jb[t].low; *fail += jb[t].fail; *bx += jb[t].boxes; if (jb[t].worst < *worst) *worst = jb[t].worst; }
  return low;
}
// print a Z in decimal
static void pz(const char *tag, Z v) { char t[64]; int n = 0; if (v == 0) t[n++] = '0'; while (v > 0) { t[n++] = (char)('0' + (int)(v % 10)); v /= 10; }
  printf("%s ", tag); for (int k = n - 1; k >= 0; k--) printf("%c", t[k]); printf(" /2^90\n"); }
int main(int argc, char **argv) {
  N3 = atoi(argv[1]); M3 = atoi(argv[2]); int mode5 = atoi(argv[3]); M5 = atoi(argv[4]); D = atoi(argv[5]); MAXB = atoi(argv[6]);
  CHECK = !strcmp(argv[7], "check"); NOWIN[1] = getenv("NO5") != 0; // control: no base-5 windows
  NT = atoi(argv[9]);
  // delta3 exactly as exact3.c; delta5 = 5^-4.49 = 7.2e-4, enclosure +-2^-50
  double d3 = pow(3, -4.49); Z dm = todyad(d3, 60); dlo[0] = dm - ((Z)1 << (F - 50)); dhi[0] = dm + ((Z)1 << (F - 50));
  double d5 = pow(5, -4.49); Z dm5 = todyad(d5, 60); dlo[1] = dm5 - ((Z)1 << (F - 50)); dhi[1] = dm5 + ((Z)1 << (F - 50));
  { double U = log2(6); int M2 = (int)fmax(1, round(M3 * (U - 2) / (U - 1))), M1 = M3 - M2; double e[64]; int c = 0;
    for (int t = 0; t <= M1; t++) e[c++] = 1 + (double)t / M1; for (int t = 1; t <= M2; t++) e[c++] = 2 + (U - 2) * t / M2;
    for (int j = 0; j <= M3; j++) redge3[j] = todyad(d3 * pow(2, e[j]), 40);
    redge3[0] = 2 * dlo[0]; redge3[M3] = 6 * dhi[0]; }
  { double U = log2(10); for (int j = 0; j <= M5; j++) redge5[j] = todyad(d5 * pow(2, 1 + (U - 1) * j / M5), 40);
    redge5[0] = 2 * dlo[1]; redge5[M5] = 10 * dhi[1]; }
  // base-5 x edges: uniform 2^m grid, plus geometric refinement near 0 and 1 down to 2^-12
  { int c = 0, U = 1 << mode5; xedge5[c++] = 0; for (int t = 12; t > mode5; t--) xedge5[c++] = ONE >> t;
    for (int u = 1; u < U; u++) xedge5[c++] = ((Z)u << F) / U;
    for (int t = mode5 + 1; t <= 12; t++) xedge5[c++] = ONE - (ONE >> t); xedge5[c] = ONE; N5 = c; }
  NB3 = (long)N3 * M3; NB5 = (long)N5 * M5; Q = (long)S * NB3 * NB5;
  printf("N3 %d M3 %d N5 %d M5 %d D %d MAXB %d bins %ld threads %d\n", N3, M3, N5, M5, D, MAXB, Q, NT);
  pz("d5lo", dlo[1]); pz("d5hi", dhi[1]);
  for (int j = 0; j <= M5; j++) pz("redge5", redge5[j]);
  for (int i = 0; i <= N5; i++) pz("xedge5", xedge5[i]);
  W = calloc(Q, sizeof(long long));
  if (CHECK) { NUM = 1; DEN = 1; for (int i = 0; i < D; i++) { NUM *= 9; DEN *= 5; }
    FILE *f = fopen(argv[8], "r"); char line[64]; long q = 0; while (q < Q && fgets(line, 64, f)) W[q++] = strtoll(line, 0, 10);
    if (q != Q) { printf("SHORT FILE\n"); return 1; }
    for (q = 0; q < Q; q++) if (W[q] < 0) { printf("NEGATIVE %ld\n", q); return 1; }
    double worst; long bx, fail; pass(&worst, &bx, &fail); long pos = 0; for (q = 0; q < Q; q++) if (W[q] > 0) pos++;
    printf("CHECK %s: positive %ld/%ld, failures %ld, worst ratio %.6f, boxes %ld\n", fail ? "FAILED" : "PASSED", pos, Q, fail, worst, bx);
    return fail ? 1 : 0; }
  int IT = atoi(argv[8]);
  if (getenv("QONE")) { long q0 = atol(getenv("QONE")); long Q3 = (long)S * NB3; FILE *f = fopen(argv[7], "r"); char line[64]; long q = 0;
    while (q < Q3 && fgets(line, 64, f)) { long long w = strtoll(line, 0, 10); for (long r = 0; r < NB5; r++) W[q * NB5 + r] = w; q++; }
    NUM = 1; DEN = 1; for (int i = 0; i < D; i++) { NUM *= 9; DEN *= 5; }
    for (long q = q0; q < q0 + 20; q++) { boxes = 0; long long v = binValue(q, W[q]); printf("bin %ld W %lld v %lld ratio %.4f boxes %ld\n", q, W[q], v, W[q] ? (double)v*DEN/NUM/W[q] : 0, boxes); }
    return 0; }
  // argv[7] = W3 file (gate-4 integer weights, S*N3*M3 lines), initial W = W3 (x) 1
  { long Q3 = (long)S * NB3; FILE *f = fopen(argv[7], "r"); char line[64]; long q = 0;
    while (q < Q3 && fgets(line, 64, f)) { long long w = strtoll(line, 0, 10); for (long r = 0; r < NB5; r++) W[q * NB5 + r] = w; q++; }
    if (q != Q3) { printf("SHORT W3 (%ld of %ld)\n", q, Q3); return 1; } }
  int gn = argc > 10 ? atoi(argv[10]) : 9, gd = argc > 11 ? atoi(argv[11]) : 5;
  NUM = 1; DEN = 1; for (int i = 0; i < D; i++) { NUM *= gn; DEN *= gd; }
  for (int it = 0; it < IT; it++) {
    double worst; long bx, fail; long low = pass(&worst, &bx, &fail);
    long z = 0; long long mx = 0; for (long q = 0; q < Q; q++) { if (W[q] <= 0) z++; if (W[q] > mx) mx = W[q]; }
    printf("iter %d lowered %ld zeros %ld boxes %ld worst %.5f maxW %lld\n", it, low, z, bx, worst, mx); fflush(0);
    if (!low) { printf("EXACT CERTIFICATE growth %d/%d positive %ld/%ld maxW %lld\n", gn, gd, Q - z, Q, mx);
      if (argc > 12) { FILE *o = fopen(argv[12], "w"); for (long q = 0; q < Q; q++) fprintf(o, "%lld\n", W[q]); fclose(o); }
      return 0; }
    if (mx == 0) { printf("DEAD\n"); return 1; }
  }
  return 1;
}
