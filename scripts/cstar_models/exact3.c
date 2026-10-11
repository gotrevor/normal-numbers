// EXACT checker for CleanCertificate449 (gate 4): fixed-point integer arithmetic (__int128, denominator 2^F),
// sound enclosures for the irrational delta3 = 3^-4.49, Good449 semantics:
//   cell [x, x + rho] in pending-stage coordinates (x = 3^n a / 2^k, rho = 3^n / 2^k in (2 delta3, 6 delta3]);
//   a child resolves its stage when rho/2 <= 2 delta3; then it must be DISJOINT from every closed window
//   [A - delta3, A + delta3] (containment kills, partial overlap leaves a zone that must be gone at the leaf);
//   binary part = SFT (sft449.h, = minimal forbidden words of Forb2, checked by forb2_check.js).
// Weights W[s,i,j] (integers; W = R[s] V[bin] from the float dump).  Certificate: for every bin,
//   5^(D) * (lower bound of sum over alive leaves of W[leaf]) >= 9^D * W[bin]   (growth 9/5).
// Zones: upper bound of the forbidden end-zone length, -1 = none; a zone >= 0 means the closed window may
// still meet the cell (touching counts), so a leaf with any zone >= 0 is killed.
// Ambiguous resolution (rho/2 within the delta3 enclosure of 2 delta3): min over both interpretations.
// usage: exact3 N M D MAXB check Wfile    (read-only check of frozen integer weights, growth 9/5)
//        exact3 N M D MAXB vdump.txt [iters [gnum gden [dumpfile]]]   (growth gnum/gden, default 9/5)
typedef unsigned long size_t;
int printf(const char*, ...); int fflush(void*); void *malloc(size_t); void *calloc(size_t, size_t);
int atoi(const char*); int strcmp(const char*, const char*); double pow(double,double); double log2(double); double round(double); double fmax(double,double);
double floor(double); double strtod(const char*, char**); long strtol(const char*, char**, int);
typedef void FILE; FILE *fopen(const char*, const char*); char *fgets(char*, int, FILE*); int fprintf(FILE*, const char*, ...); int fclose(FILE*); void exit(int);
#ifndef SFT_H
#include "sft449.h"
#else
#include SFT_H
#endif
typedef __int128 Z;
#define F 90
static const Z ONE = (Z)1 << F;
static Z dlo, dhi;           // delta3 enclosure
static int N, M, D, MAXB; static Z redge[64];  // rho bin edges (enclosure: bin j has rho in [redge[j], redge[j+1]])
static long long *W;
static int needx, needr;
static Z half(Z v) { if (v & 1) { printf("INEXACT HALF\n"); exit(1); } return v >> 1; }
static Z zmax(Z a, Z b) { return a > b ? a : b; }
static Z fl(Z v) { return v >> F; } // floor (v >= 0 or arithmetic shift)
// leaf value: min W over bins met by x in [xlo,xhi] (mod 1), rho in [rlo,rhi]
static long long leafmin(int s, Z xlo, Z xhi, Z rlo, Z rhi) {
  Z f0 = fl(xlo); xlo -= f0 * ONE; xhi -= f0 * ONE;
  long ia = (long)((xlo * N) >> F), ib = (long)((xhi * N) >> F);
  int ja = 0, jb = M - 1;
  while (ja < M - 1 && redge[ja + 1] < rlo) ja++;
  while (jb > 0 && redge[jb] > rhi) jb--;
  if (ib > ia || jb > ja) { if (ib > ia) needx = 1; else needr = 1; }
  long long m = -1;
  for (long x = ia; x <= ib; x++) for (int j = ja; j <= jb; j++) { long long v = W[(long)s * N * M + (x % N) * M + j]; if (m < 0 || v < m) m = v; }
  return m;
}
// value of the subtree of cell box (x in [xlo,xhi], rho in [rlo,rhi]) with zone upper bounds zl, zr
static long long go(int s, Z xlo, Z xhi, Z rlo, Z rhi, int depth, Z zl, Z zr);
static long long child(int t, Z cxlo, Z cxhi, Z crlo, Z crhi, int depth, Z zl, Z zr, int resolve) {
  if (resolve) {
    // windows [A - d, A + d], d in [dlo, dhi]; cell [c, c + h], c in [cxlo, cxhi], h in [crlo, crhi]
    for (Z A = fl(cxlo) - 1; A <= fl(cxhi + crhi) + 2; A++) {
      Z Ac = A * ONE;
      if (cxhi + crhi < Ac - dhi || cxlo > Ac + dhi) continue;           // surely disjoint
      needx = 1;
      // possibly contained: exists c with A - dhi <= c <= A + dhi - crlo
      if (zmax(cxlo, Ac - dhi) <= (cxhi < Ac + dhi - crlo ? cxhi : Ac + dhi - crlo)) return 0;
      // left zone possible: window covers c  (A - d <= c <= A + d)
      if (cxlo <= Ac + dhi && cxhi >= Ac - dhi) zl = zmax(zl, Ac + dhi - cxlo);
      // right zone possible: window covers c + h
      if (cxlo + crlo <= Ac + dhi && cxhi + crhi >= Ac - dhi) zr = zmax(zr, cxhi + crhi - (Ac - dhi));
    }
    Z f0 = fl(cxlo); cxlo = 3 * (cxlo - f0 * ONE); cxhi = 3 * (cxhi - f0 * ONE);
    crlo *= 3; crhi *= 3; if (zl >= 0) zl *= 3; if (zr >= 0) zr *= 3;
  }
  return go(t, cxlo, cxhi, crlo, crhi, depth + 1, zl, zr);
}
static long long go(int s, Z xlo, Z xhi, Z rlo, Z rhi, int depth, Z zl, Z zr) {
  if (depth == D) { if (zl >= 0 || zr >= 0) { needx = 1; return 0; } return leafmin(s, xlo, xhi, rlo, rhi); }
  Z hlo = half(rlo), hhi = half(rhi);
  long long v = 0;
  for (int d = 0; d < 2; d++) {
    int t = T[s][d]; if (t < 0) continue;
    Z cxlo = d ? xlo + hlo : xlo, cxhi = d ? xhi + hhi : xhi;
    Z czl = d ? (zl >= hlo ? zl - hlo : -1) : zl, czr = d ? zr : (zr >= hlo ? zr - hlo : -1);
    if (czl >= 0 && czr >= 0 && czl + czr >= hlo) { needx = 1; continue; } // possibly fully zoned: kill (sound)
    Z two = 2 * dlo, twohi = 2 * dhi;
    if (hhi <= two) v += child(t, cxlo, cxhi, hlo, hhi, depth, czl, czr, 1);
    else if (hlo > twohi) v += child(t, cxlo, cxhi, hlo, hhi, depth, czl, czr, 0);
    else { needr = 1;
      long long a = child(t, cxlo, cxhi, hlo, hhi, depth, czl, czr, 1), b = child(t, cxlo, cxhi, hlo, hhi, depth, czl, czr, 0);
      v += a < b ? a : b; }
  }
  return v;
}
static long long NUM, DEN; // growth^D = NUM / DEN
static long boxes;
// lower bound of the bin value, refined (bisection) while below target
static long long bb(int s, Z xlo, Z xhi, Z rlo, Z rhi, int lvl, long long target) {
  boxes++; needx = needr = 0;
  long long v = go(s, xlo, xhi, rlo, rhi, 0, -1, -1);
  if ((__int128)DEN * v >= (__int128)NUM * target || lvl >= MAXB || !(needx || needr)) return v;
  int nx = needx, nr = needr; long long a, b;
  if (nx && (!nr || lvl % 3 != 2)) { Z m = (xlo + xhi) / 2; a = bb(s, xlo, m, rlo, rhi, lvl + 1, target); if ((__int128)DEN * a < (__int128)NUM * target) return a; b = bb(s, m, xhi, rlo, rhi, lvl + 1, target); }
  else { Z m = ((rlo + rhi) / 2) & ~(Z)0xFFFFF; a = bb(s, xlo, xhi, rlo, m, lvl + 1, target); if ((__int128)DEN * a < (__int128)NUM * target) return a; b = bb(s, xlo, xhi, m, rhi, lvl + 1, target); }
  return a < b ? a : b;
}
static Z todyad(double v, int bits) { return (Z)(long long)round(v * pow(2, bits)) << (F - bits); }
int main(int argc, char **argv) {
  N = atoi(argv[1]); M = atoi(argv[2]); D = atoi(argv[3]); MAXB = atoi(argv[4]); int IT = argc > 6 ? atoi(argv[6]) : 50;
  // delta3 = 3^-4.49 = 0.007193...; enclosure +-2^-50 around the double (double error ~1e-18 << 2^-50)
  double d3 = pow(3, -4.49); Z dm = todyad(d3, 60); dlo = dm - ((Z)1 << (F - 50)); dhi = dm + ((Z)1 << (F - 50));
  double U = log2(6); int M2 = (int)fmax(1, round(M * (U - 2) / (U - 1))), M1 = M - M2; double e[64]; int c = 0;
  for (int t = 0; t <= M1; t++) e[c++] = 1 + (double)t / M1; for (int t = 1; t <= M2; t++) e[c++] = 2 + (U - 2) * t / M2;
  for (int j = 0; j <= M; j++) redge[j] = todyad(d3 * pow(2, e[j]), 40);
  redge[0] = 2 * dlo; redge[M] = 6 * dhi;
  { char b[64]; for (int j = 0; j <= M + 2; j++) { Z v = j <= M ? redge[j] : (j == M + 1 ? dlo : dhi); int n = 0; char t[64];
      while (v > 0) { t[n++] = (char)('0' + (int)(v % 10)); v /= 10; } for (int k = 0; k < n; k++) b[k] = t[n - 1 - k]; b[n] = 0;
      printf("%s %s /2^90\n", j <= M ? "edge" : (j == M + 1 ? "dlo" : "dhi"), b); } }
  int gn = argc > 8 && strcmp(argv[5], "check") ? atoi(argv[7]) : 9, gd = argc > 8 ? atoi(argv[8]) : 5;
  NUM = 1; DEN = 1; for (int i = 0; i < D; i++) { NUM *= gn; DEN *= gd; }
  long Q = (long)S * N * M; W = calloc(Q, sizeof(long long)); double *V = calloc(Q, sizeof(double));
  if (strcmp(argv[5], "check")) { FILE *f = fopen(argv[5], "r"); char line[256]; while (fgets(line, 256, f)) if (line[0] == 'V') { char *p; long q = strtol(line + 2, &p, 10); V[q] = strtod(p, 0); } }
  for (long q = 0; q < Q; q++) W[q] = (long long)floor(R[q / (N * M)] * V[q] * 1099511627776.0); // 2^40
  if (!strcmp(argv[5], "check")) { // read-only check of a frozen integer weight vector (argv[6]); growth 9/5
    FILE *f = fopen(argv[6], "r"); char line[64]; long q = 0; while (q < Q && fgets(line, 64, f)) W[q++] = strtol(line, 0, 10);
    if (q != Q) { printf("SHORT FILE\n"); return 1; }
    long bad = 0, pos = 0; double worst = 1e9; boxes = 0;
    for (long q = 0; q < Q; q++) { if (W[q] < 0) { printf("NEGATIVE %ld\n", q); return 1; } if (W[q] == 0) continue; pos++;
      int s = q / (N * M), i = (q / M) % N, j = q % M;
      long long v = bb(s, ((Z)i << F) / N, ((Z)(i + 1) << F) / N, redge[j], redge[j + 1], 0, W[q]);
      if ((__int128)DEN * v < (__int128)NUM * W[q]) { bad++; if (bad < 10) printf("FAIL bin %ld\n", q); }
      double r = (double)v * DEN / NUM / W[q]; if (r < worst) worst = r; }
    printf("CHECK %s: positive %ld/%ld, failures %ld, worst ratio %.6f, boxes %ld\n", bad ? "FAILED" : "PASSED", pos, Q, bad, worst, boxes);
    return bad ? 1 : 0; }
  for (int it = 0; it < IT; it++) {
    long low = 0, z = 0; double worst = 1e9; boxes = 0;
    for (long q = 0; q < Q; q++) { if (W[q] <= 0) { z++; continue; }
      int s = q / (N * M), i = (q / M) % N, j = q % M;
      long long v = bb(s, ((Z)i << F) / N, ((Z)(i + 1) << F) / N, redge[j], redge[j + 1], 0, W[q]);
      double r = (double)v * DEN / NUM / W[q]; if (r < worst) worst = r;
      if ((__int128)DEN * v < (__int128)NUM * W[q]) { W[q] = (long long)((__int128)v * DEN * 99 / (NUM * 100)); low++; }
    }
    long long mx = 0; for (long q = 0; q < Q; q++) if (W[q] > mx) mx = W[q];
    printf("iter %d lowered %ld zeros %ld boxes %ld worst %.5f maxW %lld W(root-ish bin 0) %lld\n", it, low, z, boxes, worst, mx, W[0]); fflush(0);
    if (!low) { printf("EXACT CERTIFICATE N=%d M=%d D=%d growth %d/%d positive %ld/%ld maxW %lld\n", N, M, D, gn, gd, Q - z, Q, mx);
      if (argc > 9) { FILE *o = fopen(argv[9], "w"); for (long q = 0; q < Q; q++) fprintf(o, "%lld\n", W[q]); fclose(o); }
      return 0; }
    if (mx == 0) { printf("DEAD\n"); return 1; }
  }
  return 1;
}
