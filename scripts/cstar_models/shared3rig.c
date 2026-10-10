// Interval (rigorous-in-the-abs3-model) shared-phase block certificate, adaptive refinement.
// Same model as shared3rig.js / abs3.js (sft45 binary SFT, touching kills for base 3).
// Each bin (s,i,j) is covered by boxes in (x,u); a box is bisected (x or u) while a leaf box meets
// 2+ bins or a base-3 touch is possible-but-not-certain, up to MAXB bisections.
// Box value = sum_leaf w * min V over met bins; bin value = min over its boxes.
// usage: ./shared3rig N M D IT C MAXB [no3]
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#define S 25
static const int T[S][2] = {{1,2},{3,2},{1,4},{5,2},{1,6},{7,2},{1,8},{-1,9},{10,-1},{11,4},{3,12},{-1,13},{14,-1},{-1,15},{16,-1},{17,6},{5,18},{-1,19},{20,-1},{21,4},{3,22},{-1,23},{24,-1},{-1,4},{3,-1}};
static const double R[S] = {1.0,0.9451260262333576,0.9451260262333576,0.8414003846939574,0.8414003846939574,0.6453327778806791,0.6453327778806791,0.274715581679643,0.274715581679643,0.5192816921145327,0.5192816921145327,0.1401728996339273,0.1401728996339273,0.26496211123324204,0.26496211123324204,0.5008451745845498,0.5008451745845498,0.30139084134581684,0.30139084134581684,0.5697046564486004,0.5697046564486004,0.2354850114578546,0.2354850114578546,0.44512602623335756,0.44512602623335756};
static const double LAM = 1.8902520524667157;
static int N, M, D, NO3, MAXB; static double C, delta, U, L3, edges[64]; static const double eps = 1e-12;
static double P[S][2];
typedef struct { float w; short s, ia, ib; unsigned char ja, jb; } Leaf;
typedef struct { Leaf *a; long n, cap; } LV;
static void push(LV *v, Leaf l) { if (v->n == v->cap) { v->cap = v->cap ? 2 * v->cap : 256; v->a = realloc(v->a, v->cap * sizeof(Leaf)); } v->a[v->n++] = l; }
static int binLo(double v) { int j = 0; while (j < M - 1 && edges[j + 1] <= v + eps) j++; return j; }
static int binHi(double v) { int j = M - 1; while (j > 0 && edges[j] >= v - eps) j--; return j; }
// status flags
static double usplit; static int needx, needu;
static int descend(int s, double xlo, double xhi, double ulo, double uhi, int depth, double w, LV *out) {
  if (depth == D) {
    double fl = floor(xlo); xlo -= fl; xhi -= fl;
    Leaf l; l.w = w; l.s = s; l.ia = (short)floor(xlo * N + eps); l.ib = (short)(ceil(xhi * N - eps) - 1);
    l.ja = binLo(ulo); l.jb = binHi(uhi); if (l.ib < l.ia) l.ib = l.ia;
    if (l.ib > l.ia) needx = 1; if (l.jb > l.ja) needu = 1;
    push(out, l); return 1;
  }
  double rlo = delta * pow(2, ulo), rhi = delta * pow(2, uhi);
  for (int d = 0; d < 2; d++) {
    int t = T[s][d]; if (t < 0) continue;
    double cxlo = xlo + d * rlo / 2, cxhi = xhi + d * rhi / 2, culo = ulo - 1, cuhi = uhi - 1;
    if (culo < 1 - eps && cuhi > 1 + eps) { usplit = 1 - culo; return 0; }
    if (cuhi <= 1 + eps) {
      if (!NO3) {
        double clo = rlo / 2, chi = rhi / 2; int touch = 0, certain = 0;
        for (long k = (long)floor(cxlo) - 1; k <= (long)ceil(cxhi + chi) + 1; k++) {
          if (cxlo <= k + delta + eps && cxhi + chi >= k - delta - eps) touch = 1;
          if (cxhi <= k + delta && cxlo + clo >= k - delta) certain = 1;
        }
        if (touch) { if (!certain) needx = 1; continue; }
      }
      double fl = floor(3 * cxlo); cxlo = 3 * cxlo - fl; cxhi = 3 * cxhi - fl; culo += L3; cuhi += L3;
    }
    if (!descend(t, cxlo, cxhi, culo, cuhi, depth + 1, w * P[s][d], out)) return 0;
  }
  return 1;
}
typedef struct { long *off; int nb, cap; } BL; // box offsets into leaf store (off[k]..off[k+1])
static LV store; static BL *bins; static long nboxes = 0, maxdepthhit = 0;
static void boxes(int s, double xlo, double xhi, double ulo, double uhi, int lvl, int q) {
  long start = store.n; usplit = -1; needx = needu = 0;
  int ok = descend(s, xlo, xhi, ulo, uhi, 0, 1, &store);
  if (!ok) { store.n = start; double um = ulo + usplit; boxes(s, xlo, xhi, ulo, um, lvl, q); boxes(s, xlo, xhi, um, uhi, lvl, q); return; }
  if ((needx || needu) && lvl < MAXB) {
    store.n = start;
    if (needx) { double xm = (xlo + xhi) / 2; boxes(s, xlo, xm, ulo, uhi, lvl + 1, q); boxes(s, xm, xhi, ulo, uhi, lvl + 1, q); }
    else { double um = (ulo + uhi) / 2; boxes(s, xlo, xhi, ulo, um, lvl + 1, q); boxes(s, xlo, xhi, um, uhi, lvl + 1, q); }
    return;
  }
  if (needx || needu) maxdepthhit++;
  BL *b = &bins[q]; if (b->nb + 2 > b->cap) { b->cap = b->cap ? 2 * b->cap : 8; b->off = realloc(b->off, b->cap * sizeof(long)); }
  b->off[b->nb] = start; b->off[b->nb + 1] = store.n; b->nb++; nboxes++;
}
int main(int argc, char **argv) {
  N = atoi(argv[1]); M = atoi(argv[2]); D = atoi(argv[3]); int IT = atoi(argv[4]); C = atof(argv[5]); MAXB = atoi(argv[6]);
  NO3 = argc > 7 && !strcmp(argv[7], "no3");
  delta = pow(3, -C) * 1.0001; U = log2(6); L3 = log2(3);
  int M2 = (int)fmax(1, round(M * (U - 2) / (U - 1))), M1 = M - M2, e = 0;
  for (int t = 0; t <= M1; t++) edges[e++] = 1 + (double)t / M1; for (int t = 1; t <= M2; t++) edges[e++] = 2 + (U - 2) * t / M2;
  for (int s = 0; s < S; s++) for (int d = 0; d < 2; d++) P[s][d] = T[s][d] < 0 ? 0 : R[T[s][d]] / (LAM * R[s]);
  int NB = N * M, Q = S * NB; bins = calloc(Q, sizeof(BL));
  for (int q = 0; q < Q; q++) { int s = q / NB, i = (q % NB) / M, j = q % M; boxes(s, (double)i / N, (double)(i + 1) / N, edges[j], edges[j + 1], 0, q); }
  fprintf(stderr, "boxes %ld leaves %ld (%.1f MB) unrefined-at-cap %ld\n", nboxes, store.n, store.n * sizeof(Leaf) / 1e6, maxdepthhit);
  double *V = malloc(Q * sizeof(double)), *W = malloc(Q * sizeof(double)), lo = 0;
  for (int q = 0; q < Q; q++) V[q] = 1;
  for (int it = 0; it < IT; it++) {
    lo = INFINITY;
    #pragma omp parallel for schedule(dynamic, 64) reduction(min:lo)
    for (int q = 0; q < Q; q++) {
      double val = INFINITY; BL *b = &bins[q];
      for (int k = 0; k < b->nb; k++) {
        double sm = 0;
        for (long l = b->off[k]; l < b->off[k + 1]; l++) { Leaf *L = &store.a[l]; double m = INFINITY;
          for (int x = L->ia; x <= L->ib; x++) { int base = L->s * NB + (((x % N) + N) % N) * M; for (int y = L->ja; y <= L->jb; y++) if (V[base + y] < m) m = V[base + y]; }
          sm += L->w * m; }
        if (sm < val) val = sm;
      }
      W[q] = val; if (V[q] > 1e-12 && val / V[q] < lo) lo = val / V[q];
    }
    double mx = 0; for (int q = 0; q < Q; q++) if (W[q] > mx) mx = W[q];
    if (mx == 0) { printf("rigC C=%g D=%d: DEAD at it %d\n", C, D, it); return 0; }
    for (int q = 0; q < Q; q++) V[q] = W[q] / mx;
    if (it % 10 == 9) fprintf(stderr, "it %d lo %.6f growth %.6f\n", it, lo, LAM * pow(fmax(lo, 0), 1.0 / D));
  }
  int z = 0; double mp = INFINITY; for (int q = 0; q < Q; q++) { if (V[q] < 1e-9) z++; else if (V[q] < mp) mp = V[q]; }
  printf("rigC%s N=%d M=%d D=%d C=%g MAXB=%d: block ratio %.6f per-level growth %.6f zeros %d/%d minpos %.3e rootV %.3e boxes %ld capped %ld\n",
    NO3 ? " no3" : "", N, M, D, C, MAXB, lo, LAM * pow(fmax(lo, 0), 1.0 / D), z, Q, mp, V[0], nboxes, maxdepthhit);
  return 0;
}
