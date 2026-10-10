// Exact-infimum bin iteration (gate 4): V(bin) <= inf_{p in bin} sum_leaf w V(bin(leaf(p))), each W(bin) a rigorous
// branch-and-bound lower bound (relative tolerance TOL, depth cap MAXB) of that infimum.
// Same model as shared3rig.js / abs3.js (sft45 binary SFT, touching kills for base 3).
// Each bin (s,i,j) is covered by boxes in (x,u); a box is bisected (x or u) while a leaf box meets
// 2+ bins or a base-3 touch is possible-but-not-certain, up to MAXB bisections.
// Box value = sum_leaf w * min V over met bins; bin value = min over its boxes.
// usage: ./shared3rig N M D IT C MAXB [no3]
typedef unsigned long size_t;
int printf(const char*, ...); int fflush(void*); void *malloc(size_t); void *realloc(void*, size_t); void *calloc(size_t, size_t);
int atoi(const char*); double atof(const char*); int strcmp(const char*, const char*);
double floor(double); double ceil(double); double pow(double,double); double log2(double); double round(double); double fmax(double,double);
#define INFINITY __builtin_inf()
#define fprintf(f, ...) printf(__VA_ARGS__)
#define S 25
static const int T[S][2] = {{1,2},{3,2},{1,4},{5,2},{1,6},{7,2},{1,8},{-1,9},{10,-1},{11,4},{3,12},{-1,13},{14,-1},{-1,15},{16,-1},{17,6},{5,18},{-1,19},{20,-1},{21,4},{3,22},{-1,23},{24,-1},{-1,4},{3,-1}};
static const double R[S] = {1.0,0.9451260262333576,0.9451260262333576,0.8414003846939574,0.8414003846939574,0.6453327778806791,0.6453327778806791,0.274715581679643,0.274715581679643,0.5192816921145327,0.5192816921145327,0.1401728996339273,0.1401728996339273,0.26496211123324204,0.26496211123324204,0.5008451745845498,0.5008451745845498,0.30139084134581684,0.30139084134581684,0.5697046564486004,0.5697046564486004,0.2354850114578546,0.2354850114578546,0.44512602623335756,0.44512602623335756};
static const double LAM = 1.8902520524667157;
static int N, M, D, NO3, MAXB; static double C, delta, U, L3, edges[64]; static const double eps = 1e-12;
static double P[S][2];
typedef struct { float w; short s, ia, ib; unsigned char ja, jb; } Leaf;
typedef struct { Leaf *a; long n, cap; } LV;
static void push(LV *v, Leaf l) { if (v->n == v->cap) { v->cap = v->cap ? 2 * v->cap : 256; v->a = realloc(v->a, v->cap * sizeof(Leaf)); } v->a[v->n++] = l; }
static int binLo(double v) { int j = 0; while (j < M - 1 && edges[j + 1] < v - eps) j++; return j; } // outward: an edge point owns both bins
static int binHi(double v) { int j = M - 1; while (j > 0 && edges[j] > v + eps) j--; return j; }
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
          if (cxlo < k + delta && cxhi + chi > k - delta) touch = 1; // open: real cells never touch exactly (delta irrational)
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

// ---- evaluate a box against V: returns sum_leaf w*minV, or -1 on u-straddle (usplit set) ----
static LV scratch; static double *V; static int NB;
static double evalbox(int s, double xlo, double xhi, double ulo, double uhi) {
  scratch.n = 0; usplit = -1; needx = needu = 0;
  if (!descend(s, xlo, xhi, ulo, uhi, 0, 1, &scratch)) return -1;
  double sm = 0;
  for (long l = 0; l < scratch.n; l++) { Leaf *L = &scratch.a[l]; double m = INFINITY;
    for (int x = L->ia; x <= L->ib; x++) { int base = L->s * NB + (((x % N) + N) % N) * M; for (int y = L->ja; y <= L->jb; y++) if (V[base + y] < m) m = V[base + y]; }
    sm += L->w * m; }
  return sm;
}
static long nb_eval;
// branch and bound: min over the box of the block sum, refined until >= target or depth cap
// rigorous lower bound on inf over the box of the point block sum
static double ub; static double TOL; static long nev;
static double bbmin(int s, double xlo, double xhi, double ulo, double uhi, int lvl) {
  nev++;
  double v = evalbox(s, xlo, xhi, ulo, uhi);
  if (v < 0) { double um = ulo + usplit; double a = bbmin(s, xlo, xhi, ulo, um, lvl), b = bbmin(s, xlo, xhi, um, uhi, lvl); return a < b ? a : b; }
  int nx = needx, nu = needu;
  if (!(nx || nu)) { if (v < ub) ub = v; return v; } // exact on this box (no leaf straddles, no uncertain kill)
  { double xc = (xlo + xhi) / 2, uc = (ulo + uhi) / 2; double pv = evalbox(s, xc, xc, uc, uc); if (pv >= 0 && pv < ub) ub = pv; }
  if (v >= ub * (1 - TOL) || lvl >= MAXB) return v;
  if (nx && (!nu || lvl % 3 != 2)) { double xm = (xlo + xhi) / 2; double a = bbmin(s, xlo, xm, ulo, uhi, lvl + 1), b = bbmin(s, xm, xhi, ulo, uhi, lvl + 1); return a < b ? a : b; }
  double um = (ulo + uhi) / 2; double a = bbmin(s, xlo, xhi, ulo, um, lvl + 1), b = bbmin(s, xlo, xhi, um, uhi, lvl + 1); return a < b ? a : b;
}
int main(int argc, char **argv) {
  // usage: N M D C IT0 K IT MAXB TOL
  N = atoi(argv[1]); M = atoi(argv[2]); D = atoi(argv[3]); C = atof(argv[4]); int IT0 = atoi(argv[5]), K = atoi(argv[6]), IT = atoi(argv[7]); MAXB = atoi(argv[8]); TOL = atof(argv[9]);
  delta = pow(3, -C) * 1.0001; U = log2(6); L3 = log2(3);
  int M2 = (int)fmax(1, round(M * (U - 2) / (U - 1))), M1 = M - M2, e = 0;
  for (int t = 0; t <= M1; t++) edges[e++] = 1 + (double)t / M1; for (int t = 1; t <= M2; t++) edges[e++] = 2 + (U - 2) * t / M2;
  for (int s = 0; s < S; s++) for (int d = 0; d < 2; d++) P[s][d] = T[s][d] < 0 ? 0 : R[T[s][d]] / (LAM * R[s]);
  NB = N * M; int Q = S * NB;
  V = malloc(Q * sizeof(double)); double *W = malloc(Q * sizeof(double)), lo = 0;
  for (int q = 0; q < Q; q++) V[q] = 1;
  for (int it = 0; it < IT0 + IT; it++) {
    lo = INFINITY; nev = 0;
    for (int q = 0; q < Q; q++) {
      int s = q / NB, i = (q % NB) / M, j = q % M; double val = INFINITY;
      if (it < IT0) {
        for (int a = 0; a < K && val > 0; a++) for (int b = 0; b < K; b++) {
          double x = (i + (a + 0.5) / K) / N, u = edges[j] + (edges[j + 1] - edges[j]) * (b + 0.5) / K;
          double v = evalbox(s, x, x, u, u); if (v < 0) v = evalbox(s, x, x, u + 1e-9, u + 1e-9); if (v < val) val = v; }
      } else { ub = INFINITY; val = bbmin(s, (double)i / N, (double)(i + 1) / N, edges[j], edges[j + 1], 0); if (val < 0) val = 0; }
      W[q] = val; if (V[q] > 1e-12 && val / V[q] < lo) lo = val / V[q];
    }
    double mx = 0; for (int q = 0; q < Q; q++) if (W[q] > mx) mx = W[q];
    if (mx == 0) { printf("DEAD at it %d\n", it); return 0; }
    for (int q = 0; q < Q; q++) V[q] = W[q] / mx;
    int z = 0; for (int q = 0; q < Q; q++) if (V[q] < 1e-9) z++;
    printf("%s it %d ratio %.6f growth %.6f zeros %d/%d rootV %.3e evals %ld\n", it < IT0 ? "sampled" : "exactinf", it, lo, LAM * pow(fmax(lo, 0), 1.0 / D), z, Q, V[0], nev); fflush(0);
  }
  return 0;
}
