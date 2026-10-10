// Interval (rigorous-in-the-abs3-model) shared-phase block certificate, adaptive refinement.
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
          if (cxlo < k + delta && cxhi + chi > k - delta) touch = 1; // open (delta irrational)
          if (cxhi < k + delta && cxlo + clo > k - delta) certain = 1;
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
static double bb(int s, double xlo, double xhi, double ulo, double uhi, int lvl, double target) {
  nb_eval++;
  double v = evalbox(s, xlo, xhi, ulo, uhi);
  if (v < 0) { double um = ulo + usplit; double a = bb(s, xlo, xhi, ulo, um, lvl, target); if (a < target) return a; double b = bb(s, xlo, xhi, um, uhi, lvl, target); return a < b ? a : b; }
  if (v >= target || lvl >= MAXB || !(needx || needu)) return v;
  int nx = needx, nu = needu;
  double a, b;
  if (nx && (!nu || lvl % 3 != 2)) { double xm = (xlo + xhi) / 2; a = bb(s, xlo, xm, ulo, uhi, lvl + 1, target); if (a < target && lvl + 1 >= MAXB) return a; b = bb(s, xm, xhi, ulo, uhi, lvl + 1, target); }
  else { double um = (ulo + uhi) / 2; a = bb(s, xlo, xhi, ulo, um, lvl + 1, target); if (a < target && lvl + 1 >= MAXB) return a; b = bb(s, xlo, xhi, um, uhi, lvl + 1, target); }
  return a < b ? a : b;
}
int main(int argc, char **argv) {
  // usage: N M D IT C MAXB K GROWTH [no3]   (K x K point samples per bin for the candidate V)
  N = atoi(argv[1]); M = atoi(argv[2]); D = atoi(argv[3]); int IT = atoi(argv[4]); C = atof(argv[5]); MAXB = atoi(argv[6]);
  int K = atoi(argv[7]); double G = atof(argv[8]);
  NO3 = argc > 9 && !strcmp(argv[9], "no3");
  delta = pow(3, -C) * 1.0001; U = log2(6); L3 = log2(3);
  int M2 = (int)fmax(1, round(M * (U - 2) / (U - 1))), M1 = M - M2, e = 0;
  for (int t = 0; t <= M1; t++) edges[e++] = 1 + (double)t / M1; for (int t = 1; t <= M2; t++) edges[e++] = 2 + (U - 2) * t / M2;
  for (int s = 0; s < S; s++) for (int d = 0; d < 2; d++) P[s][d] = T[s][d] < 0 ? 0 : R[T[s][d]] / (LAM * R[s]);
  NB = N * M; int Q = S * NB;
  V = malloc(Q * sizeof(double)); double *W = malloc(Q * sizeof(double)), lo = 0;
  for (int q = 0; q < Q; q++) V[q] = 1;
  // candidate V: sampled shared-phase iteration (points; optimistic screen)
  for (int it = 0; it < IT; it++) {
    lo = INFINITY;
    for (int q = 0; q < Q; q++) {
      int s = q / NB, i = (q % NB) / M, j = q % M; double val = INFINITY;
      for (int a = 0; a < K && val > 0; a++) for (int b = 0; b < K; b++) {
        double x = (i + (a + 0.5) / K) / N, u = edges[j] + (edges[j + 1] - edges[j]) * (b + 0.5) / K;
        double v = evalbox(s, x, x, u, u); if (v < 0) v = evalbox(s, x, x, u + 1e-9, u + 1e-9); if (v < val) val = v; }
      W[q] = val; if (V[q] > 1e-12 && val / V[q] < lo) lo = val / V[q];
    }
    double mx = 0; for (int q = 0; q < Q; q++) if (W[q] > mx) mx = W[q];
    if (mx == 0) { printf("C=%g D=%d: DEAD (sampled) at it %d\n", C, D, it); return 0; }
    for (int q = 0; q < Q; q++) V[q] = W[q] / mx;
  }
  int z = 0; for (int q = 0; q < Q; q++) if (V[q] < 1e-9) z++;
  printf("sampled N=%d M=%d D=%d C=%g K=%d: ratio %.6f growth %.6f zeros %d/%d rootV %.3e\n", N, M, D, C, K, lo, LAM * pow(fmax(lo, 0), 1.0 / D), z, Q, V[0]);
  // target-driven fixed point: V <- min(V, LB(bin)/g^D) until stable; LB = branch-and-bound lower bound
  // pruned at the target g^D V(bin).  A fixed point with V > 0 somewhere is a certificate at growth G.
  double gD = pow(G / LAM, D);
  for (int pass = 0; pass < 200; pass++) {
    long changed = 0; nb_eval = 0; double worst = INFINITY;
    for (int q = 0; q < Q; q++) {
      if (V[q] < 1e-300) { V[q] = 0; continue; }
      int s = q / NB, i = (q % NB) / M, j = q % M; double tg = gD * V[q];
      double v = bb(s, (double)i / N, (double)(i + 1) / N, edges[j], edges[j + 1], 0, tg);
      if (v / V[q] < worst) worst = v / V[q];
      if (v < tg * (1 - 1e-12)) { V[q] = v / gD; changed++; }
    }
    double mx = 0; int z = 0; for (int q = 0; q < Q; q++) { if (V[q] > mx) mx = V[q]; if (V[q] < 1e-12) z++; }
    printf("pass %d: lowered %ld bins, worst ratio %.6f, zeros %d/%d, max V %.3e, bin000 %.3e evals %ld\n", pass, changed, worst, z, Q, mx, V[0], nb_eval); fflush(0);
    if (mx < 1e-200) { printf("CERT FAILED at G=%g: weights collapse to 0\n", G); return 0; }
    for (int q = 0; q < Q; q++) V[q] /= mx;
    if (!changed) { printf("CERTIFICATE (float, model) at G=%g: N=%d M=%d D=%d C=%g, %d/%d positive bins, bin000 %.3e\n", G, N, M, D, C, Q - z, Q, V[0]); return 0; }
  }
  return 0;
}
