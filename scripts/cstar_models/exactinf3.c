// Exact-infimum bin iteration, piece-cached (gate 4).  Each bin is split (V-independently) into boxes on which
// every leaf lands in one bin and every base-3 kill is decided (or the depth cap MAXB is hit, then leaf ranges are
// min-ed).  Distinct leaf lists are stored once; W(bin) = min over pieces of sum w V(target)  (exact inf up to caps).
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
// ---- piece store ----
typedef struct { long lo, hi; } Piece;
static Leaf *pstore; static long np_, capp; static Piece *pieces; static long npc, cappc; static long *binp;
static unsigned long hashl(Leaf *a, long n) { unsigned long h = 1469598103934665603UL; for (long i = 0; i < n; i++) { unsigned char *b = (unsigned char *)&a[i]; for (unsigned k = 0; k < sizeof(Leaf); k++) { h ^= b[k]; h *= 1099511628211UL; } } return h ^ n; }
#define HS (1 << 16)
static unsigned long hkey[HS]; static int hstamp[HS], stamp;
static int cmpleaf(Leaf *a, Leaf *b) { if (a->s != b->s) return a->s - b->s; if (a->ia != b->ia) return a->ia - b->ia; if (a->ja != b->ja) return a->ja - b->ja; if (a->ib != b->ib) return a->ib - b->ib; if (a->jb != b->jb) return a->jb - b->jb; return 0; }
static void sortleaves(Leaf *a, long n) { for (long i = 1; i < n; i++) { Leaf x = a[i]; long j = i - 1; while (j >= 0 && cmpleaf(&a[j], &x) > 0) { a[j + 1] = a[j]; j--; } a[j + 1] = x; } }
static long nterm, ncapped;
static void addpiece(void) {
  sortleaves(scratch.a, scratch.n);
  long m = 0; for (long i = 0; i < scratch.n; i++) { Leaf *L = &scratch.a[i];
    if (m && !cmpleaf(&scratch.a[m-1], L)) scratch.a[m-1].w += L->w; else scratch.a[m++] = *L; }
  unsigned long h = hashl(scratch.a, m); int slot = h & (HS - 1);
  while (hstamp[slot] == stamp) { if (hkey[slot] == h) return; slot = (slot + 1) & (HS - 1); }
  hstamp[slot] = stamp; hkey[slot] = h;
  if (np_ + m > capp) { while (np_ + m > capp) capp = capp ? 2 * capp : 1 << 20; pstore = realloc(pstore, capp * sizeof(Leaf)); }
  for (long i = 0; i < m; i++) pstore[np_ + i] = scratch.a[i];
  if (npc == cappc) { cappc = cappc ? 2 * cappc : 1 << 16; pieces = realloc(pieces, cappc * sizeof(Piece)); }
  pieces[npc].lo = np_; pieces[npc].hi = np_ + m; npc++; np_ += m;
}
static void build(int s, double xlo, double xhi, double ulo, double uhi, int lvl) {
  scratch.n = 0; usplit = -1; needx = needu = 0;
  if (!descend(s, xlo, xhi, ulo, uhi, 0, 1, &scratch)) { double um = ulo + usplit; build(s, xlo, xhi, ulo, um, lvl); build(s, xlo, xhi, um, uhi, lvl); return; }
  if ((needx || needu) && lvl < MAXB) {
    if (needx && (!needu || lvl % 3 != 2)) { double xm = (xlo + xhi) / 2; build(s, xlo, xm, ulo, uhi, lvl + 1); build(s, xm, xhi, ulo, uhi, lvl + 1); }
    else { double um = (ulo + uhi) / 2; build(s, xlo, xhi, ulo, um, lvl + 1); build(s, xlo, xhi, um, uhi, lvl + 1); }
    return;
  }
  nterm++; if (needx || needu) ncapped++;
  addpiece();
}
int main(int argc, char **argv) {
  // usage: N M D C IT MAXB
  N = atoi(argv[1]); M = atoi(argv[2]); D = atoi(argv[3]); C = atof(argv[4]); int IT = atoi(argv[5]); MAXB = atoi(argv[6]);
  delta = pow(3, -C) * 1.0001; U = log2(6); L3 = log2(3);
  int M2 = (int)fmax(1, round(M * (U - 2) / (U - 1))), M1 = M - M2, e = 0;
  for (int t = 0; t <= M1; t++) edges[e++] = 1 + (double)t / M1; for (int t = 1; t <= M2; t++) edges[e++] = 2 + (U - 2) * t / M2;
  for (int s = 0; s < S; s++) for (int d = 0; d < 2; d++) P[s][d] = T[s][d] < 0 ? 0 : R[T[s][d]] / (LAM * R[s]);
  NB = N * M; int Q = S * NB; binp = malloc((Q + 1) * sizeof(long));
  for (int q = 0; q < Q; q++) { int s = q / NB, i = (q % NB) / M, j = q % M; binp[q] = npc; stamp++; build(s, (double)i / N, (double)(i + 1) / N, edges[j], edges[j + 1], 0); }
  binp[Q] = npc;
  printf("built: terminal boxes %ld (capped %ld), distinct pieces %ld, leaves %ld\n", nterm, ncapped, npc, np_); fflush(0);
  V = malloc(Q * sizeof(double)); double *W = malloc(Q * sizeof(double)), lo = 0;
  for (int q = 0; q < Q; q++) V[q] = 1;
  for (int it = 0; it < IT; it++) {
    lo = INFINITY;
    for (int q = 0; q < Q; q++) {
      double val = INFINITY;
      for (long p = binp[q]; p < binp[q + 1]; p++) { double sm = 0;
        for (long l = pieces[p].lo; l < pieces[p].hi; l++) { Leaf *L = &pstore[l]; double m = INFINITY;
          for (int x = L->ia; x <= L->ib; x++) { int base = L->s * NB + (((x % N) + N) % N) * M; for (int y = L->ja; y <= L->jb; y++) if (V[base + y] < m) m = V[base + y]; }
          sm += L->w * m; }
        if (sm < val) val = sm; }
      W[q] = val; if (V[q] > 1e-12 && val / V[q] < lo) lo = val / V[q];
    }
    double mx = 0; for (int q = 0; q < Q; q++) if (W[q] > mx) mx = W[q];
    if (mx == 0) { printf("DEAD at it %d\n", it); return 0; }
    for (int q = 0; q < Q; q++) V[q] = W[q] / mx;
    if (it % 10 == 9 || it == IT - 1) { int z = 0; for (int q = 0; q < Q; q++) if (V[q] < 1e-9) z++;
      printf("exact it %d ratio %.6f growth %.6f zeros %d/%d bin000 %.3e\n", it, lo, LAM * pow(fmax(lo, 0), 1.0 / D), z, Q, V[0]); fflush(0); }
  }
  return 0;
}
