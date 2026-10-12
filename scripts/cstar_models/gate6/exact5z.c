// Gate 6: EXACT joint {2,3,5} block certificate, PRODUCT form with sparse EXCEPTIONS:
//   W(s,i3,j3,i5,j5) = E(q3,q5) if (q3,q5) is an exception (E < W3*PHI), else W3(s,i3,j3) * PHI(s,i5,j5).
// Leaf bound per path: min(a3*b5, min E over exceptions in the leaf's met bin set).
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
int rename(const char*, const char*); int mkdir(const char*, unsigned); long atol(const char*);
struct timespec { long tv_sec, tv_nsec; }; int clock_gettime(int, struct timespec*);
double now(void) { struct timespec t; clock_gettime(1, &t); return t.tv_sec + 1e-9 * t.tv_nsec; } int snprintf(char*, size_t, const char*, ...); int sscanf(const char*, const char*, ...);
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
static __thread long nnodes;   // live nodes of this thread (memory budget)
static Node *mk(int k, int s, Bx b, int lvl) { Node *n = malloc(sizeof(Node)); nnodes++; n->b = b; n->lvl = lvl; n->ch[0] = n->ch[1] = 0;
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
static void freeTree(Node *n) { if (!n) return; freeTree(n->ch[0]); freeTree(n->ch[1]); free(n); nnodes--; }
static __thread long pairs;
static void freeTree(Node *n);
static void prune(Node *n, int keep) { if (!n || !n->ch[0]) return; if (n->lvl >= keep) { freeTree(n->ch[0]); freeTree(n->ch[1]); n->ch[0] = n->ch[1] = 0; return; } prune(n->ch[0], keep); prune(n->ch[1], keep); }
static int LS[S][NP];   // leaf SFT state of path p from parent state s (-1: path not allowed)
typedef struct { int r3; ll e; } Ex;
static Ex **EX; static int *EXN;   // per q5: exceptions (r3 within the state, value), sorted by r3
static ll exLookup(long q5, int r3) { Ex *a = EX[q5]; int lo = 0, hi = EXN[q5] - 1;
  while (lo <= hi) { int m = (lo + hi) / 2; if (a[m].r3 == r3) return a[m].e; if (a[m].r3 < r3) lo = m + 1; else hi = m - 1; } return -1; }
// min exception value over the met product set of one path (or -1 if none)
static Z exMin(int sl, const Lf *u, const Lf *b) {
  Z m = -1;
  for (int y = b->ia; y <= b->ib; y++) for (int l = b->ja; l <= b->jb; l++) {
    long q5 = (long)sl * NB5 + (y % N5) * M5 + l; int n = EXN[q5]; if (!n) continue;
    Ex *a = EX[q5];
    for (int t = 0; t < n; t++) { int i3 = a[t].r3 / M3, j3 = a[t].r3 % M3;
      int di = ((i3 - u->ia) % N3 + N3) % N3;
      if (di <= u->ib - u->ia && j3 >= u->ja && j3 <= u->jb) if (m < 0 || a[t].e < m) m = a[t].e; } }
  return m;
}
// lower bound of the pair value, refining until it meets the target (or cannot)
static Z pairv(int s, Node *a, Node *b, Z target, int lvl) {
  static long NB5_; (void)NB5_;
  pairs++;
  Z v = 0; for (int p = 0; p < NP; p++) { if (!a->v[p].w || !b->v[p].w) continue;
    Z t = (Z)a->v[p].w * b->v[p].w; Z e = exMin(LS[s][p], &a->v[p], &b->v[p]); if (e >= 0 && e < t) t = e; v += t; }
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
static int NT, CHECK;
static long NEXTQ;
typedef struct { long q3, q5; ll v, tgt; } Rec;   // failing pair: lower bound v*DEN/NUM vs target
typedef struct { long lo, hi, fail, pairs; double worst; Rec *rec; long nrec, cap; } Job;
// in-pass chunks: chunk k = { q3 : q3 % NC == k } (interleaved, so any prefix of chunks samples every state).
typedef struct { int done; long fail, pairs; double worst; Rec *rec; long nrec; } Chunk;
static int NC = 100, NCRUN; static Chunk *CH; static long NEXTC, NDONE; static char PASSDIR[1024]; static double T0; static long NODECAP, INCAP; static int PKEEP;
double now(void);
static long vmkb(const char *key) { FILE *f = fopen("/proc/self/status", "r"); char line[256]; long v = -1; int L = 0; while (key[L]) L++;
  while (f && fgets(line, 256, f)) { int m = 1; for (int i = 0; i < L; i++) if (line[i] != key[i]) { m = 0; break; } if (m) { sscanf(line + L, "%ld", &v); break; } }
  if (f) fclose(f); return v; }
static void chunkSave(int k) { Chunk *c = &CH[k]; char a[1100], b[1100];
  snprintf(a, 1100, "%s/c%d.txt.tmp", PASSDIR, k); FILE *o = fopen(a, "w");
  fprintf(o, "%ld %ld %.17g %ld\n", c->fail, c->pairs, c->worst, c->nrec);
  for (long i = 0; i < c->nrec; i++) fprintf(o, "%ld %ld %lld %lld\n", c->rec[i].q3, c->rec[i].q5, c->rec[i].v, c->rec[i].tgt);
  fprintf(o, "END\n"); fclose(o); snprintf(b, 1100, "%s/c%d.txt", PASSDIR, k); rename(a, b); free(c->rec); c->rec = 0; }
static int chunkLoad(int k, int recs) { Chunk *c = &CH[k]; char a[1100], line[256]; snprintf(a, 1100, "%s/c%d.txt", PASSDIR, k);
  FILE *f = fopen(a, "r"); if (!f) return 0; if (!fgets(line, 256, f)) { fclose(f); return 0; }
  sscanf(line, "%ld %ld %lg %ld", &c->fail, &c->pairs, &c->worst, &c->nrec);
  if (recs) { c->rec = malloc((c->nrec + 1) * sizeof(Rec)); for (long i = 0; i < c->nrec; i++) { if (!fgets(line, 256, f)) { printf("CHUNK %d SHORT\n", k); exit(1); }
      sscanf(line, "%ld %ld %lld %lld", &c->rec[i].q3, &c->rec[i].q5, &c->rec[i].v, &c->rec[i].tgt); }
    if (!fgets(line, 256, f) || line[0] != 'E') { printf("CHUNK %d NO END\n", k); exit(1); } }
  fclose(f); c->done = 1; return 1; }
static void *worker(void *pp) {
  Job *j = pp; j->fail = 0; j->worst = 1e9; pairs = 0; j->nrec = 0; j->cap = 0; j->rec = 0;
  Node **T5 = calloc(S * NB5, sizeof(Node*));  // this thread's base-5 trees (lazily refined)
  for (long q5 = 0; q5 < S * NB5; q5++) if (PHI[q5] > 0) T5[q5] = mk(1, q5 / NB5, box5(q5 % NB5), 0);
  // classes: a root needing no refinement is determined by its vector; identical vectors share one evaluation
  long *rep = malloc(S * NB5 * sizeof(long)); ll *cmax = calloc(S * NB5, sizeof(ll)); long nclean = 0;
  for (long q5 = 0; q5 < S * NB5; q5++) { rep[q5] = q5; Node *n = T5[q5]; if (!n || n->nd.nx || n->nd.nr) continue;
    long s0 = q5 / NB5 * NB5;
    for (long r = s0; r < q5; r++) { Node *m = T5[rep[r]]; if (rep[r] != r || !m || m->nd.nx || m->nd.nr) continue;
      int eq = 1; for (int p = 0; p < NP && eq; p++) { Lf *x = &n->v[p], *y = &m->v[p];
        if (x->w != y->w || (x->w && (x->ia != y->ia || x->ib != y->ib || x->ja != y->ja || x->jb != y->jb))) eq = 0; }
      if (eq) { rep[q5] = r; nclean++; break; } } }
  for (long q5 = 0; q5 < S * NB5; q5++) if (PHI[q5] > cmax[rep[q5]]) cmax[rep[q5]] = PHI[q5];
  if (j->lo == 0) { printf("  classes: %ld base-5 bins share a representative\n", nclean); fflush(0); }
  Z *vcache = malloc(NB5 * sizeof(Z)); char *vok = malloc(NB5);
  long nq = 0;
  for (;;) { long k = __sync_fetch_and_add(&NEXTC, 1); if (k >= NCRUN) break; if (CH[k].done) continue;
   Chunk *C = &CH[k]; j->fail = 0; j->worst = 1e9; pairs = 0; j->nrec = 0; j->cap = 0; j->rec = 0;
   for (long q3 = k; q3 < S * NB3; q3 += NC) {
    ll w3 = W3[q3]; if (w3 <= 0) continue;
    int s = q3 / NB3, r3 = q3 % NB3; Node *a = 0;
    for (long r5 = 0; r5 < NB5; r5++) vok[r5] = 0;
    for (long r5 = 0; r5 < NB5; r5++) { long q5 = s * NB5 + r5; ll ph = PHI[q5]; if (ph <= 0) continue;
      Z target = (Z)w3 * ph; ll e = exLookup(q5, r3); if (e >= 0 && e < target) target = e;
      if (target <= 0) continue;
      if (!a) a = mk(0, s, box3(r3), 0);
      Z v; long rq = rep[q5];
      if (rq != q5 || cmax[q5] > PHI[q5]) { long rr = rq % NB5;   // shared class: evaluate once at the class's largest target
        if (!vok[rr]) { vcache[rr] = pairv(s, a, T5[rq], (Z)w3 * cmax[rq], 0); vok[rr] = 1; }
        v = vcache[rr];
        if ((Z)DEN * v < (Z)NUM * target) v = pairv(s, a, T5[rq], target, 0); }
      else v = pairv(s, a, T5[q5], target, 0);
      if (nnodes > INCAP) { prune(T5[rq], 0); if (nnodes > INCAP) prune(a, 0); }   // in-item budget (memo only)
      double r = (double)v * DEN / NUM / (double)target; if (r < j->worst) j->worst = r;
      if ((Z)DEN * v < (Z)NUM * target) { j->fail++;
        if (CHECK) { if (j->fail < 5) printf("FAIL pair q3 %ld q5 %ld ratio %.6f\n", q3, q5, r); }
        else { if (j->nrec == j->cap) { j->cap = j->cap ? 2 * j->cap : 4096; void *realloc(void*, size_t); j->rec = realloc(j->rec, j->cap * sizeof(Rec)); }
          Rec R = { q3, q5, (ll)(v * DEN / NUM), (ll)target }; j->rec[j->nrec++] = R; } } }
    freeTree(a);
    if (++nq % 4 == 0) for (long q5 = 0; q5 < S * NB5; q5++) prune(T5[q5], 8);
    // over budget: drop deep memoized refinements first (PKEEP levels kept), roots only if still over (results unchanged)
    if (nnodes > NODECAP) for (long q5 = 0; q5 < S * NB5; q5++) prune(T5[q5], PKEEP);
    if (nnodes > NODECAP * 3 / 4) for (long q5 = 0; q5 < S * NB5; q5++) prune(T5[q5], 0);
   }
   C->fail = j->fail; C->pairs = pairs; C->worst = j->worst; C->rec = j->rec; C->nrec = j->nrec; if (PASSDIR[0]) chunkSave((int)k);
   long nd = __sync_add_and_fetch(&NDONE, 1);
   printf("  chunk %ld done (%ld/%d): elapsed %.0fs, VmHWM %ld MB, VmRSS %ld MB, thread nodes %ld\n", k, nd, NCRUN, now() - T0, vmkb("VmHWM:") / 1024, vmkb("VmRSS:") / 1024, nnodes); fflush(0);
  }
  for (long q5 = 0; q5 < S * NB5; q5++) freeTree(T5[q5]); free(T5); free(rep); free(cmax); free(vcache); free(vok);
  return 0;
}
static int cmpd(const void *x, const void *y) { double a = *(const double*)x, b = *(const double*)y; return a < b ? -1 : a > b; }
void qsort(void*, size_t, size_t, int(*)(const void*, const void*));
static int cmpex(const void *x, const void *y) { return ((const Ex*)x)->r3 - ((const Ex*)y)->r3; }
static void exSet(long q5, int r3, ll e) {   // insert or lower
  for (int t = 0; t < EXN[q5]; t++) if (EX[q5][t].r3 == r3) { if (e < EX[q5][t].e) EX[q5][t].e = e; return; }
  void *realloc(void*, size_t); EX[q5] = realloc(EX[q5], (EXN[q5] + 1) * sizeof(Ex)); Ex x = { r3, e }; EX[q5][EXN[q5]++] = x; }
static Z todyad(double v, int bits) { return (Z)(long long)round(v * pow(2, bits)) << (F - bits); }
static void pz(const char *tag, Z v) { char t[64]; int n = 0; if (v == 0) t[n++] = '0'; while (v > 0) { t[n++] = (char)('0' + (int)(v % 10)); v /= 10; }
  printf("%s ", tag); for (int k = n - 1; k >= 0; k--) printf("%c", t[k]); printf("\n"); }
// checkpoint: after every pass write <CKPT>/phi.<it>.txt, ex.<it>.txt (atomic .tmp + rename), append stats.txt,
// then atomically rewrite <CKPT>/latest = "<it>".  RESUME=<dir> loads the latest PHI + exceptions, continues at it+1.
static char *CKPT;
static unsigned long long phisum(void) { unsigned long long h = 1469598103934665603ULL; for (long q = 0; q < S * NB5; q++) { h ^= (unsigned long long)PHI[q]; h *= 1099511628211ULL; } return h; }
static void ckpt(int it, const char *stats) {
  char a[1024], b[1024]; FILE *o;
  snprintf(a, 1024, "%s/phi.%d.txt.tmp", CKPT, it); o = fopen(a, "w"); for (long q = 0; q < S * NB5; q++) fprintf(o, "%lld\n", PHI[q]); fclose(o);
  snprintf(b, 1024, "%s/phi.%d.txt", CKPT, it); rename(a, b);
  snprintf(a, 1024, "%s/ex.%d.txt.tmp", CKPT, it); o = fopen(a, "w"); for (long q = 0; q < S * NB5; q++) for (int t = 0; t < EXN[q]; t++) fprintf(o, "%ld %d %lld\n", q, EX[q][t].r3, EX[q][t].e); fclose(o);
  snprintf(b, 1024, "%s/ex.%d.txt", CKPT, it); rename(a, b);
  snprintf(a, 1024, "%s/stats.txt", CKPT); o = fopen(a, "a"); fprintf(o, "%s", stats); fclose(o);
  snprintf(a, 1024, "%s/latest.tmp", CKPT); o = fopen(a, "w"); fprintf(o, "%d\n", it); fclose(o);
  snprintf(b, 1024, "%s/latest", CKPT); rename(a, b);
}
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
  if (M5 > 0) { double U = log2(10); for (int j = 0; j <= M5; j++) redge[1][j] = todyad(d5 * pow(2, 1 + (U - 1) * j / M5), 40);
    redge[1][0] = 2 * dlo[1]; redge[1][M5] = 10 * dhi[1]; }
  else { // aligned: edges at the resolution thresholds 2 delta5 * 2^m / 5^j in (2 delta5, 10 delta5), m <= 6,
         // each as a sliver [floor(2 dlo c), ceil(2 dhi c)] (rounded outward to 2^-70) so no other bin is ambiguous
    static const int TM[6] = {5, 3, 1, 6, 4, 2}, TJ[6] = {2, 1, 0, 2, 1, 0};   // 1.28 1.6 2 2.56 3.2 4
    const Z G = ((Z)1 << 20) - 1; int c = 0; redge[1][c++] = 2 * dlo[1];
    for (int t = 0; t < 6; t++) { Z p5 = 1; for (int u = 0; u < TJ[t]; u++) p5 *= 5;
      Z lo = ((2 * dlo[1]) << TM[t]) / p5, hi = (((2 * dhi[1]) << TM[t]) + p5 - 1) / p5;
      redge[1][c++] = lo & ~G; redge[1][c++] = (hi + G) & ~G; }
    redge[1][c] = 10 * dhi[1]; M5 = c; }
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
      int nz = 0, tot = 0; for (int p = 0; p < NP; p++) { if (n->v[p].w) nz++; }
      ll a3[NP]; Need nd = {0,0}; Bx b3 = box3(0); (void)b3; (void)a3; (void)nd; (void)tot;
      Bx wb; int w = worstNZ(q5 / NB5, n, atoi(getenv("DEP")), &wb);
      printf("worst leaf-box nonzero %d at x [%.9f,%.9f] r/d [%.6f,%.6f]  ", w, (double)wb.xlo / (double)ONE, (double)wb.xhi / (double)ONE, (double)wb.rlo / (double)dlo[1], (double)wb.rhi / (double)dlo[1]);
      printf("q5 %ld s %ld i5 %ld j5 %ld nonzero %d nx %d nr %d\n", q5, q5 / NB5, (q5 % NB5) / M5, q5 % M5, nz, n->nd.nx, n->nd.nr); freeTree(n); }
    return 0; }
  for (int q = 0; q < S; q++) for (int p = 0; p < NP; p++) { int st = q; for (int d = D - 1; d >= 0 && st >= 0; d--) st = T[st][(p >> d) & 1]; LS[q][p] = st; }
  EX = calloc(S * NB5, sizeof(Ex*)); EXN = calloc(S * NB5, sizeof(int));
  int KQ = getenv("KQ") ? atoi(getenv("KQ")) : 30;
  if (CHECK && argc > 11) { FILE *f = fopen(argv[11], "r"); char line[128]; while (fgets(line, 128, f)) { char *p; long q5 = strtoll(line, &p, 10); long r3 = strtoll(p, &p, 10); ll e = strtoll(p, 0, 10); exSet(q5, (int)r3, e); }
    for (long q = 0; q < S * NB5; q++) if (EXN[q]) qsort(EX[q], EXN[q], sizeof(Ex), cmpex); }
  CKPT = getenv("CKPT"); int it0 = 0;
  if (getenv("NC")) NC = atoi(getenv("NC"));
  NCRUN = getenv("SLICE") ? atoi(getenv("SLICE")) : NC; NODECAP = getenv("NODECAP") ? atol(getenv("NODECAP")) : 200000; PKEEP = getenv("PKEEP") ? atoi(getenv("PKEEP")) : 4; INCAP = getenv("INCAP") ? atol(getenv("INCAP")) : 2 * NODECAP;
  if (getenv("RESUME") && !CHECK) { char *R = getenv("RESUME"), nm[1024], line[128]; FILE *f; int last = -1;
    snprintf(nm, 1024, "%s/latest", R); f = fopen(nm, "r"); if (!f || !fgets(line, 128, f)) { printf("RESUME: no completed pass, resuming pass 0 chunks\n"); if (!CKPT) CKPT = R; goto noresume; } fclose(f); last = atoi(line);
    snprintf(nm, 1024, "%s/phi.%d.txt", R, last); f = fopen(nm, "r"); long q = 0; while (q < S * NB5 && fgets(line, 64, f)) PHI[q++] = strtoll(line, 0, 10); fclose(f);
    if (q != S * NB5) { printf("RESUME: SHORT PHI\n"); return 1; }
    snprintf(nm, 1024, "%s/ex.%d.txt", R, last); f = fopen(nm, "r"); long ne = 0;
    while (fgets(line, 128, f)) { char *p; long q5 = strtoll(line, &p, 10); long r3 = strtoll(p, &p, 10); ll e = strtoll(p, 0, 10); exSet(q5, (int)r3, e); ne++; } fclose(f);
    for (long q = 0; q < S * NB5; q++) if (EXN[q]) qsort(EX[q], EXN[q], sizeof(Ex), cmpex);
    it0 = last + 1; if (!CKPT) CKPT = R;
    printf("RESUMED from %s pass %d: exceptions %ld, phi checksum %016llx\n", R, last, ne, phisum()); fflush(0); }
  noresume:
  for (int it = it0; it < it0 + IT; it++) {
    pthread_t th[64]; Job jb[64]; NEXTC = 0; NDONE = 0; T0 = now();
    CH = calloc(NC, sizeof(Chunk)); PASSDIR[0] = 0;
    if (CKPT) { snprintf(PASSDIR, 1024, "%s/pass%d", CKPT, it); mkdir(PASSDIR, 0755); long nl = 0;
      for (int k = 0; k < NCRUN; k++) nl += chunkLoad(k, 0);
      printf("pass %d: %ld/%d chunks already done in %s\n", it, nl, NCRUN, PASSDIR); fflush(0); }
    for (int t = 0; t < NT; t++) { jb[t].lo = t; pthread_create(&th[t], 0, worker, &jb[t]); }
    for (int t = 0; t < NT; t++) pthread_join(th[t], 0);
    if (NCRUN < NC) { long f = 0, pr = 0, nr = 0; double w = 1e9; for (int k = 0; k < NCRUN; k++) { f += CH[k].fail; pr += CH[k].pairs; nr += CH[k].nrec; if (CH[k].worst < w) w = CH[k].worst; }
      printf("SLICE %d/%d chunks: failing pairs %ld, records %ld, worst %.5f, pair evals %ld, elapsed %.0fs, VmHWM %ld MB\n", NCRUN, NC, f, nr, w, pr, now() - T0, vmkb("VmHWM:") / 1024); return 0; }
    long fail = 0, pr = 0; double worst = 1e9;
    for (int k = 0; k < NC; k++) { if (PASSDIR[0]) chunkLoad(k, 1); fail += CH[k].fail; pr += CH[k].pairs; if (CH[k].worst < worst) worst = CH[k].worst; }
    long lowphi = 0, newex = 0;
    if (!CHECK) {
      // bucket failing records by q5
      long *cnt = calloc(S * NB5 + 1, sizeof(long)); long tot = 0;
      for (int t = 0; t < NC; t++) for (long i = 0; i < CH[t].nrec; i++) cnt[CH[t].rec[i].q5 + 1]++;
      for (long q = 0; q < S * NB5; q++) cnt[q + 1] += cnt[q]; tot = cnt[S * NB5];
      Rec *all = malloc((tot + 1) * sizeof(Rec)); long *pos = malloc(S * NB5 * sizeof(long)); for (long q = 0; q < S * NB5; q++) pos[q] = cnt[q];
      for (int t = 0; t < NC; t++) { for (long i = 0; i < CH[t].nrec; i++) all[pos[CH[t].rec[i].q5]++] = CH[t].rec[i]; free(CH[t].rec); }
      double *rat = malloc((tot + 1) * sizeof(double));
      for (long q = 0; q < S * NB5; q++) {
        long a0 = cnt[q], a1 = cnt[q + 1]; if (a0 == a1) continue;
        long nne = 0; for (long i = a0; i < a1; i++) { Rec *R = &all[i]; if (exLookup(q, R->q3 % NB3) < 0) rat[nne++] = (double)R->v / (double)R->tgt; }
        double f = 1.0;
        if (nne > KQ) { qsort(rat, nne, sizeof(double), cmpd); f = rat[KQ] * 0.99; if (f < 0) f = 0;
          ll np = (ll)((double)PHI[q] * f); if (np < PHI[q]) { PHI[q] = np; lowphi++; } }
        for (long i = a0; i < a1; i++) { Rec *R = &all[i]; int r3 = R->q3 % NB3;
          int isex = exLookup(q, r3) >= 0;
          if (isex || (double)R->v / (double)R->tgt < f / 0.99 * 1.0000001 || nne <= KQ) {
            if (!isex && nne > KQ && (double)R->v / (double)R->tgt >= f / 0.99) continue;
            exSet(q, r3, (ll)((Z)R->v * 99 / 100)); newex++; } }
      }
      free(all); free(pos); free(rat); free(cnt);
      // drop exceptions that no longer bind, sort
      long nex = 0;
      for (long q = 0; q < S * NB5; q++) { int k = 0; for (int t = 0; t < EXN[q]; t++) { Ex x = EX[q][t]; long q3 = (q / NB5) * NB3 + x.r3;
          if ((Z)x.e < (Z)W3[q3] * PHI[q]) EX[q][k++] = x; } EXN[q] = k; nex += k; if (k) qsort(EX[q], k, sizeof(Ex), cmpex); }
      ll mx = 0; long z = 0; for (long q = 0; q < S * NB5; q++) { if (PHI[q] > mx) mx = PHI[q]; if (!PHI[q]) z++; }
      char st[512]; snprintf(st, 512, "iter %d: failing pairs %ld, phi lowered %ld, phi zeros %ld, exceptions set %ld total %ld, worst %.5f, pair evals %ld, max phi %lld, phi checksum %016llx\n", it, fail, lowphi, z, newex, nex, worst, pr, mx, phisum());
      printf("%s", st); fflush(0); if (CKPT) ckpt(it, st);
      if (!fail) { printf("EXACT PRODUCT+EXCEPTION CERTIFICATE growth 9/5, exceptions %ld\n", nex);
        if (argc > 10) { FILE *o = fopen(argv[10], "w"); for (long q = 0; q < S * NB5; q++) fprintf(o, "%lld\n", PHI[q]); fclose(o);
          char nm[512]; int L = 0; while (argv[10][L]) { nm[L] = argv[10][L]; L++; } nm[L++] = '.'; nm[L++] = 'e'; nm[L++] = 'x'; nm[L] = 0;
          o = fopen(nm, "w"); for (long q = 0; q < S * NB5; q++) for (int t = 0; t < EXN[q]; t++) fprintf(o, "%ld %d %lld\n", q, EX[q][t].r3, EX[q][t].e); fclose(o); }
        return 0; }
      if (mx == 0) { printf("DEAD\n"); return 1; }
    } else { printf("CHECK %s: failing pairs %ld, worst %.6f, pair evals %ld\n", fail ? "FAILED" : "PASSED", fail, worst, pr); return fail ? 1 : 0; }
  }
  return 1;
}
