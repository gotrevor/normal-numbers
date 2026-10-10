// Adaptive-mesh rigorous (in the abs3 model) shared-phase block value iteration.  Gate 4.
// States: cells = rectangles in (x mod 1, u) per SFT state, kept in a kd-tree per state.
// W(cell) = min over u-pieces of sum_leaf w * min{V(cell') : cell' meets the leaf box}  (interval
// propagation of the whole cell through D binary levels, base-3 touching kills pessimistic).
// Refinement: cells with W/V below target and the argmin cells of their straddling leaves are bisected.
// Compile: leanc -O2 -o /tmp/mesh3 mesh3.c     usage: /tmp/mesh3 N M D C ROUNDS IT G MAXCELLS
typedef unsigned long size_t;
int printf(const char*, ...); void *malloc(size_t); void *realloc(void*, size_t); void *calloc(size_t, size_t); void free(void*);
int atoi(const char*); double atof(const char*);
double floor(double); double ceil(double); double pow(double,double); double log2(double); double round(double); double fmax(double,double);
int fflush(void*);
#define INF __builtin_inf()
#define S 25
static const int T[S][2] = {{1,2},{3,2},{1,4},{5,2},{1,6},{7,2},{1,8},{-1,9},{10,-1},{11,4},{3,12},{-1,13},{14,-1},{-1,15},{16,-1},{17,6},{5,18},{-1,19},{20,-1},{21,4},{3,22},{-1,23},{24,-1},{-1,4},{3,-1}};
static const double R[S] = {1.0,0.9451260262333576,0.9451260262333576,0.8414003846939574,0.8414003846939574,0.6453327778806791,0.6453327778806791,0.274715581679643,0.274715581679643,0.5192816921145327,0.5192816921145327,0.1401728996339273,0.1401728996339273,0.26496211123324204,0.26496211123324204,0.5008451745845498,0.5008451745845498,0.30139084134581684,0.30139084134581684,0.5697046564486004,0.5697046564486004,0.2354850114578546,0.2354850114578546,0.44512602623335756,0.44512602623335756};
static const double LAM = 1.8902520524667157;
static int N, M, D; static double C, delta, U, L3, P[S][2]; static const double eps = 1e-12;
typedef struct { double xlo, xhi, ulo, uhi; int s; int node; } Cell;
typedef struct { double val; int dim, lo, hi, cell; double bx0, bx1, bu0, bu1; double minV; } Node;
static Cell *cells; static int ncells, capcells; static Node *nodes; static int nnodes, capnodes; static int root[S];
static double *V, *W; static char *mark;
static int newnode(double x0, double x1, double u0, double u1) {
  if (nnodes == capnodes) { capnodes = capnodes ? 2 * capnodes : 1 << 16; nodes = realloc(nodes, capnodes * sizeof(Node)); }
  Node *n = &nodes[nnodes]; n->bx0 = x0; n->bx1 = x1; n->bu0 = u0; n->bu1 = u1; n->lo = n->hi = -1; n->cell = -1; n->minV = 1; return nnodes++;
}
static int newcell(int s, double x0, double x1, double u0, double u1, int node, double v) {
  if (ncells == capcells) { capcells = capcells ? 2 * capcells : 1 << 16; cells = realloc(cells, capcells * sizeof(Cell)); V = realloc(V, capcells * sizeof(double)); W = realloc(W, capcells * sizeof(double)); mark = realloc(mark, capcells); }
  Cell *c = &cells[ncells]; c->xlo = x0; c->xhi = x1; c->ulo = u0; c->uhi = u1; c->s = s; c->node = node; nodes[node].cell = ncells; V[ncells] = v; W[ncells] = v; mark[ncells] = 0; return ncells++;
}
// split cell id along dim at val: the cell keeps the low half, a new cell gets the high half
static void splitcell(int id, int dim, double val) {
  Cell c = cells[id]; int nd = c.node;
  int a = dim == 0 ? newnode(c.xlo, val, c.ulo, c.uhi) : newnode(c.xlo, c.xhi, c.ulo, val);
  int b = dim == 0 ? newnode(val, c.xhi, c.ulo, c.uhi) : newnode(c.xlo, c.xhi, val, c.uhi);
  nodes[nd].dim = dim; nodes[nd].val = val; nodes[nd].lo = a; nodes[nd].hi = b; nodes[nd].cell = -1;
  if (dim == 0) { cells[id].xhi = val; } else { cells[id].uhi = val; }
  cells[id].node = a; nodes[a].cell = id;
  newcell(c.s, dim == 0 ? val : c.xlo, c.xhi, dim == 0 ? c.ulo : val, c.uhi, b, V[id]);
}
static double updmin(int nd) { Node *n = &nodes[nd]; if (n->cell >= 0) return n->minV = V[n->cell]; double a = updmin(n->lo), b = updmin(n->hi); return n->minV = a < b ? a : b; }
static int qcount, qarg;
static double qmin(int nd, double x0, double x1, double u0, double u1, double best) {
  Node *n = &nodes[nd];
  if (n->bx1 < x0 - eps || n->bx0 > x1 + eps || n->bu1 < u0 - eps || n->bu0 > u1 + eps) return best;
  if (n->minV >= best) { if (n->cell >= 0) qcount++; else qcount += 2; return best; }
  if (n->cell >= 0) { qcount++; qarg = n->cell; return V[n->cell]; }
  best = qmin(n->lo, x0, x1, u0, u1, best); return qmin(n->hi, x0, x1, u0, u1, best);
}
static int *ids; static long nids, capids;
static void pushid(int v) { if (nids == capids) { capids = capids ? 2 * capids : 1 << 20; ids = realloc(ids, capids * sizeof(int)); } ids[nids++] = v; }
static void qenum(int nd, double x0, double x1, double u0, double u1) {
  Node *n = &nodes[nd];
  if (n->bx1 < x0 - eps || n->bx0 > x1 + eps || n->bu1 < u0 - eps || n->bu0 > u1 + eps) return;
  if (n->cell >= 0) { pushid(n->cell); return; }
  qenum(n->lo, x0, x1, u0, u1); qenum(n->hi, x0, x1, u0, u1);
}
// cache: leaf k has weight lw[k] and ids[lo[k] .. lo[k+1]); piece p has leaves pl[p]..pl[p+1]; cell c has pieces cp[c]..cp[c+1]
static float *lw; static long *llo, nleaf, capleaf; static long *pl, npiece, cappiece; static long *cp; static int building;
static void pushleaf(double w) { if (nleaf + 1 >= capleaf) { capleaf = capleaf ? 2 * capleaf : 1 << 20; lw = realloc(lw, capleaf * sizeof(float)); llo = realloc(llo, (capleaf + 1) * sizeof(long)); } lw[nleaf] = (float)w; llo[nleaf] = nids; nleaf++; }
static void pushpiece(long start) { if (npiece + 1 >= cappiece) { cappiece = cappiece ? 2 * cappiece : 1 << 18; pl = realloc(pl, (cappiece + 1) * sizeof(long)); } pl[npiece++] = start; }
static double usplit; static int collect; static int *marklist; static int nmark, capmark;
static void addmark(int id) { if (mark[id]) return; mark[id] = 1; if (nmark == capmark) { capmark = capmark ? 2 * capmark : 1024; marklist = realloc(marklist, capmark * sizeof(int)); } marklist[nmark++] = id; }
static double leafval(int s, double xlo, double xhi, double ulo, double uhi) {
  double fl = floor(xlo); xlo -= fl; xhi -= fl; qcount = 0; qarg = -1;
  if (building) { pushleaf(0); qenum(root[s], xlo, xhi > 1 ? 1 : xhi, ulo, uhi); if (xhi > 1) qenum(root[s], 0, xhi - 1, ulo, uhi); return 1; }
  double m = qmin(root[s], xlo, xhi > 1 ? 1 : xhi, ulo, uhi, INF);
  if (xhi > 1) m = qmin(root[s], 0, xhi - 1, ulo, uhi, m);
  if (collect && qcount > 1 && qarg >= 0) addmark(qarg);
  return m;
}
// returns block sum or -1 on u-straddle
static double descend(int s, double xlo, double xhi, double ulo, double uhi, int depth, double w) {
  if (depth == D) { double v = leafval(s, xlo, xhi, ulo, uhi); if (building) lw[nleaf - 1] = (float)w; return w * v; }
  double rlo = delta * pow(2, ulo), rhi = delta * pow(2, uhi), sum = 0;
  for (int d = 0; d < 2; d++) {
    int t = T[s][d]; if (t < 0) continue;
    double cxlo = xlo + d * rlo / 2, cxhi = xhi + d * rhi / 2, culo = ulo - 1, cuhi = uhi - 1;
    if (culo < 1 - eps && cuhi > 1 + eps) { usplit = 1 - culo; return -1; }
    if (cuhi <= 1 + eps) {
      double chi = rhi / 2; int touch = 0;
      for (long k = (long)floor(cxlo) - 1; k <= (long)ceil(cxhi + chi) + 1; k++)
        if (cxlo <= k + delta + eps && cxhi + chi >= k - delta - eps) { touch = 1; break; }
      if (touch) continue;
      double fl = floor(3 * cxlo); cxlo = 3 * cxlo - fl; cxhi = 3 * cxhi - fl; culo += L3; cuhi += L3;
    }
    double v = descend(t, cxlo, cxhi, culo, cuhi, depth + 1, w * P[s][d]); if (v < 0) return -1; sum += v;
  }
  return sum;
}
static double evalbox(int s, double xlo, double xhi, double ulo, double uhi) {
  long sl = nleaf, si = nids;
  double v = descend(s, xlo, xhi, ulo, uhi, 0, 1);
  if (building) { if (v >= 0) pushpiece(sl); else { nleaf = sl; nids = si; } }
  if (v >= 0) return v;
  double um = ulo + usplit; double a = evalbox(s, xlo, xhi, ulo, um), b = evalbox(s, xlo, xhi, um, uhi); return a < b ? a : b;
}
int main(int argc, char **argv) {
  N = atoi(argv[1]); M = atoi(argv[2]); D = atoi(argv[3]); C = atof(argv[4]); int ROUNDS = atoi(argv[5]), IT = atoi(argv[6]); double G = atof(argv[7]); int MAXC = atoi(argv[8]);
  delta = pow(3, -C) * 1.0001; U = log2(6); L3 = log2(3);
  int M2 = (int)fmax(1, round(M * (U - 2) / (U - 1))), M1 = M - M2, e = 0; double edges[64];
  for (int t = 0; t <= M1; t++) edges[e++] = 1 + (double)t / M1; for (int t = 1; t <= M2; t++) edges[e++] = 2 + (U - 2) * t / M2;
  for (int s = 0; s < S; s++) for (int d = 0; d < 2; d++) P[s][d] = T[s][d] < 0 ? 0 : R[T[s][d]] / (LAM * R[s]);
  for (int s = 0; s < S; s++) { root[s] = newnode(0, 1, 1, U); int c = newcell(s, 0, 1, 1, U, root[s], 1);
    for (int j = 1; j < M; j++) { // split off u-bins: find cell containing edges[j] (the high part, last created or c)
      int id = j == 1 ? c : ncells - 1; splitcell(id, 1, edges[j]); }
  }
  // x-split every cell N-ways (N power of 2)
  for (int lev = 1; lev < N; lev *= 2) { int nc = ncells; for (int id = 0; id < nc; id++) splitcell(id, 0, (cells[id].xlo + cells[id].xhi) / 2); }
  double target = pow(G / LAM, D);
  for (int rd = 0; rd < ROUNDS; rd++) {
    double lo = 0; int worst = -1;
    building = 1; nleaf = nids = npiece = 0; cp = realloc(cp, (ncells + 1) * sizeof(long));
    for (int id = 0; id < ncells; id++) { Cell *c = &cells[id]; cp[id] = npiece; evalbox(c->s, c->xlo, c->xhi, c->ulo, c->uhi); }
    cp[ncells] = npiece; pushpiece(nleaf); npiece--; pushleaf(0); nleaf--; llo[nleaf] = nids; building = 0;
    printf("  cache: %ld pieces %ld leaves %ld ids\n", npiece, nleaf, nids); fflush(0);
    for (int it = 0; it < IT; it++) {
      lo = INF;
      for (int id = 0; id < ncells; id++) {
        double best = INF;
        for (long p = cp[id]; p < cp[id + 1]; p++) { double sm = 0;
          for (long k = pl[p]; k < pl[p + 1]; k++) { double m = INF; for (long q = llo[k]; q < llo[k + 1]; q++) if (V[ids[q]] < m) m = V[ids[q]]; sm += lw[k] * m; }
          if (sm < best) best = sm; }
        W[id] = best; if (V[id] > 1e-12 && W[id] / V[id] < lo) { lo = W[id] / V[id]; worst = id; } }
      double mx = 0; for (int id = 0; id < ncells; id++) if (W[id] > mx) mx = W[id];
      if (mx == 0) { printf("DEAD\n"); return 0; }
      for (int id = 0; id < ncells; id++) V[id] = W[id] / mx;
    }
    int z = 0; double zarea = 0; for (int id = 0; id < ncells; id++) if (V[id] < 1e-9) { z++; zarea += (cells[id].xhi - cells[id].xlo) * (cells[id].uhi - cells[id].ulo); }
    printf("round %d cells %d ratio %.6f growth %.6f zeros %d (area %.4f of %.1f) worst cell s=%d x[%.6g,%.6g] u[%.4f,%.4f]\n", rd, ncells, lo, LAM * pow(fmax(lo, 0), 1.0 / D), z, zarea, S * (U - 1),
      cells[worst].s, cells[worst].xlo, cells[worst].xhi, cells[worst].ulo, cells[worst].uhi); fflush(0);
    if (rd == ROUNDS - 1 || ncells >= MAXC) break;
    // mark bottleneck cells and argmin targets of their straddling leaves
    updmin(0); for (int s = 0; s < S; s++) updmin(root[s]);
    nmark = 0; double thr = lo < target ? fmax(lo * 1.02, target) : lo * 1.02;
    for (int id = 0; id < ncells; id++) {
      if (!(V[id] > 1e-12)) continue;
      Cell *c = &cells[id]; collect = 0; double w = evalbox(c->s, c->xlo, c->xhi, c->ulo, c->uhi);
      if (w / V[id] < thr) { addmark(id); collect = 1; evalbox(c->s, c->xlo, c->xhi, c->ulo, c->uhi); collect = 0; }
    }
    int nm = nmark;
    for (int k = 0; k < nm; k++) { int id = marklist[k]; Cell *c = &cells[id]; mark[id] = 0;
      double wx = (c->xhi - c->xlo) * N, wu = (c->uhi - c->ulo) * M / (U - 1) * 0.5;
      if (wx >= wu) splitcell(id, 0, (c->xlo + c->xhi) / 2); else splitcell(id, 1, (c->ulo + c->uhi) / 2); }
    printf("  split %d cells\n", nm);
  }
  return 0;
}
