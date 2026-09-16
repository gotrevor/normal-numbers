/* Ambient-scale pruning + dead-edge verification for single-track base-g
   adder families (see experiments/adder_baseg_emit.py for the reference
   implementation; this one exists because the (6,1) hitting-set family has
   9067520 ambient states, out of reach of the pure-Python emitter).

   usage: adder_prune <g> <ell> <word digits LSD-first, comma> <multipliers, comma>
   prints:  S <ambient>
            LIVE <s> ...           (one line, all live states)
            EDGE <s> <sp> <sig>    (live -> live edges)
            OMEGA <s> <w>          (nonzero omega, dead states)
            DEADOK <failures>      (dead-state edge condition, C3')
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main(int argc, char **argv) {
  long g = atol(argv[1]), ell = atol(argv[2]);
  long word[8], nw = 0, ms[16], nm = 0;
  char *p = strtok(argv[3], ","); while (p) { word[nw++] = atol(p); p = strtok(NULL, ","); }
  p = strtok(argv[4], ","); while (p) { ms[nm++] = atol(p); p = strtok(NULL, ","); }
  long wsz = 1; for (long i = 1; i < ell; i++) wsz *= g;
  long wordval = 0; for (long i = nw - 1; i >= 0; i--) wordval = word[i] + g * wordval;
  long sizes[16], strides[16], S = 1;
  for (long i = 0; i < nm; i++) { sizes[i] = ms[i] * wsz; strides[i] = S; S *= sizes[i]; }
  fprintf(stderr, "ambient %ld\n", S);
  printf("S %ld\n", S);
  int *pred = malloc((size_t)S * g * sizeof(int));
  if (!pred) { fprintf(stderr, "oom\n"); return 1; }
  for (long x = 0; x < g; x++) {
    int *P = pred + x * S;
    for (long sp = 0; sp < S; sp++) {
      long s = 0; int bad = 0;
      for (long i = 0; i < nm; i++) {
        long code = (sp / strides[i]) % sizes[i];
        long cprime = code / wsz, wprime = code % wsz;
        long v = ms[i] * x + cprime;
        long z = v % g, c = v / g;
        long full = z + g * wprime;
        if (full == wordval) { bad = 1; break; }
        s += (c * wsz + full % wsz) * strides[i];
      }
      P[sp] = bad ? -1 : (int)s;
    }
  }
  char *alive = malloc(S); memset(alive, 1, S);
  int *omega = calloc(S, sizeof(int));
  int *outdeg = malloc(S * sizeof(int));
  long rnd = 0;
  for (;;) {
    memset(outdeg, 0, (size_t)S * sizeof(int));
    for (long x = 0; x < g; x++) {
      int *P = pred + x * S;
      for (long sp = 0; sp < S; sp++) {
        int s = P[sp];
        if (s >= 0 && alive[s] && alive[sp]) outdeg[s]++;
      }
    }
    long ndie = 0;
    for (long s = 0; s < S; s++) if (alive[s] && outdeg[s] == 0) { omega[s] = (int)rnd; alive[s] = 0; ndie++; }
    if (!ndie) break;
    rnd++;
    fprintf(stderr, "round %ld: killed %ld\n", rnd, ndie);
  }
  long nlive = 0; for (long s = 0; s < S; s++) if (alive[s]) nlive++;
  fprintf(stderr, "live %ld rounds %ld\n", nlive, rnd);
  printf("LIVE");
  for (long s = 0; s < S; s++) if (alive[s]) printf(" %ld", s);
  printf("\n");
  for (long x = 0; x < g; x++) {
    int *P = pred + x * S;
    for (long sp = 0; sp < S; sp++) {
      if (!alive[sp]) continue;
      int s = P[sp];
      if (s >= 0 && alive[s]) printf("EDGE %d %ld %ld\n", s, sp, x);
    }
  }
  for (long s = 0; s < S; s++) if (!alive[s] && omega[s]) printf("OMEGA %ld %d\n", s, omega[s]);
  long fail = 0;
  for (long x = 0; x < g; x++) {
    int *P = pred + x * S;
    for (long sp = 0; sp < S; sp++) {
      int s = P[sp];
      if (s < 0 || alive[s]) continue;
      if (alive[sp] || omega[sp] >= omega[s]) fail++;
    }
  }
  printf("DEADOK %ld\n", fail);
  return 0;
}
