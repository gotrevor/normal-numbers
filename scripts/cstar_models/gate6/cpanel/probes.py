# (iii-a) point probes: random interior points of (A) the terminal failing sub-box of the tight (WORLDS) evaluation and
# (B) the whole pair box; each probe is evaluated on a 2^-82-wide box around the point (a positive-measure set, so a
# failing probe is an open set of parents, realizable by the density of real signatures).  Seed fixed.
import random, sys
rng = random.Random(7)
ONE = 2**90
E = {}
for l in open('edges.txt'):
    k, v = l.split(); E.setdefault(k, []).append(int(v))
NB3, NB5, M3, M5, N3, N5 = 128*24, 64*13, 24, 13, 128, 64
L = open(sys.argv[1]).read().split('\n'); boxes = {}
i = 0
while i < len(L):
    if L[i].startswith('WORST'):
        h = L[i].split(); boxes[(int(h[2]), int(h[3]))] = [int(h[4])] + [int(L[i+j]) for j in range(1, 8)]; i += 8
    i += 1
NP = int(sys.argv[2])
out = open(sys.argv[3], 'w')
for l in open('panel.txt'):
    if l[0] == '#': continue
    k, q3, q5 = l.split(); q3, q5 = int(q3), int(q5); r3, r5 = q3 % NB3, q5 % NB5
    i3, j3, i5, j5 = r3 // M3, r3 % M3, r5 // M5, r5 % M5
    pb = [(i3 * ONE) // N3, ((i3 + 1) * ONE) // N3, E['redge3'][j3], E['redge3'][j3+1], E['xedge5'][i5], E['xedge5'][i5+1], E['redge5'][j5], E['redge5'][j5+1]]
    for tag, b in (('B', pb), ('A', boxes.get((q3, q5)))):
        if not b: continue
        for t in range(NP):
            pt = [rng.randrange(b[2*u] + 1, b[2*u+1]) if b[2*u+1] - b[2*u] > 2 else b[2*u] for u in range(4)]
            out.write(f"{q3} {q5} {pt[0]} {pt[1]} {pt[2]} {pt[3]} {k}{tag}\n")
