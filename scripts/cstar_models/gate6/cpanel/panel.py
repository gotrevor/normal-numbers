# Step (2): fix the causal panel BEFORE any evaluation.  40 newly failing positive-target pairs (pass at pass 0 on
# the cost lap's frozen pass-0 weights, fail on the frozen post-update snapshot U), stratified by parent state
# (2 per state present + the remaining 8 by largest share), and 40 matched controls: same parent bin q3 (so same
# state and base-3 side; if that q3 has none, same state), passing both times with positive target, drawn uniformly.  Seed 20261012.
import random
exec(open('cpanel/frac.py').read().split('from collections')[0])
SEED = 20261012; rng = random.Random(SEED)
fails = set(after) | set(before)
bys = {}
for k in sorted(newf): bys.setdefault(k[0]//NB3, []).append(k)
alloc = {s: 2 for s in bys}; rest = 40 - sum(alloc.values())
tot = sum(len(v) for v in bys.values())
share = sorted(bys, key=lambda s: -(len(bys[s]) / tot * 40 - alloc[s]))
for s in share[:rest]: alloc[s] += 1
out = []
for s in sorted(bys):
    pick = rng.sample(bys[s], alloc[s])
    for (q3, q5) in sorted(pick):
        ctl = [(q3, s*NB5 + r5) for r5 in range(NB5) if (q3, s*NB5 + r5) not in fails and PHI1[s*NB5 + r5] > 0]
        if not ctl:   # fallback: same state, any slice parent
            ctl = [(p3, s*NB5 + r5) for p3 in par if p3 // NB3 == s for r5 in range(NB5) if (p3, s*NB5 + r5) not in fails and PHI1[s*NB5 + r5] > 0]
        c = rng.choice(ctl)
        out.append(('F', q3, q5)); out.append(('C', c[0], c[1]))
with open('cpanel/panel.txt', 'w') as o:
    o.write(f"# causal panel, seed {SEED}; kind q3 q5 (F = newly failing, C = matched control: same q3, passes both)\n")
    for i, (k, q3, q5) in enumerate(out): o.write(f"{k} {q3} {q5}\n")
print(len(out), alloc)
