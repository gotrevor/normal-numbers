"""Dead-count distribution along resLaw paths (evidence for CantorBadNormal.AvgDeadDensity).
usage: python3 cantorbad_deadcount.py seed paths stages"""
import sys, random, importlib.util, collections
spec = importlib.util.spec_from_file_location("lb", __file__.replace("cantorbad_deadcount", "cantorbad_localbias_lib"))
lb = importlib.util.module_from_spec(spec); spec.loader.exec_module(lb)
seed, paths, stages = map(int, sys.argv[1:4])
rng = random.Random(seed)
hist = collections.Counter(); per = collections.defaultdict(list)
for _ in range(paths):
    W = 0
    for s in range(stages):
        D = lb.dead_children(W, 10 * s, 'q')
        hist[len(D)] += 1; per[s].append(len(D))
        while True:
            J = lb.KID[rng.randrange(1024)]
            if J not in D: break
        W = W * 3 ** 10 + J
n = sum(hist.values())
print("hist", sorted(hist.items()))
print("mean", sum(k * v for k, v in hist.items()) / n, "max", max(hist))
print("per-stage mean", [round(sum(v) / len(v), 2) for s, v in sorted(per.items())])
