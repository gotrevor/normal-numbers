#!/usr/bin/env -S uv run --quiet --with numpy --with scipy python3
# Liouville cover for binary runs: for every odd B, some m in S has 1^k in binary(m*B)
# (x = B * sum 2^-(i!): m x shows m*B between zero gaps, so 0^k is free and 1^k needs m*B).
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
def cover(k, mmax, bmax):
    ms = list(range(1, mmax + 1, 2)); Bs = list(range(1, bmax + 1, 2))
    one = '1' * k
    A = np.array([[1 if one in bin(m * B) else 0 for m in ms] for B in Bs])
    keep = A.sum(1) > 0
    if not keep.all():
        return None, [B for B, kk in zip(Bs, keep) if not kk][:3]
    res = milp(c=np.ones(len(ms)), constraints=LinearConstraint(A, lb=1),
               integrality=np.ones(len(ms)), bounds=Bounds(0, 1), options={"time_limit": 120})
    lb = getattr(res, "mip_dual_bound", None)
    return (round(res.fun), lb, res.status), [m for m, v in zip(ms, res.x) if v > 0.5]
for k, mmax, bmax in ((2, 64, 1000), (3, 64, 1000), (3, 128, 1000), (3, 256, 2000), (4, 256, 2000)):
    print(k, mmax, bmax, cover(k, mmax, bmax))
