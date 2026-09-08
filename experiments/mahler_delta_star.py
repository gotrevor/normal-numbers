#!/usr/bin/env python3
"""M(g,1) >= (g-1)*g/delta*(g), where
     delta*(g) = min{ prod_{p|g} p^{u_p} : u_p <= v_p(g), product > 1 }.
Checked against the exact census."""
from fractions import Fraction
from itertools import product as iproduct

EXACT = {2:1,3:2,4:6,5:6,6:20,7:9,8:28,9:24,10:72,11:25,12:99,13:35,14:104,
         15:126,16:120,17:64,18:272,19:80,20:304,21:224,22:336,23:120,24:414,
         25:189,26:400,27:375,28:500,29:192,31:224,32:588}

def fac(n):
    f={}; d=2
    while d*d<=n:
        while n%d==0: f[d]=f.get(d,0)+1; n//=d
        d+=1
    if n>1: f[n]=f.get(n,0)+1
    return f

def delta_star(g, lo=-40):
    """min product > 1 with u_p <= v_p(g).  Brute force over a window."""
    f=fac(g); ps=sorted(f); best=None; bestu=None
    rng=[range(max(lo,-60), f[p]+1) for p in ps]
    for us in iproduct(*rng):
        v=Fraction(1)
        for p,u in zip(ps,us): v*=Fraction(p)**u
        if v>1 and (best is None or v<best): best=v; bestu=us
    return best, dict(zip(ps,bestu))

print(f"{'g':>4} {'exact':>6} {'(g-1)g/delta*':>14} {'delta*':>10} {'ratio':>7}  match")
for g in sorted(EXACT):
    d,u = delta_star(g, lo=-12)
    lb = int((g-1)*g/d)          # floor; the true bound is ceil of an exact hit
    ok = "EXACT" if lb==EXACT[g] else ("ok(<)" if lb<=EXACT[g] else "*** OVERSHOOT ***")
    print(f"{g:>4} {EXACT[g]:>6} {lb:>14} {str(d):>10} {lb/(g*g):>7.4f}  {ok}")
