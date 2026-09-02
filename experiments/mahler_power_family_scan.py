"""For each base g and each L, the largest t with t | g^L such that every guard
block s*c (s < t, c = g^L/t) is free of the base-g digit g-1.
Gives M(g,k) >= t(g^k - 1) via `mahler_lower_bound_power`."""
def guards_ok(g, t, c):
    for s in range(t):
        v = s * c
        while v:
            if v % g == g - 1: return False
            v //= g
    return True

EXACT = {4:6, 6:20, 8:28, 9:24, 10:72, 14:104, 15:126, 16:120, 18:272, 20:304,
         21:224, 22:336, 24:414, 25:189, 26:400, 27:375, 28:500, 12:None}

for g in range(4, 29):
    best = (0, 0, 0)
    for L in range(1, 6):
        gL = g ** L
        if gL > 3 * 10 ** 7: break
        t = 1
        while t * t <= gL:
            for tt in ({t, gL // t} if gL % t == 0 else set()):
                c = gL // tt
                if c >= 2 and tt > best[0] and guards_ok(g, tt, c):
                    best = (tt, c, L)
            t += 1
    t, c, L = best
    ex = EXACT.get(g)
    tag = ""
    if ex:
        if t * (g - 1) == ex: tag = "  EXACT"
        else: tag = f"  (exact {ex} = {ex/(g-1):.2f}*(g-1))"
    print(f"g={g:3d}  best t={t:6d} c={c:8d} L={L}  =>  M(g,k) >= {t}(g^k-1),"
          f"  k=1: {t*(g-1):6d}  /g^2 = {t*(g-1)/g**2:.3f}{tag}", flush=True)
