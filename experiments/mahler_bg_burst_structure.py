"""Structure hunt: with a=2 and target digit w=g-1, which B are near-optimal?
Background digit b=(2m mod g-1) is even and < g-1, so w=g-1 never comes from
the background; the whole constraint is that adding N=m*B into the b^infty
background creates no digit g-1."""
def f(a, B, g, w, cap):
    for m in range(1, cap + 1):
        b = (m * a) % (g - 1)
        N = m * B
        L = 0; t = N
        while t: t //= g; L += 1
        d = L + 3
        R = (b * (g ** d - 1) // (g - 1) + N) % (g ** d)
        for _ in range(d):
            if R % g == w: return m
            R //= g
    return cap + 1

for g in [5,7,11,13,17,19,23,29,31]:
    cap = 5*g*g
    Bmax = 40*g*g
    res = []
    for B in range(1, Bmax):
        v = f(2, B, g, g-1, cap)
        res.append((v, B))
    res.sort(reverse=True)
    top = res[:8]
    print(f"g={g:3d} ((g-1)/2)^2={((g-1)//2)**2:5d}  top: " +
          "  ".join(f"{v}@B={B}" for v, B in top), flush=True)
