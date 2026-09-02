"""Emit / verify the Lean certificate data for `mahler_lower_bound_bg_digit`."""
def repunit(g, d): return (g**d - 1)//(g - 1)
def bgResidue(g, a, B, m, d): return ((m*a % (g-1)) * repunit(g, d) + m*B) % g**d

def check(g, a, B, W, M):
    # smallest D with  b*S_D + m*B < g^D  for all m <= M
    D = 1
    while any((m*a % (g-1))*repunit(g, D) + m*B >= g**D for m in range(M+1)):
        D += 1
    ok_dig = all(bgResidue(g,a,B,m,d)//g**(d-1) != W
                 for m in range(M+1) for d in range(1, D+1))
    ok_back = all((m*a % (g-1)) != W for m in range(M+1))
    # K with M*B <= g^K
    K = 0
    while M*B > g**K: K += 1
    return D, K, ok_dig, ok_back

def firstfail(g, a, B, W):
    m = 0
    while True:
        m += 1
        D = 1
        while (m*a % (g-1))*repunit(g,D) + m*B >= g**D: D += 1
        if (m*a % (g-1)) == W: return m
        if any(bgResidue(g,a,B,m,d)//g**(d-1) == W for d in range(1, D+1)): return m

for (g,a,B,W) in [(5,2,1,1),(7,2,1,1),(11,2,73,10),(13,2,958,12),(23,2,2549,22),(23,2,2641,22)]:
    ff = firstfail(g,a,B,W)
    M = ff - 1
    D,K,od,ob = check(g,a,B,W,M)
    print(f"g={g:3d} a={a} B={B:5d} W={W:2d}  M={M:4d} (bound M(g,1) >= {M+1})  D={D} K={K}  dig={od} back={ob}  g^D={g**D}")
