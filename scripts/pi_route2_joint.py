# /// script
# requires-python = ">=3.10"
# dependencies = []
# ///
"""Route 2 probe: joint statistics of (fract R_n, fract S_n), R = fresh-prime reservoir,
S = residual = 16^n * piPartial(n) - R.  Each term c*16^(n-j)/m is reduced exactly
(c*16^(n-j) mod m)/m with integer pow; only the final summation is in float (error ~1e-12).

Pre-stated targets (N = 2000): if the pair is ~independent uniform,
  every 8x8 cell is hit (expected 31/cell), |corr| < 0.05, chi2/64 ~ 1.
Control: same window, prime condition replaced by 'odd composite' (no fresh pole).
Known-answer control: the selected part must be the whole thing when the window is (0, 8n)."""
import sys, math
try:
    from sympy import isprime
except ImportError:
    def isprime(m):
        return m > 1 and all(m % d for d in range(2, math.isqrt(m) + 1))

C = {1: 4, 4: -2, 5: -1, 6: -1}

def pair(n, select, all_r=False):
    R = 0.0; T = 0.0
    for j in range(n):
        for r, c in C.items():
            m = 8 * j + r
            v = (c * pow(16, n - j, m)) % m / m
            T += v
            if (all_r or r in (1, 5)) and select(m, n):
                R += v
    R %= 1.0; T %= 1.0
    return R, (T - R) % 1.0

def stats(name, pts):
    N = len(pts); k = 8
    grid = [[0]*k for _ in range(k)]
    for x, y in pts:
        grid[min(int(x*k), k-1)][min(int(y*k), k-1)] += 1
    e = N / k**2
    chi = sum((g-e)**2/e for row in grid for g in row) / k**2
    mx = sum(x for x, _ in pts)/N; my = sum(y for _, y in pts)/N
    cov = sum((x-mx)*(y-my) for x, y in pts)/N
    sx = math.sqrt(sum((x-mx)**2 for x, _ in pts)/N); sy = math.sqrt(sum((y-my)**2 for _, y in pts)/N)
    # circular correlation via e(x - y), e(x + y)
    em = abs(sum(complex(math.cos(2*math.pi*(x-y)), math.sin(2*math.pi*(x-y))) for x, y in pts))/N
    ep = abs(sum(complex(math.cos(2*math.pi*(x+y)), math.sin(2*math.pi*(x+y))) for x, y in pts))/N
    empty = sum(1 for row in grid for g in row if g == 0)
    print(f"{name}: N={N} chi2/cell={chi:.3f} empty_cells={empty} min={min(map(min,grid))} "
          f"corr={cov/(sx*sy):+.4f} |E e(x-y)|={em:.4f} |E e(x+y)|={ep:.4f} (1/sqrtN={1/math.sqrt(N):.4f})")

N = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
fresh = lambda m, n: 4*n < m and isprime(m)
comp = lambda m, n: 4*n < m and not isprime(m)
# known-answer control: selecting everything gives residual 0
assert all(min(pair(n, lambda m, n: True, True)[1], 1 - pair(n, lambda m, n: True, True)[1]) < 1e-9 for n in range(1, 30))
for name, sel in [("fresh-prime", fresh), ("composite-control", comp)]:
    stats(name, [pair(n, sel) for n in range(1, N+1)])
