"""Census for the PROVED theorem `mahler_lower_bound_runjump`:
for each prime p, the best admissible b (3 <= b < p/2, -1 in <p> mod b) and the
constant b(p-b-1)/p^2.  Focus: p ≡ 1 (mod 12), where the b | p+1 corollaries are silent."""
import sys
def primerange(a, b):
    for n in range(max(a, 2), b):
        if all(n % d for d in range(2, int(n ** 0.5) + 1)):
            yield n

def admissible(p, b):
    x = p % b
    seen = set()
    while x not in seen:
        if x == (b - 1) % b:
            return True
        seen.add(x)
        x = x * p % b
    return False

def best(p):
    cands = [b for b in range(3, (p + 1) // 2) if 2 * b < p and admissible(p, b)]
    if not cands:
        return None, 0.0
    b = max(cands, key=lambda b: b * (p - b - 1))
    return b, b * (p - b - 1) / p**2

N = int(sys.argv[1]) if len(sys.argv) > 1 else 1000
worst = (1.0, None, None)
rows = []
for p in primerange(11, N):
    b, c = best(p)
    if p % 12 == 1:
        rows.append((p, b, c))
    if c < worst[0]:
        worst = (c, p, b)
print("p ≡ 1 (mod 12):")
for p, b, c in rows:
    print(f"  p={p:5d}  best b={b}  b/p={b/p:.3f}  const={c:.4f}")
print("worst over all primes <", N, ":", worst)
print("min const over p ≡ 1 mod 12:", min(rows, key=lambda r: r[2]))

# the gap j = p - 2b of the best admissible b, and the census deficit for p <= 31
census = {11:25,13:35,17:64,19:80,23:120,29:192,31:224}
gaps = []
for p in primerange(11, N):
    b, c = best(p)
    gaps.append((p - 2 * b, p, b))
    if p in census:
        print(f"  p={p}: best b={b}, bound={b*(p-b-1)}, census M={census[p]}, deficit={census[p]-b*(p-b-1)}")
gaps.sort(reverse=True)
print("largest gaps j = p - 2b:", gaps[:12])
