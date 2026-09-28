"""C4 probe: the AP-defect family P_m and its symmetrized correlations.

P_m: digits are i.i.d. uniform EXCEPT on one arithmetic progression of common difference m
(random offset theta, uniform in [0,m)), where the digits follow the alternating pattern
0,1,0,1,... with a random global phase.

Correlations.  c(T) = 0 unless every element of T lies in the AP, i.e. all elements of T are
congruent mod m; the random phase kills odd |T|.  For even j,
    c(T) = (1/m) * (-1)^(sum of the AP-indices of T).
Hence the symmetrized sums are

    F_j^{(m)}(L) = (1/m) * sum_{r<m} K(n_r(L), j)      (j even, >= 2),   0 for j odd,

with n_r(L) = #{i < L : i = r mod m} and
    K(n, j) = [x^j] (1+x)^ceil(n/2) (1-x)^floor(n/2).

IsAbelianAt at L, for a mixture mu = sum_m alpha_m P_m, is:  sum_m alpha_m F_j^{(m)}(L) = 0 for
all 1 <= j <= L.  F_j^{(m)}(L) = 0 whenever L <= m, so P_m is abelian at every L <= m.

Known-answer checks below: F_2^{(m)}(m+1) = -1/m, and P_1 (the pure alternating sequence 0101...)
is abelian exactly at L = 1.
"""
from fractions import Fraction as F
from math import comb

def poly_mul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] += x * y
    return r

def K(n, j):
    p = [1]
    for i in range(n):
        p = poly_mul(p, [1, 1 if i % 2 == 0 else -1])
    return p[j] if j < len(p) else 0

def Fjm(m, L, j):
    if j % 2 == 1:
        return F(0)
    tot = 0
    for r in range(m):
        n_r = len([i for i in range(L) if i % m == r])
        tot += K(n_r, j)
    return F(tot, m)

# known-answer checks
for m in range(1, 8):
    assert Fjm(m, m + 1, 2) == F(-1, m), (m, Fjm(m, m + 1, 2))
    for L in range(1, m + 1):
        for j in range(1, L + 1):
            assert Fjm(m, L, j) == 0
# P_1 = 0101...: abelian exactly at L=1
for L in range(2, 12):
    assert any(Fjm(1, L, j) != 0 for j in range(1, L + 1)), L

K_MAX = 12
print("F_j^{(m)}(L) for the AP-defect family (nonzero even j only)")
for m in range(1, 6):
    for L in range(m + 1, K_MAX + 1):
        row = [(j, Fjm(m, L, j)) for j in range(2, L + 1, 2) if Fjm(m, L, j) != 0]
        print(f"  m={m} L={L}: {row}")
