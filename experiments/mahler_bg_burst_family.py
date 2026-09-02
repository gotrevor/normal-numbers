"""Probe: the FORMALIZABLE family  alpha = a/(g-1) + B*L  (L = sum g^{-i!}).

For multiplier m the eventual digit set of m*alpha is the digit set of the
d-digit base-g string  R = b*(g^d-1)/(g-1) + m*B  (mod g^d),  d large,
where b = (m*a) mod (g-1).  f(a,B) = max over target digits w of
min{m>=1 : w occurs}.  We report max over (a,B) and compare with g^2/4.
"""
import sys

def digset(n, g, d):
    s = set()
    for _ in range(d):
        s.add(n % g); n //= g
    return s

def f(a, B, g, cap):
    # first m at which each digit w becomes reachable
    first = {}
    for m in range(1, cap + 1):
        b = (m * a) % (g - 1)
        N = m * B
        L = 0
        t = N
        while t: t //= g; L += 1
        d = L + 3
        R = (b * (g ** d - 1) // (g - 1) + N) % (g ** d)
        for w in digset(R, g, d):
            first.setdefault(w, m)
        if len(first) == g:
            break
    if len(first) < g:
        return cap + 1, None          # some digit never reached within cap
    w = max(first, key=lambda w: first[w])
    return first[w], w

def main():
    for g in [3, 5, 7, 11, 13, 17, 19, 23, 29]:
        cap = 4 * g * g
        best = (0, None, None, None)
        Bmax = 3 * g * g * g
        for a in range(0, g - 1):
            for B in range(1, Bmax):
                v, w = f(a, B, g, cap)
                if v > best[0]:
                    best = (v, a, B, w)
        print(f"g={g:3d}  bg+burst max M+1 = {best[0]:5d}  (a={best[1]}, B={best[2]}, w={best[3]})"
              f"   ((g-1)/2)^2={((g-1)//2)**2:5d}  (3/2)(g-1)={1.5*(g-1):6.1f}", flush=True)

main()
