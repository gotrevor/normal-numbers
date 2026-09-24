#!/usr/bin/env python3
"""Probe of `WeylLambertTwist` (SwingC3Lambert2), the swing's sharpest conditional:

    (1/N) sum_{n<N} e(j n / Q) * e(h * b^n * L_P)   ->  0 ,     L_P = sum_{p>P} 1/(b^p - 1).

Lap 9 proves  e(h * tailLarge P b n) = e(h * L_P * b^n)  exactly, and
    tailLarge P b n = sum_{k>=1} omega_{>P}(n+k) / b^k .
So we evaluate the phase from the digit stream d_m = omega_{>P}(m), which is exact and cheap.

Two known-answer checks are hand-computed below.
"""
import cmath, math

def primes_upto(N):
    s = bytearray([1])*(N+1); s[0]=s[1]=0
    for i in range(2,int(N**0.5)+1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(N+1) if s[i]]

def omega_large_sieve(P, M):
    """d[m] = #{p > P prime : p | m} for m <= M."""
    d = [0]*(M+1)
    for p in primes_upto(M):
        if p > P:
            for m in range(p, M+1, p):
                d[m] += 1
    return d

# ---- known-answer checks -------------------------------------------------
# (1) b=2, P=1 (so all primes), d = omega.  omega(2..8) = 1,1,1,1,2,1,1
d = omega_large_sieve(1, 8)
assert d[1:9] == [0,1,1,1,1,2,1,1], d[1:9]
# tailLarge 1 2 0 head over k=1..8 = 0/2+1/4+1/8+1/16+1/32+2/64+1/128+1/256 = 131/256
head = sum(d[k]/2**k for k in range(1,9))
assert abs(head - 131/256) < 1e-15, head
# (2) P=3: only primes > 3 count, so d[6]=1 (only 5? no: 6=2*3 -> 0), check directly
d3 = omega_large_sieve(3, 12)
assert d3[6] == 0 and d3[5] == 1 and d3[10] == 1 and d3[12] == 0, (d3[5],d3[6],d3[10],d3[12])
print("known-answer checks OK")

# ---- the twisted Weyl sum ------------------------------------------------
DEPTH = 64   # b^-64 <= 1e-19 for b>=2

def run(b, P, Q, j, h, Ns):
    M = max(Ns) + DEPTH + 2
    d = omega_large_sieve(P, M)
    invb = [b**-k for k in range(DEPTH+1)]
    out = {}
    acc = 0j
    n = 0
    for N in sorted(Ns):
        while n < N:
            t = 0.0
            for k in range(1, DEPTH+1):
                dk = d[n+k]
                if dk:
                    t += dk*invb[k]
            acc += cmath.exp(2j*math.pi*(j*n/Q + h*t))
            n += 1
        out[N] = abs(acc)/N
    return out

Ns = [10**3, 10**4, 10**5, 4*10**5]
print(f"{'b':>2} {'P':>2} {'Q':>3} {'j':>2} {'h':>3} | " +
      " ".join(f"N={N:<8}" for N in Ns) + "   fitted (log N)^-a")
for (b,P,Q,j,h) in [(3,2,2,1,1), (3,2,2,1,2), (4,3,6,1,1), (4,3,6,3,1),
                    (4,3,6,1,3), (5,3,6,1,1), (3,5,30,7,1)]:
    r = run(b,P,Q,j,h,Ns)
    xs = [math.log(math.log(N)) for N in Ns]
    ys = [math.log(r[N]) for N in Ns]
    nn = len(xs); sx=sum(xs); sy=sum(ys)
    a = -(nn*sum(x*y for x,y in zip(xs,ys)) - sx*sy)/(nn*sum(x*x for x in xs) - sx*sx)
    print(f"{b:>2} {P:>2} {Q:>3} {j:>2} {h:>3} | " +
          " ".join(f"{r[N]:<10.6f}" for N in Ns) + f"   a = {a:.2f}")
print()
print("h=0 control (must be |mean of e(jn/Q)| ~ 1/N, i.e. -> 0 trivially):")
r = run(3,2,2,1,0,Ns)
print("   ", {N: round(v,8) for N,v in r.items()})
