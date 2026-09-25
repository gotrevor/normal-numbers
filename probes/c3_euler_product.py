#!/usr/bin/env python3
"""REFLECTION-LAP PROBE (2026-09-25): is the C3 crux a Delange/Euler-product phenomenon?

Prediction to test.  With  F(n) = e(h * b^n * L_P) = e(h * sum_{i>=1} omega_{>P}(n+i) b^-i)
                           = prod_{i>=1} z_i^{omega_{>P}(n+i)},   z_i = e(h b^-i),
the Selberg-Delange heuristic for the mean of a multiplicative function of "Delange type" gives

    (1/N) sum_{n<N} F(n)  ~  C * (log N)^(-c),    c = sum_{i>=1} (1 - z_i)   (COMPLEX)

so   |mean| ~ (log N)^(-A),  A = sum_i (1 - cos(2 pi h b^-i)),
and  arg(mean) drifts like  -B log log N,  B = sum_i sin(2 pi h b^-i).

Equivalently, by the EXACT local decomposition
    tail_P(n) = sum_{p>P} b^{-r_p(n)} / (1 - b^{-p}),   r_p(n) = p - (n mod p) in [1,p],
F(n) = prod_{p>P} g_p(n mod p) is a product of INDEPENDENT local factors, and the
"independent-residues" model predicts

    (1/N) sum_{n<N} F(n)  ~  EULER(N) := prod_{P<p<=N} ( (1/p) sum_{r=1}^{p} e(h b^{-r}/(1-b^{-p})) ).

EULER(N) is computable directly.  We compare it against the TRUE partial mean.  A match
confirms the mechanism (and therefore that the crux is a mean-value theorem for a function
with a DIVERGENT Euler product, i.e. Delange-strength, not a bounded-sieve statement).
"""
import cmath, math, sys

def primes_upto(N):
    s = bytearray([1])*(N+1); s[0]=s[1]=0
    for i in range(2,int(N**0.5)+1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(N+1) if s[i]]

def omega_large(P, M):
    d = bytearray(M+1)
    for p in primes_upto(M):
        if p > P:
            for m in range(p, M+1, p):
                d[m] += 1
    return d

# --- known-answer check (same as probes/swingc3_weyl_lambert_twist.py) ---
d = omega_large(1, 8)
assert list(d[1:9]) == [0,1,1,1,1,2,1,1], list(d[1:9])
assert abs(sum(d[k]/2**k for k in range(1,9)) - 131/256) < 1e-15
d3 = omega_large(3, 12)
assert d3[6]==0 and d3[5]==1 and d3[10]==1 and d3[12]==0
# stable downward recurrence check: t[n] = (d[n+1] + t[n+1])/b  vs direct depth sum
def tails(d, b, M, pad):
    t = [0.0]*(M+2)
    for n in range(M-1, -1, -1):
        t[n] = (d[n+1] + t[n+1]) / b
    return t
dd = omega_large(1, 200)
tt = tails(dd, 2, 190, 0)
direct = sum(dd[0+k]/2**k for k in range(1,120))
assert abs(tt[0]-direct) < 1e-12, (tt[0], direct)
print("known-answer checks OK", file=sys.stderr)

def euler_pred(b, P, h, N):
    """prod_{P<p<=N} (1/p) sum_{r=1}^p e(h b^{-r}/(1-b^{-p}))  -- log-accumulated."""
    acc = 0j
    for p in primes_upto(N):
        if p <= P: continue
        den = 1.0 - b**(-p) if p < 60 else 1.0
        s = 0j
        for r in range(1, min(p, 200)+1):
            s += cmath.exp(2j*math.pi*h*(b**(-r))/den)
        if p > 200:
            s += (p-200)           # b^{-r} underflows to 0 for r>200 -> factor 1
        acc += cmath.log(s/p)
    return cmath.exp(acc)

def run(b, P, Q, j, h, Ns):
    NMAX = max(Ns)
    M = NMAX + 400
    d = omega_large(P, M)
    t = tails(d, b, M, 0)
    out = {}
    acc_u = 0j; acc_t = 0j; n = 0
    for N in sorted(Ns):
        while n < N:
            ph = cmath.exp(2j*math.pi*h*t[n])
            acc_u += ph
            acc_t += ph*cmath.exp(2j*math.pi*j*n/Q)
            n += 1
        out[N] = (acc_u/N, acc_t/N)
    return out

Ns = [10**4, 10**5, 10**6, 4*10**6]
CASES = [(3,2,2,1,1), (3,2,2,1,2), (4,3,6,1,1), (4,3,6,3,1),
         (4,3,6,1,3), (5,3,6,1,1), (3,5,30,7,1)]
print(f"{'b':>2} {'P':>2} {'Q':>3} {'j':>2} {'h':>2} {'A(pred)':>8} {'B(pred)':>8} | "
      "  N        |untw|     EULER     ratio    argdiff   |twisted|   a_fit")
for (b,P,Q,j,h) in CASES:
    A = sum(1-math.cos(2*math.pi*h*b**(-i)) for i in range(1,80))
    B = sum(math.sin(2*math.pi*h*b**(-i)) for i in range(1,80))
    r = run(b,P,Q,j,h,Ns)
    # fit a on |untwisted|
    xs=[math.log(math.log(N)) for N in Ns]; ys=[math.log(abs(r[N][0])) for N in Ns]
    nn=len(xs); sx=sum(xs); sy=sum(ys)
    a = -(nn*sum(x*y for x,y in zip(xs,ys))-sx*sy)/(nn*sum(x*x for x in xs)-sx*sx)
    xs2=[math.log(math.log(N)) for N in Ns]; ys2=[math.log(abs(r[N][1])) for N in Ns]
    a2 = -(nn*sum(x*y for x,y in zip(xs2,ys2))-sx*sy0) if False else \
         -(nn*sum(x*y for x,y in zip(xs2,ys2))-sx*sum(ys2))/(nn*sum(x*x for x in xs2)-sx*sx)
    first=True
    for N in Ns:
        u,tw = r[N]
        E = euler_pred(b,P,h,N)
        ratio = abs(u)/abs(E) if abs(E)>0 else float('nan')
        argd = (cmath.phase(u)-cmath.phase(E)+math.pi)%(2*math.pi)-math.pi
        head = (f"{b:>2} {P:>2} {Q:>3} {j:>2} {h:>2} {A:8.4f} {B:8.4f} | " if first
                else " "*41+"| ")
        print(head + f"{N:>9} {abs(u):9.6f} {abs(E):9.6f} {ratio:7.3f} {argd:9.4f} "
              f"{abs(tw):10.6f}" + (f"   a={a:.2f}/{a2:.2f}" if N==Ns[-1] else ""))
        first=False
    sys.stdout.flush()
