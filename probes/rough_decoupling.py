"""PROBE (2026-09-20): frozen node N1a' `SmoothRoughDecoupling` in G4WiringRough.lean.

Both halves, at y = 2,3,5 and h = 1,3,5, along J = windowJ N = log2(log2 N)+1.
Reports the RELATIVE error  err / prod|fullSiteMean|  which the statement bounds by C/log N.
Pure stdlib (no numpy on the box).
"""
import math, cmath, sys
from array import array

def omega_arrays(M, y):
    tot = array('b', bytes(M+1))
    sm  = array('b', bytes(M+1))
    comp = bytearray(M+1)
    for p in range(2, M+1):
        if not comp[p]:
            for q in range(p, M+1, p):
                comp[q] = 1
                tot[q] += 1
                if p <= y: sm[q] += 1
    return tot, sm

def windowJ(N):
    l2 = N.bit_length()-1
    return (l2.bit_length()-1) + 1

def run(N, h, y, tot, sm):
    J = windowJ(N)
    # phase tables: ph[j][k] = e(h*k/4^j)
    KMAX = 40
    tab = [[cmath.exp(2j*math.pi*h*k/4.0**j) for k in range(KMAX)] for j in range(J+1)]
    W = S = R = 0j
    sf = [0j]*(J+1); ss = [0j]*(J+1); sr = [0j]*(J+1)
    for n in range(N, 2*N):
        wf = ws = wr = 1+0j
        for j in range(1, J+1):
            t = tot[n+j]; s = sm[n+j]; r = t - s
            a = tab[j][t]; b = tab[j][s]; c = tab[j][r]
            wf *= a; ws *= b; wr *= c
            sf[j] += a; ss[j] += b; sr[j] += c
        W += wf; S += ws; R += wr
    W/=N; S/=N; R/=N
    sf=[z/N for z in sf[1:]]; ss=[z/N for z in ss[1:]]; sr=[z/N for z in sr[1:]]
    Pf = 1.0
    for z in sf: Pf *= abs(z)
    Pfc = 1+0j; Ps = 1+0j; Pr = 1+0j
    for z in sf: Pfc *= z
    for z in ss: Ps *= z
    for z in sr: Pr *= z
    e1 = abs(W - S*R); e2 = abs(Pfc - Ps*Pr)
    return J, Pf, e1/Pf, e2/Pf, math.log(N)

if __name__ == "__main__":
    kmax = int(sys.argv[1]) if len(sys.argv)>1 else 20
    Ns = [1<<k for k in range(12, kmax+1)]
    M = 2*Ns[-1] + 40
    for y in (2,3,5):
        tot, sm = omega_arrays(M, y)
        for h in (1,3,5):
            print(f"=== y={y} h={h} ===")
            print(f"{'N':>9} {'J':>2} {'prodFull':>10} {'rel1':>10} {'rel2':>10} {'rel1*logN':>10} {'rel2*logN':>10}")
            for N in Ns:
                J,Pf,r1,r2,lg = run(N,h,y,tot,sm)
                print(f"{N:>9} {J:>2} {Pf:10.3e} {r1:10.3e} {r2:10.3e} {r1*lg:10.3e} {r2*lg:10.3e}")
                sys.stdout.flush()
