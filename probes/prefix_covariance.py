"""PROBE (2026-09-20): the prefix/site covariances of `winMean_prod_telescope`, y = 2.

cov_k = E[prod_{j<=k} r_j] - E[prod_{j<k} r_j] * E[r_k],  r_j(n) = e(h om_{>2}(n+j) 4^-j).
Reported: ratio_k = cov_k / (E[prod_{j<k} r_j] * E[r_k])   (the RELATIVE prefix correlation)
and  R = (E[prod_{j<=J} r_j]) / prod_{j<=J} E[r_j]   (the would-be CRT constant c(J)).
If R -> 1 the sites decorrelate; if R -> c != 1 the node must carry that constant.
"""
import math, cmath, sys
from array import array

def omega_rough(M):
    tot = array('b', bytes(M+1)); comp = bytearray(M+1)
    for p in range(3, M+1, 2):
        if not comp[p]:
            for q in range(p, M+1, p):
                comp[q] = 1; tot[q] += 1
    return tot

def windowJ(N):
    l2 = N.bit_length()-1
    return (l2.bit_length()-1) + 1

def e(x): return cmath.exp(2j*math.pi*x)

def run(N, h, ro):
    J = windowJ(N)
    pref = [1+0j]*N
    Epref_prev = 1+0j
    rows = []
    R = 1+0j
    prodE = 1+0j
    for k in range(1, J+1):
        w = 4.0**k
        Ek = 0j
        for i, n in enumerate(range(N, 2*N)):
            z = e(h*ro[n+k]/w)
            Ek += z
            pref[i] *= z
        Ek /= N
        Epref = sum(pref)/N
        cov = Epref - Epref_prev*Ek
        den = Epref_prev*Ek
        rows.append(abs(cov)/abs(den) if abs(den) > 0 else float('nan'))
        Epref_prev = Epref
        prodE *= Ek
    R = Epref_prev/prodE
    return J, rows, R

if __name__ == "__main__":
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 19
    Ns = [1 << k for k in range(12, kmax+1)]
    ro = omega_rough(2*Ns[-1]+40)
    for h in (1, 3, 5):
        print(f"=== h={h}: rel prefix-corr per k, and R = E[prod]/prod E ===")
        for N in Ns:
            J, rows, R = run(N, h, ro)
            print(f"N={N:>8} J={J} rel={[f'{x:.4f}' for x in rows]} |R|={abs(R):.4f} argR={cmath.phase(R):.4f}")
            sys.stdout.flush()
