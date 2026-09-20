"""PROBE (2026-09-20): the node `ParityDiscrepancy` of G4WiringRough.lean, y = 2.

Measures  ||parityDisc_j|| / (N^2 ||fullSiteMean_j||) * log N   for j = 1..J,
and the window analogue against prod_j ||fullSiteMean_j||.
"""
import math, cmath, sys
from array import array

def omega_arrays(M):
    tot = array('b', bytes(M+1)); sm = array('b', bytes(M+1)); comp = bytearray(M+1)
    for p in range(2, M+1):
        if not comp[p]:
            for q in range(p, M+1, p):
                comp[q] = 1; tot[q] += 1
                if p <= 2: sm[q] += 1
    return tot, sm

def windowJ(N):
    l2 = N.bit_length()-1
    return (l2.bit_length()-1) + 1

def e(x): return cmath.exp(2j*math.pi*x)

def run(N, h, tot, sm):
    J = windowJ(N); lg = math.log(N)
    out = []
    Pf = 1.0
    for j in range(1, J+1):
        w = 4.0**j
        full = sum(e(h*tot[n+j]/w) for n in range(N, 2*N))/N
        Se = sum(e(h*(tot[n+j]-sm[n+j])/w) for n in range(N, 2*N) if (n+j) % 2 == 0)
        So = sum(e(h*(tot[n+j]-sm[n+j])/w) for n in range(N, 2*N) if (n+j) % 2 == 1)
        ce = sum(1 for n in range(N, 2*N) if (n+j) % 2 == 0)
        co = N - ce
        disc = co*Se - ce*So
        Pf *= abs(full)
        out.append(abs(disc)/(N*N*abs(full))*lg)
    # window
    Tf = [0.0]*N; Tr = [0.0]*N
    for j in range(1, J+1):
        w = 4.0**j
        for i, n in enumerate(range(N, 2*N)):
            Tr[i] += (tot[n+j]-sm[n+j])/w
    Se = sum(e(h*Tr[i]) for i, n in enumerate(range(N, 2*N)) if n % 2 == 0)
    So = sum(e(h*Tr[i]) for i, n in enumerate(range(N, 2*N)) if n % 2 == 1)
    ce = sum(1 for n in range(N, 2*N) if n % 2 == 0); co = N - ce
    wdisc = abs(co*Se - ce*So)/(N*N*Pf)*lg
    return J, out, wdisc

if __name__ == "__main__":
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 18
    Ns = [1 << k for k in range(12, kmax+1)]
    tot, sm = omega_arrays(2*Ns[-1]+40)
    for h in (1, 3, 5):
        print(f"=== h={h} (entries are  ||disc||/(N^2||full_j||) * log N ) ===")
        for N in Ns:
            J, out, wd = run(N, h, tot, sm)
            print(f"N={N:>8} J={J} sites={[f'{x:.3f}' for x in out]} window={wd:.3f}")
            sys.stdout.flush()
