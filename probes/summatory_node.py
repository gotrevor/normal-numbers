#!/usr/bin/env -S uv run --quiet --with numpy python3
"""PROBE (2026-09-20, Ren): the ONE summatory node behind PrefixLimit + ParityDiscrepancy.

R_k(M) = sum_{m<M} prod_{j<=k} e(h om_{>2}(m+j) / 4^j).
Conjectured shape (Selberg-Delange with shifts): R_k(M) = c_k * M * (log M)^{kappa_k} * (1 + O(1/log M))
with kappa_k = sum_{j<=k} (z_j - 1), z_j = e(h/4^j) (complex exponent).

Reported per (h, k), over dyadic M:
  Q = R_k(M) / (M (log M)^kappa_k)        -- should be FLAT (-> c_k) if the node holds
  fitted exponent from consecutive dyadic pairs: kappa_hat = log(R(2M)/(2 R(M))) / log(log 2M / log M)
                                                  -- should approach kappa_k (complex)
  rate: D = (Q(2M) - Q(M)) * log M           -- bounded iff the 1 + O(1/log M) rate holds
  |Q_k/Q_{k-1}|                               -- flat iff PrefixLimit's main-term ratio exists (exponents cancel)
Known-answer control: k = 1 IS classical Selberg-Delange (omega over odd primes), so its convergence
pattern at this range is what a TRUE node looks like; judge k >= 2 against it, not against 0.
Method: sieve om_{>2} once as int8; per site j build the phase array; running product over shifts;
cumulative sum gives every R_k(M) at once (numpy).
"""
import sys, math, cmath
import numpy as np

def omega_rough(L):
    om = np.zeros(L + 1, dtype=np.int8)
    comp = np.zeros(L + 1, dtype=bool)
    for p in range(3, L + 1, 2):
        if not comp[p]:
            comp[p*p::p] = True
            om[p::p] += 1
    return om

def run(h, kmax, lmax):
    L = (1 << lmax) + kmax + 2
    om = omega_rough(L)
    Ms = [1 << l for l in range(12, lmax + 1)]
    prod = np.ones(1 << lmax, dtype=np.complex128)
    kappa = 0j
    out = {}
    for k in range(1, kmax + 1):
        z = cmath.exp(2j * math.pi * h / 4**k)
        kappa += z - 1
        # phase at shift k: e(h om(m+k)/4^k) for m = 0 .. 2^lmax - 1
        prod *= np.exp(2j * math.pi * h * om[k:k + (1 << lmax)].astype(np.float64) / 4**k)
        R = np.cumsum(prod)
        rows = []
        prevQ = None
        for M in Ms:
            RM = R[M - 1]
            Q = RM / (M * cmath.exp(kappa * math.log(math.log(M))))
            rows.append((M, RM, Q))
        out[k] = (kappa, rows)
        print(f"=== h={h} k={k}  kappa_pred = {kappa.real:+.4f}{kappa.imag:+.4f}i ===")
        for i, (M, RM, Q) in enumerate(rows):
            line = f"M=2^{int(math.log2(M)):2d} |Q|={abs(Q):.4f} argQ={cmath.phase(Q):+.4f}"
            if k > 1:  # PrefixLimit content: main-term ratio c_k/c_{k-1} should be flat in M
                Qm = out[k-1][1][i][2]
                line += f" |Q_k/Q_k-1|={abs(Q/Qm):.4f}"
            if i > 0:
                Mp, RMp, Qp = rows[i - 1]
                khat = cmath.log(RM / (2 * RMp)) / math.log(math.log(M) / math.log(Mp))
                D = (Q - Qp) * math.log(Mp)
                line += f"  kappa_hat={khat.real:+.4f}{khat.imag:+.4f}i  |D|={abs(D):.3f}"
            print(line)
        sys.stdout.flush()
    return out

# ---------------------------------------------------------------------------------------------
# Mode 2 (added 20:5x EDT): the node's two extra clauses.
#   (S) singletons {k}: S_k(M) = sum_{m<M} e(h om(m+k)/4^k) = c'_k M L^{z_k-1} (1 + O(4^-k / L))
#       -> report relative secondary size |D|/|Q| per k; should decay like 4^-k (analytic in z_k, exact at z_k=1).
#   (P) parity classes: sum over m<M, m = a (mod 2) has main term (c/2) M L^kappa with the SAME c for a=0,1
#       -> report |Q_even/Q_odd| for prefixes and singletons; should -> 1.
def run_modes(h, kmax, lmax):
    L = (1 << lmax) + kmax + 2
    om = omega_rough(L)
    n = 1 << lmax
    Ms = [1 << l for l in range(12, lmax + 1)]
    par = (np.arange(n) % 2 == 0)
    prod = np.ones(n, dtype=np.complex128)
    kappa = 0j
    print(f"=== h={h}: singleton relative secondary |D|/|Q| (want ~4^-k), parity ratio |Q_e/Q_o| (want 1) ===")
    for k in range(1, kmax + 1):
        z = cmath.exp(2j * math.pi * h / 4**k)
        site = np.exp(2j * math.pi * h * om[k:k + n].astype(np.float64) / 4**k)
        prod *= site
        kappa += z - 1
        def Qs(arr, kap):
            R = np.cumsum(arr); Re = np.cumsum(np.where(par, arr, 0))
            out = []
            for M in Ms:
                mt = M * cmath.exp(kap * math.log(math.log(M)))
                out.append((R[M-1] / mt, Re[M-1] / (mt / 2)))
            return out
        qs = Qs(site, z - 1); qp = Qs(prod, kappa)
        Dsq = [abs((qs[i][0] - qs[i-1][0]) * math.log(Ms[i-1])) / abs(qs[i][0]) for i in range(1, len(Ms))]
        Dpq = [abs((qp[i][0] - qp[i-1][0]) * math.log(Ms[i-1])) / abs(qp[i][0]) for i in range(1, len(Ms))]
        Qe_s = qs[-1][1] / (2*qs[-1][0] - qs[-1][1]); Qe_p = qp[-1][1] / (2*qp[-1][0] - qp[-1][1])
        print(f"k={k} |1-z_k|={abs(z-1):.4f}  site |D|/|Q| last3={[f'{x:.3f}' for x in Dsq[-3:]]}  prefix |D|/|Q| last3={[f'{x:.3f}' for x in Dpq[-3:]]}"
              f"  |c'_k|={abs(qs[-1][0]):.4f}  parity site={abs(Qe_s):.4f} prefix={abs(Qe_p):.4f}")
        sys.stdout.flush()

# Mode 3 (22:0x EDT, handoff request): is the parity-class constant clause sharp?
#   dev(M) = R_s(M, even)/R_s(M, odd) - 1.  Under the node dev(M) = O(1/log M): print dev * log M (bounded, flat)
#   versus dev itself (would tend to a constant != 0 if the class constants differ).
def run_parity(h, kmax, lmax):
    L = (1 << lmax) + kmax + 2
    om = omega_rough(L)
    n = 1 << lmax
    Ms = [1 << l for l in range(14, lmax + 1, 2)]
    par = (np.arange(n) % 2 == 0)
    prod = np.ones(n, dtype=np.complex128)
    print(f"=== h={h}: parity-class deviation dev = R_even/R_odd - 1, and dev*log M (want: bounded, flat) ===")
    for k in range(1, kmax + 1):
        prod *= np.exp(2j * math.pi * h * om[k:k + n].astype(np.float64) / 4**k)
        Re = np.cumsum(np.where(par, prod, 0)); R = np.cumsum(prod)
        cells = []
        for M in Ms:
            dev = Re[M-1] / (R[M-1] - Re[M-1]) - 1
            cells.append(f"2^{int(math.log2(M))}: |dev|={abs(dev):.4f} |dev|logM={abs(dev)*math.log(M):.3f}")
        print(f"k={k}  " + " | ".join(cells))
        sys.stdout.flush()

if __name__ == "__main__":
    lmax = int(sys.argv[1]) if len(sys.argv) > 1 else 24
    kmax = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    hs = [int(x) for x in sys.argv[3].split(",")] if len(sys.argv) > 3 else [1, 3, 5]
    mode = sys.argv[4] if len(sys.argv) > 4 else "prefix"
    for h in hs:
        {"modes": run_modes, "parity": run_parity}.get(mode, run)(h, kmax, lmax)
