# HANDOFF twopoint — lap 47, 2026-09-25

Branch `wip/twopoint-avg`.  `src/NormalNumbers/TwoPointDelangeOmega.lean`.  Green; new theorems
`#print axioms`-clean.

## Crux
After lap 46, `DelangeKernelMean` follows from `sup_N sup_{r∈[0,1]} ‖delangeE N (rξ)‖ < ∞`.
This lap localises *where* that obligation actually lives.

## Landed
* **`sum_inv_prime_sdiff_le`** — `Σ_{K < p ≤ N} 1/p ≤ (log N + log 4 + 9 − log K)/log K`.
  A `Σ 1/p` Mertens corollary the tree did not have, immediate from the two-sided bracket
  (laps 40–41) via `1/p ≤ (log p/p)/log K`.  At `K = √N` the bound is `1 + O(1/log N)`; at
  `K = N^{1/log log N}` it is `O(log log N)` but the *complementary* reading is what matters:
  the primes above any `K = N^{δ}` carry total weight `≤ (1−δ)/δ + o(1)`, an absolute constant.
* **`norm_delangeE_le_split`** — for any cutoff `K ≤ N` and any `Φ` bounding `‖S‖` and `‖S^{(p)}‖`,

      ‖E_N(v)‖ ≤ Σ_{p ≤ K} (1/p)‖S^{(p)}(N/p;v) − S(N;v)‖  +  (Σ_{K<p≤N} 1/p)·2Φ .

## The reading — and a sub-approach REFUTED

Combining the two: at `K = √N` the large-prime half of `E_N` is `≤ 4Φ + o(1)` with an **absolute**
constant, and `norm_delangeSv_le`'s gain turns it into `4Φ/(L|Re ξ|)` — a genuine contraction,
since `L = log log N → ∞`.  So the large primes are settled modulo a bootstrap on `Φ`.

**Refuted this lap (do NOT retry): majorising `E_N` by the absolute sum.**  Write
`A(M) = Σ_{n≤M} μ²(n)u^{ω(n)}/n ≍ (log M)^u`, `u = ‖v‖`.  Termwise,
`‖S^{(p)}(N/p;v) − S(N;v)‖ ≤ (A(N) − A(N/p)) + (1/p)A(N/p)`, and with `t = log p/log N` the first
piece is `(log N)^u(1 − (1−t)^u)`, whose `Σ_p 1/p` average is `≍ ∫_0^1 (1−(1−t)^u) dt/t · (log N)^u
≍ (log N)^u → ∞`.  The *true* difference is `≍ |v|·t·(log N)^{Re v}`, whose average is `O(1)` —
so the small-prime half of `E_N` is irreducibly a statement about cancellation inside
`S(N) − S(N/p)`, not about its absolute majorant.  (This is the same phenomenon that killed
Rankin in lap 33 and the real Gronwall in lap 35, now localised to a single named sum.)

## The open core, in one line
    Σ_{p ≤ √N} (1/p) · ‖ S^{(p)}(N/p; v) − S(N; v) ‖  =  O(1)   uniformly in `N`, `‖v‖ ≤ 1`.
Equivalently: `S` is slowly varying on the `log log` scale, with modulus of continuity `O(1/L)`
against the `Σ 1/p` measure.  Everything else in the Wirsing step is now machine-checked.

## Next
1. The bootstrap lemma: `∀ M, ‖delangeSv M v‖ ≤ Φ` exists (a `Φ` depending on `N` is enough if
   one inducts on `N`); state `norm_delangeSv_le` in the self-improving form
   `Φ(N) ≤ e^{L Re ξ} + (small + 4Φ(N))/(L|Re ξ|)` and extract `Φ = O(1)`.
2. Then attack the open core above.  The natural handle is the same ODE applied to the
   *difference*: `∂_v (S(N;v) − S(M;v)) = Σ_p (1/p)(S^{(p)}(N/p) − S^{(p)}(M/p))`, i.e. the
   difference satisfies the same equation with the same multiplier, so its own integrating-factor
   bound applies with initial condition `0`.

## Confidence
- `twoPointWeightedAvg_all` TRUE 90%, provable with known techniques 3% (C1 unchanged).
- `DelangeKernelMean`: **38%** (unchanged; this lap localises rather than advances the number, and
  it retires one route).
