# HANDOFF twopoint — lap 45, 2026-09-25

Branch `wip/twopoint-avg`.  `src/NormalNumbers/TwoPointDelangeOmega.lean` extended.  Build green;
new theorems `#print axioms`-clean.

## Crux
`DelangeMean` ⟶ (lap 43) exactly "`delangeS z N` converges" ⟶ (lap 44) attacked through the
`ω`-weighted identity, whose multiplier keeps the phase of `v = z−1`.

## Advance: the identity is now an actual ODE in the parameter

* `delangeSv`, `delangeSvRestr` — `S` and `S^{(p)}` as functions of the parameter `v`
  (`delangeSv_eq : delangeSv N (z−1) = delangeS z N`).
* `delangeSvDeriv_eq` — the `ω`-identity in derivative form, **with no division by `v`**, hence
  valid at every `v` including `0` (both sides are `Σ_{p≤N} 1/p` there).
* `hasDerivAt_delangeSv` — **`HasDerivAt (delangeSv N) (Σ_{p≤N} (1/p)·S^{(p)}(N/p; v)) v`.**

So `S(N; ·)` is a genuine holomorphic (polynomial) solution of

    ∂_v S(N; v) = Σ_{p ≤ N} (1/p) · S^{(p)}(N/p; v),   S(N; 0) = 1.

## The decisive next step, now fully specified

Write `L := Σ_{p≤N} 1/p = log log N + O(1)` (real, positive), fix `ξ = v/‖v‖ = e^{iθ}` with
`cos θ < 0` (⟺ `Re z < 1`), and set `F(r) := S(N; rξ)`, `c := ξ·L`.  The **integrating factor**
`H(r) := e^{-cr} F(r)` has, exactly,

    H'(r) = e^{-cr} · ξ · E_N(rξ),    E_N(v) := Σ_{p≤N} (1/p)·( S^{(p)}(N/p; v) − S(N; v) ).

Hence `F(1) = e^{c}( 1 + ∫_0^1 e^{-cr} ξ E_N(rξ) dr )` and, since `‖e^{c}‖ = e^{L cos θ}`,

    ‖S(N; ξ)‖  ≤  e^{L cos θ}  +  (sup_{r∈[0,1]} ‖E_N(rξ)‖) · (1 − e^{L cos θ}) / (L |cos θ|).

`e^{L cos θ} ≍ (log N)^{cos θ} → 0`, and the second term carries a **gain factor `1/(L|cos θ|)`**.
This matters and is why the crude mean-value form is not enough: `E_N` is genuinely `O(1)` and not
`o(1)` (the primes `p ∈ (N^{1/2}, N]` alone contribute weight `O(1)` with `S^{(p)}(N/p)` at a
completely different scale).  With the `1/L` gain, `E_N = O(1)` suffices and
`DelangeKernelMean` follows.  So the crux is now a **bounded-ness** statement, not a cancellation
statement — that is the qualitative change this lap buys.

## Next (in order)
1. `delangeE` : the named error `E_N(v)`, and `hasDerivAt_integratingFactor` :
   `HasDerivAt H (e^{-cr}·ξ·E_N(rξ)) r`.  Pure chain rule on top of `hasDerivAt_delangeSv`.
2. FTC (`intervalIntegral.integral_eq_sub_of_hasDerivAt`; `H'` is continuous, a polynomial times
   an exponential) and the weighted bound above, as a theorem conditional on a named
   `∀ r ∈ [0,1], ‖E_N(rξ)‖ ≤ B` hypothesis.
3. Then the single remaining obligation is `E_N = O(1)` uniformly in `N`, i.e.
   `Σ_{p≤N}(1/p)·‖S^{(p)}(N/p;v) − S(N;v)‖ = O(1)` — a comparison of `S` at nearby scales,
   for which the grading (`delangeS_grade`, nonnegative coefficients) gives a monotone majorant.

## Confidence
- `twoPointWeightedAvg_all` TRUE 90%, provable with known techniques 3% (C1 unchanged).
- `DelangeKernelMean`: 22% → **30%** — the reduction to a bounded-ness statement with a `1/log log N`
  gain is a real qualitative improvement over every previous formulation in this repo.
