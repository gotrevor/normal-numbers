# HANDOFF twopoint — SESSION WRAP 4 (laps 28–42), 2026-09-25

Branch `wip/twopoint-avg`.  HEAD `0a8f0f0`.  Working tree **clean**; every lap committed green
(pre-commit runs `lake build`, 9291 jobs).  All new declarations `#print axioms`-clean
(`[propext, Classical.choice, Quot.sound]`).  No `sorry` introduced anywhere this run.

## Rules honoured
`twoPointWeightedAvg_all` never deleted, renamed or weakened.  No edits to `PairDecouple*.lean`,
`SwingC1*.lean`, `CastingOut*.lean`, `Maze.lean`, `papers/`, `agent-mail/`, other KICKOFFs, or
`DIRECTION.md`.  All new code in `src/NormalNumbers/TwoPoint*.lean`, imports added to
`src/NormalNumbers.lean`.

## Part A — the C1 crux: MEASURED AND PINNED (kickoff success criterion met)

`DIRECTION.md` step 2 (the `K ≈ log_b log M` peel) and step 3 (pin the obstruction as a theorem)
are both discharged.

| lap | commit | file | result |
|---|---|---|---|
| 29 | `ab283df` | `TwoPointDepthPeel.lean` | `pairDecorr_of_unweighted` — the peel weight DROPS at growing depth |
| 30 | `2d4d2c3` | `TwoPointShiftLocal.lean` | `card_hit_eq` — exact CRT counts for the `2K` forms |
| 31 | `6775ae3` | `TwoPointDepthPeel.lean` | **`pairDecorr_iff_unweighted`** — an EQUIVALENCE |
| 32 | `f29262a` | `TwoPointDepthInvariance.lean` | depth invariance; weight ⟺ unbounded depth |

**The pin.**  `PairDecorr b t` is *equivalent* (for any depth schedule meeting the explicit carry
budget `peelBound`, and hypothesis-free at `K(M)=M`) to the vanishing of

    E_{n<M} ∏_{k<K(M)} ζ_k^{ω(pn+1+k)} · conj(ζ_k^{ω(qn+1+k)}),   ζ_k = e(t/b^{k+1}),

an **unweighted, natural-density, growing-length Elliott correlation along DILATES** `pn`, `qn`.
Tao 2016 is log-density and two-point; MRT 2015 averages over SHIFTS.  Neither applies.  No route
lies strictly between the leaf and that named open problem.

**New escape hatches closed in kernel (do NOT re-open):**
* "choose a cheaper depth schedule" — `multiElliottGrowing_schedule_invariant`;
* "drop the weight for an easier leaf" — `multiElliottWeighted_iff_growing` (the `K₀=1` instance
  says the repo's shortest leaf already equals the full unbounded-length correlation);
* "the small-prime variance closes it" — lap 30: used mass over `(K,z]` is `≍ 2K log(log z/log K)`,
  divergent at every admissible schedule, so it is irreducibly a cancellation statement.

## Part B — the 🟡 `DelangeMean` axiom: narrowed to ONE Tauberian statement

Laps 28, 33–42.  Files `TwoPointDelangeTail.lean`, `TwoPointDelangeLF.lean`,
`TwoPointMertensLower.lean`.

**Landed as theorems, in dependency order:**
1. `delangeKernelTail_of_norm_lt_one` (28, `92ede26`) — the `ℓ¹` residue, unconditional for
   `‖z−1‖<1`.  So for `‖t‖_{ℝ/ℤ}<1/6` the axiom rests on the single residue `DelangeKernelMean`.
2. `sum_delangeKernel_mul_log` (33, `3019208`) — the Levin–Fainleib identity.
3. `delangeSrestr_rec`, `norm_delangeT_le` (34, `32cc493`) — restriction removal (an EXACT
   recursion), the working inequality with no hidden constant.
4. `delangeS_mul_log`, `norm_delangeS_mul_log_le` (35, `d847b72`) — discrete Abel summation and
   the Wirsing recursion.  **Everything to here is an identity or a triangle inequality.**
5. `delangeA_le_prod` (36, `f34b636`) — the error term's size, by index-set inclusion.
6. `sum_log_telescope`, `tendsto_delangeAbel_div_log`, `tendsto_delangeT_div_log`
   (37, `ecfc5b6`) — Toeplitz; a convergent `S` forces `T(N)=o(log N)`.
7. `log_factorial_ge`, `sum_div_pow_le` (38, `60f455a`); `sum_log_div_mul_pred_le` (39, `f0dd52e`);
   **`mertens_lower`** (40, `58c4860`); **`mertens_upper`** (41, `acae678`) —
   **Mertens' first theorem, both halves, sharp, elementary:**
   `log N − 9 ≤ Σ_{p≤N}(log p)/p ≤ log N + log 4`.  New to the tree (it had only the crude
   `≤ 4 log N`).  No integrals, no zeta, no PNT.
8. `norm_delangeSrestr_le_two_mul`, `norm_delangeT_sub_primeSum_le` (42, `0a8f0f0`) — replacing
   `S^{(p)}` by `S` costs an absolute `16B`, uniformly in `N`.

**Two sub-approaches refuted and recorded (do NOT retry):**
* **Rankin / any absolute-value sum-vs-product comparison** (lap 33): for `u=‖z−1‖∈(0,1)` the
  absolute sum `≍(log N)^u` diverges while the product `→0`, so the separating tail exceeds both.
  Rankin exponent priced: `σ=c/log N` gives `e^{-c}(log N)^{ue^c}`, minimised at `≍1`, never `o(1)`.
* **A real-valued Gronwall on `‖S‖`** (lap 35): fixed point `θ≈u`, so it provably stalls at
  `(log N)^u`.  The endgame must run on `S` itself.

**The structural payoff (lap 37).**  Using the two exact identities together forces the VALUE of
the limit: `T/log N → 0` and `T/log N → (z−1)L` give `(z−1)L = 0`, so `L = 0` for `z ≠ 1`.
Therefore `DelangeKernelMean` ⟺ "`S(N)` converges" — the limit need not be identified.

## Next session — start here

**One brick finishes part II** (est. 1 lap, ~70%):

`tendsto_primeSum_div_log` : if `S(N) → L` then `Σ_{p≤N}(log p/p)·S(N/p)/log N → L`.
Same ε-split as `tendsto_delangeAbel_div_log` (lap 37), normalised by the two-sided Mertens
bracket (laps 40–41).  Wrinkle: split the primes at a fixed `P₀`; the head is a finite sum so its
mass is `O_{P₀}(1)` and dies after dividing by `log N`; on the tail `N/p → ∞` so `S(N/p)` is
within `ε` of `L`.  Then chain with `norm_delangeT_sub_primeSum_le` (42) and
`tendsto_delangeT_div_log` (37) to get `(z−1)L = 0`, and state
`delangeKernelMean_of_converges`.

**After that**, the remaining wall is genuinely Tauberian: proving `S` converges at all.  That is
Wirsing's theorem proper and is a multi-lap (or multi-session) analytic project; the entire
elementary scaffolding beneath it is now machine-checked, which is the honest narrowing.

**On the C1 side** there is no cheap work left: the route's depth is measured at three surfaces
(weighted fixed, weighted growing, unweighted growing) which are machine-checked to agree.  Any
new attack must supply a *cancellation* mechanism for a natural-density dilate correlation, not a
triangle inequality.

## Confidence at wrap
- `twoPointWeightedAvg_all` TRUE: **90%**; provable with known techniques: **3%**.
- C1 is equivalent to a named open problem, with the equivalence a theorem in `src/`: **done**,
  not an estimate.
- Part II of the Wirsing step closable next lap: **70%**.
- Full `DelangeKernelMean` (i.e. convergence of `S`): **15%** this run.
