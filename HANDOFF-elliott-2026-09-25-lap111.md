# HANDOFF elliott 2026-09-25 laps 103–111 — (c′-I) is one step from proved

Branch `wip/elliott-port`, HEAD `d379747`, working tree **clean**.
**Green means BOTH targets**: `lake build` → 9257 jobs · `lake build NormalNumbers.ElliottAxiomAudit`
→ 9683 jobs.  Never `lake exe cache get`.  Never edit `.lake/packages/`.
`DIRECTION.md` CURRENT DIRECTIVE governs — read it first, do **not** edit it (altitude laps own it).
`src/` Elliott scope has **zero `sorry`**; every open obligation is a named `Prop`.

## Headline status (unchanged, re-verified)

`ElliottGeneral.nonasymptoticLogElliott` and `…Mult` are PROVED and `#print axioms`-clean (no
`sorryAx`).  The operator kickoff objective for this session (the two `ElliottLeafTwo` sorries) was
already met at lap ~64; these laps worked DIRECTION's live objective instead: making
`TwoPointElliottLog` rest on TRUE classical inputs.

## What these laps did: (c′-I) taken apart and almost fully discharged

Lap 102 left both soft inputs as `SliceBound{Small,Moderate}` — "cited" bounds on the slice.  Laps
103–111 turned that from a citation into (almost) a proof, and fixed a **fidelity bug** on the way.

| lap | landed (all sorry-free, all in the audit surface) |
|---|---|
| **103** | ⚠ **fidelity repair.**  Lap 102's Props claimed the pole bound for the *truncated* sum at every `Y`; `ζ'/ζ` gives no such thing (at `Y = X, w = 0` the discarded tail is `≍ 1/δ`, the size of the main term).  `norm_dampedPrefix_sub_le`, `norm_dampedPrefix_transfer`: the damping is tuned to `X`, so `dampedTail_le` (uniform in `Y`) makes **the cutoff free** — Props now asked at `sliceCut X = exp((log X)²)`, consumers still call at `Y = X`, cost one additive `cutCost`. |
| **104** | `sum_log_div_primesUpTo_ge` (Mertens I, lower half), `sum_log_div_primesInInterval_le`, `logBlock_le`, `logTail_blocks` (`∑_{p∈(Y,Z]} log p·p^{-1-a} ≤ ∑_k Y^{-a2^k}(2^k log Y + 2C)`). |
| **105** | **`logTail_le`** — that tail is `≤ 1` for `Y ≥ sliceCut X`, `a ≥ δ`, `X ≥ 2²⁰`.  Key step: `t = a2^k log Y ≥ 2^k log X` and `t e^{-t} ≤ 2e^{-t/2}` convert the *growing* log-weight into a *decaying* block weight; then `∑_k X^{-2^k/2} ≤ 2X^{-1/2}` and `s = X^{1/4} ≥ 32`, `log X ≤ 4(s−1)` give `16s + 4C − 16 ≤ s²`.  `2²⁰` is the honest threshold and both Props now carry it. |
| **106** | **`sum_log_rpow_le`**: `∑_{p≤Y} log p·p^{-1-a} ≤ 1/a + (log 4 + 4)` with the coefficient of `1/a` **exactly 1** — Mertens I via `p^{-a} = a∫_{log p}^∞ e^{-as}ds` (finite-sum `integral_finsetSum`; `∫_0^∞ e^{-as} = 1/a`, `∫_0^∞ s e^{-as} = 1/a²` through `Γ(2)=1`).  Since `a = δ+w ≥ w`, the **harmonic clause `w ≥ T` of both inputs is now a THEOREM**; `SliceBound*` follow from the cap clause alone (`SliceCapSmall`, `SliceCapModerate`). |
| **107** | New `ElliottZetaPole.lean`: **`exists_pole_local_bound`** — `∃ r,K > 0, ∀ s ≠ 1, ‖s−1‖ ≤ r → ζ(s) ≠ 0 ∧ ‖ζ'/ζ(s)‖ ≤ 1/‖s−1‖ + K`, with **no zero-free region**: `zetaG := update (s ↦ (s−1)ζ s) 1 1` is analytic at `1` (Riemann removable singularity + `riemannZeta_residue_one`), `logDeriv ζ = logDeriv G − 1/(s−1)`, and `logDeriv G` is bounded on a small ball by compactness. |
| **108** | `exists_far_band_bound` (compactness + `riemannZeta_ne_zero_of_one_le_re`) ⟹ **`exists_subunit_logDeriv_bound`**: `‖ζ'/ζ(s)‖ ≤ 1/‖s−1‖ + K` on all of `1 ≤ Re s ≤ 2`, `|Im s| ≤ 1`, `s ≠ 1`.  **(c′-I)'s analytic side is complete.** |
| **109** | New `ElliottPrimePower.lean`: **`sum_pairs_le`** — any finite set of pairs `(m,j)`, `m,j ≥ 2`, has `∑ log m·m^{-σj} ≤ ppCost = 16∑n^{-3/2}` for `σ ≥ 1`.  Stated over *pairs* so the bridge's `n = p^j ↦ (p,j)` may be any injection; the grouping-free trick is to majorize by a **product** `a_m·b_j` and use `F ⊆ (image fst) ×ˢ (image snd)` + `Finset.sum_product`. |
| **110** | New `ElliottBridge.lean`: **`slice_eq_sum_term`** — the slice **is** `∑_{p≤Y} LSeries.term ↗Λ s p` at `s = sliceAbscissa X w v = (1+δ+w)+iv`, *exactly*.  Content: `conj(archimedeanTwist v p) = p^{-iv}` is the Archimedean factor inside `p^{-s}` (`Complex.cpow_add`, `Complex.ofReal_cpow`, `Complex.natCast_log`). |
| **111** | **`sum_complement_le`** — every finite `G` disjoint from `primesUpTo Y` has `∑_{n∈G} Λ n·n^{-σ} ≤ 1 + ppCost` (`σ ≥ 1+δ`): primes ⟹ `logTail_le`, non-primes ⟹ `IsPrimePow` ⟹ `sum_pairs_le` under `n ↦ (minFac n, factorization)`.  Supporting: `primePow_decomp`, `term_primePow`. |

## NEXT LAP — finish (c′-I).  One step, fully scoped

`SliceCapSmall (C·K)` — i.e. `‖logWeightedSlice v X Y w‖ ≤ T⁻¹ + K` on `w ≤ T` — now follows from:

1. `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` (needs `1 < Re s`; `Re s = 1+δ+w` ✓) to read
   `L ↗Λ s = −ζ'/ζ(s)`, i.e. `= −logDeriv riemannZeta s`.
2. `Finset.sum_add_tsum_compl` (with `LSeriesSummable_vonMangoldt`, `1 < Re s`) to write
   `L ↗Λ s = (∑_{p ∈ primesUpTo Y} term) + ∑'_{n ∉ primesUpTo Y} term`, then `slice_eq_sum_term`
   identifies the finite part with the slice, so
   `‖slice + logDeriv ζ s‖ ≤ ∑'_{n∉S} ‖term n‖`.
3. `‖term n‖ = Λ n·n^{-σ}` (`Complex.norm_natCast_cpow_of_pos`-style, `σ = Re s`), and
   `tsum_le_of_sum_le` (nonneg) + **`sum_complement_le`** gives `≤ 1 + ppCost`.
4. Then `exists_subunit_logDeriv_bound` at `s = sliceAbscissa X w v`: in the cap band
   `‖s−1‖ = ‖(δ+w) + iv‖ ≥ max(δ+w, |v|) ≥ T`, so `1/‖s−1‖ ≤ T⁻¹`.  Note `Re s ≤ 2` needs
   `δ + w ≤ 1`, true since `w ≤ T ≤ 1` and `δ ≤ 1`; and `|Im s| = |v| ≤ 1` ✓ on the sub-unit band.
   **Constant caveat**: this yields `T⁻¹ + K'`, coefficient 1, so `SliceCapSmall` as stated is fine —
   no need for the relaxed `C·T⁻¹` form (which is nevertheless available, see below).

**After that**: (c′-II) `SliceCapModerate` wants `‖ζ'/ζ(σ+iv)‖ ≪ log|v|` for `|v| > 1` — de la
Vallée Poussin, the genuinely deep one, together with `ArchCorrNearMaxHeight` (Vinogradov–Korobov).
Those two remain the only walls.

## Facts worth not re-deriving

* **The cap clause's coefficient does not matter.**  The cap band has length `T`, so a bound
  `C·T⁻¹ + K` costs only `C` in the `w`-integral; the `log(1/T)` main term comes entirely from the
  harmonic band (lap 106, coefficient 1).  `ElliottLogIntegral.integral_le_const_mul_one_add_log` is
  the routing lemma if a relaxed cap is ever needed.
* **Sharp constant 1 on `1/a` is available from Mertens I** by Abel summation — a dyadic-block
  derivation of the "same" bound loses a constant factor and is what made earlier laps think the
  trivial bound was useless.
* `primesInInterval` lives in `Erdos67b.PrimeEstimates`; `primesUpTo` in `Erdos67b.Pretentious`.
* `Finset.sum_image` takes the *map* as `g` and the summand as `f` (both implicit) and wants
  `Set.InjOn`.
* `Λ n = log (minFac n)` for prime powers is `vonMangoldt_apply` directly — no fibre bookkeeping
  needed.
* Lean trap (lap 111): `p, j` are defined *from* `n`, so `rw [← hpow]` rewrites the `n` inside `p`.
  Prove the pair-shape identity standalone in `p, j` and rewrite `hpow : p^j = n` **into** it.
* `Nat.lt_two_pow_self` (not `Nat.one_add_le_two_pow_iff`); `inv_anti₀` (not `inv_le_inv_of_le`);
  `MeasureTheory.integrable_finsetSum`; `integral_rpow_mul_exp_neg_mul_rpow` is in the **root**
  namespace.

## Doc map

`DIRECTION.md` CURRENT DIRECTIVE (lap 92, binding) · `PENDING_WORK.md` top section (live attack
paths, laps 95–111, with the next-lap recipe) · `ROUTE-ESCALATION-2026-09-25-archimedean.md` (the
lap-92 refutation+repair) · `HANDOFF-elliott-2026-09-25-lap102.md` (previous) · audit surface
`src/NormalNumbers/ElliottAxiomAudit.lean`.
