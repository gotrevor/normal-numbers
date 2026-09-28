# HANDOFF elliott 2026-09-25 laps 71–82 — Case B: obstruction found, SOLVED, and the outer shell proved

Branch `wip/elliott-port`, HEAD `d02aef3`, **working tree clean**, `lake build` green.
Never `lake exe cache get`.  Never edit `.lake/packages/lean-proofs-latest/`.
**`DIRECTION.md` CURRENT DIRECTIVE governs — read it first.  Do NOT edit it.**

## One-paragraph version

`src/` still holds **exactly one** sorry, `ElliottLeafTwo.exists_caseB_threshold`, but it is now a
**different and correct** statement.  The lap's real content: the lap-54 route had a genuine gap —
the Case A/B dichotomy is on the defect at the *thin* scale `L ≈ a₁X/W`, while the pretentious
transfer needs it at `≈ X`, and `Σ_X − Σ_L ≈ log(log X / log L)` is unbounded when `W ≈ X`; Case A
does **not** cover the gap.  The fix (truncate the window from below at a `2^j`-th root of `W`) is
now fully formalised, and `nonasymptotic_of_affineCM` — the whole outer shell, truncation +
dichotomy + budget — is **proved** on top of the corrected Case B.

## `src/` sorry inventory (authoritative, Elliott scope)

| file:line | name | state |
|---|---|---|
| `ElliottLeafTwo.lean:~264` | `exists_caseB_threshold` | corrected statement; every ingredient proved; only the ε-budget assembly remains |

## The obstruction and the repair (do NOT re-derive — see `PENDING_WORK.md` laps 71–75)

`mrtNonpretentious_transfer` costs `2·Σ_x(g₁)` at the scale `x` where non-pretentiousness is
wanted.  Case B needs `x ≈ X`; the dichotomy only bounds `Σ_L`.  Counterexample regime: `W ≈ X`
gives `L ≈ a₁`, `Σ_L ≈ 0`, `Σ_X ≈ log log X`, unbounded against `A ≥ A₀`.  Case A cannot take up
the slack: its `≈ log W` dyadic blocks near `L` each save `e^{−Σ_L} ≈ 1`.

**Repair.**  Truncate at `ν = ⌊X/W''⌋+1`, `W'' = truncRatio j X W = min W (X / max 2 (iterSqrt j W))`:
* discarded harmonic mass `≤ 1 + 2log2 + (log W)/2^j ≤ (ε/2) log W` for `2^j ≥ 8/ε`;
* `X < ν^(2^(j+1))` with **no case split**, because `X < W''·ν` and
  `W'' ≤ W < (iterSqrt j W + 1)^(2^j) ≤ ν^(2^j)`;
* hence `X ≤ (thinScale a₁ b₁ X W'')^(2^(j+2))`, and
  `ElliottMertensIterate.reciprocalPrimeInterval_iter` turns that into
  `Σ_X ≤ Σ_{L''} + (j+2)(log 2 + 2·mertensBound)` — absolute in `ε`.
* `√W ≤ W''`, so `log W'' ≥ (1/2) log W` and `W''` still clears every threshold.

## New modules this session (all zero-sorry, all in the audit surface)

| module | content |
|---|---|
| `ElliottStageStep` | `sum_Icc_norm_squarefullPart_le` (`∑_{d≤D}‖u d‖ ≤ D e²`); **`norm_le_of_reduced`** and **`norm_le_of_reduced_second`** — the reusable one-function expansion brick (`≤ (M+4D)·D e² + tail`), for the first and (after `elliottLogCorrelation_swap`) the second argument |
| `ElliottScaleWindow` | `thinScale`, `thinScale_le_integerAffine`, **`logRatio_le`** (`1 + log Y − log L ≤ log W + logRatioConst a b`) |
| `ElliottZeroExt` | **`norm_sub_posExt_le`** (`≤ 2(|b₁|+|b₂|)`), `completelyMultiplicative_restrictToNat`, `coprime_mul_restrictToNat` |
| `ElliottThresholdFamily` | `finalDil₁/₂`, `finalShift₁/₂`, **`det_final`**, `memberThreshold(_spec)`, **`familyThreshold`** |
| `ElliottMertensIterate` | `reciprocalPrimeInterval_add/_iter`, `primeDefect_le_add`, `mrtNonpretentious_descend_iter` |
| `ElliottWindowTruncate` | `elliottLogWindow_subset`, **`norm_le_truncated`**, `discarded_mass_le` |
| `ElliottIterSqrt` | `iterSqrt`, `iterSqrt_pow_le`, `lt_iterSqrt_succ_pow`, `iterSqrt_le`, `one_le_iterSqrt` |
| `ElliottTruncScale` | `truncScale`, `truncRatio`, `sqrt_le_truncRatio`, `truncScale_le_div`, **`lt_pow_trunc_low`**, `div_truncRatio_lt` |
| `ElliottTruncAssemble` | `log_iterSqrt_le`, **`discarded_mass_bound`**, **`X_le_thinScale_pow`**, `primeDefect_thinScale_eq` |

`ElliottRestricted.norm_restrictedCorr_le` was **narrowed** to residues with `d ∣ a₁n₀+b₁` (the
others are empty classes) — essential, since only there does `det_newShift` preserve the
determinant.  `ElliottLeafTwo.nonasymptotic_of_affineCM` was rewritten around the truncation.

## NEXT (lap 83) — the ε-budget assembly, and nothing else

Inside `exists_caseB_threshold` (`h : AffineCMLogElliott`, `k = j+2` given, `D₀` given):

1. `ε` → `D` from `exists_squarefull_tail` at `εt := ε/(8·(a₁+|b₁|+a₂+|b₂|+1)·(1+logRatioConst))`.
2. `T := ElliottThresholdFamily.familyThreshold h a₁ a₂ b₁ b₂ ε'' D` with
   `ε'' := ε/(8·(D e²)²·…)`; then `T' := max (max T (2*D*D)) 4`.
3. `A₀ := max` of: `3(T' + 2D₀ + 2·(k+2)·mrtDescentCost + 1)`, `D²(T'+4)`, and a size big enough
   that the additive constants `2(|b₁|+|b₂|) + 4D·D e² ·(1+…)` are `≤ (ε/4) log W`.
4. Chain: `ElliottZeroExt.norm_sub_posExt_le` → `ElliottRandomize.exists_cover_pair_ge`
   (at `Y = a₁X+|b₁|+a₂X+|b₂|`) → `ElliottStageStep.norm_le_of_reduced` on `U₁`
   → `norm_le_of_reduced_second` on `U₂` → `ElliottThresholdFamily.memberThreshold_spec`.
5. Non-pretentiousness chain: `hpret` (on `restrictToNat g₁`, at `A`, scale `X`)
   → `mrtNonpretentious_transfer` (cost `2D₀ + 2·(k+2)·(log2+2B)`, using
   `ElliottMertensIterate.primeDefect_le_add` + `reciprocalPrimeInterval_iter` to pass from
   `Σ_{L''} ≤ D₀` to `Σ_X`)
   → prime-values equality `cmExt u₁ p = u₁ p` (needs a one-line lemma: `MRTNonpretentious`
   depends only on the prime values)
   → `mrtNonpretentious_descend_iter` from `X` down to `X₂ ≈ X/(d₁d₂)`
   (`X ≤ X₂²` from `A₀ ≥ D²(T'+4)`; `X₂ ≥ T'` likewise).

## Traps recorded this session — do NOT re-derive

1. **`omega` cannot see `X / W` when `W` is a variable.**  `1 ≤ X/W+1` needs
   `Nat.le_add_left 1 _`, not `omega`.  (Same family as last session's trap 4.)
2. **`omega` cannot see `W₀ * W₀`.**  Feed it `Nat.le_mul_of_pos_left` facts first.
3. `Nat.le_sqrt'` is stated with `^2`, not `*`: `rw [pow_two]` before supplying the product form.
4. `Nat.sqrt_le'` is already `sqrt W ^ 2 ≤ W` (no `pow_two` needed); `Nat.lt_succ_sqrt'` likewise.
5. `Nat.mul_div_le'` and `Nat.lt_div_add_one_mul_self` **do not exist**; use
   `Nat.div_mul_le_self` and `ElliottCaseAThin.lt_mul_div_add_one`.
6. A `filter` predicate `fun n₀ => (d:ℤ) ∣ (a₁:ℤ)*n₀ + b₁` elaborates `n₀ : ℤ`; annotate
   `fun n₀ : ℕ => … (n₀ : ℤ) …`.
7. `Nat.primesLE 0 = Nat.primesLE 1 = ∅` — provable by `decide`, not by `simp`.
8. `gcongr <;> [t1; t2; t3]` overshoots when `gcongr` discharges side goals; use an explicit
   `mul_le_mul` chain.
9. `linarith` will not multiply `ε` by `log W`; supply `0 ≤ (ε/8) * log W` by `positivity` first.

## Fidelity note (unchanged, do not lose)

`Erdos67b.IsMultiplicativeOnPositiveInt` has **no coprimality hypothesis** — it is *complete*
multiplicativity, so the dependency's `NonasymptoticLogElliott` is Tao 2016 Thm 1.3 restricted to
completely multiplicative `g₁,g₂`.  The kickoff ratifies that `Prop` as the target, so the target
stands, but `STATUS.md` must describe the headline as the CM case.  The leaf-2 route never uses
complete multiplicativity of the `gᵢ`, so a genuinely general `NonasymptoticLogElliottMult` is a
cheap stretch goal once the headline lands.
