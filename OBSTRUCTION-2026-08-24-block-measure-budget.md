# ROUTE-DECISIVE OBSTRUCTION — B6 two-stream construction forces super-exponential blocks

**Status:** the B6 crux `schedA_block_linear` (`CFScheduleA.lean`), on which the
whole `exists_interleaved_affine_witness` / `exists_cfNormal_and_affine_cfNormal`
rests, is **not provable with the current two-stream cylinder-nesting
construction** — and the failure is DEEPER than the cfK-control issue the prior
directive targeted. It is a *measure-budget* obstruction. Recorded for attended
review (per DIRECTION's "if the route-decisive case fails, record precisely and
STOP for attended review — do not grind substitutes").

## The claim

In the two-stream recursion (`exists_freq_good_extend_affine_steer_uniform`),
each stage appends a freq-good steer block to each stream. The block length is
forced to grow **super-exponentially** in the stage index, so
`|chainApp w s| ≤ K₁·|w s| + K₂` (affine) — and even the weaker geometric
`|chainApp w s| ≤ ρ·|w s|` — is FALSE.

## The mechanism (verified against the code)

1. **Targets are full cylinder hulls.** The x-block target is
   `A = ψ⁻¹(hull(cfCylinder wz'))` where `(e',f') = hull` comes from
   `exists_Ioo_irrational_subset_cfCylinder wz'` (`CFScheduleA.lean:148`), which
   returns the interval-hull of the whole cylinder. So
   `width(A) ≈ 1/(2q·cfK(wz')²)`.

2. **Base is the current x-cylinder**, `width(cfCylinder wx) ≈ 1/(2·cfK(wx)²)`.
   Hence the RELATIVE target size
   `ρ := μ(A)/μ(cfCylinder wx) ≈ cfK(wx)²/(q·cfK(wz')²)`.

3. **The multiscale measure budget needs `n₁ ≳ 1/ρ`.** The freq-good selection
   (`exists_irrational_notMem_multiscale_cfBadZone_in_Ioo` +
   `gaussMeasure_multiscale_cfBadZone_le`) requires
   `NS.card · A₁ < μ(target)`, with `A₁ ∝ μ(cfCylinder wx)/(δ²·n₁)`. Dividing:
   `n₁ ≳ NS.card/(δ²·ρ)`. This is intrinsic — to GUARANTEE a freq-good point in a
   target of relative size `ρ`, the bad-zone mass (which scales with the WHOLE
   base cylinder) must drop below `μ(target)`, forcing `n₁ ≳ 1/ρ`.

4. **`z'` is one full block deeper than `wx`**, so
   `cfK(wz') ≈ cfK(wx)·e^{κ·|zblock|}` and `ρ ≈ e^{-2κ|zblock|}/q`.

5. **`|zblock| → ∞`** is mandatory (CF-normality of `z` needs block frequencies to
   converge; `schedEps s = 1/(s+1) → 0` alone forces `n₁(z) ∝ (s+1)² → ∞`).

6. Combining 3–5: `n₁(x) ≳ e^{2κ|zblock|}`, and since `|xblock| ≥ n₁(x)`, the
   blocks satisfy `|xblock_s| ≳ e^{2κ·|zblock_s|}` with `|zblock_s|` itself already
   `≳ s²`. So `|block_s|` is **super-exponential**; `|block_s|/|word_s| → ∞`.

## Why it also breaks the frequency telescoping directly

`n₁_s` enters the per-block slack `C_s = 4√|blk_s| + 2|v| + n₁_s` (the first `n₁`
digits of the block are the freq-uncontrolled "burn-in": the multiscale only
controls scales `≥ n₁`). `chain_cf_digit_freq_tendsto_uniform`'s `hslack`
(`CFChainFreq.lean:567`) needs `∑_{i≤k}(C(s₀+i)+…) < ε·(w(s₀+k)).length`, i.e.
`C_s < ε·word(s)`. But `C_s ⊇ n₁_s ≈ e^{2κ|zblock|} ≫ word(s)`. So `hslack` fails
independently of the length bound. The geometric hypothesis in
`slack_telescoping` is not a proof artifact — it is exactly what fails.

## What is NOT the fix

- **cfK control** (this session's `exists_fib_threshold_linear_of_cfK`,
  `frac_mass_bad_extensions`, `cfKbadExtSet`, the combined selection lemma) fixes
  the RESOLUTION cost `log cfK = O(word)`. Those lemmas are correct and reusable,
  but they do NOT touch the measure-budget `n₁ ≳ 1/ρ` blowup. The obstruction
  survives them.
- **Digit-cap steering** (prior directive) is independently fatal (breaks
  normality / super-linear log-cfK) — see PENDING_WORK route-correction note.
- **Navigate-then-select** (short placement prefix into `A`, then freq-select in
  the sub-cylinder) does not help: the placement prefix has length `≈ log cfK(wz')
  ≈ |word|`, is freq-UNCONTROLLED, and is the MAJORITY of the block, so it dilutes
  freq-goodness. (This is the "uncontrolled placement prefix" the multiscale steer
  block was designed to avoid — and avoiding it is precisely what costs the
  exponential `n₁`.)

## Proposed pivot (for the attended review to ratify)

**Single-stream construction with pulled-back bad zones.** Build ONE stream `x`
directly, whose digit selection simultaneously avoids (a) the x-CF bad zones and
(b) the **ψ-pullback** of the z-CF bad zones, `ψ⁻¹(cfBadZone_z v n δ)`. Since `ψ`
is affine with bounded distortion, `μ(ψ⁻¹(S)) ≤ C_q·μ(S)` (Gauss density ratio
`≤ 2` on `[0,1]` composed with the `1/q` Lebesgue scaling), so the pulled-back bad
zones are still small. The selection target is then the FULL cylinder
`cfCylinder wx` (`ρ = 1`), the measure budget is `n₁ ∝ NS.card/δ²` (polynomial, no
`1/ρ` blowup), and blocks are polynomial/linear. No two-stream alternation, no
metric-scale matching, no exponentially-small targets.

Cost: a new `cfBadZone`-analogue for "`ψ(x)` has bad `v`-frequency", plus the
pullback-measure bound. This is a real redesign of the B6 engine, but it removes
the obstruction at its root. It reuses W1–W5 (Gauss bad-zone Chebyshev machinery)
essentially unchanged, applied to both `x` and `ψ(x)`.

## What stays banked

Both B5′ headlines remain proved and `#print axioms`-clean
(`[propext, Classical.choice, Quot.sound]`). This obstruction is entirely within
the (open, `sorry`-disclosed) B6 crux; nothing landed is affected.
