# HANDOFF — lap 125: the head is proved; the flanks are capped; item 4 is the only thing left

**Branch** `wip/g4-entropy`.  **HEAD** `4f06f96`.  Working tree **clean**.
`lake build` 🟢 **9021 jobs**.  `src/` carries **two** `sorry`s, both pre-expedition and off-path
(`PrimeLambertOscillation.phaseOscillation`, `MahlerDriftOne.exists_drift_one_background`).
**The active decomposition has no open leaf.**  Every new endpoint prints
`[propext, Classical.choice, Quot.sound]`.

## This lap's three commits

| commit | content |
|---|---|
| `eaa10e1` | `G4GridP0Lower.lean` — the **lower** bound on `P₀` and the level-to-level growth |
| `cbae128` | 🎯 `head_frac_tiny` — the last leaf of the mid-band decomposition, proved |
| `4f06f96` | `G4EntropyWCap.lean` — mid-band prefix control with **no upper hypothesis** |

### 1. The `P₀` hierarchy (`G4GridP0Lower.lean`)

Lap 123 named the leaf exactly: *what is missing is a LOWER bound on `P₀`*.  Its suggested route
(`Mprod = ∏_α d_α² ≥ gridQ^{2|Atom|}`) **cannot close it** — count logs:
`log Mprod(K+4) ≈ 2H(K+4)·log Q ≈ K^{6K}` against `log P₀(K) ≳ T(K)²·log Q ≈ K^{8K}`, because
`H(K)² = K^{4K}` dwarfs `H(K+4) = K^{2K+8}`.  The primorial fallback is worse (`K^{2K+10}`).
**Do not retry either.**

What works is that `freezeQ` counts **pairs**:

* `gridQ_le_dist` — two distinct atoms **on the same layer** have shifts differing by a *nonzero
  multiple of `Q`*: `shiftG_eq` gives `ρ_{α,j} = j + Q(jD₀ + proj B j α)`, and `ρ_injective`
  kills the zero case.  (Different layers give only `dist ≥ 1`, since `ρ ≡ j (mod Q)`.)
* `distProd_ge` / `P₀_ge_pow` — there are `T(H−1)` such ordered pairs, so `P₀ ≥ Q^{T(H−1)}`.
* `P₀_le_pow_gridQ` — the other side in the same base: `Dm ≤ Q²`, `2T+1 ≤ Q`, `K+N ≤ Q` turn
  `gridP₀Bound` into `Q^{7T²}`; the only factorial fact needed is `W! ≥ W(W−1)`.
* `exponent_growth` — `H(K+4) ≥ (K²+1)⁴·H K`, so `T'(H'−1) ≥ 7T²+3` with `K^{14}` of slack.
* **`P₀_growth`** — `256·(K+4)²·Dm(K+4)·H(K+4)·P₀ K ≤ P₀ (K+4)`.

### 2. `head_frac_tiny` (`G4EntropyWHead.lean`)

`wFloor (i+1) = 4·Dm_{i+1}·wTop i`, so the head's window count `≈ 60·Dm'·wTop i·|Atom'|/P₀'`
against a history `≥ (wTop i − wFloor i)/P₀_i·kk_i`: the scale `wTop i` cancels and what is left
is exactly `P₀_growth`, transported as `head_growth`.  `head_slack`
(`8·P₀·junk ≤ wTop i`, via `|Atom'| ≤ 2^{2(K+4)²} ≤ Xlo (KK i)` and `8·Xlo² ≤ 18·X ≤ wTop`) is
the additive term; `head_core` is the schedule-free real arithmetic.

### 3. The capped flanks (`G4EntropyWCap.lean`)

`abs_prefix_ratio_sub_le`'s hypothesis `cutHi i c ≤ wTop i` **genuinely fails for the top
`O(1/K)` of every band**: a consumed start is `c = 2·kIdx(n,α) ≤ 2n/d_α`, so
`cutHi i c ≈ wTop·(1+2/K)`.  Cap both flanks at the tile top:
`cutBot = min (cutLo) (wTop)`, `cutTop = min (cutHi) (wTop)`.  Both inclusions survive
(`pairsLe i c ⊆ bandWPairs i` already forces `z.1 < wTop i`); `card_flank_ratio_cap` is a case
split — below the cap the old statement, above it both flanks *are* `bandWtr i (wTop i)`.
**`abs_prefix_ratio_sub_le_cap`** is the mid-band estimate at *every* cutoff above the gate.

## Next lap — DIRECTION item 4, the squeeze and the endpoint (the ONLY thing left)

All ingredients are now in kernel.  For `fTW i ≤ n < fTW (i+1)` with `i ≥ 1`, put
`T := fTW i`, `s := n − T`, `a := s / kk i`, `G := winCount v T`, `D := winCount v n − G`:

1. **The mediant lemma** (schedule-free, in `ℝ`): `(r−e₁)T ≤ G ≤ (r+e₁)T` and
   `(r−e₂)s ≤ D ≤ (r+e₂)s` with `T > 0`, `s ≥ 0` ⇒ `|(G+D)/(T+s) − r| ≤ max e₁ e₂`.
2. **The band-`i` increment.**  `winCount_split` at `T`; `fullW_prefix_winCount_bounds x i a v`
   gives `fullGoodWPre i a ≤ D' ≤ fullGoodWPre i a + T + a·ℓ` at `n = T + a·kk i`, and the
   partial window costs `≤ kk i` (monotonicity of `winCount`, `winCount(n) − winCount(m) ≤ n−m`).
   `s ∈ [a·kk i, (a+1)·kk i)`.
3. **Gated branch** (`8·wFloor i ≤ cutLo i c`, `c := fnthW i (a−1)`, `a ≥ 1`): `aLe_fnthW` turns
   the read index into the cutoff (`aLe i c = a`), then `abs_prefix_ratio_sub_le_cap` gives
   `|fullGoodWPre i a/(a·F) − r| ≤ ε_i + 128/K_i` with `F = kk i − ℓ + 1`; `F/kk i = 1 − O(ℓ/kk)`
   converts it to `|D/s − r| ≤ ε_i + 128/K_i + O(ℓ/kk i)`.
4. **Ungated branch**: `aLe_le_headW` gives `a ≤ headW i`, and `head_frac_tiny` (stated at `i`,
   i.e. for `i ≥ 1`) gives `a·kk i·KK i ≤ T`, so `s ≤ T/KK i + kk i` and directly
   `|(G+D)/(T+s) − r| ≤ |G/T − r| + 2/KK i` (use `D ≤ s` and `G/(T+s) ≥ (G/T)(1−1/KK i)`).
5. **The limit.**  `|winCount v n/n − r| ≤ |winCount v (fTW i)/(fTW i) − r| + midErr i` with
   `i = fgrpW n`; `fgrpW n → ∞` (from `self_le_fTW` / `lt_fTW_fgrpW_succ`), the first term → 0 by
   **`tendsto_fullWRead_freq`** at `i−1`, and `midErr i → 0`.  Handle `n < fTW 1` by
   `eventually_ge_atTop`.
6. **The endpoint.**  `isNormalSequence_of_tendsto_winCount` (`G4EntropyOcc`) →
   `IsNormalSequence 2 (fullDigW (primeLambertAtBase 4))`; then `properDigits_fullDigW`,
   `fullRealW`, `Bridge.isNormal_realOfDigits` → **`IsNormal 2 fullRealW`**.
   (`properDigits_fullDigW` and `fullRealW` do **not** exist yet — write them; `fullDigW_lt` is
   there.  `exists_matchesAt_fullDigW` still needs a wide non-vacuity witness.)

## Hygiene (new this lap)

* `set G := gridOf K N hK` **blocks the `G.K = K` defeq**; `congrArg Prod.fst (G.ρ_injective h)`
  then fails to typecheck.  Write `(gridOf K N hK)` out instead of `set`.
* `Fin.sum_univ_eq_sum_range` will not `rw` in the `gridSum` shape — apply it as a term.
* `nlinarith` cannot do AM-GM in `ℕ` (`4ab ≤ (a+b)²`): cast that one step to `ℤ`, feed
  `sq_nonneg ((a:ℤ) − b)`, `exact_mod_cast` back.
* Proof-irrelevant `gridOf` arguments: use `gridOf_congr` (`subst`, then `rfl`); a bare
  `rw [KK_succ i]` hits the dependent proof argument and fails.
* `Finset.range_subset.2` wants `∀ x < K, x ∈ range K'` in this mathlib — use an inline
  `intro/simp/omega` instead.

## Do not re-derive

`DIRECTION.md`'s CURRENT DIRECTIVE (review lap 122) still forbids re-litigating the scale gap or
the head obstruction, lowering the band floor, adding joint-ladder rungs or sharpening constants,
and touching `fullReal`/`fullPos`/`bandT`.  `density_antitone` stays withdrawn.  **`Mprod` and
the primorial as routes to a `P₀` lower bound are refuted above (§1) — do not retry them.**
