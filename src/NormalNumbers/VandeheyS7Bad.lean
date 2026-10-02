/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Lattice

/-!
# S7-B2: a bad state costs conjugate height

Directive fact 2 (lap 30) names the one mechanism that defeats every soft treatment of the crux:
a **bad state**, whose image interval straddles a rational `1/k` at a scale far below `γ(E)`, has
`γ(s⁻¹E) ≈ 1/2` with `γ(E)` arbitrarily small.  Laps 48–49 handled bad states by *assuming*
`ImageTight` and paying for a floor `η` on the image width.  This module prices them instead, from
the arithmetic of `Φ`, and the price is paid in the second archimedean factor.

For the additive instance the state has entries in `ℤ[φ]` (`VandeheyS7Lattice`), so each endpoint
of its image interval is a quotient `β/δ` of `ℤ[φ]`-numbers.

## The theorems

* `conj_comb_ge_of_close` — if the endpoint `β/δ` lies within `δ₀` of the rational `p/q`, the
  conjugate combination satisfies `|qβ' − pδ'| ≥ 1/(q·|δ|·δ₀)`.
* `conjHeight_ge_of_bad` — in the form the route wants: for an endpoint in `[0,1]` and a scale
  `δ₀ ≤ 1`, the **conjugate height** `max(|β'|, |δ'|)` of the state's entries is at least
  `1/(3q²·|δ|·δ₀)`.  Badness at scale `δ₀` against a rational of denominator `q` forces the state
  to sit that far out in the conjugate factor — at the *reciprocal* rate in `δ₀`.

## What this buys, and what it does not

It does **not** by itself bound the frequency of bad times: the conjugate component of `s_n` grows
like `q_ℓ(y)·q_n(x) = e^{Θ(n)}`, so the bound forbids scale-`δ₀` badness only for `n ≲ log(1/δ₀)`.
What it does is convert the bad half of the crux from an ergodic statement about a moving target
(refuted as soft by `not_gappedHitPrinciple`) into a **lattice-point count**: how many `n < N`
admit a coincidence between the `SL₂(ℤ[φ])`-point `s_n` and a rational of denominator `q ≲ 1/δ₀`.
That is a Hilbert-modular counting problem — hard, but well posed, and unlike the self-joining
wall it is the kind of statement a quantitative argument can reach.

## Guard rule

Content locator: the `1/(q·|δ|·δ₀)` is sharp in shape — it is `dist_rat_ge` with nothing thrown
away, and the only inequality spent in `conjHeight_ge_of_bad` is the crude `|p| ≤ 2q`, which costs
the factor `3`.  Degenerate cases: `δ₀ ≥ 1` makes the conclusion weaker than the trivial
`|δ'| ≥ 1/|δ|` for `δ` a unit, so the content is at small `δ₀`; and a rational endpoint
(`β/δ = p/q`) is excluded, as it must be — there the state is *exactly* bad and no conjugate
bound can hold.
-/

namespace NormalNumbers.VandeheyS7

open NormalNumbers

/-- **The conjugate combination is large.**  Rearranged `zquot_sub_rat_ge`. -/
theorem conj_comb_ge_of_close {b1 b2 d1 d2 p q : ℤ} (hq : 0 < q) (hd : zval d1 d2 ≠ 0)
    (hne : zval b1 b2 / zval d1 d2 ≠ (p : ℝ) / (q : ℝ)) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hclose : |zval b1 b2 / zval d1 d2 - (p : ℝ) / (q : ℝ)| ≤ δ₀) :
    1 / ((q : ℝ) * |zval d1 d2| * δ₀)
      ≤ |(q : ℝ) * zconj b1 b2 - (p : ℝ) * zconj d1 d2| := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hdpos : 0 < |zval d1 d2| := abs_pos.2 hd
  have key := zquot_sub_rat_ge hq hd hne
  have hnz : ¬ (q * b1 - p * d1 = 0 ∧ q * b2 - p * d2 = 0) := by
    rintro ⟨h1, h2⟩
    apply hne
    have hz : (q : ℝ) * zval b1 b2 - (p : ℝ) * zval d1 d2 = 0 := by
      rw [← zval_lin, h1, h2]; simp [zval]
    field_simp
    linarith [hz]
  have hcpos : 0 < |(q : ℝ) * zconj b1 b2 - (p : ℝ) * zconj d1 d2| := by
    rw [← zconj_lin]; exact abs_pos.2 (zconj_ne_zero hnz)
  have h1 : 1 / ((q : ℝ) * |zval d1 d2| * |(q : ℝ) * zconj b1 b2 - (p : ℝ) * zconj d1 d2|)
      ≤ δ₀ := le_trans key hclose
  rw [div_le_iff₀ (by positivity)] at h1
  rw [div_le_iff₀ (by positivity)]
  nlinarith [h1, hcpos, hdpos, hq0]

/-- **Badness costs conjugate height.**  For a state endpoint `β/δ ∈ [0,1]` that sits within
`δ₀ ≤ 1` of a rational `p/q` (`q ≥ 1`), the conjugate height of the pair `(β, δ)` is at least
`1/(3q²·|δ|·δ₀)`. -/
theorem conjHeight_ge_of_bad {b1 b2 d1 d2 p q : ℤ} (hq : 0 < q) (hd : zval d1 d2 ≠ 0)
    (hne : zval b1 b2 / zval d1 d2 ≠ (p : ℝ) / (q : ℝ)) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (hδ1 : δ₀ ≤ 1)
    (hmem : zval b1 b2 / zval d1 d2 ∈ Set.Icc (0 : ℝ) 1)
    (hclose : |zval b1 b2 / zval d1 d2 - (p : ℝ) / (q : ℝ)| ≤ δ₀) :
    1 / (3 * (q : ℝ) ^ 2 * |zval d1 d2| * δ₀)
      ≤ max |zconj b1 b2| |zconj d1 d2| := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hdpos : 0 < |zval d1 d2| := abs_pos.2 hd
  have hcomb := conj_comb_ge_of_close hq hd hne hδ₀ hclose
  -- the rational is not far from `[0,1]`, so `|p| ≤ 2q`
  obtain ⟨hm0, hm1⟩ := hmem
  have habs : |(p : ℝ)| ≤ 2 * (q : ℝ) := by
    have h1 : |zval b1 b2 / zval d1 d2 - (p : ℝ) / (q : ℝ)| ≤ 1 := le_trans hclose hδ1
    have h2 : (p : ℝ) / (q : ℝ) ≤ 2 := by
      have := abs_le.1 h1
      linarith [this.1, this.2]
    have h3 : -1 ≤ (p : ℝ) / (q : ℝ) := by
      have := abs_le.1 h1
      linarith [this.1, this.2]
    rw [div_le_iff₀ hq0] at h2
    rw [le_div_iff₀ hq0] at h3
    rw [abs_le]
    constructor <;> linarith
  set M := max |zconj b1 b2| |zconj d1 d2| with hM
  have hMb : |zconj b1 b2| ≤ M := le_max_left _ _
  have hMd : |zconj d1 d2| ≤ M := le_max_right _ _
  have hupper : |(q : ℝ) * zconj b1 b2 - (p : ℝ) * zconj d1 d2| ≤ 3 * (q : ℝ) * M := by
    calc |(q : ℝ) * zconj b1 b2 - (p : ℝ) * zconj d1 d2|
        ≤ |(q : ℝ) * zconj b1 b2| + |(p : ℝ) * zconj d1 d2| := abs_sub _ _
      _ = (q : ℝ) * |zconj b1 b2| + |(p : ℝ)| * |zconj d1 d2| := by
          rw [abs_mul, abs_mul, abs_of_pos hq0]
      _ ≤ (q : ℝ) * M + (2 * (q : ℝ)) * M := by
          have h1 : (q : ℝ) * |zconj b1 b2| ≤ (q : ℝ) * M := by nlinarith [hMb, hq0]
          have h2 : |(p : ℝ)| * |zconj d1 d2| ≤ (2 * (q : ℝ)) * M := by
            have hnn : 0 ≤ |zconj d1 d2| := abs_nonneg _
            have hMn : 0 ≤ M := le_trans hnn hMd
            nlinarith [habs, hMd, hnn, hMn]
          linarith
      _ = 3 * (q : ℝ) * M := by ring
  have hchain : 1 / ((q : ℝ) * |zval d1 d2| * δ₀) ≤ 3 * (q : ℝ) * M := le_trans hcomb hupper
  rw [div_le_iff₀ (by positivity)] at hchain
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hchain, hq0, hdpos, hδ₀]

section Audit

#print axioms conj_comb_ge_of_close
#print axioms conjHeight_ge_of_bad

end Audit

end NormalNumbers.VandeheyS7
