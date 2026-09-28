import NormalNumbers.ElliottTwistedGraph
import NormalNumbers.ElliottLadder

/-!
# The graph edge for a *general* pair of affine forms — the dilation `a` is a spectator

This file removes the detour of `NormalNumbers.ElliottDilatedSlice`.

Lap 15 factored the crux `NormalNumbers.ElliottLadder.DilatedCMLogElliott` through the
multiples-of-`a` **slice** rung, on the grounds that the graph dilation `m ↦ p m` preserves the
residue class `0`.  That is true but it is the wrong bookkeeping: it forces the extra indicator
`a ∣ m` through the whole Fourier layer, and (worse) the translation by `p c₁` that centres the
observable on `f₁` turns the condition `a ∣ m` into `a ∣ n - p c₁`, which depends on `p mod a`
and therefore does *not* factor out of the prime sum.  Recorded as refuted; do not re-derive.

The right bookkeeping is already in `NormalNumbers.ElliottLadder.pairObservable_dilation_twisted`:

```
conj (f₁ q * f₂ q) * pairObservable f₁ f₂ a (q*c₁) (q*c₂) (q*n) = pairObservable f₁ f₂ a c₁ c₂ n
```

The graph step `n ↦ q n` sends the *pair of forms* `(a n + c₁, a n + c₂)` to
`(a (q n) + q c₁, a (q n) + q c₂) = q · (a n + c₁, a n + c₂)`: **both shifts dilate with `q`,
exactly as `h ↦ q h` does in the proved pure-shift rung, and the common dilation `a` rides along
untouched.**  There is no divisibility side condition at all, and no slice.

So the edge observable for the general crux is

```
affineTwistedObservable w f₁ f₂ a q c₁ c₂ n = if q ∣ n then w q * pairObservable f₁ f₂ a (q c₁) (q c₂) n else 0
```

and this file proves the lower-bound engine for it: **every translated edge has mean `C/q`**, with
the dependency's verbatim error terms, where `C` is the correlation the crux has to bound.  This is
the exact analogue of `NormalNumbers.ElliottTwistedGraph.norm_logProb_pairTwistedDivisible_sub_correlation_le`
(which is the case `a = 1`, `c₁ = 0`, `c₂ = h`), and it is what
`ElliottTwistedGraphCorrelation`/`Bounded` consume.

What is still open after this file is *only* the Fourier layer: in block coordinates the edge is
`b (a*j + q*c₁) * c (a*j + q*c₂)`, i.e. the block index is **dilated by `a`**, where the proved case
has `b j * c (j + q h)`.  The Fourier identity survives:

```
∑_j b (a j + q c₁) c (a j + q c₂) e(t j / T)
  = ∑_{t₁, t₂ : a (t₁ + t₂) ≡ -t} b̂ t₁ ĉ t₂ · e ((t₁ c₁ + t₂ c₂) q / T),
```

so the phase in `q` is still a *single* frequency `s = t₁ c₁ + t₂ c₂`, and the twisted multiplier
`twistedPrimeGraphMultiplier` is evaluated at `s` exactly as before — the fourth-moment bound
`fourth_moment_twistedPrimeGraphMultiplier_le_energy` is untouched.  Only the bilinear pairing
`pairBlockPairing` has to be replaced by this `a`-dilated pairing.

Never edit dependency files; everything here is a new statement in `src/`.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace NormalNumbers.ElliottAffineGraph

open Erdos67b
open NormalNumbers.ElliottTwistedGraph
open NormalNumbers.ElliottLadder

noncomputable section

/-- The correlation the crux has to bound, under the finite logarithmic probability law.
Compare `NormalNumbers.ElliottTwistedGraph.pairLogCorrelation`, which is `a = 1`, `c₁ = 0`. -/
def affineLogCorrelation (L U : ℕ) (f₁ f₂ : ℕ → ℂ) (a : ℕ) (c₁ c₂ : ℤ) : ℂ :=
  logProbExpectation L U (pairObservable f₁ f₂ a c₁ c₂)

/-- The graph-edge observable for a general pair of affine forms with common dilation `a`.
Compare `NormalNumbers.ElliottTwistedGraph.pairTwistedDivisibleObservable`, which is the case
`a = 1`, `c₁ = 0`, `c₂ = h` (there the surviving shift `q*h` is written into `f₂`'s argument). -/
def affineTwistedObservable (w : ℕ → ℂ) (f₁ f₂ : ℕ → ℂ) (a q : ℕ) (c₁ c₂ : ℤ) (n : ℕ) : ℂ :=
  if q ∣ n then w q * pairObservable f₁ f₂ a ((q : ℤ) * c₁) ((q : ℤ) * c₂) n else 0

theorem norm_affineTwistedObservable_le_one {w f₁ f₂ : ℕ → ℂ} {q : ℕ}
    (hw : ‖w q‖ ≤ 1)
    (h₁ : ∀ n : ℕ, 0 < n → ‖f₁ n‖ ≤ 1) (h₂ : ∀ n : ℕ, 0 < n → ‖f₂ n‖ ≤ 1)
    (a : ℕ) (c₁ c₂ : ℤ) (n : ℕ) :
    ‖affineTwistedObservable w f₁ f₂ a q c₁ c₂ n‖ ≤ 1 := by
  unfold affineTwistedObservable
  split_ifs
  · rw [norm_mul]
    exact mul_le_one₀ hw (norm_nonneg _)
      (norm_pairObservable_le_one h₁ h₂ a ((q : ℤ) * c₁) ((q : ℤ) * c₂) n)
  · norm_num

/-- **Each translated general-affine graph edge has mean `C/q`**, with the dependency's explicit
errors.  The common dilation `a` never appears in the estimate: it is a spectator.

This is the general-forms replacement for
`NormalNumbers.ElliottTwistedGraph.norm_logProb_pairTwistedDivisible_sub_correlation_le`; the only
change in the proof is that `pair_dilation_twisted` is replaced by
`NormalNumbers.ElliottLadder.pairObservable_dilation_twisted`. -/
theorem norm_logProb_affineTwistedObservable_sub_correlation_le
    {L U q : ℕ} (hL : 0 < L) (hLU : L ≤ U) (hq : 0 < q)
    {f₁ f₂ : ℕ → ℂ}
    (hm₁ : IsCompletelyMultiplicativeOnPositive f₁)
    (hm₂ : IsCompletelyMultiplicativeOnPositive f₂)
    (hu₁ : ∀ n : ℕ, 0 < n → ‖f₁ n‖ = 1) (hu₂ : ∀ n : ℕ, 0 < n → ‖f₂ n‖ = 1)
    (a : ℕ) (c₁ c₂ : ℤ) (j : ℕ) :
    ‖logProbExpectation L U
        (fun n ↦ affineTwistedObservable (pairTwist f₁ f₂) f₁ f₂ a q c₁ c₂ (n + j)) -
      (q : ℝ)⁻¹ • affineLogCorrelation L U f₁ f₂ a c₁ c₂‖ ≤
        2 / (logProbMassNN L U : ℝ) +
          2 * j / ((L : ℝ) * logProbMassNN L U) := by
  have hM : (0 : ℝ) < logProbMassNN L U := by
    exact_mod_cast logProbMassNN_pos hL hLU
  have hqr : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have htw : ‖pairTwist f₁ f₂ q‖ = 1 := norm_pairTwist hu₁ hu₂ hq
  have hu₁' : ∀ n : ℕ, 0 < n → ‖f₁ n‖ ≤ 1 := fun n hn ↦ (hu₁ n hn).le
  have hu₂' : ∀ n : ℕ, 0 < n → ‖f₂ n‖ ≤ 1 := fun n hn ↦ (hu₂ n hn).le
  -- the dilation estimate, applied to the twisted general-affine observable
  have hdil := norm_logProbExpectation_dilation_sub_le hL hLU hq
    (fun n ↦ pairTwist f₁ f₂ q * pairObservable f₁ f₂ a ((q : ℤ) * c₁) ((q : ℤ) * c₂) n)
    (B := 1) zero_le_one (by
      intro n _
      rw [norm_mul, htw, one_mul]
      exact norm_pairObservable_le_one hu₁' hu₂' _ _ _ n)
  have heq : logProbExpectation L U
      (fun n ↦ pairTwist f₁ f₂ q *
        pairObservable f₁ f₂ a ((q : ℤ) * c₁) ((q : ℤ) * c₂) (q * n)) =
      affineLogCorrelation L U f₁ f₂ a c₁ c₂ := by
    apply Finset.sum_congr rfl
    intro n _
    congr 1
    exact pairObservable_dilation_twisted hm₁ hm₂ hu₁ hu₂ hq c₁ c₂ n
  rw [heq] at hdil
  change ‖affineLogCorrelation L U f₁ f₂ a c₁ c₂ -
    (q : ℝ) • logProbExpectation L U
      (affineTwistedObservable (pairTwist f₁ f₂) f₁ f₂ a q c₁ c₂)‖ ≤ _ at hdil
  have hbase : ‖logProbExpectation L U
      (affineTwistedObservable (pairTwist f₁ f₂) f₁ f₂ a q c₁ c₂) -
      (q : ℝ)⁻¹ • affineLogCorrelation L U f₁ f₂ a c₁ c₂‖ ≤ 2 / (logProbMassNN L U : ℝ) := by
    have hcancel : (q : ℝ)⁻¹ • (affineLogCorrelation L U f₁ f₂ a c₁ c₂ -
        (q : ℝ) • logProbExpectation L U
          (affineTwistedObservable (pairTwist f₁ f₂) f₁ f₂ a q c₁ c₂)) =
        (q : ℝ)⁻¹ • affineLogCorrelation L U f₁ f₂ a c₁ c₂ -
          logProbExpectation L U
            (affineTwistedObservable (pairTwist f₁ f₂) f₁ f₂ a q c₁ c₂) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hqr.ne', one_smul]
    calc
      _ = ‖(q : ℝ)⁻¹ • (affineLogCorrelation L U f₁ f₂ a c₁ c₂ -
          (q : ℝ) • logProbExpectation L U
            (affineTwistedObservable (pairTwist f₁ f₂) f₁ f₂ a q c₁ c₂))‖ := by
        rw [hcancel, norm_sub_rev]
      _ = (q : ℝ)⁻¹ * ‖affineLogCorrelation L U f₁ f₂ a c₁ c₂ -
          (q : ℝ) • logProbExpectation L U
            (affineTwistedObservable (pairTwist f₁ f₂) f₁ f₂ a q c₁ c₂)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hqr.le)]
      _ ≤ (q : ℝ)⁻¹ * (2 * 1 * q / (logProbMassNN L U : ℝ)) :=
        mul_le_mul_of_nonneg_left hdil (inv_nonneg.mpr hqr.le)
      _ = 2 / (logProbMassNN L U : ℝ) := by field_simp
  have htranslate := norm_logProbExpectation_translate_sub_le hL hLU j
    (affineTwistedObservable (pairTwist f₁ f₂) f₁ f₂ a q c₁ c₂) (B := 1) zero_le_one
    (fun n _ ↦ norm_affineTwistedObservable_le_one (by rw [htw]) hu₁' hu₂' a c₁ c₂ n)
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (logProbExpectation L U
      (fun n ↦ affineTwistedObservable (pairTwist f₁ f₂) f₁ f₂ a q c₁ c₂ (n + j)))
    (logProbExpectation L U (affineTwistedObservable (pairTwist f₁ f₂) f₁ f₂ a q c₁ c₂))
    ((q : ℝ)⁻¹ • affineLogCorrelation L U f₁ f₂ a c₁ c₂)
  linarith

/-! ## The `a = 1` consistency check -/

/-- At `a = 1`, `c₁ = 0`, `c₂ = h` the general-affine observable is the proved one. -/
theorem affineTwistedObservable_one (w f₁ f₂ : ℕ → ℂ) (q : ℕ) (h n : ℕ) :
    affineTwistedObservable w f₁ f₂ 1 q 0 (h : ℤ) n =
      pairTwistedDivisibleObservable w (positiveIntExtension f₁ ∘ (Nat.cast : ℕ → ℤ))
        (positiveIntExtension f₂ ∘ (Nat.cast : ℕ → ℤ)) q h n := by
  unfold affineTwistedObservable pairTwistedDivisibleObservable pairObservable integerAffine
  split_ifs
  · simp only [Function.comp_apply]
    push_cast
    ring_nf
  · rfl

end

end NormalNumbers.ElliottAffineGraph
