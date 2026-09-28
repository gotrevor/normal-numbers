import NormalNumbers.TwoPointKataiFree
import Mathlib.NumberTheory.Primorial

/-!
# The small-prime half of leaf (D), UNCONDITIONALLY, at a growing cut

`SwingC1Pair.lean` proves the periodic-model form of the Daboussi–Kátai input
(`periodMean_pair_tendsto_zero`): the mean of `e(t(θ^{(P)}_{pn} − θ^{(P)}_{qn}))` over **one full
primorial period** tends to `0` as the prime cut `P → ∞`.  What it does not give is a statement
about the *natural-density* mean, because the period `Q_P = Π_{r≤P} r` grows like `e^P`, so at a
fixed `P` the density mean converges to the nonzero constant `Π_{r≤P} pairLocalFactor`.

This file closes that half.  Take the cut to grow with `R`, slowly enough that the period stays
below `√R`:

    primeCut R = ⌊log₄ R⌋ / 2,      so   primorialLe (primeCut R) ≤ 4^{primeCut R} ≤ √R

(`Nat.primorial_le_four_pow`).  A periodic function's Cesàro mean is its period mean to within
`2Q/N` (`norm_fullMean_sub_periodMean_le`), and `2Q/R ≤ 2/Q → 0`.  Hence

**`truncPair_fullMean_tendsto_zero`** — for every `b ≥ 2`, `t ≠ 0` and distinct primes `p ≠ q`,

    E_{n<R} e(t·(θ^{(primeCut R)}_{pn} − θ^{(primeCut R)}_{qn})) → 0,

with NO hypothesis.  This is the "small primes alone" horn of leaf (D), and it is a statement about
the honest natural-density mean, not about a periodic model.

**What is left, named exactly.**  `PairDecoupleGrowing` below is the defect between the full pair
mean and its `primeCut R` truncation.  `pairDecorr_of_pairDecoupleGrowing` shows the crux follows
from that defect alone — the model term is no longer needed at all, since it is now a theorem.  And
the defect is genuinely a *cancellation* statement, not an `L¹` one: with `P ≍ log R` the large-prime
remainder has `E_{n<R} |pairRemainder| ≍ log(log R / log P) ≍ log log R → ∞`, so no triangle
inequality can close it.  That is the precise shape of the parity-type obstruction at leaf (D), and
it is why the alternative shift-cut route (`MultiElliott`, `TwoPointKataiFree.lean`) pays for its
`o(1)` tail with a `4K`-point correlation instead.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-! ### The growing cut -/

/-- The prime cut that grows with `R` while keeping the primorial period below `√R`. -/
def primeCut (R : ℕ) : ℕ := Nat.log 4 R / 2

lemma primorialLe_eq_primorial (P : ℕ) : primorialLe P = primorial P := rfl

lemma primorialLe_le_four_pow (P : ℕ) : primorialLe P ≤ 4 ^ P := by
  rw [primorialLe_eq_primorial]
  exact primorial_le_four_pow P

/-- The period stays below `√R`. -/
lemma four_pow_primeCut_sq_le {R : ℕ} (hR : R ≠ 0) : (4 ^ primeCut R) ^ 2 ≤ R := by
  have h1 : (4 : ℕ) ^ primeCut R ^ 1 ^ 1 = 4 ^ primeCut R := by ring_nf
  have h2 : ((4 : ℕ) ^ primeCut R) ^ 2 = 4 ^ (primeCut R * 2) := (pow_mul 4 (primeCut R) 2).symm
  rw [h2]
  refine le_trans (Nat.pow_le_pow_right (by norm_num) ?_) (Nat.pow_log_le_self 4 hR)
  simp only [primeCut]
  omega

lemma tendsto_primeCut : Tendsto primeCut atTop atTop := by
  refine tendsto_atTop.mpr fun k => ?_
  filter_upwards [Filter.eventually_ge_atTop (4 ^ (2 * k))] with R hR
  have h1 : 2 * k ≤ Nat.log 4 R := Nat.le_log_of_pow_le (by norm_num) hR
  simp only [primeCut]
  omega

lemma tendsto_period_over_R :
    Tendsto (fun R : ℕ => 2 * (primorialLe (primeCut R) : ℝ) / (R : ℝ)) atTop (𝓝 0) := by
  have hQ : Tendsto (fun R : ℕ => ((4 : ℝ) ^ (primeCut R))) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 4)).comp tendsto_primeCut
  have hinv : Tendsto (fun R : ℕ => 2 / ((4 : ℝ) ^ (primeCut R))) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using hQ.inv_tendsto_atTop.const_mul (2 : ℝ)
  refine squeeze_zero' ?_ ?_ hinv
  · filter_upwards [Filter.eventually_gt_atTop 0] with R hR
    have : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
    positivity
  · filter_upwards [Filter.eventually_gt_atTop 0] with R hR
    have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
    have hQpos : (0 : ℝ) < (4 : ℝ) ^ (primeCut R) := by positivity
    have hsq : ((4 : ℝ) ^ (primeCut R)) ^ 2 ≤ (R : ℝ) := by
      have h := four_pow_primeCut_sq_le (R := R) (by omega)
      have h2 : (((4 ^ primeCut R : ℕ) : ℝ)) ^ 2 ≤ (R : ℝ) := by exact_mod_cast h
      push_cast at h2
      exact h2
    have hprim : ((primorialLe (primeCut R) : ℕ) : ℝ) ≤ (4 : ℝ) ^ (primeCut R) := by
      have h := primorialLe_le_four_pow (primeCut R)
      have h2 : ((primorialLe (primeCut R) : ℕ) : ℝ) ≤ ((4 ^ primeCut R : ℕ) : ℝ) := by
        exact_mod_cast h
      push_cast at h2
      exact h2
    rw [div_le_div_iff₀ hRpos hQpos]
    nlinarith [hprim, hsq, hQpos, hRpos]

/-! ### The small-prime half, unconditionally -/

/-- **THE SMALL-PRIME HALF OF LEAF (D).**  At the growing cut `primeCut R` the truncated pair
phase has natural-density mean tending to `0`, with no hypothesis.  The period mean is
`Π_{r ≤ primeCut R} pairLocalFactor → 0` (Mertens plus the separation bound) and the Cesàro/period
defect is `≤ 2 Q/R ≤ 2/Q → 0`. -/
theorem truncPair_fullMean_tendsto_zero (b : ℕ) (hb : 2 ≤ b) (t : ℝ) (ht : t ≠ 0)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Tendsto (fun R : ℕ =>
        ‖fullMean (fun n => phase (t * truncPairTail b (primeCut R) p q n)) R‖) atTop (𝓝 0) := by
  have hmodel : Tendsto (fun R : ℕ => ‖periodMean
      (fun n => phase (t * truncPairTail b (primeCut R) p q n))
      (primorialLe (primeCut R))‖) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (periodMean_pair_tendsto_zero b hb t ht p q hp hq hpq).comp tendsto_primeCut
  have hmaj : Tendsto (fun R : ℕ =>
      2 * (primorialLe (primeCut R) : ℝ) / (R : ℝ)
        + ‖periodMean (fun n => phase (t * truncPairTail b (primeCut R) p q n))
            (primorialLe (primeCut R))‖) atTop (𝓝 0) := by
    simpa using tendsto_period_over_R.add hmodel
  refine squeeze_zero' (Filter.Eventually.of_forall fun R => norm_nonneg _) ?_ hmaj
  filter_upwards [Filter.eventually_gt_atTop 0] with R hR
  set P := primeCut R with hP
  set g : ℕ → ℂ := fun n => phase (t * truncPairTail b P p q n) with hg
  have hper : ∀ n, g (n + primorialLe P) = g n := by
    intro n
    have := truncPairTail_add_mul_primorial b P p q n 1
    rw [one_mul] at this
    simp only [hg, this]
  have hgnorm : ∀ n, ‖g n‖ ≤ 1 := fun n => le_of_eq (norm_phase _)
  have hdef := norm_fullMean_sub_periodMean_le g (primorialLe P) R (primorialLe_pos P) hR
    hper hgnorm
  calc ‖fullMean g R‖
      ≤ ‖fullMean g R - periodMean g (primorialLe P)‖ + ‖periodMean g (primorialLe P)‖ := by
        simpa [add_comm] using
          norm_le_norm_add_norm_sub' (fullMean g R) (periodMean g (primorialLe P))
    _ ≤ 2 * (primorialLe P : ℝ) / (R : ℝ) + ‖periodMean g (primorialLe P)‖ := by
        have h2 : (2 : ℝ) * (primorialLe P : ℝ) / (R : ℝ) = 2 * (primorialLe P : ℕ) / (R : ℕ) := by
          push_cast; ring
        linarith [hdef]

/-! ### What is left: the large-prime defect at the growing cut -/

/-- **LEAF (D), SHARPENED.**  The defect between the full pair mean and its `primeCut R`
truncation.  Note the cut is a single growing sequence, not a family of fixed cuts: the model term
that `PairDecouple` still had to cancel against is now a theorem
(`truncPair_fullMean_tendsto_zero`), so this defect is all that remains. -/
def PairDecoupleGrowing (b p q : ℕ) (t : ℝ) : Prop :=
  Tendsto (fun R : ℕ => ‖fullMean (fun n => phase (t * pairTail b p q n)) R
      - fullMean (fun n => phase (t * truncPairTail b (primeCut R) p q n)) R‖) atTop (𝓝 0)

/-- **The crux from the sharpened leaf (D) alone.** -/
theorem pairDecorr_of_pairDecoupleGrowing (b : ℕ) (hb : 2 ≤ b) (t : ℝ) (ht : t ≠ 0)
    (h : ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → PairDecoupleGrowing b p q t) :
    PairDecorr b t := by
  intro p q hp hq hpq
  have hfull : Tendsto (fun R : ℕ =>
      ‖fullMean (fun n => phase (t * pairTail b p q n)) R‖) atTop (𝓝 0) := by
    have hmaj := (h p q hp hq hpq).add (truncPair_fullMean_tendsto_zero b hb t ht p q hp hq hpq)
    rw [add_zero] at hmaj
    refine squeeze_zero' (Filter.Eventually.of_forall fun R => norm_nonneg _)
      (Filter.Eventually.of_forall fun R => ?_) hmaj
    simpa [add_comm] using
      norm_le_norm_add_norm_sub' (fullMean (fun n => phase (t * pairTail b p q n)) R)
        (fullMean (fun n => phase (t * truncPairTail b (primeCut R) p q n)) R)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine hfull.congr fun R => ?_
  simp only [pairTail]

/-- **`ConjC1` from Delange plus the sharpened leaf (D).** -/
theorem conjC1_of_delange_pairDecoupleGrowing
    (hD : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) → DelangeMean (((m : ℤ) : ℝ) / b))
    (hG : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
      ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → PairDecoupleGrowing b p q (((m : ℤ) : ℝ) / b)) :
    ConjC1 := by
  refine conjC1_of_delange_pairDecorr hD (fun b hb m hm hdvd => ?_)
  have hbpos : (0 : ℝ) < (b : ℝ) := by
    have : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  have hmR : ((m : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
  exact pairDecorr_of_pairDecoupleGrowing b (by omega) (((m : ℤ) : ℝ) / b)
    (div_ne_zero hmR (ne_of_gt hbpos)) (hG b hb m hm hdvd)

end NormalNumbers.CastingOut
