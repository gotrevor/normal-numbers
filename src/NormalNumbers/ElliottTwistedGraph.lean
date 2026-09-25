import ErdosProblems.Erdos67b.PrimeGraphRestriction

/-!
# The phase-twisted prime graph

`NormalNumbers.ElliottLadder.pairObservable_dilation_twisted` isolates the one new device the
two-function case of Tao's two-point log-Elliott theorem needs: each prime `p` of the prime graph
must carry the **known** unimodular weight `conj (f₁(p) f₂(p))`, which restores the exact dilation
identity that `Erdos67b.unit_pair_dilation` provides when `f₂ = conj f₁`.

This file carries out the weighting on the *Fourier* side of the graph argument and settles the
route-decisive question: **does the additive-energy input survive a per-prime unimodular weight?**
It does, with no loss at all in the constant.  The reason is structural: the dependency's
fourth-moment bound `Erdos67b.fourth_moment_weightedExponentialSum_le_energy` is already stated for
an *arbitrary* complex weight `w : ℕ → ℂ` subject only to `‖w x‖ ≤ B`, so folding a unimodular phase
into the reciprocal-prime coefficient changes nothing.

Results, all proved here:

* `twistedPrimeGraphMean_eq_fourier` — the exact Fourier pairing identity of
  `Erdos67b.primeGraphMean_eq_fourier` holds verbatim for the twisted mean, with the twist living
  entirely inside the multiplier.  So the weight enters the upper-bound chain *only* through
  `twistedPrimeGraphMultiplier`.
* `fourth_moment_twistedPrimeGraphMultiplier_le_energy` — the twisted multiplier obeys **the same**
  fourth-moment/additive-energy bound `T · #(additiveQuadruples s) · B⁴` as the untwisted one.
* `norm_twistedPrimeGraphMultiplier_le` — the trivial bound is also unchanged.
* `twistedPrimeGraphMean_one`, `twistedPrimeGraphMultiplier_one` — the untwisted case is the
  instance `w = 1`, so nothing is lost relative to the proved development.

Never edit dependency files; everything here is a new statement in `src/`.
-/

open scoped BigOperators ComplexConjugate
open Finset
open Erdos438.Fourier

namespace NormalNumbers.ElliottTwistedGraph

open Erdos67b

noncomputable section

/-! ## Definitions -/

/-- The prime graph mean with a weight `w p` attached to each prime of the graph.  Compare
`Erdos67b.primeGraphMean_eq_sum`: the case `w = 1` is the mean of the proved development. -/
def twistedPrimeGraphMean {H : ℕ} (w : ℕ → ℂ) (b : Fin H → ℂ) (h : ℕ) (s : Finset ℕ) : ℂ :=
  ∑ p ∈ s, w p * (p : ℂ)⁻¹ * ∑ j : Fin H, primeGraphEdge b p h j

/-- The Fourier multiplier of the twisted prime graph.  Compare
`Erdos67b.primeGraphMultiplier`. -/
def twistedPrimeGraphMultiplier (T h : ℕ) (s : Finset ℕ) (w : ℕ → ℂ) (t : ℤ) : ℂ :=
  ∑ p ∈ s, w p * (p : ℂ)⁻¹ * phase T t (p * h : ℕ)

@[simp]
theorem twistedPrimeGraphMultiplier_one (T h : ℕ) (s : Finset ℕ) (t : ℤ) :
    twistedPrimeGraphMultiplier T h s (fun _ ↦ 1) t = primeGraphMultiplier T h s t := by
  simp only [twistedPrimeGraphMultiplier, primeGraphMultiplier, one_mul]

@[simp]
theorem twistedPrimeGraphMean_one {H : ℕ} (b : Fin H → ℂ) (h : ℕ) (s : Finset ℕ)
    (hs : s ⊆ Nat.primesLE H) :
    twistedPrimeGraphMean (fun _ ↦ 1) b h s = primeGraphMean b h s := by
  rw [primeGraphMean_eq_sum b h s hs, twistedPrimeGraphMean]
  exact Finset.sum_congr rfl fun p _ ↦ by rw [one_mul]

/-! ## The weight enters only through the multiplier -/

/-- **The exact Fourier pairing identity survives the twist.**  Compare
`Erdos67b.primeGraphMean_eq_fourier`: the block transform `blockFourier` is untouched, and the
weight appears only inside the multiplier.  Consequently every upper bound for the twisted graph
mean reduces to a bound for `twistedPrimeGraphMultiplier`. -/
theorem twistedPrimeGraphMean_eq_fourier {H T : ℕ} [NeZero T]
    (w : ℕ → ℂ) (b : Fin H → ℂ) (h : ℕ) (s : Finset ℕ)
    (hT : ∀ p ∈ s, H + p * h ≤ T) :
    twistedPrimeGraphMean w b h s = (T : ℂ)⁻¹ * ∑ t ∈ Finset.range T,
      (‖blockFourier T b (t : ℤ)‖ : ℂ) ^ 2 * twistedPrimeGraphMultiplier T h s w (t : ℤ) := by
  have hT0 : (T : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne T)
  have hsum : (∑ t ∈ Finset.range T,
      (‖blockFourier T b (t : ℤ)‖ : ℂ) ^ 2 * twistedPrimeGraphMultiplier T h s w (t : ℤ)) =
        (T : ℂ) * twistedPrimeGraphMean w b h s := by
    simp only [twistedPrimeGraphMultiplier, Finset.mul_sum]
    rw [Finset.sum_comm, twistedPrimeGraphMean, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    calc
      _ = w p * (p : ℂ)⁻¹ * ∑ t ∈ Finset.range T,
          (‖blockFourier T b (t : ℤ)‖ : ℂ) ^ 2 * phase T (t : ℤ) (p * h : ℕ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ ↦ by ring
      _ = _ := by rw [sum_blockFourier_norm_sq_mul_phase b p h (hT p hp)]; ring
  rw [hsum, ← mul_assoc, inv_mul_cancel₀ hT0, one_mul]

/-! ## The twisted multiplier: trivial bound and fourth moment -/

theorem norm_twistedPrimeGraphMultiplier_le (T h : ℕ) (s : Finset ℕ) {w : ℕ → ℂ}
    (hw : ∀ p ∈ s, ‖w p‖ ≤ 1) (t : ℤ) :
    ‖twistedPrimeGraphMultiplier T h s w t‖ ≤ ∑ p ∈ s, (p : ℝ)⁻¹ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp ↦ ?_)
  rw [norm_mul, norm_mul, norm_phase, mul_one, norm_inv, Complex.norm_natCast]
  exact mul_le_of_le_one_left (by positivity) (hw p hp)

/-- The twisted multiplier is a weighted exponential sum whose coefficient is the reciprocal prime
scaled by the phase.  Compare `Erdos67b.primeGraphMultiplier_eq_weightedExponentialSum`. -/
theorem twistedPrimeGraphMultiplier_eq_weightedExponentialSum
    (T : ℕ) {h : ℕ} (hh : 0 < h) (s : Finset ℕ) (w : ℕ → ℂ) (t : ℤ) :
    twistedPrimeGraphMultiplier T h s w t =
      weightedExponentialSum T (s.image fun p ↦ p * h)
        (fun m ↦ w (m / h) * ((m / h : ℕ) : ℂ)⁻¹) t := by
  classical
  rw [weightedExponentialSum, Finset.sum_image]
  · simp only [Nat.mul_div_left _ hh]
    rfl
  · intro p _ q _ heq
    exact Nat.eq_of_mul_eq_mul_right hh heq

/-- **The route-decisive estimate: a per-prime unimodular weight costs nothing.**

The twisted multiplier obeys *exactly* the fourth-moment/additive-energy bound of
`Erdos67b.fourth_moment_primeGraphMultiplier_le_energy`, with the same constant.  This is what makes
the phase-twisted prime graph a viable device for the two-function case of Tao's theorem: the
additive-energy input — the sharp arithmetic ingredient of the upper-bound chain — is blind to
unimodular per-prime phases, because the dependency's
`Erdos67b.fourth_moment_weightedExponentialSum_le_energy` already allows an arbitrary complex
coefficient bounded by `B`, and `‖w p · p⁻¹‖ = ‖w p‖ · p⁻¹ ≤ p⁻¹`. -/
theorem fourth_moment_twistedPrimeGraphMultiplier_le_energy
    (T X : ℕ) [NeZero T] {h : ℕ} (hh : 0 < h) (s : Finset ℕ) {w : ℕ → ℂ}
    (hw : ∀ p ∈ s, ‖w p‖ ≤ 1)
    {B : ℝ} (hB : 0 ≤ B) (hweight : ∀ p ∈ s, (p : ℝ)⁻¹ ≤ B)
    (hs : ∀ p ∈ s, p ≤ X) (hT : 2 * (X * h) < T) :
    ∑ t ∈ Finset.range T, ‖twistedPrimeGraphMultiplier T h s w (t : ℤ)‖ ^ 4 ≤
      T * (additiveQuadruples s).card * B ^ 4 := by
  classical
  simp_rw [twistedPrimeGraphMultiplier_eq_weightedExponentialSum T hh s w]
  have hbound := fourth_moment_weightedExponentialSum_le_energy T (X * h)
    (s.image fun p ↦ p * h) (fun m ↦ w (m / h) * ((m / h : ℕ) : ℂ)⁻¹) B hB (by
      intro m hm
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
      rw [Nat.mul_div_left _ hh, norm_mul, norm_inv, Complex.norm_natCast]
      calc ‖w p‖ * (p : ℝ)⁻¹ ≤ 1 * (p : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_right (hw p hp) (by positivity)
        _ = (p : ℝ)⁻¹ := one_mul _
        _ ≤ B := hweight p hp)
    (by
      intro m hm
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
      exact Nat.mul_le_mul_right h (hs p hp)) hT
  simpa only [card_additiveQuadruples_image_mul s hh] using hbound

end

end NormalNumbers.ElliottTwistedGraph
