import ErdosProblems.Erdos67b.PrimeGraphFourierUpper

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
open Erdos67b.FiniteEntropy

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


/-! ## The two-block (pair) graph

`Erdos67b.primeGraphEdge b p h j = b j * conj (b (j + p·h))` hardcodes the shape `b ⊗ conj b`, which
is the `f₂ = conj f₁` specialisation.  The two-function case needs `b j * c (j + p·h)` where `b`, `c`
are the blocks of `f₁`, `f₂`.  This section builds that edge, its bilinear Fourier pairing, and the
large-frequency upper bound.

The bound records a structural fact worth naming: the Fourier **first moment** that the MRT input
has to supply falls on the `b` block *only* — because one spends the trivial bound
`‖blockFourier T c t‖ ≤ H` on the second block.  That is exactly why Tao's Theorem 1.3 assumes
non-pretentiousness of `g₁` alone.
-/

/-- The two-block graph edge with a raw shift. -/
def pairShiftEdge {H : ℕ} (b c : Fin H → ℂ) (a : ℕ) (j : Fin H) : ℂ :=
  if hj : j.1 + a < H then b j * c ⟨j.1 + a, hj⟩ else 0

/-- The proved development's edge is the `c = conj b` specialisation. -/
theorem pairShiftEdge_conj {H : ℕ} (b : Fin H → ℂ) (p h : ℕ) (j : Fin H) :
    pairShiftEdge b (fun i ↦ conj (b i)) (p * h) j = primeGraphEdge b p h j := rfl

theorem norm_pairShiftEdge_le {H : ℕ} {b c : Fin H → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ j, ‖b j‖ ≤ B) (hc : ∀ j, ‖c j‖ ≤ B) (a : ℕ) (j : Fin H) :
    ‖pairShiftEdge b c a j‖ ≤ B ^ 2 := by
  unfold pairShiftEdge
  split_ifs with hj
  · rw [norm_mul, pow_two]
    exact mul_le_mul (hb j) (hc _) (norm_nonneg _) hB
  · simpa only [norm_zero] using sq_nonneg B

/-- The bilinear Fourier pairing of two blocks.  For `c = conj b` this is `‖blockFourier T b t‖ ^ 2`
(see `pairBlockPairing_conj`). -/
def pairBlockPairing {H : ℕ} (T : ℕ) (b c : Fin H → ℂ) (t : ℤ) : ℂ :=
  blockFourier T b t * conj (blockFourier T (fun j ↦ conj (c j)) t)

theorem norm_pairBlockPairing {H : ℕ} (T : ℕ) (b c : Fin H → ℂ) (t : ℤ) :
    ‖pairBlockPairing T b c t‖ =
      ‖blockFourier T b t‖ * ‖blockFourier T (fun j ↦ conj (c j)) t‖ := by
  rw [pairBlockPairing, norm_mul, RCLike.norm_conj]

theorem pairBlockPairing_mul_phase {H : ℕ} (T : ℕ) (b c : Fin H → ℂ) (t : ℤ) (a : ℕ) :
    pairBlockPairing T b c t * phase T t a =
      ∑ j : Fin H, ∑ k : Fin H, (b j * c k) * phase T t ((j.1 : ℤ) + a - k.1) := by
  simp only [pairBlockPairing, blockFourier, map_sum, map_mul, Complex.conj_conj,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  rw [conj_phase]
  calc
    (b j * phase T t j.1) * (c k * phase T t (-(k.1 : ℤ))) * phase T t a =
        (b j * c k) * (phase T t j.1 * phase T t a * phase T t (-(k.1 : ℤ))) := by ring
    _ = _ := by
      rw [← phase_add_right, ← phase_add_right]
      congr 2

/-- Orthogonality for the bilinear pairing: the analogue of
`Erdos67b.sum_blockFourier_norm_sq_mul_phase` for two distinct blocks. -/
theorem sum_pairBlockPairing_mul_phase {H T : ℕ} [NeZero T] (b c : Fin H → ℂ)
    (a : ℕ) (hT : H + a ≤ T) :
    (∑ t ∈ Finset.range T, pairBlockPairing T b c (t : ℤ) * phase T (t : ℤ) a) =
      (T : ℂ) * ∑ j : Fin H, pairShiftEdge b c a j := by
  classical
  simp_rw [pairBlockPairing_mul_phase]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.sum_comm]
  have hinner : ∀ k : Fin H,
      (∑ t ∈ Finset.range T, (b j * c k) * phase T (t : ℤ) ((j.1 : ℤ) + a - k.1)) =
        (b j * c k) * (if j.1 + a = k.1 then (T : ℂ) else 0) := by
    intro k
    rw [← Finset.mul_sum, sum_phase_block_shift a hT j k]
  simp_rw [hinner]
  by_cases hj : j.1 + a < H
  · have hmem : (⟨j.1 + a, hj⟩ : Fin H) ∈ (Finset.univ : Finset (Fin H)) := Finset.mem_univ _
    rw [Finset.sum_eq_single_of_mem _ hmem]
    · have hrfl : j.1 + a = (⟨j.1 + a, hj⟩ : Fin H).1 := rfl
      rw [pairShiftEdge, dif_pos hj, if_pos hrfl]
      ring
    · intro k _ hk
      have hne : ¬ (j.1 + a = k.1) := fun hEq ↦ hk (Fin.ext hEq.symm)
      simp [hne]
  · have hzero : ∀ k : Fin H, ¬ (j.1 + a = k.1) := fun k hEq ↦ hj (hEq ▸ k.2)
    rw [pairShiftEdge, dif_neg hj]
    simp [hzero]

/-! ## The pair-twisted mean -/

/-- The prime graph mean for two blocks, with the per-prime unimodular twist. -/
def pairTwistedPrimeGraphMean {H : ℕ} (w : ℕ → ℂ) (b c : Fin H → ℂ) (h : ℕ) (s : Finset ℕ) : ℂ :=
  ∑ p ∈ s, w p * (p : ℂ)⁻¹ * ∑ j : Fin H, pairShiftEdge b c (p * h) j

@[simp]
theorem pairTwistedPrimeGraphMean_conj {H : ℕ} (w : ℕ → ℂ) (b : Fin H → ℂ)
    (h : ℕ) (s : Finset ℕ) :
    pairTwistedPrimeGraphMean w b (fun i ↦ conj (b i)) h s = twistedPrimeGraphMean w b h s := by
  simp only [pairTwistedPrimeGraphMean, twistedPrimeGraphMean, pairShiftEdge_conj]

/-- **The exact Fourier pairing identity for the pair-twisted mean.**  Both generalisations live in
separate factors: the second block only in `pairBlockPairing`, the twist only in
`twistedPrimeGraphMultiplier`. -/
theorem pairTwistedPrimeGraphMean_eq_fourier {H T : ℕ} [NeZero T]
    (w : ℕ → ℂ) (b c : Fin H → ℂ) (h : ℕ) (s : Finset ℕ)
    (hT : ∀ p ∈ s, H + p * h ≤ T) :
    pairTwistedPrimeGraphMean w b c h s = (T : ℂ)⁻¹ * ∑ t ∈ Finset.range T,
      pairBlockPairing T b c (t : ℤ) * twistedPrimeGraphMultiplier T h s w (t : ℤ) := by
  have hT0 : (T : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne T)
  have hsum : (∑ t ∈ Finset.range T,
      pairBlockPairing T b c (t : ℤ) * twistedPrimeGraphMultiplier T h s w (t : ℤ)) =
        (T : ℂ) * pairTwistedPrimeGraphMean w b c h s := by
    simp only [twistedPrimeGraphMultiplier, Finset.mul_sum]
    rw [Finset.sum_comm, pairTwistedPrimeGraphMean, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    calc
      _ = w p * (p : ℂ)⁻¹ * ∑ t ∈ Finset.range T,
          pairBlockPairing T b c (t : ℤ) * phase T (t : ℤ) (p * h : ℕ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ ↦ by ring
      _ = _ := by rw [sum_pairBlockPairing_mul_phase b c (p * h) (hT p hp)]; ring
  rw [hsum, ← mul_assoc, inv_mul_cancel₀ hT0, one_mul]

/-- The frequencies at which the twisted multiplier is large. -/
def pairTwistedLargeFrequencies (T h : ℕ) (s : Finset ℕ) (w : ℕ → ℂ) (θ : ℝ) : Finset ℕ :=
  (Finset.range T).filter fun t ↦ θ ≤ ‖twistedPrimeGraphMultiplier T h s w (t : ℤ)‖

/-- **The pair-twisted large-frequency bound, and the asymmetry of Tao's hypothesis.**

The analogue of `Erdos67b.norm_primeGraphMean_le_largeFrequencies` for two blocks and a per-prime
twist.  Note what the right-hand side involves: the large-frequency Fourier first moment of the
**first** block `b` only.  The second block enters solely through the trivial bound
`‖blockFourier T (conj ∘ c) t‖ ≤ H`, together with Parseval.  Formalised, this is the reason Tao's
Theorem 1.3 needs non-pretentiousness of `g₁` and nothing at all about `g₂`: the MRT input is spent
on the first block, and the second block is merely `1`-bounded. -/
theorem norm_pairTwistedPrimeGraphMean_le_largeFrequencies {H T : ℕ} [NeZero T]
    (w : ℕ → ℂ) (b c : Fin H → ℂ) (h : ℕ) (s : Finset ℕ)
    (hHT : H ≤ T) (hT : ∀ p ∈ s, H + p * h ≤ T)
    (hb : ∀ j, ‖b j‖ ≤ 1) (hc : ∀ j, ‖c j‖ ≤ 1)
    {θ M : ℝ} (hθ : 0 ≤ θ)
    (hmult : ∀ t ∈ Finset.range T, ‖twistedPrimeGraphMultiplier T h s w (t : ℤ)‖ ≤ M) :
    ‖pairTwistedPrimeGraphMean w b c h s‖ ≤ θ * H + ((H : ℝ) * M / T) *
      ∑ t ∈ pairTwistedLargeFrequencies T h s w θ, ‖blockFourier T b (t : ℤ)‖ := by
  classical
  have hTr : (0 : ℝ) < T := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne T))
  set c' : Fin H → ℂ := fun j ↦ conj (c j) with hc'
  have hc'b : ∀ j, ‖c' j‖ ≤ 1 := by
    intro j; rw [hc', RCLike.norm_conj]; exact hc j
  -- pointwise split at the threshold `θ`
  have hpoint (t : ℕ) (ht : t ∈ Finset.range T) :
      ‖pairBlockPairing T b c (t : ℤ)‖ * ‖twistedPrimeGraphMultiplier T h s w (t : ℤ)‖ ≤
        θ * ((‖blockFourier T b (t : ℤ)‖ ^ 2 + ‖blockFourier T c' (t : ℤ)‖ ^ 2) / 2) +
          if θ ≤ ‖twistedPrimeGraphMultiplier T h s w (t : ℤ)‖ then
            H * M * ‖blockFourier T b (t : ℤ)‖ else 0 := by
    have hcH : ‖blockFourier T c' (t : ℤ)‖ ≤ H := by
      simpa using norm_blockFourier_le T c' (t : ℤ) hc'b
    have hnorm : ‖pairBlockPairing T b c (t : ℤ)‖ =
        ‖blockFourier T b (t : ℤ)‖ * ‖blockFourier T c' (t : ℤ)‖ := norm_pairBlockPairing T b c _
    by_cases htlarge : θ ≤ ‖twistedPrimeGraphMultiplier T h s w (t : ℤ)‖
    · rw [if_pos htlarge, hnorm]
      have hkey : ‖blockFourier T b (t : ℤ)‖ * ‖blockFourier T c' (t : ℤ)‖ *
          ‖twistedPrimeGraphMultiplier T h s w (t : ℤ)‖ ≤
            (H : ℝ) * M * ‖blockFourier T b (t : ℤ)‖ := by
        have h1 : ‖blockFourier T b (t : ℤ)‖ * ‖blockFourier T c' (t : ℤ)‖ ≤
            ‖blockFourier T b (t : ℤ)‖ * (H : ℝ) :=
          mul_le_mul_of_nonneg_left hcH (norm_nonneg _)
        calc
          _ ≤ ‖blockFourier T b (t : ℤ)‖ * (H : ℝ) *
              ‖twistedPrimeGraphMultiplier T h s w (t : ℤ)‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
          _ ≤ ‖blockFourier T b (t : ℤ)‖ * (H : ℝ) * M :=
            mul_le_mul_of_nonneg_left (hmult t ht) (by positivity)
          _ = _ := by ring
      nlinarith [sq_nonneg ‖blockFourier T b (t : ℤ)‖,
        sq_nonneg ‖blockFourier T c' (t : ℤ)‖, mul_nonneg hθ
          (add_nonneg (sq_nonneg ‖blockFourier T b (t : ℤ)‖)
            (sq_nonneg ‖blockFourier T c' (t : ℤ)‖))]
    · rw [if_neg htlarge, add_zero, hnorm]
      have hlt := le_of_not_ge htlarge
      have hamgm : ‖blockFourier T b (t : ℤ)‖ * ‖blockFourier T c' (t : ℤ)‖ ≤
          (‖blockFourier T b (t : ℤ)‖ ^ 2 + ‖blockFourier T c' (t : ℤ)‖ ^ 2) / 2 := by
        nlinarith [sq_nonneg (‖blockFourier T b (t : ℤ)‖ - ‖blockFourier T c' (t : ℤ)‖)]
      have hprodnn : 0 ≤ ‖blockFourier T b (t : ℤ)‖ * ‖blockFourier T c' (t : ℤ)‖ :=
        mul_nonneg (norm_nonneg _) (norm_nonneg _)
      calc
        _ ≤ ‖blockFourier T b (t : ℤ)‖ * ‖blockFourier T c' (t : ℤ)‖ * θ :=
          mul_le_mul_of_nonneg_left hlt hprodnn
        _ = θ * (‖blockFourier T b (t : ℤ)‖ * ‖blockFourier T c' (t : ℤ)‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hamgm hθ
  have hsum := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_filter, ← Finset.mul_sum] at hsum
  -- Parseval on both blocks
  have hpb := sum_blockFourier_norm_sq_le b hHT hb
  have hpc := sum_blockFourier_norm_sq_le c' hHT hc'b
  have hparseval : (∑ t ∈ Finset.range T,
      (‖blockFourier T b (t : ℤ)‖ ^ 2 + ‖blockFourier T c' (t : ℤ)‖ ^ 2) / 2) ≤ (T : ℝ) * H := by
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    linarith
  have htotal := hsum.trans (add_le_add (mul_le_mul_of_nonneg_left hparseval hθ) le_rfl)
  calc
    ‖pairTwistedPrimeGraphMean w b c h s‖ ≤ (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
        ‖pairBlockPairing T b c (t : ℤ)‖ *
          ‖twistedPrimeGraphMultiplier T h s w (t : ℤ)‖ := by
      rw [pairTwistedPrimeGraphMean_eq_fourier w b c h s hT, norm_mul, norm_inv,
        Complex.norm_natCast]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ ↦ ?_)
      rw [norm_mul]
    _ ≤ (T : ℝ)⁻¹ * (θ * ((T : ℝ) * H) + H * M *
        ∑ t ∈ pairTwistedLargeFrequencies T h s w θ, ‖blockFourier T b (t : ℤ)‖) :=
      mul_le_mul_of_nonneg_left htotal (by positivity)
    _ = _ := by
      rw [pairTwistedLargeFrequencies]
      field_simp


/-! ## Uniform bounds for the twisted multiplier

Ports of `Erdos67b.norm_dyadic_primeGraphMultiplier_le_primeCounting`,
`Erdos67b.exists_dyadic_primeGraphMultiplier_fourth_moment_bound` and
`Erdos67b.exists_eventually_primeGraphMultiplier_bounds` to the twisted multiplier.  Each proof is
the dependency's, with `fourth_moment_twistedPrimeGraphMultiplier_le_energy` and
`norm_twistedPrimeGraphMultiplier_le` in place of their untwisted counterparts: the *only* thing the
twist costs is carrying the hypothesis `‖w p‖ ≤ 1` along.
-/

theorem norm_dyadic_twistedPrimeGraphMultiplier_le_primeCounting
    (T h : ℕ) {P : ℕ} (hP : 0 < P) {w : ℕ → ℂ}
    (hw : ∀ p ∈ PrimeEstimates.dyadicPrimes P, ‖w p‖ ≤ 1) (t : ℤ) :
    ‖twistedPrimeGraphMultiplier T h (PrimeEstimates.dyadicPrimes P) w t‖ ≤
      (Nat.primeCounting (2 * P) : ℝ) / P := by
  have hPr : (0 : ℝ) < P := Nat.cast_pos.mpr hP
  have hs : PrimeEstimates.dyadicPrimes P ⊆ Nat.primesLE (2 * P) := by
    intro p hp
    have hp' := PrimeEstimates.mem_primesInInterval.mp hp
    exact Nat.mem_primesLE.mpr ⟨hp'.2.1, hp'.2.2⟩
  have hcard : (PrimeEstimates.dyadicPrimes P).card ≤ Nat.primeCounting (2 * P) := by
    simpa only [Nat.primesLE_card_eq_primeCounting] using Finset.card_le_card hs
  calc
    _ ≤ ∑ p ∈ PrimeEstimates.dyadicPrimes P, (p : ℝ)⁻¹ :=
      norm_twistedPrimeGraphMultiplier_le _ _ _ hw _
    _ ≤ ∑ _p ∈ PrimeEstimates.dyadicPrimes P, (P : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      exact inv_anti₀ hPr (by exact_mod_cast (PrimeEstimates.mem_primesInInterval.mp hp).1.le)
    _ = (PrimeEstimates.dyadicPrimes P).card / (P : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
    _ ≤ (Nat.primeCounting (2 * P) : ℝ) / P := by gcongr

/-- The dyadic twisted multiplier inherits the same sharp fourth-moment saving from the four-prime
sieve as the untwisted one: the constant `A` and threshold `P₀` are literally the dependency's. -/
theorem exists_dyadic_twistedPrimeGraphMultiplier_fourth_moment_bound :
    ∃ A : ℝ, 0 < A ∧ ∃ P₀ : ℕ, 2 ≤ P₀ ∧ ∀ P ≥ P₀,
      ∀ T h : ℕ, 0 < h → 4 * P * h < T →
      ∀ w : ℕ → ℂ, (∀ p ∈ PrimeEstimates.dyadicPrimes P, ‖w p‖ ≤ 1) →
      ∑ t ∈ Finset.range T,
        ‖twistedPrimeGraphMultiplier T h (PrimeEstimates.dyadicPrimes P) w (t : ℤ)‖ ^ 4 ≤
          A * T / ((P : ℝ) * Real.log P ^ 4) := by
  obtain ⟨A, hA, henergy⟩ := exists_primesLE_additiveQuadruples_bound
  obtain ⟨P₀, hP₀⟩ := Filter.eventually_atTop.mp henergy
  refine ⟨A, hA, max P₀ 2, le_max_right _ _, ?_⟩
  intro P hP T h hh hT w hw
  have hP2 : 2 ≤ P := (le_max_right _ _).trans hP
  have hPr : (0 : ℝ) < P := by positivity
  have hlog : 0 < Real.log (P : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < P))
  have hTpos : 0 < T := by omega
  let _ : NeZero T := ⟨hTpos.ne'⟩
  have hs : PrimeEstimates.dyadicPrimes P ⊆ Nat.primesLE (2 * P) := by
    intro p hp
    have hp' := PrimeEstimates.mem_primesInInterval.mp hp
    exact Nat.mem_primesLE.mpr ⟨hp'.2.1, hp'.2.2⟩
  have hcard : (additiveQuadruples (PrimeEstimates.dyadicPrimes P)).card ≤
      (additiveQuadruples (Nat.primesLE (2 * P))).card := by
    rw [card_additiveQuadruples, card_additiveQuadruples]
    exact Finset.addEnergy_mono hs hs
  have he := hP₀ P ((le_max_left _ _).trans hP)
  have hbound := fourth_moment_twistedPrimeGraphMultiplier_le_energy T (2 * P) hh
    (PrimeEstimates.dyadicPrimes P) hw (B := (P : ℝ)⁻¹) (by positivity) (by
      intro p hp
      exact inv_anti₀ hPr (by exact_mod_cast (PrimeEstimates.mem_primesInInterval.mp hp).1.le))
    (fun p hp ↦ (PrimeEstimates.mem_primesInInterval.mp hp).2.1) (by nlinarith)
  calc
    _ ≤ T * (additiveQuadruples (PrimeEstimates.dyadicPrimes P)).card * ((P : ℝ)⁻¹) ^ 4 := hbound
    _ ≤ T * (A * (P : ℝ) ^ 3 / Real.log P ^ 4) * ((P : ℝ)⁻¹) ^ 4 := by
      gcongr
      exact (show ((additiveQuadruples (PrimeEstimates.dyadicPrimes P)).card : ℝ) ≤
        (additiveQuadruples (Nat.primesLE (2 * P))).card by exact_mod_cast hcard).trans he
    _ = A * T / ((P : ℝ) * Real.log P ^ 4) := by field_simp

/-- Sharp fourth moment and uniform supremum bound for the twisted multiplier at the
entropy-selected dyadic scale.  Port of `Erdos67b.exists_eventually_primeGraphMultiplier_bounds`;
the bounds are **uniform in the twist**. -/
theorem exists_eventually_twistedPrimeGraphMultiplier_bounds {h : ℕ} (hh : 0 < h) :
    ∃ C : ℝ, 0 < C ∧ ∃ H₁ : ℕ, 2 ≤ H₁ ∧ ∀ H ≥ H₁,
      ∀ w : ℕ → ℂ, (∀ p ∈ PrimeEstimates.dyadicPrimes (H / (4 * h + 4)), ‖w p‖ ≤ 1) →
      (∑ t ∈ Finset.range (4 * h * H + 1),
        ‖twistedPrimeGraphMultiplier (4 * h * H + 1) h
          (PrimeEstimates.dyadicPrimes (H / (4 * h + 4))) w (t : ℤ)‖ ^ 4 ≤
            C / Real.log H ^ 4) ∧
        ∀ t : ℤ, ‖twistedPrimeGraphMultiplier (4 * h * H + 1) h
          (PrimeEstimates.dyadicPrimes (H / (4 * h + 4))) w t‖ ≤ 16 / Real.log H := by
  obtain ⟨A, hA, P₀, hP₀, hfourth⟩ := exists_dyadic_twistedPrimeGraphMultiplier_fourth_moment_bound
  obtain ⟨P₁, hprime⟩ := Filter.eventually_atTop.mp eventually_primeCounting_le_four_mul_div_log
  let K : ℕ := 4 * h + 4
  have hK : 2 ≤ K := by dsimp [K]; omega
  let P₂ : ℕ := max (max P₀ P₁) (2 * K)
  have hP₂ : 2 * K ≤ P₂ := le_max_right _ _
  let C : ℝ := 32 * A * K * (4 * h + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, max 2 (K * P₂), le_max_left _ _, ?_⟩
  intro H hHH w hw
  set P := H / K with hPdef
  set T := 4 * h * H + 1 with hTdef
  obtain ⟨hPP₂, hPH, hratio, hlogP, hlogH, hlogratio⟩ :=
    primeGraph_quotient_comparisons hK hP₂ ((le_max_right _ _).trans hHH)
  have hPP₀ : P₀ ≤ P := ((le_max_left _ _).trans (le_max_left _ _)).trans hPP₂
  have hPP₁ : P₁ ≤ P := ((le_max_right _ _).trans (le_max_left _ _)).trans hPP₂
  have hP2 : 2 ≤ P := hP₀.trans hPP₀
  have hPr : (0 : ℝ) < P := by positivity
  have hHr : (0 : ℝ) < H := by
    have : 0 < H := by omega
    exact_mod_cast this
  have hTr : (T : ℝ) ≤ (4 * h + 1) * H := by
    have hH1 : (1 : ℝ) ≤ H := by
      have : 1 ≤ H := by omega
      exact_mod_cast this
    rw [hTdef]
    push_cast
    nlinarith
  have hTP : (T : ℝ) / P ≤ 2 * K * (4 * h + 1) := by
    apply (div_le_iff₀ hPr).mpr
    nlinarith
  have hlogInv : (1 : ℝ) / Real.log P ^ 4 ≤ 16 / Real.log H ^ 4 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hpow := pow_le_pow_left₀ hlogH.le hlogratio 4
    nlinarith [hpow]
  have hTlow : 4 * P * h < T := by
    have hPH' : P ≤ H := by rw [hPdef]; omega
    have hmul := Nat.mul_le_mul_left (4 * h) hPH'
    rw [hTdef]
    nlinarith
  have h4 := hfourth P hPP₀ T h hh hTlow w hw
  constructor
  · calc
      _ ≤ A * T / ((P : ℝ) * Real.log P ^ 4) := h4
      _ = A * ((T : ℝ) / P) * (1 / Real.log P ^ 4) := by ring
      _ ≤ A * (2 * K * (4 * h + 1)) * (16 / Real.log H ^ 4) := by gcongr
      _ = C / Real.log H ^ 4 := by dsimp [C]; ring
  · intro t
    have hp := hprime (2 * P) (by omega)
    have hlog2P : 0 < Real.log (2 * P : ℕ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * P))
    have hlogle : Real.log (P : ℝ) ≤ Real.log (2 * P : ℕ) :=
      Real.log_le_log hPr (by exact_mod_cast (by omega : P ≤ 2 * P))
    calc
      _ ≤ (Nat.primeCounting (2 * P) : ℝ) / P :=
        norm_dyadic_twistedPrimeGraphMultiplier_le_primeCounting T h (by omega) hw t
      _ ≤ (4 * (2 * P : ℕ) / Real.log (2 * P : ℕ)) / P :=
        div_le_div_of_nonneg_right (by simpa only [mul_div_assoc] using hp) hPr.le
      _ = 8 / Real.log (2 * P : ℕ) := by push_cast; field_simp; ring
      _ ≤ 8 / Real.log P := div_le_div_of_nonneg_left (by norm_num) hlogP hlogle
      _ ≤ 16 / Real.log H := by
        apply (div_le_div_iff₀ hlogP hlogH).mpr
        linarith

/-- Markov's inequality for the twisted frequency count.  Port of
`Erdos67b.card_primeGraphLargeFrequencies_le`. -/
theorem card_pairTwistedLargeFrequencies_le {T h : ℕ} (s : Finset ℕ) (w : ℕ → ℂ)
    {θ B : ℝ} (hθ : 0 < θ)
    (hmoment : ∑ t ∈ Finset.range T,
      ‖twistedPrimeGraphMultiplier T h s w (t : ℤ)‖ ^ 4 ≤ B) :
    (pairTwistedLargeFrequencies T h s w θ).card ≤ B / θ ^ 4 := by
  have hsmall : (pairTwistedLargeFrequencies T h s w θ).card * θ ^ 4 ≤
      ∑ t ∈ pairTwistedLargeFrequencies T h s w θ,
        ‖twistedPrimeGraphMultiplier T h s w (t : ℤ)‖ ^ 4 := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun t ht ↦
      pow_le_pow_left₀ hθ.le (Finset.mem_filter.mp ht).2 4
  have hsub : pairTwistedLargeFrequencies T h s w θ ⊆ Finset.range T := Finset.filter_subset _ _
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ ↦ by positivity :
    ∀ t ∈ Finset.range T, t ∉ pairTwistedLargeFrequencies T h s w θ →
      0 ≤ ‖twistedPrimeGraphMultiplier T h s w (t : ℤ)‖ ^ 4)
  exact (le_div_iff₀ (by positivity : 0 < θ ^ 4)).mpr ((hsmall.trans hsum).trans hmoment)



/-! ## The logarithmic-average layer and the upper-bound assembly -/

/-- Port of `Erdos67b.norm_logProb_primeGraphMean_le_of_fourier_first_moment`.  Note the
first-moment hypothesis `hfirst` concerns the **first** block only: `F₂` is merely `1`-bounded.
This is lap 4's structural observation, now carried through the logarithmic average. -/
theorem norm_logProb_pairTwistedPrimeGraphMean_le_of_fourier_first_moment
    {L U H T : ℕ} [NeZero T] (hL : 0 < L) (hLU : L ≤ U)
    (w : ℕ → ℂ) (F₁ F₂ : ℕ → ℂ) (h : ℕ) (s : Finset ℕ)
    (hHT : H ≤ T) (hT : ∀ p ∈ s, H + p * h ≤ T)
    (hF₁ : ∀ n, 0 < n → ‖F₁ n‖ ≤ 1) (hF₂ : ∀ n, 0 < n → ‖F₂ n‖ ≤ 1)
    {θ M Z : ℝ} (hθ : 0 ≤ θ) (hM : 0 ≤ M)
    (hmult : ∀ t ∈ Finset.range T, ‖twistedPrimeGraphMultiplier T h s w (t : ℤ)‖ ≤ M)
    (hfirst : ∀ t ∈ pairTwistedLargeFrequencies T h s w θ,
      logProbExpectation L U
        (fun n ↦ ‖blockFourier T (finiteSequenceBlock F₁ H n) (t : ℤ)‖) ≤ Z) :
    ‖logProbExpectation L U (fun n ↦ pairTwistedPrimeGraphMean w
        (finiteSequenceBlock F₁ H n) (finiteSequenceBlock F₂ H n) h s)‖ ≤
      θ * H + ((H : ℝ) * M / T) * (pairTwistedLargeFrequencies T h s w θ).card * Z := by
  have hpoint (n : ℕ) : ‖pairTwistedPrimeGraphMean w (finiteSequenceBlock F₁ H n)
      (finiteSequenceBlock F₂ H n) h s‖ ≤
      θ * H + ((H : ℝ) * M / T) *
        ∑ t ∈ pairTwistedLargeFrequencies T h s w θ,
          ‖blockFourier T (finiteSequenceBlock F₁ H n) (t : ℤ)‖ :=
    norm_pairTwistedPrimeGraphMean_le_largeFrequencies w _ _ h s hHT hT
      (fun j ↦ hF₁ (n + j.1 + 1) (by omega)) (fun j ↦ hF₂ (n + j.1 + 1) (by omega)) hθ hmult
  have hweights : ∑ n : LogProbIndex L U, (logProbWeightNN L U n : ℝ) = 1 := by
    exact_mod_cast sum_logProbWeightNN hL hLU
  have hexpand : logProbExpectation L U (fun n ↦ θ * H + ((H : ℝ) * M / T) *
      ∑ t ∈ pairTwistedLargeFrequencies T h s w θ,
        ‖blockFourier T (finiteSequenceBlock F₁ H n) (t : ℤ)‖) =
      θ * H + ((H : ℝ) * M / T) * ∑ t ∈ pairTwistedLargeFrequencies T h s w θ,
        logProbExpectation L U
          (fun n ↦ ‖blockFourier T (finiteSequenceBlock F₁ H n) (t : ℤ)‖) := by
    simp only [logProbExpectation, smul_eq_mul, mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, hweights, one_mul]
    congr 1
    simp_rw [mul_left_comm (logProbWeightNN L U _ : ℝ) ((H : ℝ) * M / T)]
    rw [← Finset.mul_sum]
    congr 1
    simp only [Finset.mul_sum]
    exact Finset.sum_comm
  calc
    _ ≤ logProbExpectation L U (fun n ↦ ‖pairTwistedPrimeGraphMean w
        (finiteSequenceBlock F₁ H n) (finiteSequenceBlock F₂ H n) h s‖) :=
      norm_logProbExpectation_le_expectation_norm _ _ _
    _ ≤ logProbExpectation L U (fun n ↦ θ * H + ((H : ℝ) * M / T) *
        ∑ t ∈ pairTwistedLargeFrequencies T h s w θ,
          ‖blockFourier T (finiteSequenceBlock F₁ H n) (t : ℤ)‖) :=
      logProbExpectation_mono _ _ (fun n _ ↦ hpoint n)
    _ = _ := hexpand
    _ ≤ θ * H + ((H : ℝ) * M / T) * ∑ _t ∈ pairTwistedLargeFrequencies T h s w θ, Z := by
      gcongr
      exact hfirst _ ‹_›
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **The twisted, two-block graph upper bound.**  Port of
`Erdos67b.exists_primeGraphMean_small_of_fourier_first_moment`.

The parameter choreography is the dependency's verbatim — `cutoff = η/64`, `N = C/cutoff⁴`,
`ζ = η/(1024(N+1))`, budget `cutoff + 16ζN ≤ η/32` — which is possible only because
`exists_eventually_twistedPrimeGraphMultiplier_bounds` delivers the dependency's own constants.
Both generalisations needed for Tao's Theorem 1.3 are present: two independent blocks, and the
per-prime unimodular twist.  The Fourier first moment is required on `F₁` alone. -/
theorem exists_pairTwistedPrimeGraphMean_small_of_fourier_first_moment
    {h : ℕ} (hh : 0 < h) {η : ℝ} (hη : 0 < η) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∃ H₁ : ℕ, 2 ≤ H₁ ∧ ∀ H ≥ H₁,
      ∀ L U : ℕ, 0 < L → L ≤ U → ∀ F₁ F₂ : ℕ → ℂ,
      (∀ n, 0 < n → ‖F₁ n‖ ≤ 1) → (∀ n, 0 < n → ‖F₂ n‖ ≤ 1) →
      ∀ w : ℕ → ℂ, (∀ p ∈ PrimeEstimates.dyadicPrimes (H / (4 * h + 4)), ‖w p‖ ≤ 1) →
      (∀ t ∈ Finset.range (4 * h * H + 1),
        logProbExpectation L U (fun n ↦
          ‖blockFourier (4 * h * H + 1) (finiteSequenceBlock F₁ H n) (t : ℤ)‖) ≤ ζ * H) →
      ‖logProbExpectation L U (fun n ↦ pairTwistedPrimeGraphMean w
        (finiteSequenceBlock F₁ H n) (finiteSequenceBlock F₂ H n) h
        (PrimeEstimates.dyadicPrimes (H / (4 * h + 4))))‖ ≤ η * H / (32 * Real.log H) := by
  obtain ⟨C, hC, H₁, hH₁, hcontrol⟩ := exists_eventually_twistedPrimeGraphMultiplier_bounds hh
  let cutoff : ℝ := η / 64
  have hcutoff : 0 < cutoff := by dsimp [cutoff]; positivity
  let N : ℝ := C / cutoff ^ 4
  have hN : 0 < N := by dsimp [N]; positivity
  let ζ : ℝ := η / (1024 * (N + 1))
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  have hbudget : cutoff + 16 * ζ * N ≤ η / 32 := by
    have hratio : N / (N + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    calc
      cutoff + 16 * ζ * N = η / 64 + (η / 64) * (N / (N + 1)) := by
        dsimp [cutoff, ζ]
        field_simp; ring
      _ ≤ η / 64 + (η / 64) * 1 := by gcongr
      _ = η / 32 := by ring
  refine ⟨ζ, hζ, H₁, hH₁, ?_⟩
  intro H hH L U hL hLU F₁ F₂ hF₁ hF₂ w hw hfirst
  set P := H / (4 * h + 4) with hPdef
  set T := 4 * h * H + 1 with hTdef
  set s := PrimeEstimates.dyadicPrimes P with hsdef
  have hH2 : 2 ≤ H := hH₁.trans hH
  have hHr : (0 : ℝ) < H := by positivity
  have hlog : 0 < Real.log (H : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < H))
  have hTpos : 0 < T := by rw [hTdef]; omega
  let _ : NeZero T := ⟨hTpos.ne'⟩
  have hTr : (0 : ℝ) < T := Nat.cast_pos.mpr hTpos
  have hHT : H ≤ T := by rw [hTdef]; nlinarith
  have hdiv : P * (4 * h + 4) ≤ H := Nat.div_mul_le_self H _
  have hPH : 2 * P ≤ H := by nlinarith
  have hsprimes : s ⊆ Nat.primesLE H := by
    intro p hp
    have hp' := PrimeEstimates.mem_primesInInterval.mp hp
    exact Nat.mem_primesLE.mpr ⟨hp'.2.1.trans hPH, hp'.2.2⟩
  have hnowrap : ∀ p ∈ s, H + p * h ≤ T := by
    intro p hp
    have hpH := (Nat.mem_primesLE.mp (hsprimes hp)).1
    have hprod := Nat.mul_le_mul_right h hpH
    rw [hTdef]
    nlinarith
  obtain ⟨hfourth, hsup⟩ := hcontrol H hH w hw
  have hcard : (pairTwistedLargeFrequencies T h s w (cutoff / Real.log H)).card ≤ N := by
    have hc := card_pairTwistedLargeFrequencies_le s w
      (show 0 < cutoff / Real.log H by positivity) hfourth
    have heq : (C / Real.log H ^ 4) / (cutoff / Real.log H) ^ 4 = N := by
      dsimp [N]
      field_simp
    exact heq ▸ hc
  have hbound := norm_logProb_pairTwistedPrimeGraphMean_le_of_fourier_first_moment
    hL hLU w F₁ F₂ h s hHT hnowrap hF₁ hF₂
    (θ := cutoff / Real.log H) (M := 16 / Real.log H) (Z := ζ * H)
    (by positivity) (by positivity) (fun t _ ↦ hsup t)
    (fun t ht ↦ hfirst t (Finset.mem_filter.mp ht).1)
  have hratio : (H : ℝ) * (16 / Real.log H) / T ≤ 16 / Real.log H := by
    apply (div_le_iff₀ hTr).mpr
    have hHTr : (H : ℝ) ≤ T := by exact_mod_cast hHT
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hHTr
      (show 0 ≤ (16 : ℝ) / Real.log H by positivity)
  calc
    _ ≤ cutoff / Real.log H * H + ((H : ℝ) * (16 / Real.log H) / T) *
        (pairTwistedLargeFrequencies T h s w (cutoff / Real.log H)).card * (ζ * H) := hbound
    _ ≤ cutoff / Real.log H * H + (16 / Real.log H) * N * (ζ * H) := by gcongr
    _ = (cutoff + 16 * ζ * N) * (H / Real.log H) := by ring
    _ ≤ (η / 32) * (H / Real.log H) :=
      mul_le_mul_of_nonneg_right hbudget (by positivity)
    _ = η * H / (32 * Real.log H) := by ring

end

end NormalNumbers.ElliottTwistedGraph
