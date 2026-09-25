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

/-! ## The two remaining obligations of the twisted graph -/

end

end NormalNumbers.ElliottTwistedGraph
