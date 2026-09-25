import NormalNumbers.ElliottGenericGraphDecoupling
import NormalNumbers.ElliottDilatedUpper

/-!
# The bridge: the generic CRT mean *is* the dilated Fourier mean

`NormalNumbers.ElliottTwistedGraphCRT.pairTwistedMeanCRT_eq_pairTwistedPrimeGraphMean` is the join
between the two halves of the graph argument: the lower-bound side's CRT mean and the upper-bound
side's Fourier mean are the same number.  This file proves the same join for the generic edge
family of `NormalNumbers.ElliottGenericGraph`, and then instantiates it at the `a`-dilated edge, so
that `ElliottDilatedUpper`'s Fourier bound and `ElliottGenericGraphDecoupling`'s entropy bound
speak about **one** object.

Never edit dependency files; everything here is a new statement in `src/`.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace NormalNumbers.ElliottDilatedBridge

open Erdos67b
open NormalNumbers.ElliottGenericGraph
open NormalNumbers.ElliottDilatedPairing

noncomputable section

/-- The generic graph mean in the Fourier side's shape: a sum over the active primes. -/
def genPrimeGraphMean {H : ℕ} (w : ℕ → ℂ) (E : ℕ → Fin H → ℂ) (s : Finset ℕ) : ℂ :=
  ∑ p ∈ s, w p * (p : ℂ)⁻¹ * ∑ j : Fin H, E p j

/-- **The join, for an arbitrary edge family.**  Port of
`NormalNumbers.ElliottTwistedGraph.pairTwistedMeanCRT_eq_pairTwistedPrimeGraphMean`. -/
theorem genMeanCRT_eq_genPrimeGraphMean {H : ℕ} (w : ℕ → ℂ) (E : ℕ → Fin H → ℂ) (s : Finset ℕ)
    (hs : s ⊆ Nat.primesLE H) :
    genMeanCRT w E s = genPrimeGraphMean w E s := by
  classical
  calc
    _ = ∑ p ∈ Nat.primesLE H, if p ∈ s then
        (p : ℝ)⁻¹ • (w p * ∑ j : Fin H, E p j) else 0 :=
      Finset.sum_coe_sort (Nat.primesLE H) _
    _ = ∑ p ∈ s, (p : ℝ)⁻¹ • (w p * ∑ j : Fin H, E p j) := by
      rw [← Finset.sum_filter]
      congr 1
      ext p
      simp only [Finset.mem_filter]
      exact ⟨fun hp ↦ hp.2, fun hp ↦ ⟨hs hp, hp⟩⟩
    _ = _ := by
      simp only [genPrimeGraphMean, Complex.real_smul, Complex.ofReal_inv,
        Complex.ofReal_natCast]
      exact Finset.sum_congr rfl fun p _ ↦ by ring

/-- The `a`-dilated edge family, as a generic edge family. -/
def dilatedEdgeFamily {H : ℕ} (b c : Fin H → ℂ) (α c₁ h : ℕ) : ℕ → Fin H → ℂ :=
  fun p m ↦ dilatedPairShiftEdge b c α ((p * c₁ : ℕ) : ℤ) (p * h) m

/-- **The dilated Fourier mean is the generic graph mean of the dilated edge family.** -/
theorem genPrimeGraphMean_dilatedEdgeFamily {H : ℕ} (w : ℕ → ℂ) (b c : Fin H → ℂ)
    (α c₁ h : ℕ) (s : Finset ℕ) :
    genPrimeGraphMean w (dilatedEdgeFamily b c α c₁ h) s =
      dilatedPairTwistedMean w b c α c₁ h s := rfl

/-- **The join at the dilated edge.**  The CRT mean that the entropy/decoupling layer controls is
literally the Fourier mean that `ElliottDilatedUpper` bounds. -/
theorem genMeanCRT_dilatedEdgeFamily {H : ℕ} (w : ℕ → ℂ) (b c : Fin H → ℂ)
    (α c₁ h : ℕ) (s : Finset ℕ) (hs : s ⊆ Nat.primesLE H) :
    genMeanCRT w (dilatedEdgeFamily b c α c₁ h) s =
      dilatedPairTwistedMean w b c α c₁ h s :=
  (genMeanCRT_eq_genPrimeGraphMean w _ s hs).trans
    (genPrimeGraphMean_dilatedEdgeFamily w b c α c₁ h s)

/-- The dilated edge family is `1`-bounded whenever the two blocks are. -/
theorem norm_dilatedEdgeFamily_le {H : ℕ} {b c : Fin H → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ j, ‖b j‖ ≤ B) (hc : ∀ j, ‖c j‖ ≤ B) (α c₁ h : ℕ) (p : ℕ) (m : Fin H) :
    ‖dilatedEdgeFamily b c α c₁ h p m‖ ≤ B ^ 2 := by
  unfold dilatedEdgeFamily dilatedPairShiftEdge
  have hsq : (0 : ℝ) ≤ B ^ 2 := by positivity
  split_ifs
  · rw [norm_mul, sq]
    exact mul_le_mul (hb _) (hc _) (norm_nonneg _) hB
  · simpa using hsq
  · simpa using hsq

/-! ## The CRT residue shift, and the expansion of `genSum` at a shifted residue

The dilated graph's divisibility condition is `p ∣ n + 1 + j − d p` with `d p = ⌊p c₁ / a⌋`.  By
CRT the family `(d p)_p` assembles into one element `crtShift H d` of
`ZMod (primeGraphModulus H)`, and testing `genSum` at `n − crtShift H d` imposes exactly that
condition prime by prime.  This is the promised "the residue shift never enters the layer".
-/

/-- The CRT element whose `p`-component is `d p`. -/
def crtShift (H : ℕ) (d : ℕ → ℕ) : ZMod (primeGraphModulus H) :=
  (ZMod.prodEquivPi (fun p : PrimeGraphIndex H ↦ p.1) (primeGraphModuli_pairwise H)).symm
    (fun p ↦ ((d p.1 : ℕ) : ZMod p.1))

theorem crtShift_component (H : ℕ) (d : ℕ → ℕ) (p : PrimeGraphIndex H) :
    ZMod.prodEquivPi (fun q : PrimeGraphIndex H ↦ q.1) (primeGraphModuli_pairwise H)
      (crtShift H d) p = ((d p.1 : ℕ) : ZMod p.1) := by
  rw [crtShift, RingEquiv.apply_symm_apply]

/-- **`genSum` at the shifted residue is the shifted-divisibility graph sum.**  Generic analogue of
`NormalNumbers.ElliottTwistedGraph.pairTwistedSum_natCast`. -/
theorem genSum_natCast_sub_crtShift {H : ℕ} (w : ℕ → ℂ) (E : ℕ → Fin H → ℂ) (s : Finset ℕ)
    (d : ℕ → ℕ) (n : ℕ) (hd : ∀ p : PrimeGraphIndex H, d p.1 ≤ n) :
    genSum w E s ((n : ZMod (primeGraphModulus H)) - crtShift H d) =
      ∑ p : PrimeGraphIndex H, if p.1 ∈ s then
        ∑ j : Fin H, if p.1 ∣ n + (j.1 + 1) - d p.1 then w p.1 * E p.1 j else 0
      else 0 := by
  classical
  have hcrt (p : PrimeGraphIndex H) :
      ZMod.prodEquivPi (fun q : PrimeGraphIndex H ↦ q.1) (primeGraphModuli_pairwise H)
        ((n : ZMod (primeGraphModulus H)) - crtShift H d) p =
        (n : ZMod p.1) - ((d p.1 : ℕ) : ZMod p.1) := by
    have hms : (ZMod.prodEquivPi (fun q : PrimeGraphIndex H ↦ q.1)
          (primeGraphModuli_pairwise H)) ((n : ZMod (primeGraphModulus H)) - crtShift H d) =
        (ZMod.prodEquivPi (fun q : PrimeGraphIndex H ↦ q.1)
          (primeGraphModuli_pairwise H)) ((n : ZMod (primeGraphModulus H))) -
        (ZMod.prodEquivPi (fun q : PrimeGraphIndex H ↦ q.1)
          (primeGraphModuli_pairwise H)) (crtShift H d) := map_sub _ _ _
    have hnat : (ZMod.prodEquivPi (fun q : PrimeGraphIndex H ↦ q.1)
        (primeGraphModuli_pairwise H)) ((n : ZMod (primeGraphModulus H))) =
        (n : ∀ q : PrimeGraphIndex H, ZMod q.1) := map_natCast _ n
    rw [hms, Pi.sub_apply, crtShift_component, hnat]
    simp
  simp only [genSum, crtComplexSum, genObservable, genCoordinate, hcrt]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  split_ifs with hp
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hcast : ((n + (j.1 + 1) - d p.1 : ℕ) : ZMod p.1) =
        (n : ZMod p.1) - ((d p.1 : ℕ) : ZMod p.1) + ((j.1 + 1 : ℕ) : ZMod p.1) := by
      have hle : d p.1 ≤ n + (j.1 + 1) := (hd p).trans (by omega)
      push_cast [Nat.cast_sub hle]
      ring
    have hiff : ((n : ZMod p.1) - ((d p.1 : ℕ) : ZMod p.1) + ((j.1 + 1 : ℕ) : ZMod p.1) = 0) ↔
        p.1 ∣ n + (j.1 + 1) - d p.1 := by
      rw [← hcast, ZMod.natCast_eq_zero_iff]
    simp only [Nat.cast_add, Nat.cast_one] at hiff ⊢
    by_cases hdvd : p.1 ∣ n + (j.1 + 1) - d p.1
    · rw [if_pos (hiff.mpr hdvd), if_pos hdvd]
    · rw [if_neg (fun hc ↦ hdvd (hiff.mp hc)), if_neg hdvd]
  · rfl

/-! ## The *reindexed* dilated edge family — the one the residue condition wants

`dilatedEdgeFamily` is indexed by the block position `m`.  That is the wrong index for the CRT
layer: the divisibility the dilated observable carries is `p ∣ n + 1 + j − ⌊p c₁/a⌋` where
`m = a j + (p c₁ mod a)`, i.e. it is affine in the **progression index `j`**, not in `m`.  Writing
it in `m` would force the residue random variable to be `a·n + Δ_p`, and
`Erdos67b.logProb_block_rare_event_le` needs it to be `n` itself.

The fix is to index the edge family by `j` from the start.  Then `genCoordinate`'s standard
condition `z + (j+1) = 0`, tested at `z = n − crtShift`, is *exactly* the dilated divisibility, and
laps 27–32 apply unchanged.  The total is unchanged too, by
`sum_dilatedPairShiftEdge_eq_progression`.
-/

/-- The `a`-dilated edge family indexed by the progression index `j`: the block position is
`a*j + (p c₁ mod a)`. -/
def dilatedEdgeReindexed {H : ℕ} (b c : Fin H → ℂ) (α c₁ h : ℕ) : ℕ → Fin H → ℂ :=
  fun p j ↦ blockExtend b (α * j.1 + (p * c₁) % α) *
    blockExtend c (α * j.1 + (p * c₁) % α + p * h)

/-- **Same total.**  Reindexing does not change the edge sum of a prime. -/
theorem sum_dilatedEdgeReindexed {H : ℕ} (b c : Fin H → ℂ) {α : ℕ} (hα : 0 < α) (c₁ h p : ℕ) :
    (∑ j : Fin H, dilatedEdgeReindexed b c α c₁ h p j) =
      ∑ m : Fin H, dilatedPairShiftEdge b c α ((p * c₁ : ℕ) : ℤ) (p * h) m := by
  classical
  have hrcast : ((((p * c₁ : ℕ)) : ℤ) % (α : ℤ)).toNat = (p * c₁) % α := by
    have hc : (((p * c₁ : ℕ) : ℤ) % (α : ℤ)) = (((p * c₁) % α : ℕ) : ℤ) :=
      (Int.natCast_mod (p * c₁) α).symm
    rw [hc, Int.toNat_natCast]
  rw [sum_dilatedPairShiftEdge_eq_progression _ _ hα, hrcast]
  set r : ℕ := (p * c₁) % α with hrdef
  have hzero : ∀ j ∈ Finset.range H, j ∉ (Finset.range H).filter (fun j ↦ α * j + r < H) →
      blockExtend b (α * j + r) * blockExtend c (α * j + r + p * h) = 0 := by
    intro j hj hj'
    simp only [Finset.mem_filter, Finset.mem_range] at hj hj'
    have hover : ¬ (α * j + r < H) := fun hlt ↦ hj' ⟨hj, hlt⟩
    simp only [blockExtend]
    rw [dif_neg hover, zero_mul]
  rw [Finset.sum_subset (Finset.filter_subset _ _) hzero]
  exact Fin.sum_univ_eq_sum_range
    (fun j ↦ blockExtend b (α * j + r) * blockExtend c (α * j + r + p * h)) H

/-- **The dilated Fourier mean, from the reindexed family.** -/
theorem genPrimeGraphMean_dilatedEdgeReindexed {H : ℕ} (w : ℕ → ℂ) (b c : Fin H → ℂ)
    {α : ℕ} (hα : 0 < α) (c₁ h : ℕ) (s : Finset ℕ) :
    genPrimeGraphMean w (dilatedEdgeReindexed b c α c₁ h) s =
      dilatedPairTwistedMean w b c α c₁ h s := by
  simp only [genPrimeGraphMean, dilatedPairTwistedMean]
  exact Finset.sum_congr rfl fun p _ ↦ by rw [sum_dilatedEdgeReindexed b c hα c₁ h p]

/-- **The join, at the reindexed dilated edge.** -/
theorem genMeanCRT_dilatedEdgeReindexed {H : ℕ} (w : ℕ → ℂ) (b c : Fin H → ℂ)
    {α : ℕ} (hα : 0 < α) (c₁ h : ℕ) (s : Finset ℕ) (hs : s ⊆ Nat.primesLE H) :
    genMeanCRT w (dilatedEdgeReindexed b c α c₁ h) s =
      dilatedPairTwistedMean w b c α c₁ h s :=
  (genMeanCRT_eq_genPrimeGraphMean w _ s hs).trans
    (genPrimeGraphMean_dilatedEdgeReindexed w b c hα c₁ h s)

theorem norm_blockExtend_le {H : ℕ} {b : Fin H → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ j, ‖b j‖ ≤ B) (i : ℕ) : ‖blockExtend b i‖ ≤ B := by
  unfold blockExtend
  split_ifs with hi
  · exact hb _
  · simpa using hB

theorem norm_dilatedEdgeReindexed_le {H : ℕ} {b c : Fin H → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ j, ‖b j‖ ≤ B) (hc : ∀ j, ‖c j‖ ≤ B) (α c₁ h : ℕ) (p : ℕ) (j : Fin H) :
    ‖dilatedEdgeReindexed b c α c₁ h p j‖ ≤ B ^ 2 := by
  unfold dilatedEdgeReindexed
  rw [norm_mul, sq]
  exact mul_le_mul (norm_blockExtend_le hB hb _) (norm_blockExtend_le hB hc _)
    (norm_nonneg _) hB

end

end NormalNumbers.ElliottDilatedBridge

#print axioms NormalNumbers.ElliottDilatedBridge.genMeanCRT_dilatedEdgeFamily
#print axioms NormalNumbers.ElliottDilatedBridge.norm_dilatedEdgeFamily_le

#print axioms NormalNumbers.ElliottDilatedBridge.genSum_natCast_sub_crtShift

#print axioms NormalNumbers.ElliottDilatedBridge.genMeanCRT_dilatedEdgeReindexed
#print axioms NormalNumbers.ElliottDilatedBridge.norm_dilatedEdgeReindexed_le
