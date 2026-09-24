import NormalNumbers.TwoPointDeficit

/-!
# The right combinatorial tool: a rotation pairing

Lap 20's `norm_sum_le_of_separated` asks for *all* cross pairs `(m, m')` to have separated
values — far too strong for an arithmetic input, since `ω(pm+1)` and `ω(pm'+1)` are unrelated for
unrelated `m, m'`.  What an arithmetic argument can plausibly supply is a **pairing**: an
injection `σ` on a positive-density set `A` of indices with `f(σ m) = z·f(m)` for a fixed
rotation `z ≠ 1` — e.g. `σ` moving `m` so that exactly one extra prime divides `pm+1` while the
`q`-side and the weight are unchanged, which multiplies the summand by exactly `ζ`.

That hypothesis does give a saving, and this file proves the conversion:

    ‖Σ_{m∈S} f(m)‖  ≤  (|S| − 2|A|)  +  ‖1 + z‖·|A| ,

a saving of `(2 − ‖1+z‖)·|A|`, which is positive for every `z ≠ 1` on the unit circle.  With
`|A| = α|S|` the relative saving is `(2 − ‖1+z‖)·α`, and lap 19 needs only `≍ L(w)²/π(w)`.

`twoPointTruncSum_pairing` states it for the leaf's summand.  The remaining arithmetic task is
now completely explicit: **find a density-`α` pairing of the `m`-range that multiplies
`ζ^{ω(pm+1)} conj ζ^{ω(qm+1)} W_{p,q}(m)` by a fixed `z ≠ 1`.**
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-- **THE ROTATION-PAIRING BOUND.** -/
theorem norm_sum_le_of_rotation (S A : Finset ℕ) (σ : ℕ → ℕ) (f : ℕ → ℂ) (z : ℂ)
    (hf : ∀ m ∈ S, ‖f m‖ ≤ 1) (hA : A ⊆ S)
    (hinj : ∀ m ∈ A, ∀ m' ∈ A, σ m = σ m' → m = m')
    (hσS : ∀ m ∈ A, σ m ∈ S) (hσA : ∀ m ∈ A, σ m ∉ A)
    (hrot : ∀ m ∈ A, f (σ m) = z * f m) :
    ‖∑ m ∈ S, f m‖ ≤ ((S.card : ℝ) - 2 * (A.card : ℝ)) + ‖1 + z‖ * (A.card : ℝ) := by
  classical
  set B := A.image σ with hB
  have hBcard : B.card = A.card := Finset.card_image_of_injOn (fun m hm m' hm' h => hinj m hm m' hm' h)
  have hBS : B ⊆ S := by
    intro y hy
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hy
    exact hσS m hm
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_right]
    intro y hy hyA
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hy
    exact hσA m hm hyA
  have hunion : A ∪ B ⊆ S := Finset.union_subset hA hBS
  have hsplit : ∑ m ∈ S, f m = ∑ m ∈ S \ (A ∪ B), f m + ∑ m ∈ A ∪ B, f m := by
    rw [Finset.sum_sdiff hunion]
  have hAB : ∑ m ∈ A ∪ B, f m = (1 + z) * ∑ m ∈ A, f m := by
    rw [Finset.sum_union hdisj, hB, Finset.sum_image (fun m hm m' hm' h => hinj m hm m' hm' h)]
    rw [Finset.sum_congr rfl hrot, ← Finset.mul_sum]
    ring
  have hcardU : (A ∪ B).card = 2 * A.card := by
    rw [Finset.card_union_of_disjoint hdisj, hBcard]; ring
  have hcardS : ((S \ (A ∪ B)).card : ℝ) = (S.card : ℝ) - 2 * (A.card : ℝ) := by
    have hle : 2 * A.card ≤ S.card := by
      rw [← hcardU]; exact Finset.card_le_card hunion
    have hcs : (S \ (A ∪ B)).card = S.card - 2 * A.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hunion, hcardU]
    rw [hcs, Nat.cast_sub hle]
    push_cast
    ring
  have h1 : ‖∑ m ∈ S \ (A ∪ B), f m‖ ≤ (S.card : ℝ) - 2 * (A.card : ℝ) := by
    refine le_trans (norm_sum_le _ _) ?_
    calc ∑ m ∈ S \ (A ∪ B), ‖f m‖ ≤ ∑ _m ∈ S \ (A ∪ B), (1:ℝ) :=
          Finset.sum_le_sum fun m hm => hf m (Finset.mem_sdiff.mp hm).1
      _ = ((S \ (A ∪ B)).card : ℝ) := by simp
      _ = _ := hcardS
  have h2 : ‖∑ m ∈ A ∪ B, f m‖ ≤ ‖1 + z‖ * (A.card : ℝ) := by
    rw [hAB, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine le_trans (norm_sum_le _ _) ?_
    calc ∑ m ∈ A, ‖f m‖ ≤ ∑ _m ∈ A, (1:ℝ) := Finset.sum_le_sum fun m hm => hf m (hA hm)
      _ = (A.card : ℝ) := by simp
  calc ‖∑ m ∈ S, f m‖ ≤ ‖∑ m ∈ S \ (A ∪ B), f m‖ + ‖∑ m ∈ A ∪ B, f m‖ := by
        rw [hsplit]; exact norm_add_le _ _
    _ ≤ _ := by linarith

/-- The leaf's per-pair sum, bounded by a rotation pairing of its index range. -/
theorem twoPointTruncSum_pairing (b p q : ℕ) (t : ℝ) (N : ℕ) (A : Finset ℕ) (σ : ℕ → ℕ) (z : ℂ)
    (hA : A ⊆ Finset.Ioc 0 (min (N / p) (N / q)))
    (hinj : ∀ m ∈ A, ∀ m' ∈ A, σ m = σ m' → m = m')
    (hσS : ∀ m ∈ A, σ m ∈ Finset.Ioc 0 (min (N / p) (N / q)))
    (hσA : ∀ m ∈ A, σ m ∉ A)
    (hrot : ∀ m ∈ A, twoPointFactor b p q t (σ m) * peelWeight b p q t (σ m)
      = z * (twoPointFactor b p q t m * peelWeight b p q t m)) :
    ‖twoPointTruncSum b p q t N‖
      ≤ (((min (N / p) (N / q) : ℕ) : ℝ) - 2 * (A.card : ℝ)) + ‖1 + z‖ * (A.card : ℝ) := by
  classical
  set S := Finset.Ioc 0 (min (N / p) (N / q)) with hS
  set f : ℕ → ℂ := fun m => twoPointFactor b p q t m * peelWeight b p q t m with hfdef
  have hf : ∀ m ∈ S, ‖f m‖ ≤ 1 := by
    intro m _
    rw [hfdef, norm_mul, norm_twoPointFactor, norm_peelWeight, mul_one]
  have hcardS : (S.card : ℝ) = ((min (N / p) (N / q) : ℕ) : ℝ) := by
    rw [hS, Nat.card_Ioc]; simp
  have := norm_sum_le_of_rotation S A σ f z hf hA hinj hσS hσA hrot
  rw [hcardS] at this
  calc ‖twoPointTruncSum b p q t N‖ = ‖∑ m ∈ S, f m‖ := by rw [twoPointTruncSum, hS, hfdef]
    _ ≤ _ := this

/-- With `|A| = α·|S|` the relative saving is `(2 − ‖1+z‖)·α`, positive whenever `z ≠ 1`
on the unit circle.  (Stated as the clean rearrangement of `norm_sum_le_of_rotation`.) -/
theorem norm_sum_le_of_rotation' (S A : Finset ℕ) (σ : ℕ → ℕ) (f : ℕ → ℂ) (z : ℂ) (α : ℝ)
    (hf : ∀ m ∈ S, ‖f m‖ ≤ 1) (hA : A ⊆ S)
    (hinj : ∀ m ∈ A, ∀ m' ∈ A, σ m = σ m' → m = m')
    (hσS : ∀ m ∈ A, σ m ∈ S) (hσA : ∀ m ∈ A, σ m ∉ A)
    (hrot : ∀ m ∈ A, f (σ m) = z * f m)
    (hz : ‖1 + z‖ ≤ 2) (hcard : α * (S.card : ℝ) ≤ (A.card : ℝ)) (hα : 0 ≤ α) :
    ‖∑ m ∈ S, f m‖ ≤ (1 - (2 - ‖1 + z‖) * α) * (S.card : ℝ) := by
  have h := norm_sum_le_of_rotation S A σ f z hf hA hinj hσS hσA hrot
  have hstep : ((S.card : ℝ) - 2 * (A.card : ℝ)) + ‖1 + z‖ * (A.card : ℝ)
      = (S.card : ℝ) - (2 - ‖1 + z‖) * (A.card : ℝ) := by ring
  rw [hstep] at h
  have hmul : (2 - ‖1 + z‖) * (α * (S.card : ℝ)) ≤ (2 - ‖1 + z‖) * (A.card : ℝ) :=
    mul_le_mul_of_nonneg_left hcard (by linarith)
  calc ‖∑ m ∈ S, f m‖ ≤ (S.card : ℝ) - (2 - ‖1 + z‖) * (A.card : ℝ) := h
    _ ≤ (S.card : ℝ) - (2 - ‖1 + z‖) * (α * (S.card : ℝ)) := by linarith
    _ = (1 - (2 - ‖1 + z‖) * α) * (S.card : ℝ) := by ring

end NormalNumbers.CastingOut
