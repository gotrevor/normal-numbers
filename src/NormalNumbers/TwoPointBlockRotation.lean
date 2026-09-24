import NormalNumbers.TwoPointPairingRigidity

/-!
# Blockwise rotation: the fix for lap 22's failure

Lap 21's tool required the rotation `z` with `f(σ m) = z·f(m)` to be **constant** on the paired
set.  Lap 22 showed that is unattainable: the multiplicative move `σ(m) = rm + k` controls the
`p`-dilate exactly but leaves the `q`-dilate shifted by `(q−p)k`, so the rotation varies with `m`.

The requirement was an artefact.  What the argument actually needs is only that `1 + z` is
*uniformly short*, pointwise:

* **`norm_sum_le_of_rotation_pointwise`** — if `σ` injects `A ⊆ S` into `S \ A` and
  `f(σ m) = Z(m)·f(m)` with `‖1 + Z(m)‖ ≤ 2 − c` for every `m ∈ A`, then

      ‖Σ_{m∈S} f(m)‖  ≤  |S| − c·|A| .

  No constancy of `Z`, no separation between different `m`'s: a *pointwise* gap suffices,
  because the pairing sums `f(m) + f(σ m) = (1 + Z(m))·f(m)` term by term.
* `norm_one_add_lt_two` — for unimodular `z ≠ 1`, `‖1+z‖ < 2`, so every nontrivial rotation
  carries a gap; and `norm_one_add_le_of_re_le` makes the gap explicit from a bound on `Re z`.
* `twoPointTruncSum_blockRotation` — the leaf's per-pair sum under a pointwise-gap pairing.

## The arithmetic target, restated

With `σ(m) = rm + k`, `r = pk+1`, `pairing_shift` gives `p·σ(m)+1 = r·(pm+1)` and
`q·σ(m)+1 = r·(qm+1) + (q−p)k`.  The rotation is therefore
`Z(m) = ζ^{Δ_p(m) − Δ_q(m)}·(weight ratio)` with `Δ_p(m) = ω(r(pm+1)) − ω(pm+1) = 1` off a thin
set, and `Δ_q(m) = ω(r(qm+1)+(q−p)k) − ω(qm+1)` unknown.  What is needed is **not** that `Δ_q` is
constant, only that `Δ_p − Δ_q ≢ 0 (mod b)` — equivalently `Δ_q(m) ≠ 1` in the relevant class —
for a positive density of `m`.  That is a statement about the `ω`-difference of two linear forms
missing one prescribed value: a sieve/statistical question, strictly weaker than any
equidistribution of `ω`, and the first target in this run that is not an Elliott-type statement.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-- **POINTWISE ROTATION BOUND.**  A per-`m` gap in `‖1 + Z(m)‖` suffices. -/
theorem norm_sum_le_of_rotation_pointwise (S A : Finset ℕ) (σ : ℕ → ℕ) (f : ℕ → ℂ) (Z : ℕ → ℂ)
    (c : ℝ) (hf : ∀ m ∈ S, ‖f m‖ ≤ 1) (hA : A ⊆ S)
    (hinj : ∀ m ∈ A, ∀ m' ∈ A, σ m = σ m' → m = m')
    (hσS : ∀ m ∈ A, σ m ∈ S) (hσA : ∀ m ∈ A, σ m ∉ A)
    (hrot : ∀ m ∈ A, f (σ m) = Z m * f m)
    (hgap : ∀ m ∈ A, ‖1 + Z m‖ ≤ 2 - c) :
    ‖∑ m ∈ S, f m‖ ≤ (S.card : ℝ) - c * (A.card : ℝ) := by
  classical
  set B := A.image σ with hB
  have hBcard : B.card = A.card :=
    Finset.card_image_of_injOn (fun m hm m' hm' h => hinj m hm m' hm' h)
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
  have hAB : ∑ m ∈ A ∪ B, f m = ∑ m ∈ A, (1 + Z m) * f m := by
    rw [Finset.sum_union hdisj, hB,
      Finset.sum_image (fun m hm m' hm' h => hinj m hm m' hm' h),
      Finset.sum_congr rfl hrot, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  have hcardU : (A ∪ B).card = 2 * A.card := by
    rw [Finset.card_union_of_disjoint hdisj, hBcard]; ring
  have hle : 2 * A.card ≤ S.card := by
    rw [← hcardU]; exact Finset.card_le_card hunion
  have hcardS : ((S \ (A ∪ B)).card : ℝ) = (S.card : ℝ) - 2 * (A.card : ℝ) := by
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
  have h2 : ‖∑ m ∈ A ∪ B, f m‖ ≤ (2 - c) * (A.card : ℝ) := by
    rw [hAB]
    refine le_trans (norm_sum_le _ _) ?_
    calc ∑ m ∈ A, ‖(1 + Z m) * f m‖ ≤ ∑ _m ∈ A, (2 - c) := by
          refine Finset.sum_le_sum fun m hm => ?_
          rw [norm_mul]
          have hfm := hf m (hA hm)
          have hgm := hgap m hm
          nlinarith [norm_nonneg (1 + Z m), norm_nonneg (f m), hfm, hgm]
      _ = (2 - c) * (A.card : ℝ) := by rw [Finset.sum_const]; simp [mul_comm]
  calc ‖∑ m ∈ S, f m‖ ≤ ‖∑ m ∈ S \ (A ∪ B), f m‖ + ‖∑ m ∈ A ∪ B, f m‖ := by
        rw [hsplit]; exact norm_add_le _ _
    _ ≤ ((S.card : ℝ) - 2 * (A.card : ℝ)) + (2 - c) * (A.card : ℝ) := by linarith
    _ = (S.card : ℝ) - c * (A.card : ℝ) := by ring

/-- For unimodular `z`, `‖1+z‖² = 2 + 2 Re z`; a bound on `Re z` is an explicit gap. -/
theorem norm_one_add_le_of_re_le (z : ℂ) (hz : ‖z‖ = 1) (ρ : ℝ) (hρ : z.re ≤ ρ)
    (hρ1 : -1 ≤ ρ) : ‖1 + z‖ ≤ Real.sqrt (2 + 2 * ρ) := by
  have hsq : ‖1 + z‖ ^ 2 = 2 + 2 * z.re := by
    have h := Complex.normSq_add 1 z
    rw [← Complex.normSq_eq_norm_sq, h]
    simp [Complex.normSq_eq_norm_sq, hz]
    ring
  have hnn : (0:ℝ) ≤ ‖1 + z‖ := norm_nonneg _
  have hle : ‖1 + z‖ ^ 2 ≤ 2 + 2 * ρ := by rw [hsq]; linarith
  calc ‖1 + z‖ = Real.sqrt (‖1 + z‖ ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ _ := Real.sqrt_le_sqrt hle

/-- Every nontrivial unimodular rotation carries a gap. -/
theorem norm_one_add_lt_two (z : ℂ) (hz : ‖z‖ = 1) (hne : z ≠ 1) : ‖1 + z‖ < 2 := by
  have hnormsq : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hz]; norm_num
    rw [Complex.normSq_apply] at h
    nlinarith [h]
  have hsq : ‖1 + z‖ ^ 2 = 2 + 2 * z.re := by
    have h : Complex.normSq (1 + z) = 1 + 2 * z.re + (z.re ^ 2 + z.im ^ 2) := by
      simp [Complex.normSq_apply]; ring
    rw [← Complex.normSq_eq_norm_sq, h, hnormsq]; ring
  have hre : z.re < 1 := by
    by_contra hcon
    push_neg at hcon
    have him : z.im = 0 := by nlinarith [hnormsq, hcon]
    have hre1 : z.re = 1 := by nlinarith [hnormsq, hcon, him]
    exact hne (Complex.ext (by simpa using hre1) (by simpa using him))
  have hnn : (0:ℝ) ≤ ‖1 + z‖ := norm_nonneg _
  nlinarith [hsq, hnn, hre]

/-- The leaf's per-pair sum under a pointwise-gap pairing. -/
theorem twoPointTruncSum_blockRotation (b p q : ℕ) (t : ℝ) (N : ℕ) (A : Finset ℕ) (σ : ℕ → ℕ)
    (Z : ℕ → ℂ) (c : ℝ)
    (hA : A ⊆ Finset.Ioc 0 (min (N / p) (N / q)))
    (hinj : ∀ m ∈ A, ∀ m' ∈ A, σ m = σ m' → m = m')
    (hσS : ∀ m ∈ A, σ m ∈ Finset.Ioc 0 (min (N / p) (N / q)))
    (hσA : ∀ m ∈ A, σ m ∉ A)
    (hrot : ∀ m ∈ A, twoPointFactor b p q t (σ m) * peelWeight b p q t (σ m)
      = Z m * (twoPointFactor b p q t m * peelWeight b p q t m))
    (hgap : ∀ m ∈ A, ‖1 + Z m‖ ≤ 2 - c) :
    ‖twoPointTruncSum b p q t N‖
      ≤ ((min (N / p) (N / q) : ℕ) : ℝ) - c * (A.card : ℝ) := by
  classical
  set S := Finset.Ioc 0 (min (N / p) (N / q)) with hS
  set f : ℕ → ℂ := fun m => twoPointFactor b p q t m * peelWeight b p q t m with hfdef
  have hf : ∀ m ∈ S, ‖f m‖ ≤ 1 := by
    intro m _
    rw [hfdef, norm_mul, norm_twoPointFactor, norm_peelWeight, mul_one]
  have hcardS : (S.card : ℝ) = ((min (N / p) (N / q) : ℕ) : ℝ) := by
    rw [hS, Nat.card_Ioc]; simp
  have hmain := norm_sum_le_of_rotation_pointwise S A σ f Z c hf hA hinj hσS hσA hrot hgap
  rw [hcardS] at hmain
  calc ‖twoPointTruncSum b p q t N‖ = ‖∑ m ∈ S, f m‖ := by rw [twoPointTruncSum, hS, hfdef]
    _ ≤ _ := hmain

end NormalNumbers.CastingOut
