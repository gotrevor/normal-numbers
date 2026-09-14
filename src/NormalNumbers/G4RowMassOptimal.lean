/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4RowMass

/-!
# The row `L¹` mass is optimal — and why that closes base two

The §4D error budget is carried by the row mass `rowL1 b K = (2/b)^K/(b−1)`: the test array
`A = D_s^{⊗K}` has `∑_α |A_{aα}| = 2^K` (`sum_abs_kronPow_diffZ`) and the retained layers
contribute `∑_{j>K} b^{−j} = b^{−K}/(b−1)`.  At `b = 2` that product is exactly `1`
(`rowL1_two`), which is what refutes base two on this route.

This module shows the refutation is **not** an artefact of the particular array.  A test array
must annihilate the first `K` arithmetic layers, and in the affine grid each tensor coordinate
kills exactly one layer (the shift `ρ_{αj} = j·d_α − t_α` is affine in the atom digits, so the
coordinate `α_i` drops out of layer `j` exactly when `j·D_i = T_i` — one `j` per coordinate).
So such an array has **vanishing line sums in all `K` directions**, and:

* `two_pow_le_sum_abs` — every nonzero integer array on `(Fin K → Fin (s+1))` whose line sums
  all vanish has `∑_α |μ α| ≥ 2^K`.  Induction on `K`: the slices along the last coordinate
  each have vanishing line sums in the remaining `K−1` directions, and at least two of them
  are nonzero because they sum to zero.
* `sum_abs_kronPow_diffZ` attains it (`lineSumsZero_kronPow_diffZ` +
  `kronPow_diffZ_ne_zero`), so `D_s^{⊗K}` is `L¹`-optimal;
* `rowL1_le_rowMass` — hence *every* such design has row mass `≥ rowL1 b K`;
* `one_le_rowMass_two` — and at `b = 2` that is `≥ 1`, for every design in the family.
  Since the §4D budget needs the very-large-prime term `≤ δ·ε·η < 1`, base two is refuted for
  the whole family, not just for our parameters.  The only escape is *signed* cancellation in
  the `p > Y` range, i.e. the deep two-point correlation input this campaign excludes.
-/

open Finset

namespace NormalNumbers.G4


/-- All of `μ`'s line sums vanish: in every coordinate direction `i`, summing `μ` over that
coordinate alone gives zero. -/
def LineSumsZero {K s : ℕ} (μ : (Fin K → Fin (s + 1)) → ℤ) : Prop :=
  ∀ (i : Fin K) (β : Fin K → Fin (s + 1)), ∑ c : Fin (s + 1), μ (Function.update β i c) = 0

theorem two_pow_le_sum_abs {s : ℕ} : ∀ {K : ℕ} (μ : (Fin K → Fin (s + 1)) → ℤ),
    LineSumsZero μ → μ ≠ 0 → (2 : ℤ) ^ K ≤ ∑ α, |μ α| := by
  intro K
  induction K with
  | zero =>
    intro μ _ hne
    obtain ⟨α, hα⟩ := Function.ne_iff.1 hne
    simp only [Pi.zero_apply] at hα
    have hsum : (∑ a : Fin 0 → Fin (s + 1), |μ a|) = |μ α| :=
      Finset.sum_eq_single α (fun b _ hb => absurd (Subsingleton.elim b α) hb)
        (fun hb => absurd (Finset.mem_univ α) hb)
    rw [hsum, pow_zero]
    exact Int.one_le_abs hα
  | succ K ih =>
    intro μ h hne
    classical
    set ν : Fin (s + 1) → (Fin K → Fin (s + 1)) → ℤ := fun c β => μ (Fin.cons c β) with hν
    have h0 : ∀ β, ∑ c, ν c β = 0 := by
      intro β
      have := h 0 (Fin.cons 0 β)
      simpa [hν, Fin.update_cons_zero] using this
    have hslice : ∀ c, LineSumsZero (ν c) := by
      intro c i β
      have := h i.succ (Fin.cons c β)
      simpa [hν, Fin.cons_update] using this
    obtain ⟨α, hα⟩ := Function.ne_iff.1 hne
    simp only [Pi.zero_apply] at hα
    have hc0 : ν (α 0) (Fin.tail α) ≠ 0 := by
      simpa [hν, Fin.cons_self_tail] using hα
    have hne0 : ν (α 0) ≠ 0 := fun hh => hc0 (by rw [hh]; rfl)
    obtain ⟨c₁, hc₁ne, hc₁⟩ : ∃ c₁, c₁ ≠ α 0 ∧ ν c₁ ≠ 0 := by
      by_contra hcon
      simp only [not_exists, not_and, not_not] at hcon
      have hz := h0 (Fin.tail α)
      rw [Finset.sum_eq_single (α 0)] at hz
      · exact hc0 hz
      · intro c _ hcne
        rw [hcon c hcne]
        rfl
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    have hsplit : (∑ a : Fin (K + 1) → Fin (s + 1), |μ a|)
        = ∑ c : Fin (s + 1), ∑ β : Fin K → Fin (s + 1), |ν c β| := by
      have e := Fintype.sum_equiv (Fin.consEquiv fun _ => Fin (s + 1))
        (fun p : Fin (s + 1) × (Fin K → Fin (s + 1)) => |μ (Fin.cons p.1 p.2)|)
        (fun a => |μ a|) (fun p => rfl)
      rw [← e, Fintype.sum_prod_type]
    have hnonneg : ∀ c, 0 ≤ ∑ β, |ν c β| := fun c => Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hpair : (∑ c ∈ ({α 0, c₁} : Finset (Fin (s + 1))), ∑ β, |ν c β|)
        ≤ ∑ c, ∑ β, |ν c β| :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun c _ _ => hnonneg c
    rw [Finset.sum_pair (Ne.symm hc₁ne)] at hpair
    have h1 := ih (ν (α 0)) (hslice _) hne0
    have h2 := ih (ν c₁) (hslice _) hc₁
    rw [hsplit]
    calc (2 : ℤ) ^ (K + 1) = 2 ^ K + 2 ^ K := by ring
      _ ≤ (∑ β, |ν (α 0) β|) + ∑ β, |ν c₁ β| := by omega
      _ ≤ _ := hpair


/-! ### The tensor row attains the bound -/

/-- Every row of `A = D_s^{⊗K}` has vanishing line sums: fixing all but one atom coordinate
and summing over that coordinate gives `(∑_c D_s(a_i, c)) · ∏_{i' ≠ i} D_s(a_{i'}, β_{i'}) = 0`.
This is the "coordinate-fibre cancellation" that annihilates the first `K` layers. -/
theorem lineSumsZero_kronPow_diffZ {K s : ℕ} (a : Fin K → Fin s) :
    LineSumsZero (fun α => kronPow K (diffZ s) a α) := by
  classical
  intro i β
  have hfac : ∀ c : Fin (s + 1), kronPow K (diffZ s) a (Function.update β i c)
      = diffZ s (a i) c * ∏ i' ∈ Finset.univ.erase i, diffZ s (a i') (β i') := by
    intro c
    rw [kronPow, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self]
    congr 1
    exact Finset.prod_congr rfl fun i' hi' => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi')]
  rw [Finset.sum_congr rfl fun c _ => hfac c, ← Finset.sum_mul, sum_diffZ_row s (a i), zero_mul]

/-- A row of `A = D_s^{⊗K}` is nonzero: it is `1` at the atom `α = castSucc ∘ a`. -/
theorem kronPow_diffZ_ne_zero {K s : ℕ} (a : Fin K → Fin s) :
    (fun α => kronPow K (diffZ s) a α) ≠ 0 := by
  intro hz
  have h1 : kronPow K (diffZ s) a (fun i => (a i).castSucc) = 1 := by
    rw [kronPow]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [diffZ_apply, if_pos rfl, if_neg (castSucc_ne_succ (a i))]
    ring
  rw [congrFun hz (fun i => (a i).castSucc)] at h1
  exact absurd h1 (by norm_num)

/-- The real-valued form of the lower bound. -/
theorem two_pow_le_sum_abs_real {K s : ℕ} (μ : (Fin K → Fin (s + 1)) → ℤ)
    (h : LineSumsZero μ) (hne : μ ≠ 0) :
    (2 : ℝ) ^ K ≤ ∑ α, |((μ α : ℤ) : ℝ)| := by
  have hZ := two_pow_le_sum_abs μ h hne
  have hcast : ((∑ α, |μ α| : ℤ) : ℝ) = ∑ α, |((μ α : ℤ) : ℝ)| := by push_cast; rfl
  calc (2 : ℝ) ^ K = ((2 ^ K : ℤ) : ℝ) := by push_cast; ring
    _ ≤ ((∑ α, |μ α| : ℤ) : ℝ) := by exact_mod_cast hZ
    _ = _ := hcast

/-- **`D_s^{⊗K}` is `L¹`-optimal**: the tensor row has vanishing line sums, is nonzero, and its
`L¹` mass `2^K` is the least possible for such an array. -/
theorem sum_abs_kronPow_diffZ_eq_min {K s : ℕ} (a : Fin K → Fin s) :
    ∑ α : Fin K → Fin (s + 1), |((kronPow K (diffZ s) a α : ℤ) : ℝ)| = 2 ^ K :=
  sum_abs_kronPow_diffZ a

/-! ### The row mass of any design, and base two -/

/-- **Every design in the family has row mass at least `rowL1 b K`.**  The layers `j > K`
contribute `∑_{j>K} b^{−j} = 1/(b^K(b−1))`, so the mass of a design with array `μ` is
`(∑_α|μ α|)/(b^K(b−1)) ≥ 2^K/(b^K(b−1)) = rowL1 b K`. -/
theorem rowL1_le_rowMass {K s : ℕ} {b : ℝ} (hb : 1 < b) (μ : (Fin K → Fin (s + 1)) → ℤ)
    (h : LineSumsZero μ) (hne : μ ≠ 0) :
    rowL1 b K ≤ (∑ α, |((μ α : ℤ) : ℝ)|) / (b ^ K * (b - 1)) := by
  have hb0 : (0 : ℝ) < b := by linarith
  have hden : (0 : ℝ) < b ^ K * (b - 1) := by positivity
  have hmass : (2 : ℝ) ^ K ≤ ∑ α, |((μ α : ℤ) : ℝ)| := two_pow_le_sum_abs_real μ h hne
  rw [rowL1, div_le_div_iff₀ (by positivity) hden]
  have hbK : (0 : ℝ) < b ^ K := by positivity
  have hrw : ((2 : ℝ) / b) ^ K * (b ^ K * (b - 1)) = 2 ^ K * (b - 1) := by
    rw [div_pow]
    field_simp
  rw [hrw]
  have : (0 : ℝ) < b - 1 := by linarith
  nlinarith

/-- `rowL1 2 K = 1`: at base two the `2^K` cost of killing `K` layers exactly cancels the
`2^{−K}` gain. -/
@[simp] theorem rowL1_two (K : ℕ) : rowL1 2 K = 1 := by
  rw [rowL1]; norm_num

/-- **Base two is refuted for the whole design family.**  Every nonzero integer test array
with vanishing line sums has row mass `≥ 1` at `b = 2`, while §4D's very-large-prime budget
needs that mass `≤ δ_big·ε·η < 1`. -/
theorem one_le_rowMass_two {K s : ℕ} (μ : (Fin K → Fin (s + 1)) → ℤ)
    (h : LineSumsZero μ) (hne : μ ≠ 0) :
    (1 : ℝ) ≤ (∑ α, |((μ α : ℤ) : ℝ)|) / (2 ^ K * (2 - 1)) := by
  have := rowL1_le_rowMass (K := K) (s := s) (b := 2) (by norm_num) μ h hne
  rwa [rowL1_two] at this

end NormalNumbers.G4
