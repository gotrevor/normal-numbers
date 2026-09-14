/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4Remainder

/-!
# G4 disjunctivity, §4D: the row masses of `A = D_s^{⊗K}`

The two §4D estimates both live on one row of the tensor matrix, so they both need its exact
masses.  Since `kronPow K M a α = ∏ᵢ M (a i) (α i)`, summing over all atoms factorises:

  `∑_α ∏ᵢ g i (α i) = ∏ᵢ ∑_c g i c`     (`sum_kronPow_eq_prod`)

and for `M = D_s`, whose rows are `+1` at `castSucc` and `−1` at `succ`:

* `∑_c D_s(a,c) = 0`, hence **`sum_kronPow_diffZ_eq_zero`**: every row of `A` has vanishing
  total mass — the *signed cancellation* the medium-prime range must preserve;
* `∑_c |D_s(a,c)| = 2`, hence **`sum_abs_kronPow_diffZ`**: `∑_α |A_{aα}| = 2^K`;
* `∑_c D_s(a,c)² = 2`, hence **`sum_sq_kronPow_diffZ`**: `∑_α A_{aα}² = 2^K`.

Combined with `∑_{j>K} 4^{−j} = 4^{−K}/3` and `∑_{j>K} 16^{−j} = 16^{−K}/15` these give the
draft's row budgets `∑_{α,j>K} |c_{αj}| = 2^{−K}/3` and `∑_{α,j>K} c_{αj}² = 8^{−K}/15`
(`sum_abs_coeff_le`, `sum_sq_coeff_le`).
-/

open Finset Matrix
open scoped BigOperators

namespace NormalNumbers.G4

variable {K s : ℕ}

/-! ### The tensor sum factorises -/

lemma sum_kronPow_eq_prod {R : Type*} [CommRing R] (M : Matrix (Fin s) (Fin (s + 1)) R)
    (a : Fin K → Fin s) :
    ∑ α : Fin K → Fin (s + 1), kronPow K M a α = ∏ i, ∑ c, M (a i) c := by
  classical
  rw [Finset.prod_univ_sum (fun _ => (Finset.univ : Finset (Fin (s + 1))))
    (fun i c => M (a i) c), Fintype.piFinset_univ]
  rfl

/-- The same, for any pointwise transform of the entries (absolute value, square, …). -/
lemma sum_kronPow_map_eq_prod {R : Type*} [CommRing R] (M : Matrix (Fin s) (Fin (s + 1)) R)
    (φ : R → ℝ) (hφ : ∀ x y, φ (x * y) = φ x * φ y) (hφ1 : φ 1 = 1)
    (a : Fin K → Fin s) :
    ∑ α : Fin K → Fin (s + 1), φ (kronPow K M a α) = ∏ i, ∑ c, φ (M (a i) c) := by
  classical
  rw [Finset.prod_univ_sum (fun _ => (Finset.univ : Finset (Fin (s + 1))))
    (fun i c => φ (M (a i) c)), Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun α _ => ?_
  unfold kronPow
  induction (Finset.univ : Finset (Fin K)) using Finset.induction_on with
  | empty => simp [hφ1]
  | insert i T hiT ih => rw [Finset.prod_insert hiT, Finset.prod_insert hiT, hφ, ih]

/-! ### The three masses of one `D_s` row -/

lemma castSucc_ne_succ (a : Fin s) : a.castSucc ≠ a.succ := Fin.castSucc_lt_succ.ne

lemma diffZ_apply (a : Fin s) (c : Fin (s + 1)) :
    diffZ s a c = (if c = a.castSucc then 1 else 0) - (if c = a.succ then 1 else 0) := by
  simp only [diffZ, Pi.sub_apply, Pi.single_apply]

private lemma sum_one_ite {b : Fin (s + 1)} :
    ∑ c : Fin (s + 1), (if c = b then (1 : ℝ) else 0) = 1 := by simp

lemma sum_diffZ_abs (a : Fin s) : ∑ c, |((diffZ s a c : ℤ) : ℝ)| = 2 := by
  classical
  have hne := castSucc_ne_succ a
  have h : ∀ c, |((diffZ s a c : ℤ) : ℝ)|
      = (if c = a.castSucc then (1 : ℝ) else 0) + (if c = a.succ then 1 else 0) := by
    intro c
    rw [diffZ_apply]
    by_cases h1 : c = a.castSucc
    · subst h1; simp [hne]
    · by_cases h2 : c = a.succ
      · subst h2; simp [h1]
      · simp [h1, h2]
  rw [Finset.sum_congr rfl (fun c _ => h c), Finset.sum_add_distrib, sum_one_ite, sum_one_ite]
  norm_num

lemma sum_diffZ_sq (a : Fin s) : ∑ c, ((diffZ s a c : ℤ) : ℝ) ^ 2 = 2 := by
  classical
  have hne := castSucc_ne_succ a
  have h : ∀ c, ((diffZ s a c : ℤ) : ℝ) ^ 2 = |((diffZ s a c : ℤ) : ℝ)| := by
    intro c
    rw [diffZ_apply]
    by_cases h1 : c = a.castSucc
    · subst h1; simp [hne]
    · by_cases h2 : c = a.succ
      · subst h2; simp [h1]
      · simp [h1, h2]
  rw [Finset.sum_congr rfl (fun c _ => h c), sum_diffZ_abs]

/-- **The signed row mass vanishes**: `∑_α A_{aα} = 0` for `K ≥ 1`.  This is the cancellation the
medium-prime range of §4D must preserve. -/
theorem sum_kronPow_diffZ_eq_zero (hK : 0 < K) (a : Fin K → Fin s) :
    ∑ α : Fin K → Fin (s + 1), ((kronPow K (diffZ s) a α : ℤ) : ℝ) = 0 := by
  have h := sum_kronPow_eq_prod (R := ℤ) (diffZ s) a
  have h0 : ∑ α : Fin K → Fin (s + 1), (kronPow K (diffZ s) a α : ℤ) = 0 := by
    rw [h]
    refine Finset.prod_eq_zero (Finset.mem_univ ⟨0, hK⟩) ?_
    exact sum_diffZ_row s _
  rw [← Int.cast_sum, h0, Int.cast_zero]

/-- **The ℓ¹ row mass**: `∑_α |A_{aα}| = 2^K`. -/
theorem sum_abs_kronPow_diffZ (a : Fin K → Fin s) :
    ∑ α : Fin K → Fin (s + 1), |((kronPow K (diffZ s) a α : ℤ) : ℝ)| = 2 ^ K := by
  have h := sum_kronPow_map_eq_prod (R := ℤ) (diffZ s) (fun x : ℤ => |((x : ℤ) : ℝ)|)
    (fun x y => by push_cast; exact abs_mul _ _) (by norm_num) a
  rw [h, Finset.prod_congr rfl (fun i _ => sum_diffZ_abs (a i))]
  simp

/-- **The ℓ² row mass**: `∑_α A_{aα}² = 2^K`. -/
theorem sum_sq_kronPow_diffZ (a : Fin K → Fin s) :
    ∑ α : Fin K → Fin (s + 1), ((kronPow K (diffZ s) a α : ℤ) : ℝ) ^ 2 = 2 ^ K := by
  have h := sum_kronPow_map_eq_prod (R := ℤ) (diffZ s) (fun x : ℤ => ((x : ℤ) : ℝ) ^ 2)
    (fun x y => by push_cast; ring) (by norm_num) a
  rw [h, Finset.prod_congr rfl (fun i _ => sum_diffZ_sq (a i))]
  simp

/-! ### The layer geometric budgets -/

lemma geom_range_le {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (N : ℕ) :
    ∑ i ∈ Finset.range N, r ^ i ≤ (1 - r)⁻¹ := by
  have h1 : (0 : ℝ) < 1 - r := by linarith
  have hrN : (0 : ℝ) ≤ r ^ N := by positivity
  rw [geom_sum_eq (by linarith : r ≠ 1),
    show (r ^ N - 1) / (r - 1) = (1 - r ^ N) / (1 - r) by
      rw [← neg_div_neg_eq]; congr 1 <;> ring,
    inv_eq_one_div]
  gcongr
  linarith

/-- `∑_{K < j ≤ J} 4^{−j} ≤ 4^{−K}/3`. -/
lemma sum_layer_inv_le (K N : ℕ) :
    ∑ jj : Fin N, (1 : ℝ) / (4 : ℝ) ^ layer K jj ≤ (1 / 4 : ℝ) ^ K / 3 := by
  have hterm : ∀ jj : Fin N, (1 : ℝ) / (4 : ℝ) ^ layer K jj
      = (1 / 4 : ℝ) ^ K * ((1 / 4 : ℝ) * (1 / 4 : ℝ) ^ (jj : ℕ)) := by
    intro jj
    rw [← _root_.one_div_pow]
    unfold layer
    rw [pow_add, pow_add, pow_one]
    ring
  rw [Finset.sum_congr rfl (fun jj _ => hterm jj), ← Finset.mul_sum,
    Fin.sum_univ_eq_sum_range (fun i => (1 / 4 : ℝ) * (1 / 4 : ℝ) ^ i) N, ← Finset.mul_sum]
  have h := geom_range_le (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num) N
  have h4 : (0 : ℝ) < (1 / 4 : ℝ) ^ K := by positivity
  rw [div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ h4.le
  calc (1 / 4 : ℝ) * ∑ i ∈ Finset.range N, (1 / 4 : ℝ) ^ i
      ≤ (1 / 4 : ℝ) * (1 - 1 / 4 : ℝ)⁻¹ := by linarith
    _ = (3 : ℝ)⁻¹ := by norm_num

/-- `∑_{K < j ≤ J} 16^{−j} ≤ 16^{−K}/15`. -/
lemma sum_layer_inv_sq_le (K N : ℕ) :
    ∑ jj : Fin N, ((1 : ℝ) / (4 : ℝ) ^ layer K jj) ^ 2 ≤ (1 / 16 : ℝ) ^ K / 15 := by
  have hterm : ∀ jj : Fin N, ((1 : ℝ) / (4 : ℝ) ^ layer K jj) ^ 2
      = (1 / 16 : ℝ) ^ K * ((1 / 16 : ℝ) * (1 / 16 : ℝ) ^ (jj : ℕ)) := by
    intro jj
    rw [div_pow, one_pow, ← pow_mul, mul_comm (layer K jj) 2, pow_mul, ← _root_.one_div_pow,
      show ((4 : ℝ) ^ 2) = 16 by norm_num]
    unfold layer
    rw [pow_add, pow_add, pow_one]
    ring
  rw [Finset.sum_congr rfl (fun jj _ => hterm jj), ← Finset.mul_sum,
    Fin.sum_univ_eq_sum_range (fun i => (1 / 16 : ℝ) * (1 / 16 : ℝ) ^ i) N, ← Finset.mul_sum]
  have h := geom_range_le (r := (1 / 16 : ℝ)) (by norm_num) (by norm_num) N
  have h16 : (0 : ℝ) < (1 / 16 : ℝ) ^ K := by positivity
  rw [div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ h16.le
  calc (1 / 16 : ℝ) * ∑ i ∈ Finset.range N, (1 / 16 : ℝ) ^ i
      ≤ (1 / 16 : ℝ) * (1 - 1 / 16 : ℝ)⁻¹ := by linarith
    _ = (15 : ℝ)⁻¹ := by norm_num

/-! ### The pointwise ℓ¹ bound on a layer block -/

/-- **The row ℓ¹ budget.**  If the weight is bounded by `C` on every retained argument, the whole
layer block is at most `C·2^{−K}/3`.  This is the §4D bound for the very-large primes `p > Y`,
where `C = O(1)` because an argument below `3X` has `O(1)` prime factors above `X^{1/100}`.  It
is *not* valid for all primes above `R`: that substitution is exactly what the brief forbids. -/
theorem abs_blockSum_le (G : GridParams) {w : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (n : ℕ) (a : Fin G.K → Fin G.s)
    (hw : ∀ α : G.Atom, ∀ jj : Fin G.N, |w (n + shiftAL G.B G.Q G.D₀ (α, jj))| ≤ C) :
    |blockSum G w n a| ≤ C * (1 / 2 : ℝ) ^ G.K / 3 := by
  classical
  have hlayer := sum_layer_inv_le G.K G.N
  calc |blockSum G w n a|
      ≤ ∑ α : G.Atom, |((kronPow G.K (diffZ G.s) a α : ℤ) : ℝ) *
          ∑ jj : Fin G.N, w (n + shiftAL G.B G.Q G.D₀ (α, jj)) / (4 : ℝ) ^ layer G.K jj| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ α : G.Atom, |((kronPow G.K (diffZ G.s) a α : ℤ) : ℝ)| *
          (C * ((1 / 4 : ℝ) ^ G.K / 3)) := by
        refine Finset.sum_le_sum fun α _ => ?_
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        calc |∑ jj : Fin G.N, w (n + shiftAL G.B G.Q G.D₀ (α, jj)) / (4 : ℝ) ^ layer G.K jj|
            ≤ ∑ jj : Fin G.N, |w (n + shiftAL G.B G.Q G.D₀ (α, jj)) / (4 : ℝ) ^ layer G.K jj| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ jj : Fin G.N, C * ((1 : ℝ) / (4 : ℝ) ^ layer G.K jj) := by
              refine Finset.sum_le_sum fun jj _ => ?_
              rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < (4:ℝ) ^ layer G.K jj),
                mul_one_div]
              gcongr
              exact hw α jj
          _ = C * ∑ jj : Fin G.N, (1 : ℝ) / (4 : ℝ) ^ layer G.K jj := by rw [Finset.mul_sum]
          _ ≤ C * ((1 / 4 : ℝ) ^ G.K / 3) := mul_le_mul_of_nonneg_left hlayer hC
    _ = (∑ α : G.Atom, |((kronPow G.K (diffZ G.s) a α : ℤ) : ℝ)|) *
          (C * ((1 / 4 : ℝ) ^ G.K / 3)) := by rw [Finset.sum_mul]
    _ = (2 : ℝ) ^ G.K * (C * ((1 / 4 : ℝ) ^ G.K / 3)) := by rw [sum_abs_kronPow_diffZ]
    _ = C * (1 / 2 : ℝ) ^ G.K / 3 := by
        have h2 : (0 : ℝ) < (2 : ℝ) ^ G.K := by positivity
        rw [div_pow, div_pow, one_pow,
          show ((4 : ℝ) ^ G.K) = (2 : ℝ) ^ G.K * (2 : ℝ) ^ G.K by rw [← mul_pow]; norm_num]
        field_simp

end NormalNumbers.G4
