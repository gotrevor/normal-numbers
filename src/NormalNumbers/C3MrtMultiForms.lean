/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtTupleMass

/-!
# Nondegeneracy of the `K` linear forms

After the `K`-fold CRT, the joint progression `{n : ∀ i, d_i ∣ n+i+1}` is the class `n ≡ a`
mod `L = lcm(d_i)`, so `n = L·k + a` and the `i`-th shift becomes

    (n + i + 1)/d_i = (L/d_i)·k + (a + i + 1)/d_i ,

a linear form in the progression variable `k` with leading coefficient `A_i = L/d_i` and offset
`B_i = (a+i+1)/d_i`.  `ProductLogElliott K` / `KPointLogElliott K` require these forms to be
**pairwise nondegenerate**: `A_i B_j − A_j B_i ≠ 0` for `i ≠ j`.

Lap 38 flagged this as the next place a `K = 2` accident could be hiding, since at `K = 2` the
determinant is exactly `1` (`linear_forms_det_eq_one`) and that looked like luck.  It is not:

    A_i B_j − A_j B_i  =  L·(j − i) / (d_i d_j)          (`multi_forms_det`)

so the determinant is a nonzero multiple of `j − i`, and nondegeneracy holds for **every** `K`
and every tuple, with no arithmetic hypothesis beyond `d_i ∣ L` and `d_i ∣ a+i+1` — which the CRT
supplies by construction.  At `K = 2`, `L = d_0d_1` and `j − i = 1` recover the old `1`.

`multi_forms_det` is stated as an exact integer identity after clearing the denominators
`d_i d_j`, so no division in `ℕ` has to be reasoned about beyond `Nat.mul_div_cancel'`.
-/

open Finset

namespace NormalNumbers

namespace CastingOut

/-- **The determinant of two of the `K` forms, exactly.**  Cleared of denominators:

    d_i d_j (A_i B_j − A_j B_i) = L (j − i) .
-/
theorem multi_forms_det {L a di dj i j : ℕ} (hdiL : di ∣ L) (hdjL : dj ∣ L)
    (hdi : di ∣ a + i + 1) (hdj : dj ∣ a + j + 1) :
    (di : ℤ) * (dj : ℤ) * (((L / di : ℕ) : ℤ) * (((a + j + 1) / dj : ℕ) : ℤ)
        - ((L / dj : ℕ) : ℤ) * (((a + i + 1) / di : ℕ) : ℤ))
      = (L : ℤ) * ((j : ℤ) - (i : ℤ)) := by
  have e1 : (di : ℤ) * ((L / di : ℕ) : ℤ) = (L : ℤ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) (Nat.mul_div_cancel' hdiL)
  have e2 : (dj : ℤ) * ((L / dj : ℕ) : ℤ) = (L : ℤ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) (Nat.mul_div_cancel' hdjL)
  have e3 : (di : ℤ) * (((a + i + 1) / di : ℕ) : ℤ) = (a : ℤ) + (i : ℤ) + 1 := by
    have := congrArg (Nat.cast : ℕ → ℤ) (Nat.mul_div_cancel' hdi)
    push_cast at this ⊢
    linarith [this]
  have e4 : (dj : ℤ) * (((a + j + 1) / dj : ℕ) : ℤ) = (a : ℤ) + (j : ℤ) + 1 := by
    have := congrArg (Nat.cast : ℕ → ℤ) (Nat.mul_div_cancel' hdj)
    push_cast at this ⊢
    linarith [this]
  have hrw : (di : ℤ) * (dj : ℤ) * (((L / di : ℕ) : ℤ) * (((a + j + 1) / dj : ℕ) : ℤ)
        - ((L / dj : ℕ) : ℤ) * (((a + i + 1) / di : ℕ) : ℤ))
      = ((di : ℤ) * ((L / di : ℕ) : ℤ)) * ((dj : ℤ) * (((a + j + 1) / dj : ℕ) : ℤ))
        - ((dj : ℤ) * ((L / dj : ℕ) : ℤ)) * ((di : ℤ) * (((a + i + 1) / di : ℕ) : ℤ) ) := by
    ring
  rw [hrw, e1, e2, e3, e4]
  ring

/-- **Nondegeneracy, for every `K`.**  No hypothesis beyond what the CRT supplies. -/
theorem multi_forms_nondegenerate {L a di dj i j : ℕ} (hL : 0 < L) (hdi : 0 < di) (hdj : 0 < dj)
    (hdiL : di ∣ L) (hdjL : dj ∣ L) (hia : di ∣ a + i + 1) (hja : dj ∣ a + j + 1)
    (hij : i ≠ j) :
    ((L / di : ℕ) : ℤ) * (((a + j + 1) / dj : ℕ) : ℤ)
      - ((L / dj : ℕ) : ℤ) * (((a + i + 1) / di : ℕ) : ℤ) ≠ 0 := by
  intro h0
  have hdet := multi_forms_det hdiL hdjL hia hja
  rw [h0, mul_zero] at hdet
  have hLne : (L : ℤ) ≠ 0 := by exact_mod_cast hL.ne'
  have hji : (j : ℤ) - (i : ℤ) = 0 := by
    rcases mul_eq_zero.1 hdet.symm with h | h
    · exact absurd h hLne
    · exact h
  have : (j : ℤ) = (i : ℤ) := by linarith
  exact hij (by exact_mod_cast this.symm)

/-- **The packaged `NondegenerateForms` instance** for the `K` forms the assembly produces. -/
theorem nondegenerateForms_multi {K L a : ℕ} (hL : 0 < L) (d : Fin K → ℕ)
    (hd : ∀ i, 0 < d i) (hdL : ∀ i, d i ∣ L) (hda : ∀ i : Fin K, d i ∣ a + (i : ℕ) + 1) :
    NondegenerateForms (fun i : Fin K => L / d i)
      (fun i : Fin K => (((a + (i : ℕ) + 1) / d i : ℕ) : ℤ)) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · exact Nat.div_pos (Nat.le_of_dvd hL (hdL i)) (hd i)
  · exact multi_forms_nondegenerate hL (hd i) (hd j) (hdL i) (hdL j) (hda i) (hda j)
      (fun h => hij (Fin.val_injective h))

/-! ## The `K`-fold CRT

The joint progression, when nonempty, is a single class modulo the joint modulus `lcm(d_i)`.
This is what turns the inner sum into an initial segment in a progression variable (then
`filter_linear_lt_eq_range` applies verbatim with `L` in place of `d·e`).  Note it needs no
coprimality: only that each `d_i` divides `L`.
-/

/-- **`K`-fold CRT.**  If the joint progression contains `n₀`, it is exactly the class of `n₀`
modulo `L = lcm(d_i)`. -/
theorem joint_class_multi {K : ℕ} (d : Fin K → ℕ) {n₀ : ℕ}
    (hn₀ : ∀ i : Fin K, d i ∣ n₀ + (i : ℕ) + 1) (n : ℕ) :
    (∀ i : Fin K, d i ∣ n + (i : ℕ) + 1) ↔ n ≡ n₀ [MOD Finset.univ.lcm d] := by
  have cast_of : ∀ (e m : ℕ) (k : ℕ), e ∣ m + k + 1 → (e : ℤ) ∣ (m : ℤ) + (k : ℤ) + 1 := by
    intro e m k h
    have h' : ((e : ℕ) : ℤ) ∣ ((m + k + 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr h
    push_cast at h'
    exact h'
  have of_cast : ∀ (e m : ℕ) (k : ℕ), (e : ℤ) ∣ (m : ℤ) + (k : ℤ) + 1 → e ∣ m + k + 1 := by
    intro e m k h
    have h' : ((e : ℕ) : ℤ) ∣ ((m + k + 1 : ℕ) : ℤ) := by push_cast; exact h
    exact Int.natCast_dvd_natCast.mp h'
  have hz₀ : ∀ i : Fin K, (d i : ℤ) ∣ (n₀ : ℤ) + ((i : ℕ) : ℤ) + 1 :=
    fun i => cast_of _ _ _ (hn₀ i)
  constructor
  · intro hn
    rw [Nat.modEq_iff_dvd]
    have hz : ∀ i : Fin K, (d i : ℤ) ∣ (n : ℤ) + ((i : ℕ) : ℤ) + 1 :=
      fun i => cast_of _ _ _ (hn i)
    have hdiff : ∀ i : Fin K, (d i : ℤ) ∣ (n₀ : ℤ) - (n : ℤ) := by
      intro i
      have h1 := dvd_sub (hz₀ i) (hz i)
      have heq : ((n₀ : ℤ) + ((i : ℕ) : ℤ) + 1) - ((n : ℤ) + ((i : ℕ) : ℤ) + 1)
          = (n₀ : ℤ) - (n : ℤ) := by ring
      rwa [heq] at h1
    have hnat : ∀ i : Fin K, d i ∣ ((n₀ : ℤ) - (n : ℤ)).natAbs := by
      intro i
      have := hdiff i
      rwa [Int.natCast_dvd] at this
    have hlcm : Finset.univ.lcm d ∣ ((n₀ : ℤ) - (n : ℤ)).natAbs :=
      Finset.lcm_dvd fun i _ => hnat i
    rwa [Int.natCast_dvd]
  · intro hmod i
    have hdL : d i ∣ Finset.univ.lcm d := Finset.dvd_lcm (Finset.mem_univ i)
    rw [Nat.modEq_iff_dvd] at hmod
    have h1 : (d i : ℤ) ∣ (n₀ : ℤ) - (n : ℤ) :=
      dvd_trans (Int.natCast_dvd_natCast.mpr hdL) hmod
    have h3 : (d i : ℤ) ∣ (n : ℤ) + ((i : ℕ) : ℤ) + 1 := by
      have heq : ((n : ℤ) + ((i : ℕ) : ℤ) + 1)
          = ((n₀ : ℤ) + ((i : ℕ) : ℤ) + 1) - ((n₀ : ℤ) - (n : ℤ)) := by ring
      rw [heq]
      exact dvd_sub (hz₀ i) h1
    exact of_cast _ _ _ h3

end CastingOut

end NormalNumbers

-- axiom audit
#print axioms NormalNumbers.CastingOut.multi_forms_det
#print axioms NormalNumbers.CastingOut.multi_forms_nondegenerate
#print axioms NormalNumbers.CastingOut.nondegenerateForms_multi
#print axioms NormalNumbers.CastingOut.joint_class_multi
