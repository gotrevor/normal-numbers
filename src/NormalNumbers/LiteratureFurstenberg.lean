/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Literature
import NormalNumbers.Furstenberg

/-!
# Ledger edge: Furstenberg's dense-orbit theorem 📚→✅

`Furstenberg.lean` proves the ×p×q topological rigidity theorem and its
Diophantine corollary `dense_orbit_of_not_isOfFinAddOrder` on
`UnitAddCircle`.  This file wires the ledger node
`Literature.furstenberg_dense_orbit` — the `Int.fract` form: for irrational
`x` and every `0 ≤ a < c ≤ 1` some `{2^m 3^n x}` lies in `[a, c)` — from it.

The bridge: an irrational real is a non-torsion point of the circle
(`AddCircle.not_isOfFinAddOrder_iff_forall_rat_ne_div`); the image of the
open interval `(a, c)` under the quotient map is open and nonempty, so the
dense orbit meets it; and two points of `[0, 1)` with the same image in the
circle are equal (`AddCircle.coe_eq_coe_iff_of_mem_Ico`).
-/

namespace NormalNumbers.Literature

open NormalNumbers

/-- An irrational real is a non-torsion point of `UnitAddCircle`. -/
theorem not_isOfFinAddOrder_of_irrational {x : ℝ} (hx : Irrational x) :
    ¬ IsOfFinAddOrder (x : UnitAddCircle) := by
  rw [AddCircle.not_isOfFinAddOrder_iff_forall_rat_ne_div]
  intro q hq
  rw [div_one] at hq
  exact hx ⟨q, hq⟩

/-- **Wired edge: Furstenberg 1967, the dense-orbit theorem** for `×2 ×3`,
from `Furstenberg.dense_orbit_of_not_isOfFinAddOrder`. -/
theorem furstenberg_dense_orbit_holds : furstenberg_dense_orbit := by
  intro x hx a c ha hac hc1
  have hnt := not_isOfFinAddOrder_of_irrational hx
  have hdense := Furstenberg.dense_orbit_of_not_isOfFinAddOrder (by norm_num) (by norm_num)
    Furstenberg.multIndep_two_three hnt
  set U : Set UnitAddCircle := (fun t : ℝ => (t : UnitAddCircle)) '' Set.Ioo a c with hUdef
  have hopen : IsOpen U := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hne : U.Nonempty := ⟨_, (a + c) / 2, ⟨by linarith, by linarith⟩, rfl⟩
  obtain ⟨y, hyO, hyU⟩ := hdense.exists_mem_open hopen hne
  obtain ⟨r, s, rfl⟩ := hyO
  obtain ⟨t, ⟨hta, htc⟩, ht⟩ := hyU
  refine ⟨r, s, ?_⟩
  -- the orbit point is the class of the real `2^r 3^s x`
  set u : ℝ := (2 : ℝ) ^ r * 3 ^ s * x with hudef
  have hcoe : (2 ^ r * 3 ^ s) • (x : UnitAddCircle) = (u : UnitAddCircle) := by
    rw [← QuotientAddGroup.mk_nsmul, nsmul_eq_mul, hudef]
    push_cast; rfl
  have ht' : (t : UnitAddCircle) = (2 ^ r * 3 ^ s) • (x : UnitAddCircle) := ht
  have hfr : ((Int.fract u : ℝ) : UnitAddCircle) = (t : UnitAddCircle) := by
    rw [Furstenberg.coe_fract, ← hcoe, ht']
  have hfr' : Int.fract u = t := by
    have h0 : (0 : ℝ) + 1 = 1 := by norm_num
    refine (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := 0) ?_ ?_).1 hfr
    · rw [h0]; exact ⟨Int.fract_nonneg u, Int.fract_lt_one u⟩
    · rw [h0]; exact ⟨by linarith, by linarith⟩
  rw [hfr']
  exact ⟨hta.le, htc⟩

end NormalNumbers.Literature
