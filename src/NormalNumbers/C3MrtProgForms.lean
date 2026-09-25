/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtNatural
import NormalNumbers.C3MrtMultiLinear

/-!
# The `K`-point inner sum along an extra fixed progression

`ProgressionLogRung K` (`C3MrtNatural`, obligation A) asks for the `K`-fold assembly's log-averaged
correlation bound with `n` restricted to a fixed progression `n ≡ n₀ (mod M)`.  This file is the
first brick: the CRT / reindexing layer.

**The structural point.**  The whole `K`-fold chain runs on *one* fact about the index set: the
joint progression `{n : ∀ i, d i ∣ n + i + 1}` is a single residue class mod `L = lcm(d_i)`.
Intersecting with `n ≡ n₀ (mod M)` gives a single residue class mod
`L' = lcm(M, lcm(d_i))` — same shape, larger modulus.  Nothing downstream needs `L'` to be the
*least* common multiple of the `d_i`: the forms `(L'/d_i)·X + (a+i+1)/d_i` are nondegenerate
because `multi_forms_det` only asks `d_i ∣ L'` (lap 39), and every mass estimate improves when the
modulus grows (`1/L' ≤ 1/L`).  So the extra progression is **free** for the estimates and costs
only this reindexing.

* `joint_class_prog` — the intersected CRT statement.
* `joint_base_prog` — the base point `a = n₀ % L'` satisfies both constraints, and `a < L'`.
* `inner_sum_prog_forms` — the reindexed inner sum, in the exact shape
  `initial_segment_bound_of_kElliott` consumes, with `L'` in place of `L`.
* `nondegenerateForms_prog` — the forms of a progression-restricted tuple are nondegenerate.
-/

open Finset

namespace NormalNumbers

namespace CastingOut

/-- The joint modulus of a tuple together with an extra fixed modulus `M`. -/
noncomputable def progLcm {K : ℕ} (M : ℕ) (d : Fin K → ℕ) : ℕ :=
  Nat.lcm M ((Finset.univ : Finset (Fin K)).lcm d)

theorem progLcm_pos {K : ℕ} {M : ℕ} (hM : 0 < M) (d : Fin K → ℕ) (hd : ∀ i, 0 < d i) :
    0 < progLcm M d :=
  Nat.pos_of_ne_zero (Nat.lcm_ne_zero hM.ne' (univLcm_pos d hd).ne')

theorem dvd_progLcm {K : ℕ} (M : ℕ) (d : Fin K → ℕ) (i : Fin K) : d i ∣ progLcm M d :=
  dvd_trans (Finset.dvd_lcm (Finset.mem_univ i)) (Nat.dvd_lcm_right _ _)

theorem mod_dvd_progLcm {K : ℕ} (M : ℕ) (d : Fin K → ℕ) : M ∣ progLcm M d :=
  Nat.dvd_lcm_left _ _

/-- **`K`-fold CRT with an extra progression.**  The intersection of the joint progression of `d`
with the class of `n₀` mod `M` is exactly the class of `n₀` mod `lcm(M, lcm d)`. -/
theorem joint_class_prog {K : ℕ} (M : ℕ) (d : Fin K → ℕ) {n₀ : ℕ}
    (hn₀ : ∀ i : Fin K, d i ∣ n₀ + (i : ℕ) + 1) (n : ℕ) :
    ((n ≡ n₀ [MOD M] ∧ ∀ i : Fin K, d i ∣ n + (i : ℕ) + 1)
      ↔ n ≡ n₀ [MOD progLcm M d]) := by
  constructor
  · rintro ⟨hM, hdvd⟩
    exact Nat.mod_lcm hM ((joint_class_multi d hn₀ n).1 hdvd)
  · intro h
    refine ⟨h.of_dvd (mod_dvd_progLcm M d), ?_⟩
    exact (joint_class_multi d hn₀ n).2 (h.of_dvd (Nat.dvd_lcm_right _ _))

/-- **The base point of the intersected class, below `L' = lcm(M, lcm d)`.** -/
theorem joint_base_prog {K : ℕ} {M : ℕ} (hM : 0 < M) (d : Fin K → ℕ) (hd : ∀ i, 0 < d i) {n₀ : ℕ}
    (hn₀ : ∀ i : Fin K, d i ∣ n₀ + (i : ℕ) + 1) :
    n₀ % progLcm M d < progLcm M d ∧ (n₀ % progLcm M d ≡ n₀ [MOD M]) ∧
      ∀ i : Fin K, d i ∣ n₀ % progLcm M d + (i : ℕ) + 1 := by
  have hL : 0 < progLcm M d := progLcm_pos hM d hd
  have hmod : n₀ % progLcm M d ≡ n₀ [MOD progLcm M d] := Nat.mod_modEq _ _
  obtain ⟨h1, h2⟩ := (joint_class_prog M d hn₀ (n₀ % progLcm M d)).2 hmod
  exact ⟨Nat.mod_lt _ hL, h1, h2⟩

/-- **The forms of a progression-restricted tuple are nondegenerate.**  `nondegenerateForms_of_tuple`
with `lcm d` replaced by any common multiple `L'`: `multi_forms_det` only needs `d_i ∣ L'`. -/
theorem nondegenerateForms_prog {K : ℕ} {M : ℕ} (hM : 0 < M) (d : Fin K → ℕ) (hd : ∀ i, 0 < d i)
    {a : ℕ} (ha : ∀ i : Fin K, d i ∣ a + (i : ℕ) + 1) :
    NondegenerateForms (fun i : Fin K => progLcm M d / d i)
      (fun i : Fin K => (((a + (i : ℕ) + 1) / d i : ℕ) : ℤ)) := by
  have hL : 0 < progLcm M d := progLcm_pos hM d hd
  refine ⟨fun i => Nat.div_pos (Nat.le_of_dvd hL (dvd_progLcm M d i)) (hd i),
    fun i j hij hdet => ?_⟩
  have hkey := multi_forms_det (L := progLcm M d) (a := a) (di := d i) (dj := d j)
    (i := (i : ℕ)) (j := (j : ℕ)) (dvd_progLcm M d i) (dvd_progLcm M d j) (ha i) (ha j)
  rw [hdet, mul_zero] at hkey
  have hLZ : ((progLcm M d : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hL.ne'
  have hne : ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) ≠ 0 := by
    have : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    omega
  exact absurd hkey.symm (mul_ne_zero hLZ hne)

open scoped Classical in
/-- **The `K`-point inner sum along an extra progression.**  `inner_sum_multi_forms` with the index
set additionally restricted to `n ≡ n₀ (mod M)`; the modulus becomes `L' = lcm(M, lcm d)` and the
conclusion has exactly the same shape. -/
theorem inner_sum_prog_forms {K N : ℕ} {M : ℕ} (hM : 0 < M) (d : Fin K → ℕ) (hd : ∀ i, 0 < d i)
    {n₀ : ℕ} (hn₀ : ∀ i : Fin K, d i ∣ n₀ + (i : ℕ) + 1) (z : ℕ → ℂ) (F : ℕ → ℂ) :
    ∃ a : ℕ, a < progLcm M d ∧ (a ≡ n₀ [MOD M]) ∧
      (∀ i : Fin K, d i ∣ a + (i : ℕ) + 1) ∧
      ∑ n ∈ (range N).filter
            (fun n => n ≡ n₀ [MOD M] ∧ ∀ i : Fin K, d i ∣ n + (i : ℕ) + 1),
          F n * ∏ i : Fin K, (z i) ^ ArithmeticFunction.cardFactors ((n + (i : ℕ) + 1) / d i)
        = ∑ j ∈ (range N).filter (fun j => progLcm M d * j + a < N),
            F (progLcm M d * j + a) *
              ∏ i : Fin K, (z i) ^ ArithmeticFunction.cardFactors
                ((progLcm M d / d i) * j + (a + (i : ℕ) + 1) / d i) := by
  classical
  set L : ℕ := progLcm M d with hLdef
  have hL : 0 < L := progLcm_pos hM d hd
  obtain ⟨haL, haM, hadvd⟩ := joint_base_prog hM d hd hn₀
  refine ⟨n₀ % L, haL, haM, hadvd, ?_⟩
  have hfil : (range N).filter
        (fun n => n ≡ n₀ [MOD M] ∧ ∀ i : Fin K, d i ∣ n + (i : ℕ) + 1)
      = (range N).filter (fun n => n % L = n₀ % L) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hn, hcond⟩
      exact ⟨hn, (joint_class_prog M d hn₀ n).1 hcond⟩
    · rintro ⟨hn, hmodn⟩
      exact ⟨hn, (joint_class_prog M d hn₀ n).2 hmodn⟩
  rw [hfil, sum_over_class_eq hL haL]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [shift_div_eq_linear_multi (hd i) (dvd_progLcm M d i) j]

/-- The degenerate case: a tuple with no joint solution contributes nothing, progression or not. -/
theorem inner_sum_prog_empty {K N : ℕ} (M : ℕ) (d : Fin K → ℕ)
    (hno : ¬ ∃ n₀ : ℕ, ∀ i : Fin K, d i ∣ n₀ + (i : ℕ) + 1) (n₀ : ℕ) (z : ℕ → ℂ) (F : ℕ → ℂ) :
    ∑ n ∈ (range N).filter
          (fun n => n ≡ n₀ [MOD M] ∧ ∀ i : Fin K, d i ∣ n + (i : ℕ) + 1),
        F n * ∏ i : Fin K, (z i) ^ ArithmeticFunction.cardFactors ((n + (i : ℕ) + 1) / d i)
      = 0 := by
  classical
  refine Finset.sum_eq_zero fun n hn => ?_
  exact absurd ⟨n, (Finset.mem_filter.1 hn).2.2⟩ hno

#print axioms progLcm_pos
#print axioms dvd_progLcm
#print axioms joint_class_prog
#print axioms joint_base_prog
#print axioms nondegenerateForms_prog
#print axioms inner_sum_prog_forms
#print axioms inner_sum_prog_empty

end CastingOut

end NormalNumbers
