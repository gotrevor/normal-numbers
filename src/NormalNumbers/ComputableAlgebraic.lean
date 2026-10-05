/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.Computability.Primrec.List
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Algebraic reals are computable: the leaf lemmas

Ingredients for `NormalNumbers.ComputableReal.isComputableReal_of_isAlgebraic`, via the flat
`Nat.findGreatest` route:

* `exists_simple_root`: an algebraic `x` is a simple root of some `q ∈ ℤ[X]` with `q'(x) > 0`
  (take the `(r-1)`-st derivative of an annihilating polynomial, `r` the root multiplicity);
* `exists_shifted_root`: shifting by `c ∈ ℕ` keeps this, so WLOG the root is `≥ 0`;
* `exists_primrec_floor`: for such a root `y ≥ 0`, `n ↦ ⌊2ⁿ y⌋₊` is `Primrec`.  Near `y`, `q` is
  strictly increasing; a hard-coded dyadic interval around `y` plus the sign of `2^{n·deg}·q(m/2ⁿ)`
  (compared as two `ℕ` sums of the positive and negative coefficient parts) decides
  `m / 2ⁿ ≤ y`, and `Nat.findGreatest` returns the floor;
* `primrec_int_sub`: the final `ℕ - ℕ → ℤ` step, through `ℤ`'s `Denumerable` encoding.
-/

open Polynomial

namespace NormalNumbers.ComputableAlgebraic


theorem primrec_int_sub {α : Type*} [Primcodable α] {f g : α → ℕ} (hf : Primrec f)
    (hg : Primrec g) : Primrec fun a => ((f a : ℤ) - g a) := by
  rw [← Primrec.encode_iff]
  have h : Primrec fun a => if g a ≤ f a then 2 * (f a - g a) else 2 * (g a - f a - 1) + 1 :=
    Primrec.ite (Primrec.nat_le.comp hg hf) (Primrec.nat_double.comp (Primrec.nat_sub.comp hf hg))
      (Primrec.nat_double_succ.comp
        (Primrec.nat_sub.comp (Primrec.nat_sub.comp hg hf) (Primrec.const 1)))
  refine h.of_eq fun a => ?_
  split_ifs with hle
  · have : ((f a : ℤ) - g a) = Int.ofNat (f a - g a) := by rw [Int.ofNat_eq_natCast]; push_cast [hle]; ring
    rw [this]; rfl
  · have : ((f a : ℤ) - g a) = Int.negSucc (g a - f a - 1) := by
      rw [Int.negSucc_eq]; push_cast [Nat.le_of_lt (not_le.mp hle), Nat.one_le_iff_ne_zero.mpr
        (Nat.sub_ne_zero_of_lt (not_le.mp hle))]; ring
    rw [this]; rfl

theorem primrec_two_pow : Primrec fun n : ℕ => 2 ^ n := by
  have h : Primrec fun n : ℕ => Nat.rec (motive := fun _ => ℕ) 1 (fun _ acc => 2 * acc) n :=
    Primrec.nat_rec₁ 1 (Primrec.nat_double.comp Primrec.snd).to₂
  refine h.of_eq fun n => ?_
  induction n with
  | zero => rfl
  | succ n ih => simp only at ih ⊢; rw [ih, pow_succ, mul_comm]

theorem primrec_pow_const {α : Type*} [Primcodable α] {f : α → ℕ} (hf : Primrec f) (i : ℕ) :
    Primrec fun a => f a ^ i := by
  induction i with
  | zero => simpa using Primrec.const 1
  | succ i ih => simpa [pow_succ] using Primrec.nat_mul.comp ih hf

theorem primrec_sum_range {α : Type*} [Primcodable α] (t : ℕ → α → ℕ) (ht : ∀ i, Primrec (t i))
    (N : ℕ) : Primrec fun a => ∑ i ∈ Finset.range N, t i a := by
  induction N with
  | zero => simpa using Primrec.const 0
  | succ N ih => simpa [Finset.sum_range_succ] using Primrec.nat_add.comp ih (ht N)


theorem exists_strictMonoOn {Q : ℝ[X]} {y : ℝ} (hder : 0 < (derivative Q).eval y) :
    ∃ δ > 0, StrictMonoOn (fun t => Q.eval t) (Set.Icc (y - δ) (y + δ)) := by
  have hc : ContinuousAt (fun t => (derivative Q).eval t) y := (derivative Q).continuousAt
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hc.eventually (lt_mem_nhds hder))
  refine ⟨ε / 2, by positivity, strictMonoOn_of_deriv_pos (convex_Icc _ _)
    Q.continuous.continuousOn fun t ht => ?_⟩
  rw [interior_Icc] at ht
  rw [Polynomial.deriv]
  apply hball
  rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2]

theorem scaled_eval (q : ℤ[X]) (n m : ℕ) :
    ((∑ i ∈ Finset.range (q.natDegree + 1),
        (q.coeff i).toNat * m ^ i * (2 ^ n) ^ (q.natDegree - i) : ℕ) : ℝ) -
      ((∑ i ∈ Finset.range (q.natDegree + 1),
        (-q.coeff i).toNat * m ^ i * (2 ^ n) ^ (q.natDegree - i) : ℕ) : ℝ) =
      ((2 : ℝ) ^ n) ^ q.natDegree * (q.map (Int.castRingHom ℝ)).eval ((m : ℝ) / 2 ^ n) := by
  have hdeg : (q.map (Int.castRingHom ℝ)).natDegree < q.natDegree + 1 :=
    Nat.lt_succ_of_le (natDegree_map_le)
  rw [eval_eq_sum_range' hdeg, Finset.mul_sum]
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ q.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hc : ((q.coeff i).toNat : ℝ) - ((-q.coeff i).toNat : ℝ) = (q.coeff i : ℝ) := by
    have := Int.toNat_sub_toNat_neg (q.coeff i)
    exact_mod_cast this
  rw [coeff_map, eq_intCast, div_pow, ← sub_mul, ← sub_mul, hc]
  have h2 : ((2 : ℝ) ^ n) ^ q.natDegree = ((2 : ℝ) ^ n) ^ (q.natDegree - i) * ((2 : ℝ) ^ n) ^ i := by
    rw [← pow_add, Nat.sub_add_cancel hi']
  rw [h2]; field_simp

theorem findGreatest_eq_floor (y : ℝ) (hy : 0 ≤ y) (n : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ m, P m ↔ (m : ℝ) ≤ 2 ^ n * y) :
    Nat.findGreatest P ((⌊y⌋₊ + 1) * 2 ^ n) = ⌊2 ^ n * y⌋₊ := by
  have hP' : ∀ m, P m ↔ m ≤ ⌊2 ^ n * y⌋₊ := fun m => by
    rw [hP, Nat.le_floor_iff (by positivity)]
  rw [Nat.findGreatest_eq_iff]
  refine ⟨?_, fun _ => (hP' _).2 le_rfl, fun k hk _ => fun h => absurd ((hP' k).1 h) (not_le.2 hk)⟩
  apply Nat.floor_le_of_le
  push_cast
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (Nat.lt_floor_add_one y).le (by positivity)


theorem exists_primrec_floor (q : ℤ[X]) {y : ℝ} (hy : 0 ≤ y)
    (hroot : (q.map (Int.castRingHom ℝ)).eval y = 0)
    (hder : 0 < (derivative (q.map (Int.castRingHom ℝ))).eval y) :
    ∃ F : ℕ → ℕ, Primrec F ∧ ∀ n, F n = ⌊2 ^ n * y⌋₊ := by
  classical
  set Q := q.map (Int.castRingHom ℝ) with hQ
  obtain ⟨δ, hδ, hmono⟩ := exists_strictMonoOn hder
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 2 : ℝ) < 1)
  rw [div_pow, one_pow] at hk
  set a := ⌊2 ^ k * y⌋₊ with ha
  set D := q.natDegree
  let A : ℕ → ℕ → ℕ := fun n m => ∑ i ∈ Finset.range (D + 1),
    (q.coeff i).toNat * m ^ i * (2 ^ n) ^ (D - i)
  let B : ℕ → ℕ → ℕ := fun n m => ∑ i ∈ Finset.range (D + 1),
    (-q.coeff i).toNat * m ^ i * (2 ^ n) ^ (D - i)
  let T : ℕ → ℕ → Prop := fun n m =>
    m * 2 ^ k < a * 2 ^ n ∨ (m * 2 ^ k ≤ (a + 1) * 2 ^ n ∧ A n m ≤ B n m)
  have hterm : ∀ (c : ℕ) (i : ℕ), Primrec fun p : ℕ × ℕ => c * p.2 ^ i * (2 ^ p.1) ^ (D - i) :=
    fun c i => Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const c)
      (primrec_pow_const Primrec.snd i)) (primrec_pow_const (primrec_two_pow.comp Primrec.fst) _)
  have hA : Primrec fun p : ℕ × ℕ => A p.1 p.2 :=
    primrec_sum_range _ (fun i => hterm _ i) _
  have hB : Primrec fun p : ℕ × ℕ => B p.1 p.2 :=
    primrec_sum_range _ (fun i => hterm _ i) _
  have h2n : Primrec fun p : ℕ × ℕ => 2 ^ p.1 := primrec_two_pow.comp Primrec.fst
  have hmk : Primrec fun p : ℕ × ℕ => p.2 * 2 ^ k :=
    Primrec.nat_mul.comp Primrec.snd (Primrec.const _)
  have hT : PrimrecRel T :=
    PrimrecPred.or (Primrec.nat_lt.comp hmk (Primrec.nat_mul.comp (Primrec.const _) h2n))
      (PrimrecPred.and (Primrec.nat_le.comp hmk (Primrec.nat_mul.comp (Primrec.const _) h2n))
        (Primrec.nat_le.comp hA hB))
  refine ⟨fun n => Nat.findGreatest (T n) ((⌊y⌋₊ + 1) * 2 ^ n),
    Primrec.nat_findGreatest (Primrec.nat_mul.comp (Primrec.const _) primrec_two_pow) hT,
    fun n => findGreatest_eq_floor y hy n _ fun m => ?_⟩
  -- the test `T n m` decides `m / 2ⁿ ≤ y`
  have hpn : (0 : ℝ) < 2 ^ n := by positivity
  have hpk : (0 : ℝ) < 2 ^ k := by positivity
  set d : ℝ := (m : ℝ) / 2 ^ n with hd
  have h1 : m * 2 ^ k < a * 2 ^ n ↔ d < a / 2 ^ k := by
    rw [hd, div_lt_div_iff₀ hpn hpk]; exact_mod_cast Iff.rfl
  have h2 : m * 2 ^ k ≤ (a + 1) * 2 ^ n ↔ d ≤ (a + 1) / 2 ^ k := by
    rw [hd, div_le_div_iff₀ hpn hpk]; exact_mod_cast Iff.rfl
  have h3 : A n m ≤ B n m ↔ Q.eval d ≤ 0 := by
    have e := scaled_eval q n m
    rw [← Nat.cast_le (α := ℝ), ← sub_nonpos, e]
    have hp : (0 : ℝ) < ((2 : ℝ) ^ n) ^ q.natDegree := by positivity
    constructor
    · intro h; by_contra hc; rw [not_le] at hc; nlinarith [mul_pos hp hc]
    · intro h; exact mul_nonpos_of_nonneg_of_nonpos hp.le h
  have hgoal : (m : ℝ) ≤ 2 ^ n * y ↔ d ≤ y := by
    rw [hd, div_le_iff₀ hpn, mul_comm]
  have haL : (a : ℝ) ≤ 2 ^ k * y := Nat.floor_le (by positivity)
  have haR : 2 ^ k * y < a + 1 := Nat.lt_floor_add_one _
  have hL : (a : ℝ) / 2 ^ k ≤ y := by rw [div_le_iff₀ hpk]; linarith
  have hR : y < (a + 1) / 2 ^ k := by rw [lt_div_iff₀ hpk]; linarith
  have hLδ : y - δ ≤ a / 2 ^ k := by
    have e : y - a / 2 ^ k = (2 ^ k * y - a) / 2 ^ k := by field_simp
    have : (2 ^ k * y - a) / 2 ^ k ≤ 1 / 2 ^ k :=
      div_le_div_of_nonneg_right (by linarith) hpk.le
    linarith
  have hRδ : (a + 1) / 2 ^ k ≤ y + δ := by
    have e : (a + 1) / 2 ^ k - y = ((a + 1) - 2 ^ k * y) / 2 ^ k := by field_simp
    have : ((a + 1) - 2 ^ k * y) / 2 ^ k ≤ 1 / 2 ^ k :=
      div_le_div_of_nonneg_right (by linarith) hpk.le
    linarith
  have hyI : y ∈ Set.Icc (y - δ) (y + δ) := ⟨by linarith, by linarith⟩
  show T n m ↔ _
  simp only [T]
  rw [h1, h2, h3, hgoal]
  by_cases hdL : d < a / 2 ^ k
  · exact ⟨fun _ => by linarith, fun _ => Or.inl hdL⟩
  by_cases hdR : d ≤ (a + 1) / 2 ^ k
  · have hdI : d ∈ Set.Icc (y - δ) (y + δ) := ⟨by linarith, by linarith⟩
    have := hmono.le_iff_le hdI hyI
    rw [hroot] at this
    rw [← this]
    tauto
  · constructor
    · rintro (h | ⟨h, _⟩) <;> contradiction
    · intro h; exact absurd (by linarith : d ≤ (a + 1) / 2 ^ k) hdR

theorem exists_simple_root {x : ℝ} (hx : IsAlgebraic ℤ x) :
    ∃ q : ℤ[X], (q.map (Int.castRingHom ℝ)).eval x = 0 ∧
      0 < (derivative (q.map (Int.castRingHom ℝ))).eval x := by
  obtain ⟨p, hp0, hpx⟩ := hx
  set P := p.map (Int.castRingHom ℝ) with hP
  have hP0 : P ≠ 0 := (Polynomial.map_ne_zero_iff (Int.cast_injective)).2 hp0
  have hPx : P.IsRoot x := by
    simpa [IsRoot, hP, eval_map, aeval_def, algebraMap_int_eq] using hpx
  set r := P.rootMultiplicity x with hr
  have hr0 : 0 < r := (rootMultiplicity_pos hP0).2 hPx
  set q0 := derivative^[r - 1] p
  have hmap : q0.map (Int.castRingHom ℝ) = derivative^[r - 1] P := (iterate_derivative_map _ _ _).symm
  have hroot : (q0.map (Int.castRingHom ℝ)).eval x = 0 := by
    rw [hmap]; exact isRoot_iterate_derivative_of_lt_rootMultiplicity (by omega)
  have hder : (derivative (q0.map (Int.castRingHom ℝ))).eval x ≠ 0 := by
    rw [hmap, ← Function.iterate_succ_apply' derivative, Nat.succ_eq_add_one, Nat.sub_add_cancel hr0,
      hr, eval_iterate_derivative_rootMultiplicity, nsmul_eq_mul]
    exact mul_ne_zero (by exact_mod_cast (Nat.factorial_pos _).ne')
      (eval_divByMonic_pow_rootMultiplicity_ne_zero x hP0)
  rcases lt_or_gt_of_ne hder with h | h
  · refine ⟨-q0, by simp [hroot], by simpa using h⟩
  · exact ⟨q0, hroot, h⟩

theorem exists_shifted_root (q : ℤ[X]) {x : ℝ} (c : ℕ)
    (hroot : (q.map (Int.castRingHom ℝ)).eval x = 0)
    (hder : 0 < (derivative (q.map (Int.castRingHom ℝ))).eval x) :
    ((q.comp (X - C (c : ℤ))).map (Int.castRingHom ℝ)).eval (x + c) = 0 ∧
      0 < (derivative ((q.comp (X - C (c : ℤ))).map (Int.castRingHom ℝ))).eval (x + c) := by
  rw [map_comp, derivative_comp]
  rw [derivative_map] at hder
  simp [Polynomial.map_sub, eval_comp]
  exact ⟨hroot, hder⟩

end NormalNumbers.ComputableAlgebraic
