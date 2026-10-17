/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyKorobovCompletion

/-!
# The differencing step in Vandehey's Korobov estimate

This file develops Vandehey's Lemma 3.1.  The combinatorial core below reindexes pairs of
indices in the same residue class modulo a positive period by their positive period shift.
-/

open scoped BigOperators
open Finset
open Erdos438.Fourier

namespace NormalNumbers.VandeheyKorobov

noncomputable section

/-- Reindex the strictly upper-triangular pairs which agree modulo `T` by their positive
multiple `i * T` of the period.  This is the bookkeeping behind the shifted correlations in
Vandehey's differencing lemma. -/
lemma sum_upper_modEq_eq_sum_shifts {R : Type*} [AddCommMonoid R]
    (F : ℕ → ℕ → R) (N T : ℕ) (hT : 0 < T) :
    ∑ p ∈ ((range N ×ˢ range N).filter
        (fun p => p.1 < p.2 ∧ Nat.ModEq T p.1 p.2)), F p.1 p.2 =
      ∑ i ∈ Ico 1 N, ∑ n ∈ range (N - i * T), F n (n + i * T) := by
  classical
  let S := ((Ico 1 N ×ˢ range N).filter
    (fun p => p.2 < N - p.1 * T))
  have hright :
      (∑ p ∈ S, F p.2 (p.2 + p.1 * T)) =
        ∑ i ∈ Ico 1 N, ∑ n ∈ range (N - i * T), F n (n + i * T) := by
    simp only [S, Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext n
      simp only [mem_filter, mem_range]
      omega
    · intro n hn
      rfl
  rw [← hright]
  refine Finset.sum_bij
    (fun p _ => ((p.2 - p.1) / T, p.1)) ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_product] at hp ⊢
    rcases hp with ⟨⟨hp1, hp2⟩, hlt, hmod⟩
    rw [Finset.mem_range] at hp1 hp2
    have hdvd : T ∣ p.2 - p.1 := (Nat.modEq_iff_dvd' hlt.le).mp hmod
    have hdiff : 0 < p.2 - p.1 := Nat.sub_pos_of_lt hlt
    have hTle : T ≤ p.2 - p.1 := Nat.le_of_dvd hdiff hdvd
    have hi0 : 0 < (p.2 - p.1) / T := Nat.div_pos hTle hT
    have hiT : ((p.2 - p.1) / T) * T = p.2 - p.1 := Nat.div_mul_cancel hdvd
    have hdiffN : p.2 - p.1 < N := by omega
    have hiN : (p.2 - p.1) / T < N := by
      have hle : (p.2 - p.1) / T ≤ p.2 - p.1 := Nat.div_le_self _ _
      omega
    refine ⟨⟨Finset.mem_Ico.2 ⟨hi0, hiN⟩, Finset.mem_range.2 hp1⟩, ?_⟩
    rw [hiT]
    omega
  · intro p hp q hq heq
    rw [Finset.mem_filter, Finset.mem_product] at hp hq
    rcases hp with ⟨⟨hp1, hp2⟩, hplt, hpmod⟩
    rcases hq with ⟨⟨hq1, hq2⟩, hqlt, hqmod⟩
    have hpdiv : T ∣ p.2 - p.1 := (Nat.modEq_iff_dvd' hplt.le).mp hpmod
    have hqdiv : T ∣ q.2 - q.1 := (Nat.modEq_iff_dvd' hqlt.le).mp hqmod
    have hpT : ((p.2 - p.1) / T) * T = p.2 - p.1 := Nat.div_mul_cancel hpdiv
    have hqT : ((q.2 - q.1) / T) * T = q.2 - q.1 := Nat.div_mul_cancel hqdiv
    have hfirst : p.1 = q.1 := congrArg Prod.snd heq
    have hquot : (p.2 - p.1) / T = (q.2 - q.1) / T := congrArg Prod.fst heq
    have hdiffEq : p.2 - p.1 = q.2 - q.1 := by rw [← hpT, ← hqT, hquot]
    apply Prod.ext hfirst
    omega
  · intro q hq
    simp only [S, Finset.mem_filter, Finset.mem_product] at hq
    rcases hq with ⟨⟨hqi, hqn⟩, hnlt⟩
    have hi := Finset.mem_Ico.1 hqi
    have hn := Finset.mem_range.1 hqn
    let p : ℕ × ℕ := (q.2, q.2 + q.1 * T)
    have hp1 : p.1 < N := by dsimp [p]; omega
    have hp2 : p.2 < N := by dsimp [p]; omega
    have hmulpos : 0 < q.1 * T := Nat.mul_pos hi.1 hT
    have hplt : p.1 < p.2 := by dsimp [p]; omega
    have hpmod : Nat.ModEq T p.1 p.2 := by
      apply (Nat.modEq_iff_dvd' hplt.le).mpr
      dsimp [p]
      rw [Nat.add_sub_cancel_left]
      exact dvd_mul_left T q.1
    refine ⟨p, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨Finset.mem_range.2 hp1, Finset.mem_range.2 hp2⟩, hplt, hpmod⟩
    · apply Prod.ext
      · dsimp [p]
        rw [Nat.add_sub_cancel_left, Nat.mul_div_left _ hT]
      · rfl
  · intro p hp
    rw [Finset.mem_filter] at hp
    rcases hp with ⟨_, hlt, hmod⟩
    have hdvd : T ∣ p.2 - p.1 := (Nat.modEq_iff_dvd' hlt.le).mp hmod
    have hiT : ((p.2 - p.1) / T) * T = p.2 - p.1 := Nat.div_mul_cancel hdvd
    simp only [hiT]
    congr 1
    omega

/-- A square sum of a symmetric kernel is its diagonal plus twice its strict upper triangle. -/
lemma sum_range_square_symmetric {R : Type*} [CommSemiring R]
    (K : ℕ → ℕ → R) (hsym : ∀ i j, K i j = K j i) (N : ℕ) :
    (∑ i ∈ range N, ∑ j ∈ range N, K i j) =
      (∑ i ∈ range N, K i i) +
        2 * ∑ j ∈ range N, ∑ i ∈ range j, K i j := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hswap : (∑ i ∈ range N, K i N) = ∑ i ∈ range N, K N i := by
        apply Finset.sum_congr rfl
        intro i _
        exact hsym i N
      calc
        (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), K i j) =
            (∑ i ∈ range N, ∑ j ∈ range N, K i j) +
              (∑ i ∈ range N, K i N) + (∑ j ∈ range N, K N j) + K N N := by
                rw [sum_range_succ]
                simp_rw [sum_range_succ]
                rw [sum_add_distrib]
                ring
        _ = ((∑ i ∈ range N, K i i) +
              2 * ∑ j ∈ range N, ∑ i ∈ range j, K i j) +
              (∑ i ∈ range N, K i N) + (∑ j ∈ range N, K N j) + K N N := by
                rw [ih]
        _ = (∑ i ∈ range (N + 1), K i i) +
              2 * ∑ j ∈ range (N + 1), ∑ i ∈ range j, K i j := by
                rw [sum_range_succ, sum_range_succ, hswap]
                ring

/-- Nested upper-triangular summation with a congruence condition is the same shift sum as in
`sum_upper_modEq_eq_sum_shifts`. -/
lemma sum_nested_upper_modEq_eq_sum_shifts {R : Type*} [AddCommMonoid R]
    (F : ℕ → ℕ → R) (N T : ℕ) (hT : 0 < T) :
    (∑ j ∈ range N, ∑ i ∈ range j,
        if Nat.ModEq T i j then F i j else 0) =
      ∑ k ∈ Ico 1 N, ∑ i ∈ range (N - k * T), F i (i + k * T) := by
  classical
  rw [← sum_upper_modEq_eq_sum_shifts F N T hT]
  rw [Finset.sum_filter, Finset.sum_product]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have hrange : range j = (range N).filter (fun i => i < j) := by
    ext i
    simp only [mem_range, mem_filter]
    constructor
    · intro hij
      exact ⟨hij.trans (Finset.mem_range.1 hj), hij⟩
    · exact fun hi => hi.2
  rw [hrange, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hij : i < j <;> by_cases hmod : Nat.ModEq T i j <;> simp [hij, hmod]

/-- Parseval with aliases: the total Fourier mass of an arbitrary finite sequence is the
sum of its pair correlations whose indices agree modulo `T`. -/
lemma sum_norm_sq_twisted_eq (z : ℕ → ℂ) (N T : ℕ) [NeZero T] :
    (∑ h : ZMod T,
        ‖∑ n ∈ range N, z n * phase T (h.val : ℤ) (n : ℤ)‖ ^ 2) =
      T * ∑ i ∈ range N, ∑ j ∈ range N,
        if Nat.ModEq T i j then (z i * (starRingEnd ℂ) (z j)).re else 0 := by
  have hexpand (h : ZMod T) :
      ‖∑ n ∈ range N, z n * phase T (h.val : ℤ) (n : ℤ)‖ ^ 2 =
        ∑ i ∈ range N, ∑ j ∈ range N,
          (z i * (starRingEnd ℂ) (z j) *
            phase T (h.val : ℤ) ((i : ℤ) - j)).re := by
    rw [show ‖∑ n ∈ range N, z n * phase T (h.val : ℤ) (n : ℤ)‖ ^ 2 =
        ((∑ n ∈ range N, z n * phase T (h.val : ℤ) (n : ℤ)) *
          (starRingEnd ℂ) (∑ n ∈ range N, z n * phase T (h.val : ℤ) (n : ℤ))).re by
          rw [Complex.sq_norm, Complex.mul_conj]; simp]
    rw [map_sum, Finset.sum_mul_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [map_mul, conj_phase]
    rw [show z i * phase T (h.val : ℤ) (i : ℤ) *
        ((starRingEnd ℂ) (z j) * phase T (h.val : ℤ) (-(j : ℤ))) =
      z i * (starRingEnd ℂ) (z j) *
        (phase T (h.val : ℤ) (i : ℤ) * phase T (h.val : ℤ) (-(j : ℤ))) by ring]
    rw [← phase_add_right]
    congr 1
  simp_rw [hexpand]
  have hreorder :
      (∑ h : ZMod T, ∑ i ∈ range N, ∑ j ∈ range N,
        (z i * (starRingEnd ℂ) (z j) * phase T (h.val : ℤ) ((i : ℤ) - j)).re) =
      ∑ i ∈ range N, ∑ j ∈ range N, ∑ h : ZMod T,
        (z i * (starRingEnd ℂ) (z j) * phase T (h.val : ℤ) ((i : ℤ) - j)).re := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
  rw [hreorder]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    (∑ h : ZMod T,
        (z i * (starRingEnd ℂ) (z j) * phase T (h.val : ℤ) ((i : ℤ) - j)).re) =
        (z i * (starRingEnd ℂ) (z j) *
          ∑ h : ZMod T, phase T (h.val : ℤ) ((i : ℤ) - j)).re := by
            rw [← Complex.re_sum, Finset.mul_sum]
    _ = T * (if Nat.ModEq T i j then
          (z i * (starRingEnd ℂ) (z j)).re else 0) := by
      rw [phase_orthogonality_zmod]
      have hcond : ((((i : ℤ) - j : ℤ) : ZMod T) = 0) ↔ Nat.ModEq T i j := by
        push_cast
        rw [sub_eq_zero, ZMod.natCast_eq_natCast_iff]
      split
      · rename_i hzmod
        have hmod : Nat.ModEq T i j := hcond.mp hzmod
        rw [if_pos hmod]
        simp [Complex.mul_re]
        ring
      · rename_i hzmod
        have hmod : ¬ Nat.ModEq T i j := fun h => hzmod (hcond.mpr h)
        rw [if_neg hmod]
        simp

/-- **Abstract Vandehey differencing inequality.**  Splitting a unimodular sequence by a
positive period `T` bounds its square by the diagonal and the norms of the correlations at
positive shifts `k*T`.  The outer range is written as `Ico 1 N`; terms with `k*T ≥ N` have
an empty inner sum. -/
theorem norm_sum_range_sq_le_differencing (z : ℕ → ℂ) (N T q : ℕ)
    (hT : 0 < T) (hTq : T ≤ q) (hz : ∀ n < N, ‖z n‖ = 1) :
    ‖∑ n ∈ range N, z n‖ ^ 2 ≤
      q * N + 2 * q *
        ∑ k ∈ Ico 1 N,
          ‖∑ n ∈ range (N - k * T), z n * (starRingEnd ℂ) (z (n + k * T))‖ := by
  letI : NeZero T := ⟨hT.ne'⟩
  let twist (h : ZMod T) :=
    ∑ n ∈ range N, z n * phase T (h.val : ℤ) (n : ℤ)
  have hzero : twist 0 = ∑ n ∈ range N, z n := by
    apply Finset.sum_congr rfl
    intro n hn
    simp [twist]
  have hfirst : ‖∑ n ∈ range N, z n‖ ^ 2 ≤ ∑ h : ZMod T, ‖twist h‖ ^ 2 := by
    rw [← hzero]
    exact Finset.single_le_sum (fun h _ => sq_nonneg ‖twist h‖) (Finset.mem_univ 0)
  have hparseval : (∑ h : ZMod T, ‖twist h‖ ^ 2) =
      T * ∑ i ∈ range N, ∑ j ∈ range N,
        if Nat.ModEq T i j then (z i * (starRingEnd ℂ) (z j)).re else 0 := by
    exact sum_norm_sq_twisted_eq z N T
  let K : ℕ → ℕ → ℝ := fun i j =>
    if Nat.ModEq T i j then (z i * (starRingEnd ℂ) (z j)).re else 0
  have hKsym : ∀ i j, K i j = K j i := by
    intro i j
    by_cases hij : Nat.ModEq T i j
    · have hji : Nat.ModEq T j i := hij.symm
      simp only [K, hij, hji, if_true]
      simp [Complex.mul_re]
      ring
    · have hji : ¬ Nat.ModEq T j i := fun h => hij h.symm
      simp [K, hij, hji]
  have hdiag : (∑ i ∈ range N, K i i) = N := by
    calc
      (∑ i ∈ range N, K i i) = ∑ i ∈ range N, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [K, Nat.ModEq.refl, if_true]
        rw [show (z i * (starRingEnd ℂ) (z i)).re = ‖z i‖ ^ 2 by
          rw [Complex.sq_norm, Complex.mul_conj]; simp]
        rw [hz i (Finset.mem_range.1 hi)]
        norm_num
      _ = N := by simp
  have hupper : (∑ j ∈ range N, ∑ i ∈ range j, K i j) ≤
      ∑ k ∈ Ico 1 N,
        ‖∑ n ∈ range (N - k * T), z n * (starRingEnd ℂ) (z (n + k * T))‖ := by
    rw [show (∑ j ∈ range N, ∑ i ∈ range j, K i j) =
        ∑ j ∈ range N, ∑ i ∈ range j,
          if Nat.ModEq T i j then (z i * (starRingEnd ℂ) (z j)).re else 0 by rfl]
    rw [sum_nested_upper_modEq_eq_sum_shifts
      (fun i j => (z i * (starRingEnd ℂ) (z j)).re) N T hT]
    apply Finset.sum_le_sum
    intro k hk
    rw [← Complex.re_sum]
    exact Complex.re_le_norm _
  have hcore : (∑ h : ZMod T, ‖twist h‖ ^ 2) ≤
      T * N + 2 * T *
        ∑ k ∈ Ico 1 N,
          ‖∑ n ∈ range (N - k * T), z n * (starRingEnd ℂ) (z (n + k * T))‖ := by
    rw [hparseval, show (∑ i ∈ range N, ∑ j ∈ range N,
        if Nat.ModEq T i j then (z i * (starRingEnd ℂ) (z j)).re else 0) =
          ∑ i ∈ range N, ∑ j ∈ range N, K i j by rfl,
      sum_range_square_symmetric K hKsym N, hdiag]
    have hTR : (0 : ℝ) ≤ T := by positivity
    nlinarith
  refine hfirst.trans (hcore.trans ?_)
  have hsum0 : 0 ≤ ∑ k ∈ Ico 1 N,
      ‖∑ n ∈ range (N - k * T), z n * (starRingEnd ℂ) (z (n + k * T))‖ := by positivity
  have hTqR : (T : ℝ) ≤ q := by exact_mod_cast hTq
  push_cast
  nlinarith

/-- **Vandehey, Lemma 3.1 (equation (11)), in shifted-range notation.**

Here `T = ord(b,m')`.  The summand indexed by `j` is the paper's summand with `n = j+1`;
thus the inner length `N-k*T` and the coefficient `a(b^(k*T)-1)` are exactly those of (11).
The paper assumes `m' ∣ m` later, but the differencing lemma itself only needs `b` to be a
unit modulo `m'`. -/
theorem norm_power_sum_range_sq_le_differencing
    (b m m' : ℕ) (a : ℤ) (N : ℕ) (hm : 0 < m) (hm' : 0 < m')
    (hbm' : Nat.Coprime b m') :
    ‖∑ j ∈ range N, phase m a ((b : ℤ) ^ (j + 1))‖ ^ 2 ≤
      m' * N + 2 * m' *
        ∑ k ∈ Ico 1 N,
          ‖∑ j ∈ range (N - k * orderOf (b : ZMod m')),
            phase m (a * ((b : ℤ) ^ (k * orderOf (b : ZMod m')) - 1))
              ((b : ℤ) ^ (j + 1))‖ := by
  letI : NeZero m' := ⟨hm'.ne'⟩
  let T := orderOf (b : ZMod m')
  have hbunit : IsUnit (b : ZMod m') := (ZMod.isUnit_iff_coprime b m').mpr hbm'
  have hT : 0 < T := by
    dsimp [T]
    exact orderOf_pos_iff.mpr hbunit.isOfFinOrder
  have hTm' : T ≤ m' := by
    dsimp [T]
    simpa [ZMod.card m'] using (orderOf_le_card_univ (x := (b : ZMod m')))
  let z : ℕ → ℂ := fun j => phase m a ((b : ℤ) ^ (j + 1))
  have hz : ∀ j < N, ‖z j‖ = 1 := fun j hj => norm_phase _ _ _
  have hdiff := norm_sum_range_sq_le_differencing z N T m' hT hTm' hz
  have hcorr (k : ℕ) :
      ‖∑ j ∈ range (N - k * T), z j * (starRingEnd ℂ) (z (j + k * T))‖ =
        ‖∑ j ∈ range (N - k * T),
          phase m (a * ((b : ℤ) ^ (k * T) - 1)) ((b : ℤ) ^ (j + 1))‖ := by
    have heq :
        (∑ j ∈ range (N - k * T), z j * (starRingEnd ℂ) (z (j + k * T))) =
          (starRingEnd ℂ) (∑ j ∈ range (N - k * T),
            phase m (a * ((b : ℤ) ^ (k * T) - 1)) ((b : ℤ) ^ (j + 1))) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [z]
      rw [conj_phase, ← phase_add_right]
      rw [conj_phase]
      unfold phase
      congr 1
      push_cast
      rw [pow_add]
      ring
    rw [heq]
    exact norm_star _
  simpa only [T, hcorr] using hdiff

end

end NormalNumbers.VandeheyKorobov
