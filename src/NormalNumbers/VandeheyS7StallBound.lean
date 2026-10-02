/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-SB: a width floor bounds the stall clock, hence the clock is linear

S7-AG proved that a long stall crushes the state: `stallAge = k` forces
`width ≤ 36/fib(k+1)²`.  Read the other way, a width FLOOR caps the stall clock, and a capped
stall clock makes the transducer emit at least once in every window of `K+1` steps — so the run
clock is linear in the input time, with no analytic input at all:

    (∀ n, η ≤ width (runState Φ x n))  ⟹  ∃ K, ∀ p, p ≤ (K+1) · runClock Φ x p + (K+1).

This is `ClockLinear`, the second of the two scalar debts route A carries (`DIRECTION.md`), under
a uniform floor.  It matters because S7-SK runs the implication the other way — `ClockLinear`
(plus `MeanSlack`) gives the width FREQUENCY bound `WidthFreqOrder` — so the two scalar
obligations are one loop, not two independent statements, and `MeanSlack` is the only genuinely
open scalar.

Fact (β) of `DIRECTION.md` says a uniform width floor is the wrong shape to ASSUME.  It is not
assumed here: it is the hypothesis of a lemma whose conclusion is the linear clock, and the
frequency version is what the front actually consumes.  Recording the uniform case pins the
mechanism — stalls are self-limiting, because stalling is exactly what destroys the width that
stalling needs.

## Guard rule

**Content locator.**  `exists_stallAge_bound` is where S7-AG is used; everything after it is
counting.  With `η > 36` the bound is `K = 0` (no stall is possible at all) and the clock is the
identity.

**Degenerate cases.**  `p = 0`: the conclusion reads `0 ≤ K+1`.  `η` larger than every width
makes the hypothesis vacuous, not the conclusion false.
-/
import NormalNumbers.VandeheyS7Age

namespace NormalNumbers.VandeheyS7

open Set Filter Finset NormalNumbers

namespace MapState

/-! ## The stall clock is bounded by a width floor -/

lemma nat_le_fib_succ (m : ℕ) : m ≤ Nat.fib (m + 1) := by
  induction m with
  | zero => simp
  | succ k ih =>
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp
      · have hpos : 1 ≤ Nat.fib k := Nat.fib_pos.mpr hk
        have h2 : Nat.fib (k + 1 + 1) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two (n := k)
        omega

lemma stallAge_le_self (Φ : MapState) (x : ℝ) (n : ℕ) : stallAge Φ x n ≤ n := by
  induction n with
  | zero => simp [stallAge]
  | succ k ih =>
      rw [stallAge_succ]
      by_cases h : runWord Φ x k = []
      · rw [if_pos h]; omega
      · rw [if_neg h]; omega

/-- A uniform width floor caps the stall clock. -/
theorem exists_stallAge_bound (Φ : MapState) {x : ℝ}
    (hx : ∀ j, gaussMap^[j] x ∈ Set.Ioo (0:ℝ) 1) {η : ℝ} (hη : 0 < η)
    (hwide : ∀ n, η ≤ (runState Φ x n).width) :
    ∃ K : ℕ, ∀ n, stallAge Φ x n ≤ K := by
  -- pick `K` with `36/η < fib (K+1)^2`
  obtain ⟨K, hK⟩ : ∃ K : ℕ, 36 / η < ((Nat.fib (K + 1) : ℕ) : ℝ) ^ 2 := by
    obtain ⟨m, hm⟩ := exists_nat_gt (36 / η)
    refine ⟨m, lt_of_lt_of_le hm ?_⟩
    have h1 : (m : ℝ) ≤ ((Nat.fib (m + 1) : ℕ) : ℝ) := by
      exact_mod_cast nat_le_fib_succ m
    have hf1 : (1:ℝ) ≤ ((Nat.fib (m + 1) : ℕ) : ℝ) := by
      have : 1 ≤ Nat.fib (m + 1) := Nat.fib_pos.mpr (by omega)
      exact_mod_cast this
    nlinarith
  refine ⟨K + 2, fun n => ?_⟩
  by_contra hcon
  push_neg at hcon
  set k := stallAge Φ x n with hk
  have hkn : k ≤ n := stallAge_le_self Φ x n
  have hk2 : K + 2 < k := hcon
  -- the last `k` steps stalled
  have hstalls : ∀ i < k, runWord Φ x ((n - k) + i) = [] := by
    refine stall_of_stallAge Φ x k (n - k) ?_
    rw [show n - k + k = n from by omega, ← hk]
  -- drop the first two of them, so that S7-AG's two-step reduction is available
  set k' := k - 2 with hk'
  set j := n - 2 - k' with hjdef
  have hjn : j + 2 + k' = n := by omega
  have hstall' : ∀ i < k', runWord Φ x (j + 2 + i) = [] := by
    intro i hi
    have := hstalls (i + 2) (by omega)
    rw [show n - k + (i + 2) = j + 2 + i from by omega] at this
    exact this
  have hwid := width_stall_le' Φ hx hstall'
  rw [hjn] at hwid
  have hlow := hwide n
  -- so `fib (k'+1)^2 ≤ 36/η`, contradicting the choice of `K`
  have hfibpos : (0:ℝ) < ((Nat.fib (k' + 1) : ℕ) : ℝ) := by
    have : 0 < Nat.fib (k' + 1) := Nat.fib_pos.mpr (by omega)
    exact_mod_cast this
  have hle : η ≤ 36 / ((Nat.fib (k' + 1) : ℕ) : ℝ) ^ 2 := le_trans hlow hwid
  rw [le_div_iff₀ (by positivity)] at hle
  have hmono : Nat.fib (K + 1) ≤ Nat.fib (k' + 1) := Nat.fib_mono (by omega)
  have hmR : ((Nat.fib (K + 1) : ℕ) : ℝ) ≤ ((Nat.fib (k' + 1) : ℕ) : ℝ) := by exact_mod_cast hmono
  have h0 : (0:ℝ) ≤ ((Nat.fib (K + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [div_lt_iff₀ hη] at hK
  have hsq : ((Nat.fib (K + 1) : ℕ) : ℝ) ^ 2 ≤ ((Nat.fib (k' + 1) : ℕ) : ℝ) ^ 2 :=
    pow_le_pow_left₀ h0 hmR 2
  have hmul := mul_le_mul_of_nonneg_right hsq hη.le
  linarith

/-! ## A capped stall clock forces emissions -/

lemma stallAge_add_of_stall (Φ : MapState) (x : ℝ) (n : ℕ) :
    ∀ m : ℕ, (∀ i < m, runWord Φ x (n + i) = []) → stallAge Φ x (n + m) = stallAge Φ x n + m := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ k ih =>
      intro hall
      have hprev : stallAge Φ x (n + k) = stallAge Φ x n + k :=
        ih fun i hi => hall i (by omega)
      have hlast : runWord Φ x (n + k) = [] := hall k (by omega)
      rw [show n + (k + 1) = (n + k) + 1 from by ring, stallAge_succ, if_pos hlast, hprev]
      omega

/-- With the stall clock capped by `K`, some step in every window of `K+1` emits. -/
theorem exists_emit_in_window (Φ : MapState) (x : ℝ) {K : ℕ}
    (hK : ∀ n, stallAge Φ x n ≤ K) (n : ℕ) : ∃ i ≤ K, runWord Φ x (n + i) ≠ [] := by
  by_contra hcon
  push_neg at hcon
  have hall : ∀ i < K + 1, runWord Φ x (n + i) = [] := fun i hi => hcon i (by omega)
  have := stallAge_add_of_stall Φ x n (K + 1) hall
  have hb := hK (n + (K + 1))
  omega

/-! ## The linear clock -/

lemma runClock_succ_of_emit (Φ : MapState) (x : ℝ) {n : ℕ} (h : runWord Φ x n ≠ []) :
    runClock Φ x n + 1 ≤ runClock Φ x (n + 1) := by
  rw [runClock_succ]
  have : 1 ≤ (runWord Φ x n).length := by
    rcases List.eq_nil_or_concat (runWord Φ x n) with h0 | ⟨u, a, hu⟩
    · exact absurd h0 h
    · rw [hu]; simp
  omega

theorem runClock_ge_of_stallAge_bound (Φ : MapState) (x : ℝ) {K : ℕ}
    (hK : ∀ n, stallAge Φ x n ≤ K) : ∀ t : ℕ, t ≤ runClock Φ x ((K + 1) * t) := by
  intro t
  induction t with
  | zero => simp
  | succ s ih =>
      obtain ⟨i, hiK, hemit⟩ := exists_emit_in_window Φ x hK ((K + 1) * s)
      have h1 : runClock Φ x ((K + 1) * s) ≤ runClock Φ x ((K + 1) * s + i) :=
        runClock_mono Φ x (by omega)
      have h2 := runClock_succ_of_emit Φ x hemit
      have h3 : runClock Φ x ((K + 1) * s + i + 1) ≤ runClock Φ x ((K + 1) * (s + 1)) :=
        runClock_mono Φ x (by ring_nf; omega)
      omega

/-- **S7-SB.**  A uniform width floor gives a linear clock, unconditionally. -/
theorem clock_linear_of_uniform_width (Φ : MapState) {x : ℝ}
    (hx : ∀ j, gaussMap^[j] x ∈ Set.Ioo (0:ℝ) 1) {η : ℝ} (hη : 0 < η)
    (hwide : ∀ n, η ≤ (runState Φ x n).width) :
    ∃ K : ℕ, ∀ p : ℕ, p ≤ (K + 1) * runClock Φ x p + (K + 1) := by
  obtain ⟨K, hK⟩ := exists_stallAge_bound Φ hx hη hwide
  refine ⟨K, fun p => ?_⟩
  have ht := runClock_ge_of_stallAge_bound Φ x hK (p / (K + 1))
  have hdm := Nat.div_add_mod p (K + 1)
  have hmod : p % (K + 1) < K + 1 := Nat.mod_lt _ (Nat.succ_pos K)
  have hmono : runClock Φ x ((K + 1) * (p / (K + 1))) ≤ runClock Φ x p :=
    runClock_mono Φ x (by omega)
  have hmul : (K + 1) * (p / (K + 1)) ≤ (K + 1) * runClock Φ x p :=
    Nat.mul_le_mul_left _ (le_trans ht hmono)
  omega


/-! ## The clock deficit IS the stall count

S7-CO identified the crux at the empty word with "the clock runs at rate `1`".  The identity
below turns that into a statement about STALLS, which is the form a probe can attack: the crux at
`[]` holds exactly when the transducer's stalls have density zero.
-/

open Classical in
/-- The number of stalls before time `p`. -/
noncomputable def stallCount (Φ : MapState) (x : ℝ) (p : ℕ) : ℕ :=
  ((range p).filter fun n => runWord Φ x n = []).card

theorem runClock_add_stallCount (Φ : MapState) (x : ℝ) (p : ℕ) :
    runClock Φ x p + stallCount Φ x p = p := by
  classical
  induction p with
  | zero => simp [runClock, stallCount]
  | succ n ih =>
      rw [runClock_succ, stallCount, Finset.range_add_one, Finset.filter_insert]
      by_cases h : runWord Φ x n = []
      · rw [if_pos h, Finset.card_insert_of_notMem (by simp), h]
        simp only [List.length_nil]
        rw [stallCount] at ih
        omega
      · rw [if_neg h]
        have hlen : (runWord Φ x n).length = 1 := by
          have hle := runWord_length_le_one Φ x n
          rcases List.eq_nil_or_concat (runWord Φ x n) with h0 | ⟨u, a, hu⟩
          · exact absurd h0 h
          · rw [hu] at hle ⊢; simp at hle ⊢; omega
        rw [hlen, stallCount] at *
        omega

/-- **The clock deficit is exactly the stall count.**  So a clock rate of `1` — equivalently, the
crux at the empty word (S7-CO) — says precisely that stalls have density zero. -/
theorem stallCount_eq (Φ : MapState) (x : ℝ) (p : ℕ) :
    (stallCount Φ x p : ℝ) = (p : ℝ) - ((runClock Φ x p : ℕ) : ℝ) := by
  have := runClock_add_stallCount Φ x p
  have hc : ((runClock Φ x p + stallCount Φ x p : ℕ) : ℝ) = (p : ℝ) := by exact_mod_cast this
  push_cast at hc
  linarith

/-- The crux at `[]`, restated: stalls have density zero. -/
theorem tendsto_stallCount_div_zero_iff (Φ : MapState) (x : ℝ) :
    Tendsto (fun p => ((runClock Φ x p : ℕ) : ℝ) / (p : ℝ)) atTop (nhds 1) ↔
      Tendsto (fun p => (stallCount Φ x p : ℝ) / (p : ℝ)) atTop (nhds 0) := by
  constructor
  · intro h
    have := (tendsto_const_nhds (x := (1:ℝ)) (f := atTop (α := ℕ))).sub h
    refine Tendsto.congr' ?_ (by simpa using this)
    filter_upwards [eventually_gt_atTop 0] with p hp
    have hpR : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
    rw [stallCount_eq, sub_div, div_self hpR.ne']
  · intro h
    have := (tendsto_const_nhds (x := (1:ℝ)) (f := atTop (α := ℕ))).sub h
    refine Tendsto.congr' ?_ (by simpa using this)
    filter_upwards [eventually_gt_atTop 0] with p hp
    have hpR : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
    rw [stallCount_eq, sub_div, div_self hpR.ne']
    ring

end MapState

end NormalNumbers.VandeheyS7

section Audit

#print axioms NormalNumbers.VandeheyS7.MapState.exists_stallAge_bound
#print axioms NormalNumbers.VandeheyS7.MapState.exists_emit_in_window
#print axioms NormalNumbers.VandeheyS7.MapState.clock_linear_of_uniform_width
#print axioms NormalNumbers.VandeheyS7.MapState.runClock_add_stallCount
#print axioms NormalNumbers.VandeheyS7.MapState.tendsto_stallCount_div_zero_iff

end Audit
