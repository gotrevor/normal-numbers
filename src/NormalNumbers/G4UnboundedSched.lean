/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4WeightAssembly
import NormalNumbers.G4SchedLogLog
import NormalNumbers.G4UnboundedWitness
import NormalNumbers.G4LogTame

/-!
# Campaign B: a `k₄` for a coefficient bound that grows with `k₄`

For bounded `c` the schedule picks `k₄` *after* `C` (`exists_good_k₄`).  For the tame weight the
effective constant depends on `K = 4k₄` itself:

    `effC ≤ A + 23K²(1 + 15K²) = A + 368k₄² + 88320k₄⁴`

(`effC_le_of_logLog` with `V = 23K²` from `sched_prime_size` and `L = 15K²` from
`log_card_primeFactors_P₀_leE`).  The junk budget still wins, because it is exponential:
choosing `k₄ = 2^t` turns `100000·C(k₄)·k₄³ ≤ 2^{k₄}` into `34 + 7t ≤ 2^t`.
-/

open Finset
open scoped BigOperators ArithmeticFunction.Omega

namespace NormalNumbers.G4

namespace SchedB

/-- `34 + 7t ≤ 2^t` for `t ≥ 7`. -/
lemma lin_le_two_pow : ∀ {t : ℕ}, 7 ≤ t → 34 + 7 * t ≤ 2 ^ t := by
  intro t
  induction t with
  | zero => intro h; omega
  | succ n ih =>
      intro h
      rcases Nat.lt_or_ge n 7 with hn | hn
      · have : n = 6 := by omega
        subst this
        norm_num
      · have hih := ih hn
        calc 34 + 7 * (n + 1) = (34 + 7 * n) + 7 := by ring
          _ ≤ 2 ^ n + 7 := by omega
          _ ≤ 2 ^ n + 2 ^ n := by
              have : (7 : ℕ) ≤ 2 ^ n := by
                calc (7 : ℕ) ≤ 2 ^ 3 := by norm_num
                  _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
              omega
          _ = 2 ^ (n + 1) := by ring

/-- **A `k₄` for the tame schedule.**  Unlike `exists_good_k₄`, the coefficient bound is allowed
to be the *polynomial in `k₄`* that `effC` produces. -/
theorem exists_good_k₄_poly (b ℓ a : ℕ) :
    ∃ k₄, k₄bℓ b ℓ ≤ k₄ ∧ 40 ≤ k₄ ∧ a ≤ k₄ ∧
      100000 * (a + 368 * k₄ ^ 2 + 88320 * k₄ ^ 4) * k₄ ^ 3 ≤ 2 ^ k₄ := by
  obtain ⟨t, ht7, hts⟩ : ∃ t, 7 ≤ t ∧ max (max 40 a) (k₄bℓ b ℓ) ≤ 2 ^ t := by
    refine ⟨max 7 (max (max 40 a) (k₄bℓ b ℓ)), le_max_left _ _, ?_⟩
    exact le_trans (Nat.lt_two_pow_self).le
      (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
  set k := 2 ^ t with hk
  have h40 : 40 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hts
  have ha : a ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hts
  have hbℓ : k₄bℓ b ℓ ≤ k := le_trans (le_max_right _ _) hts
  refine ⟨k, hbℓ, h40, ha, ?_⟩
  -- `a + 368k² + 88320k⁴ ≤ 88689·k⁴`, so the left side is at most `2^34·k^7`
  have hk1 : 1 ≤ k := by omega
  have hpoly : a + 368 * k ^ 2 + 88320 * k ^ 4 ≤ 88689 * k ^ 4 := by
    have h1 : a ≤ k ^ 4 := le_trans ha (Nat.le_self_pow (by norm_num) k)
    have h2 : k ^ 2 ≤ k ^ 4 := Nat.pow_le_pow_right hk1 (by norm_num)
    nlinarith
  have hstep : 100000 * (a + 368 * k ^ 2 + 88320 * k ^ 4) * k ^ 3
      ≤ 2 ^ 34 * k ^ 7 := by
    have h1 : 100000 * (a + 368 * k ^ 2 + 88320 * k ^ 4) ≤ 100000 * (88689 * k ^ 4) :=
      Nat.mul_le_mul_left _ hpoly
    have h2 : 100000 * (88689 * k ^ 4) ≤ 2 ^ 34 * k ^ 4 := by
      have : (100000 * 88689 : ℕ) ≤ 2 ^ 34 := by norm_num
      calc 100000 * (88689 * k ^ 4) = (100000 * 88689) * k ^ 4 := by ring
        _ ≤ 2 ^ 34 * k ^ 4 := Nat.mul_le_mul_right _ this
    calc 100000 * (a + 368 * k ^ 2 + 88320 * k ^ 4) * k ^ 3
        ≤ (2 ^ 34 * k ^ 4) * k ^ 3 := Nat.mul_le_mul_right _ (h1.trans h2)
      _ = 2 ^ 34 * k ^ 7 := by ring
  refine hstep.trans ?_
  -- `2^34·(2^t)^7 = 2^{34+7t} ≤ 2^{2^t}`
  have hrw : (2 : ℕ) ^ 34 * k ^ 7 = 2 ^ (34 + 7 * t) := by
    rw [hk, ← pow_mul, ← pow_add]
    ring_nf
  rw [hrw]
  exact Nat.pow_le_pow_right (by norm_num) (lin_le_two_pow ht7)


/-! ### The witness at the effective constant -/

open Sched (N J)

/-- The far-field bracket is nonnegative — the only thing needed to transport `hfarC_holdsE`
from `κ = C` down to `effC ≤ C`. -/
lemma farBracket_nonneg {bb : ℕ} (hbb : 3 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (Dm : ℕ) :
    (0 : ℝ) ≤ (2 : ℝ) ^ G.K *
      ((farBound bb (G.K + G.N) (farC G X Dm) / Real.log 2
          + ((Ω G.P₀ : ℕ) : ℝ) * ((1 / (bb : ℝ)) ^ (G.K + G.N + 1) * ((bb : ℝ) / ((bb : ℝ) - 1))))
        + farJunkBound bb (G.K + G.N) (junkA G.P₀ X) (junkB X Dm)
            / ((apSample X G.P₀ G.b₀).card : ℝ)) := by
  have hbr : (3 : ℝ) ≤ bb := by exact_mod_cast hbb
  have hbr2 : (2 : ℝ) ≤ bb := by linarith
  have hc : (0 : ℝ) < ((apSample X G.P₀ G.b₀).card : ℝ) := by exact_mod_cast hne.card_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hfb := farBound_nonneg hbr2 (G.K + G.N) (farC_nonneg G X hne Dm)
  have hfj := farJunkBound_nonneg hbr (G.K + G.N) (junkA_nonneg G.P₀ X) (junkB_nonneg X Dm)
  have hgeo : (0 : ℝ)
      ≤ ((Ω G.P₀ : ℕ) : ℝ) * ((1 / (bb : ℝ)) ^ (G.K + G.N + 1) * ((bb : ℝ) / ((bb : ℝ) - 1))) := by
    have h1 : (0 : ℝ) < (bb : ℝ) - 1 := by linarith
    have h2 : (0 : ℝ) ≤ 1 / (bb : ℝ) := by positivity
    positivity
  have h5 : (0 : ℝ) ≤ farBound bb (G.K + G.N) (farC G X Dm) / Real.log 2 :=
    div_nonneg hfb hlog2.le
  have h6 : (0 : ℝ) ≤ farJunkBound bb (G.K + G.N) (junkA G.P₀ X) (junkB X Dm)
      / ((apSample X G.P₀ G.b₀).card : ℝ) := div_nonneg hfj hc.le
  positivity

/-- `1 ≤ Ω(P₀)`: the modulus is divisible by `2` (every prime `≤ 2T` divides `freezeQ`). -/
lemma one_le_cardFactors_P₀ (G : GridParams) (hIdx : 0 < Fintype.card G.Idx) :
    (1 : ℝ) ≤ ((Ω G.P₀ : ℕ) : ℝ) := by
  have hT : 1 ≤ Fintype.card G.Idx := hIdx
  have h2 : (2 : ℕ) ∣ G.freezeQ :=
    G.prime_dvd_freezeQ_of_le Nat.prime_two (by omega)
  have hdvd : (2 : ℕ) ∣ G.P₀ := h2.trans G.freezeQ_dvd_P₀
  have hne : G.P₀ ≠ 0 := G.P₀_pos.ne'
  have hne1 : G.P₀ ≠ 1 := by
    intro h
    rw [h] at hdvd
    omega
  have : 1 ≤ Ω G.P₀ := by
    rcases Nat.eq_zero_or_pos (Ω G.P₀) with h0 | h
    · rcases ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one.1 h0 with h1 | h1
      · exact absurd h1 hne
      · exact absurd h1 hne1
    · exact h
  exact_mod_cast this

/-- **The schedule witness at the effective constant.**  The `ScheduleWitnessC` field list,
with `hjunk`/`hfar` transported from `C` down to `effC ≤ C` by monotonicity. -/
noncomputable def scheduleWitnessUE (c : ℕ → ℕ) {A : ℝ} (C : ℕ)
    (b ℓ w e k₄ : ℕ) (hb : 3 ≤ b) (hℓ : 1 ≤ ℓ)
    (hk : k₄bℓ b ℓ ≤ k₄) (hk40 : 40 ≤ k₄) (hCk : 100000 * C * k₄ ^ 3 ≤ 2 ^ k₄)
    (hE : HypE b (4 * k₄) e)
    (hEff : effC c (gridOf (4 * k₄) (N (4 * k₄)) hE.base.hK1).P₀ A ≤ (C : ℝ)) :
    ScheduleWitnessU c A b ℓ w :=
  let K := 4 * k₄
  have hK4 : K = 4 * k₄ := rfl
  have h : Hyp b K := hE.base
  have hK100 : 100 ≤ K := h.hK
  have hK1 : 1 ≤ K := h.hK1
  have hKr : (100 : ℝ) ≤ K := by exact_mod_cast hK100
  { G := gridOf K (N K) hK1
    hK := by show 0 < K; omega
    hr := Nat.one_le_pow _ _ (by show 0 < K ^ 2; positivity)
    hP₀ := (gridOf K (N K) hK1).P₀_pos
    hΩ := one_le_cardFactors_P₀ _ (by
      rw [gridOf.card_Idx hK1]
      have : 0 < N K := Sched.N_pos hK1
      positivity)
    X := XE K e
    hne := sample_nonemptyE hE
    η := (1 / 2 : ℝ) ^ k₄
    hη := by positivity
    ε := 1 / (K : ℝ)
    hε := by positivity
    hε1 := by rw [div_lt_one (by linarith)]; linarith
    M := MG b ℓ K
    hM := hM_holdsG hb hℓ hK4
    Lg := (((K ^ 2) ^ K : ℕ) : ℝ) * (Real.log 2 + 23 * Real.sqrt K)
    hlog := by
      have h := log_det_one_add_tensorGram_le' hK1
      push_cast
      exact h
    δ₁ := 1 / 8
    hδ₁ := by norm_num
    hB := by
      intro g hglo hghi
      have hr : (gridOf K (N K) hK1).rDim = (K ^ 2) ^ K := rfl
      have hH : (gridOf K (N K) hK1).hDim = (K ^ 2 + 1) ^ K := rfl
      rw [hr] at hglo hghi
      rw [hr, hH]
      have hη : ((1 / 2 : ℝ) ^ k₄) ^ 4 ≤ (1 / 2 : ℝ) ^ K := by
        rw [← pow_mul, hK4, mul_comm]
      exact gridB_bound (bb := b) (by omega) hℓ (KG_ge hk) (MG_lo hb hℓ) (MG_hi hb hℓ)
        (by positivity) hη le_rfl hglo hghi
    R := RE e
    hR := RE_ge_two e
    Y := YE K e
    hRY := RE_le_YE K e
    D := Sched.Dj K k₄
    hN := hN_holds (by omega) hK4 hK100
    Mc := McE K e
    hMc := McE_pos hE
    lam' := Real.exp 1
    hlam' := Real.one_le_exp zero_le_one
    lam := 13 / 2
    hlam := by norm_num
    Mx := ((XE K e + J K * gridDm K (N K) : ℕ) : ℝ)
    hMx1 := by
      have : 1 ≤ XE K e := Nat.one_le_two_pow
      exact_mod_cast le_add_right this
    hMx := fun n hn i => by exact_mod_cast gridOf.add_shiftAL_le hK1 hn i
    Dm := gridDm K (N K)
    hDm := gridOf.d_le hK1
    ρmax := J K * gridDm K (N K)
    hρm := fun i => gridOf.shiftAL_le hK1 i
    δbig := 1 / 8
    δjunk := 1 / 8
    δfar := 11 / 64
    hbig := hbig_holdsE hK4 hE
    hjunk := by
      refine le_trans ?_ (hjunk_holdsCE (C := C) hK4 hk40 hCk hE)
      have hjs : (0 : ℝ) ≤ junkShiftBound (gridOf K (N K) hK1).P₀ (XE K e)
          (J K * gridDm K (N K)) := junkShiftBound_nonneg _ _ _
      have hcard : (0 : ℝ) < ((apSample (XE K e) (gridOf K (N K) hK1).P₀
          (gridOf K (N K) hK1).b₀).card : ℝ) := by
        exact_mod_cast (sample_nonemptyE hE).card_pos
      have hrow : (0 : ℝ) ≤ rowL1 b K :=
        rowL1_nonneg (by exact_mod_cast (show 2 ≤ b by omega) : (2:ℝ) ≤ b) K
      have hmul : effC c (gridOf K (N K) hK1).P₀ A
            * junkShiftBound (gridOf K (N K) hK1).P₀ (XE K e) (J K * gridDm K (N K))
            / ((apSample (XE K e) (gridOf K (N K) hK1).P₀
                (gridOf K (N K) hK1).b₀).card : ℝ)
          ≤ (C : ℝ) * junkShiftBound (gridOf K (N K) hK1).P₀ (XE K e) (J K * gridDm K (N K))
            / ((apSample (XE K e) (gridOf K (N K) hK1).P₀
                (gridOf K (N K) hK1).b₀).card : ℝ) := by
        gcongr
      exact mul_le_mul_of_nonneg_right hmul hrow
    hfar := by
      have hκ : max C 1 ≤ 2 ^ k₄ := by
        have h1 : C ≤ 2 ^ k₄ := by
          have hk3 : 1 ≤ k₄ ^ 3 := Nat.one_le_pow _ _ (by omega)
          nlinarith [hCk, Nat.zero_le C]
        have h2 : 1 ≤ 2 ^ k₄ := Nat.one_le_two_pow
        omega
      refine le_trans ?_ (hfarC_holdsE (κ := max C 1) hK4 hκ hE)
      have hbr := farBracket_nonneg (bb := b) (by omega) (gridOf K (N K) hK1) (XE K e)
        (sample_nonemptyE hE) (gridDm K (N K))
      have hCk' : (C : ℝ) ≤ ((max C 1 : ℕ) : ℝ) := by exact_mod_cast le_max_left C 1
      exact mul_le_mul_of_nonneg_right (le_trans hEff hCk') hbr
    hbudget := by
      have hbud := hbudget_holdsΩE (k₄ := k₄) hK4 hE
      have hc : Fintype.card (gridOf K (N K) hK1).Idx = Sched.T K := gridOf.card_Idx hK1
      rw [← hc] at hbud
      exact hbud }



/-! ### The unbounded headline -/

/-- A schedule witness for the tame weight at every base `b ≥ 3`, depth `ℓ ≥ 1`, word `w`. -/
theorem exists_scheduleWitnessU (c : ℕ → ℕ) {A : ℝ} (hA : 1 ≤ A)
    (hc : ∀ x, c x ≤ Nat.log 2 (Nat.log 2 x)) (b ℓ w : ℕ) (hb : 3 ≤ b) (hℓ : 1 ≤ ℓ) :
    Nonempty (ScheduleWitnessU c A b ℓ w) := by
  classical
  obtain ⟨k₄, hk, hk40, ha, hCk⟩ := exists_good_k₄_poly b ℓ ⌈A⌉₊
  set K : ℕ := 4 * k₄ with hKdef
  set C : ℕ := ⌈A⌉₊ + 368 * k₄ ^ 2 + 88320 * k₄ ^ 4 with hC
  have h : Hyp b K := hyp_KG hb hℓ hk
  have hK100 : 100 ≤ K := h.hK
  have hK1 : 1 ≤ K := h.hK1
  have hhi : McE K (m₁ b K) ≤ 2 ^ Sched.m₂ K :=
    MertensAP.moment_cap_subset hb h.hbK hK100 (D := 1) (Nat.one_le_two_pow) (by omega)
  have hE : HypE b K (m₁ b K) := ⟨h, le_rfl, hhi⟩
  -- the effective constant at this grid
  have hEff : effC c (gridOf K (N K) hK1).P₀ A ≤ (C : ℝ) := by
    have hbound := effC_le_of_logLog (gridOf K (N K) hK1) hc hA
      (Dm := gridDm K (N K)) (ρmax := J K * gridDm K (N K)) (V := 23 * K ^ 2)
      (gridOf.d_le hK1) (fun i => gridOf.shiftAL_le hK1 i)
      (Sched.sched_prime_size hK100 hK1)
      (L := 15 * (K : ℝ) ^ 2) (log_card_primeFactors_P₀_leE hE) (by positivity)
    refine hbound.trans ?_
    have hKr : (K : ℝ) = 4 * (k₄ : ℝ) := by rw [hKdef]; push_cast; ring
    have hAc : A ≤ (⌈A⌉₊ : ℝ) := Nat.le_ceil A
    have hCr : (C : ℝ) = (⌈A⌉₊ : ℝ) + 368 * (k₄ : ℝ) ^ 2 + 88320 * (k₄ : ℝ) ^ 4 := by
      rw [hC]; push_cast; ring
    rw [hCr]
    simp only [hKdef]
    push_cast
    ring_nf
    nlinarith [hAc]
  exact ⟨scheduleWitnessUE c C b ℓ w (m₁ b K) k₄ hb hℓ hk hk40 hCk hE hEff⟩

/-- **The unbounded-coefficient headline.**  For every coefficient vector with
`c_p ≤ ⌊log₂ log₂ p⌋` — a genuinely unbounded class —
`∑_n (ω(n) + ∑_{p∣n} c_p (v_p(n) − 1))/bⁿ` is disjunctive in every base `b ≥ 3`. -/
theorem isDisjunctive_weight_logLog (c : ℕ → ℕ)
    (hc : ∀ x, c x ≤ Nat.log 2 (Nat.log 2 x)) {b : ℕ} (hb : 3 ≤ b) :
    IsDisjunctive b (PrimeLambert.weightLambert b c) := by
  have hlog : ∀ p, c p ≤ Nat.log 2 p := fun p =>
    (hc p).trans (Nat.log_mono_right (Nat.log_le_self 2 p))
  have hT : PrimeLambert.Tame c 4 := tame_of_natLog_le hlog
  have hmain : IsDisjunctive b ((TWeight.weightU c hT).lambert b) := by
    refine isDisjunctive_weightU_of_witness c hT b hb fun ℓ w hw homit => ?_
    rcases Nat.eq_zero_or_pos ℓ with hℓ | hℓ
    · exfalso
      subst hℓ
      have hw0 : w = 0 := by simpa using hw
      subst hw0
      have := homit 0
      simp only [Nat.cast_zero, pow_zero, zero_add, div_one] at this
      exact this (orbit_mem_Ico b _ 0)
    · exact exists_scheduleWitnessU c (by norm_num : (1:ℝ) ≤ 4) hc b ℓ w hb hℓ
  rwa [TWeight.lambert_weightU (b := b) c hT] at hmain

end SchedB

end NormalNumbers.G4
