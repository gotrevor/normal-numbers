/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Reduce

/-!
# S7-S: bad states force large digits — the separation estimate

The directive's obstruction (2) says the per-state distortion bound fails exactly at the states
whose image interval `J` straddles a rational `1/k` at a scale far below `|E|`.  This module
supplies the arithmetic that turns that obstruction into a *counting* statement, and it does so
unconditionally.

## The estimate

`dist_inv_ge_of_digits_le`: if the first **three** continued-fraction digits of `t ∈ (0,1)` are
all at most `T`, then

    |t − 1/k| ≥ 1 / (2 (T+1)³)    for every k ≥ 1.

Equivalently (`exists_large_digit_of_near_inv`): a point within `1/(2(T+1)³)` of some `1/k` has
a digit `> T` among its first three.  Three digits are needed, not two: `a₀ = a, a₁ = 1` with a
huge `a₂` puts `t` arbitrarily close to `1/(a+1)` while the first two digits stay bounded, and
`1 − gaussMap t` is exactly what the third digit controls.

## Why this is the crux's bootstrap, de-circularised

A post-emission state with tiny image straddling `1/k` is precisely a state about to emit a huge
output digit.  The frequency of such output positions is therefore bounded by the frequency of
large digits in the image — which is `ImageTight`, *already an independent hypothesis of the §7
chain* (`vandeheyS7_mul_phi_of_orbitWordBound`).  So the bootstrap the directive flagged as
circular ("the `w = []` tail-cell case must control them") is not circular on this route: the
tail-cell control is assumed, and `nearInv_blockCount_le` converts it into control of the bad
positions, with a loss of a factor `3` (the shift) and nothing else.

## Guard rule

Content locator: `dist_inv_ge_of_digits_le` applied at `k = cfDigit t 0` is the nontrivial
direction (the point is *below* `1/a₀`); `two_digits_insufficient` records that the
two-digit version of the estimate is FALSE, so the third digit is load-bearing.
-/

namespace NormalNumbers.VandeheyS7

open Filter NormalNumbers

/-! ## The real-arithmetic core -/

/-- The separation estimate as pure real arithmetic.  `t = 1/(A+S)` with `A ∈ [1,T]` the first
digit and `S ∈ (0,1)` the tail; the two hypotheses on `S` are what the second and third digits
supply. -/
theorem sep_arith {t A S K T : ℝ} (hT1 : 1 ≤ T) (hA1 : 1 ≤ A) (hAT : A ≤ T)
    (hS0 : 0 < S) (hS1 : S < 1) (hSlow : 1 ≤ (T + 1) * S) (hSup : 1 ≤ 2 * (T + 1) * (1 - S))
    (ht : t = 1 / (A + S)) (hK1 : 1 ≤ K) (hcase : K = A ∨ K ≤ A - 1 ∨ A + 1 ≤ K) :
    1 / (2 * (T + 1) ^ 3) ≤ |t - 1 / K| := by
  have hTp : (0:ℝ) < T + 1 := by linarith
  have hAS : (0:ℝ) < A + S := by linarith
  have hcpos : (0:ℝ) < 2 * (T + 1) ^ 3 := by positivity
  have hAST : A + S ≤ T + 1 := by linarith
  rcases hcase with hKA | hKA | hKA
  · -- `K = A`: the point sits below `1/A`, at distance `S / (A(A+S))`
    subst hKA
    have hK0 : (0:ℝ) < K := by linarith
    have hval : 1 / K - t = S / (K * (K + S)) := by
      rw [ht]; field_simp; try ring
    refine le_abs.2 (Or.inr ?_)
    have : 1 / (2 * (T + 1) ^ 3) ≤ 1 / K - t := by
      rw [hval, div_le_div_iff₀ hcpos (by positivity)]
      have e1 : K * (K + S) ≤ (T + 1) * (T + 1) := by nlinarith
      have e2 : (T + 1) * (T + 1) ≤ S * (2 * (T + 1) ^ 3) := by
        nlinarith [mul_le_mul_of_nonneg_left hSlow (by positivity : (0:ℝ) ≤ 2 * (T + 1) ^ 2)]
      linarith
    linarith
  · -- `K ≤ A − 1`: the point is below `1/A ≤ 1/(A−1) ≤ 1/K` by a full gap
    have hK0 : (0:ℝ) < K := by linarith
    have hval : 1 / K - t = (A + S - K) / (K * (A + S)) := by
      rw [ht]; field_simp; try ring
    refine le_abs.2 (Or.inr ?_)
    have hnum : 1 ≤ A + S - K := by linarith
    have hden : K * (A + S) ≤ (T + 1) * (T + 1) := by
      have hKT : K ≤ T := by linarith
      nlinarith
    have : 1 / (2 * (T + 1) ^ 3) ≤ 1 / K - t := by
      rw [hval, div_le_div_iff₀ hcpos (by positivity)]
      nlinarith
    linarith
  · -- `A + 1 ≤ K`: the point is above `1/(A+1) ≥ 1/K`, at distance `(1−S)/((A+S)(A+1))`
    have hK0 : (0:ℝ) < K := by linarith
    have hA1p : (0:ℝ) < A + 1 := by linarith
    have hstep : 1 / K ≤ 1 / (A + 1) := by
      apply one_div_le_one_div_of_le hA1p hKA
    have hval : t - 1 / (A + 1) = (1 - S) / ((A + S) * (A + 1)) := by
      rw [ht]; field_simp; try ring
    refine le_abs.2 (Or.inl ?_)
    have hden : (A + S) * (A + 1) ≤ (T + 1) * (T + 1) := by nlinarith
    have : 1 / (2 * (T + 1) ^ 3) ≤ t - 1 / (A + 1) := by
      rw [hval, div_le_div_iff₀ hcpos (by positivity)]
      nlinarith
    linarith

/-! ## The digit form -/

/-- **Separation.**  Three bounded digits keep `t` away from every `1/k`. -/
theorem dist_inv_ge_of_digits_le {t : ℝ} (hirr : Irrational t) (hmem : t ∈ Set.Ioo (0:ℝ) 1)
    {T : ℕ} (hT : 1 ≤ T) (h0 : cfDigit t 0 ≤ T) (h1 : cfDigit t 1 ≤ T) (h2 : cfDigit t 2 ≤ T)
    {k : ℕ} (hk : 1 ≤ k) :
    1 / (2 * ((T:ℝ) + 1) ^ 3) ≤ |t - 1 / (k:ℝ)| := by
  classical
  obtain ⟨hs_irr, hs_mem⟩ : Irrational (gaussMap t) ∧ gaussMap t ∈ Set.Ioo (0:ℝ) 1 := by
    obtain ⟨hi, ha, hb⟩ := irrational_orbit t hirr hmem 1
    rw [Function.iterate_one] at hi ha hb
    exact ⟨hi, ha, hb⟩
  obtain ⟨hs2_irr, hs2_mem⟩ : Irrational (gaussMap (gaussMap t)) ∧
      gaussMap (gaussMap t) ∈ Set.Ioo (0:ℝ) 1 := by
    obtain ⟨hi, ha, hb⟩ := irrational_orbit t hirr hmem 2
    have he : gaussMap^[2] t = gaussMap (gaussMap t) := by
      simp [Function.iterate_succ_apply]
    rw [he] at hi ha hb
    exact ⟨hi, ha, hb⟩
  set a := cfDigit t 0 with ha_def
  set b := cfDigit (gaussMap t) 0 with hb_def
  set c := cfDigit (gaussMap (gaussMap t)) 0 with hc_def
  have hb_eq : cfDigit t 1 = b := by rw [hb_def, cfDigit_succ]
  have hc_eq : cfDigit t 2 = c := by
    rw [hc_def, show (2:ℕ) = 1 + 1 from rfl, cfDigit_succ, cfDigit_succ]
  have ha1 : 1 ≤ a := one_le_cfDigit t hirr hmem 0
  have hb1 : 1 ≤ b := one_le_cfDigit _ hs_irr hs_mem 0
  have hc1 : 1 ≤ c := one_le_cfDigit _ hs2_irr hs2_mem 0
  have haT : (a:ℝ) ≤ (T:ℝ) := by exact_mod_cast h0
  have h1' : b ≤ T := h1
  have h2' : c ≤ T := h2
  have hbT : (b:ℝ) ≤ (T:ℝ) := by exact_mod_cast h1'
  have hcT : (c:ℝ) ≤ (T:ℝ) := by exact_mod_cast h2'
  have hTR : (1:ℝ) ≤ (T:ℝ) := by exact_mod_cast hT
  have haR : (1:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha1
  have hbR : (1:ℝ) ≤ (b:ℝ) := by exact_mod_cast hb1
  have hcR : (1:ℝ) ≤ (c:ℝ) := by exact_mod_cast hc1
  -- `t = 1/(a + s)`
  have hinv : t⁻¹ = (a:ℝ) + gaussMap t := by
    have := gaussMap_eq_inv_sub hmem
    rw [← ha_def] at this
    linarith
  have ht_eq : t = 1 / ((a:ℝ) + gaussMap t) := by
    rw [← hinv, one_div, inv_inv]
  -- the second digit bounds `s` from below
  have hslow : 1 / ((b:ℝ) + 1) < gaussMap t :=
    ((cfDigit_zero_eq_iff hs_mem hb1).1 rfl).1
  have hSlow : 1 ≤ ((T:ℝ) + 1) * gaussMap t := by
    have hb1p : (0:ℝ) < (b:ℝ) + 1 := by linarith
    rw [div_lt_iff₀ hb1p] at hslow
    nlinarith [hs_mem.1]
  -- the third digit bounds `s` away from `1`
  have hSup : 1 ≤ 2 * ((T:ℝ) + 1) * (1 - gaussMap t) := by
    rcases Nat.lt_or_ge b 2 with hb2 | hb2
    · -- `b = 1`: `s = 1/(1 + s₂)` and the third digit keeps `s₂` away from `0`
      have hbe : b = 1 := by omega
      have hinv2 : (gaussMap t)⁻¹ = (b:ℝ) + gaussMap (gaussMap t) := by
        have := gaussMap_eq_inv_sub hs_mem
        rw [← hb_def] at this
        linarith
      have hs2low : 1 / ((c:ℝ) + 1) < gaussMap (gaussMap t) :=
        ((cfDigit_zero_eq_iff hs2_mem hc1).1 rfl).1
      have hc1p : (0:ℝ) < (c:ℝ) + 1 := by linarith
      rw [div_lt_iff₀ hc1p] at hs2low
      have hse : gaussMap t = 1 / (1 + gaussMap (gaussMap t)) := by
        rw [hbe] at hinv2
        push_cast at hinv2
        rw [← hinv2, one_div, inv_inv]
      have h2pos := hs2_mem.1
      have h2lt := hs2_mem.2
      have hden : (0:ℝ) < 1 + gaussMap (gaussMap t) := by linarith
      have : 1 - gaussMap t = gaussMap (gaussMap t) / (1 + gaussMap (gaussMap t)) := by
        conv_lhs => rw [hse]
        rw [eq_div_iff hden.ne']
        field_simp
        ring
      rw [this]
      have hre : 2 * ((T:ℝ) + 1) * (gaussMap (gaussMap t) / (1 + gaussMap (gaussMap t)))
          = (2 * ((T:ℝ) + 1) * gaussMap (gaussMap t)) / (1 + gaussMap (gaussMap t)) := by
        ring
      rw [hre, le_div_iff₀ hden]
      nlinarith
    · -- `b ≥ 2`: `s ≤ 1/b ≤ 1/2`
      have hsu : gaussMap t ≤ 1 / (b:ℝ) := ((cfDigit_zero_eq_iff hs_mem hb1).1 rfl).2
      have hb2R : (2:ℝ) ≤ (b:ℝ) := by exact_mod_cast hb2
      have hbp : (0:ℝ) < (b:ℝ) := by linarith
      rw [le_div_iff₀ hbp] at hsu
      nlinarith
  have hkR : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  refine sep_arith hTR haR haT hs_mem.1 hs_mem.2 hSlow hSup ht_eq hkR ?_
  rcases lt_trichotomy ((k:ℝ)) ((a:ℝ)) with h | h | h
  · refine Or.inr (Or.inl ?_)
    have : k + 1 ≤ a := by exact_mod_cast (by exact_mod_cast h : k < a)
    have : ((k:ℝ)) + 1 ≤ (a:ℝ) := by exact_mod_cast this
    linarith
  · exact Or.inl h
  · refine Or.inr (Or.inr ?_)
    have : a + 1 ≤ k := by exact_mod_cast (by exact_mod_cast h : a < k)
    have : ((a:ℝ)) + 1 ≤ (k:ℝ) := by exact_mod_cast this
    linarith

/-- **Contrapositive.**  A point close to a rational `1/k` has a large digit among its first
three — the "bad state ⇒ huge output digit" implication, in the kernel. -/
theorem exists_large_digit_of_near_inv {t : ℝ} (hirr : Irrational t) (hmem : t ∈ Set.Ioo (0:ℝ) 1)
    {T : ℕ} (hT : 1 ≤ T) {k : ℕ} (hk : 1 ≤ k)
    (hclose : |t - 1 / (k:ℝ)| < 1 / (2 * ((T:ℝ) + 1) ^ 3)) :
    ∃ j < 3, T + 1 ≤ cfDigit t j := by
  by_contra hcon
  push Not at hcon
  have h0 : cfDigit t 0 ≤ T := by have := hcon 0 (by norm_num); omega
  have h1 : cfDigit t 1 ≤ T := by have := hcon 1 (by norm_num); omega
  have h2 : cfDigit t 2 ≤ T := by have := hcon 2 (by norm_num); omega
  exact absurd hclose (not_lt.2 (dist_inv_ge_of_digits_le hirr hmem hT h0 h1 h2 hk))

/-! ## The counting consequence: near-boundary positions are rare -/

/-- The `η`-neighbourhood of the set of reciprocals `{1/k : k ≥ 1}` — the image points at which
a state's bounded-distortion estimate can fail. -/
def nearInv (η : ℝ) : Set ℝ := {t | ∃ k : ℕ, 1 ≤ k ∧ |t - 1 / (k:ℝ)| < η}

/-- A shifted Birkhoff sum of an indicator exceeds the unshifted one by at most the shift. -/
theorem sum_blockIndic_shift_le (A : Set ℝ) (j p : ℕ) (y : ℝ) :
    ∑ k ∈ Finset.range p, blockIndic A (gaussMap^[j + k] y) ≤ blockCount A p y + j := by
  classical
  have hrw : ∑ k ∈ Finset.range p, blockIndic A (gaussMap^[j + k] y)
      = ∑ i ∈ Finset.Ico j (p + j), blockIndic A (gaussMap^[i] y) := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp [Nat.add_comm]
  have h2 : ∑ i ∈ Finset.Ico j (p + j), blockIndic A (gaussMap^[i] y)
      ≤ ∑ i ∈ Finset.range (p + j), blockIndic A (gaussMap^[i] y) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => blockIndic_nonneg _ _)
    intro i hi
    exact Finset.mem_range.2 (Finset.mem_Ico.1 hi).2
  have h3 : ∑ i ∈ Finset.range (p + j), blockIndic A (gaussMap^[i] y)
      ≤ (∑ i ∈ Finset.range p, blockIndic A (gaussMap^[i] y)) + j := by
    rw [Finset.sum_range_add]
    have hle : ∑ i ∈ Finset.range j, blockIndic A (gaussMap^[p + i] y) ≤ (j:ℝ) := by
      calc ∑ i ∈ Finset.range j, blockIndic A (gaussMap^[p + i] y)
          ≤ ∑ _i ∈ Finset.range j, (1:ℝ) := Finset.sum_le_sum fun i _ => blockIndic_le_one _ _
        _ = (j:ℝ) := by simp
    linarith
  calc ∑ k ∈ Finset.range p, blockIndic A (gaussMap^[j + k] y)
      = _ := hrw
    _ ≤ _ := h2
    _ ≤ _ := h3

/-- A point with a large digit at position `j` lands in the tail cell after `j` steps. -/
theorem mem_cellSet_nil_of_cfDigit_le {t : ℝ} (hirr : Irrational t) (hmem : t ∈ Set.Ioo (0:ℝ) 1)
    {T j : ℕ} (h : T ≤ cfDigit t j) : gaussMap^[j] t ∈ cellSet [] T := by
  obtain ⟨hirr', hmem'⟩ := irrational_orbit t hirr hmem j
  refine ⟨?_, ?_⟩
  · rw [cfCylinder_nil]; exact hmem'
  · show T ≤ cfDigit (gaussMap^[j] t) (List.length ([] : List ℕ))
    simpa using (cfDigit_add t j 0) ▸ (by simpa using h)

/-- **The bad positions are rare.**  Every visit of the orbit to the `1/(2(T+1)³)`-neighbourhood
of a reciprocal is paid for by a visit to the tail cell at threshold `T+1` within three steps, so
its count is at most three times the tail-cell count (plus the boundary cost `6`). -/
theorem blockCount_nearInv_le {y : ℝ} (hy : Irrational y) (hmem : y ∈ Set.Ioo (0:ℝ) 1)
    {T : ℕ} (hT : 1 ≤ T) (p : ℕ) :
    blockCount (nearInv (1 / (2 * ((T:ℝ) + 1) ^ 3))) p y
      ≤ 3 * blockCount (cellSet [] (T + 1)) p y + 6 := by
  classical
  have hpt : ∀ k, blockIndic (nearInv (1 / (2 * ((T:ℝ) + 1) ^ 3))) (gaussMap^[k] y)
      ≤ ∑ j ∈ Finset.range 3, blockIndic (cellSet [] (T + 1)) (gaussMap^[j + k] y) := by
    intro k
    by_cases hk : gaussMap^[k] y ∈ nearInv (1 / (2 * ((T:ℝ) + 1) ^ 3))
    · obtain ⟨hirr', hmem'⟩ := irrational_orbit y hy hmem k
      obtain ⟨m, hm1, hmlt⟩ := id hk
      obtain ⟨j, hj3, hjd⟩ := exists_large_digit_of_near_inv hirr' hmem' hT hm1 hmlt
      have hin : gaussMap^[j] (gaussMap^[k] y) ∈ cellSet [] (T + 1) :=
        mem_cellSet_nil_of_cfDigit_le hirr' hmem' hjd
      have hiter : gaussMap^[j + k] y = gaussMap^[j] (gaussMap^[k] y) := by
        rw [Function.iterate_add_apply]
      have hone : blockIndic (nearInv (1 / (2 * ((T:ℝ) + 1) ^ 3))) (gaussMap^[k] y) = 1 := by
        rw [blockIndic, Set.indicator_of_mem hk]; rfl
      rw [hone]
      have hterm : blockIndic (cellSet [] (T + 1)) (gaussMap^[j + k] y) = 1 := by
        rw [hiter, blockIndic, Set.indicator_of_mem hin]; rfl
      calc (1:ℝ) = blockIndic (cellSet [] (T + 1)) (gaussMap^[j + k] y) := hterm.symm
        _ ≤ _ := Finset.single_le_sum
            (f := fun j => blockIndic (cellSet [] (T + 1)) (gaussMap^[j + k] y))
            (fun i _ => blockIndic_nonneg _ _) (Finset.mem_range.2 hj3)
    · rw [blockIndic, Set.indicator_of_notMem hk]
      exact Finset.sum_nonneg fun i _ => blockIndic_nonneg _ _
  have hsum : blockCount (nearInv (1 / (2 * ((T:ℝ) + 1) ^ 3))) p y
      ≤ ∑ j ∈ Finset.range 3, ∑ k ∈ Finset.range p,
          blockIndic (cellSet [] (T + 1)) (gaussMap^[j + k] y) := by
    rw [blockCount_apply, Finset.sum_comm]
    exact Finset.sum_le_sum fun k _ => hpt k
  refine hsum.trans ?_
  have hj : ∀ j ∈ Finset.range 3, ∑ k ∈ Finset.range p,
      blockIndic (cellSet [] (T + 1)) (gaussMap^[j + k] y)
        ≤ blockCount (cellSet [] (T + 1)) p y + 2 := by
    intro j hj3
    have hs := sum_blockIndic_shift_le (cellSet [] (T + 1)) j p y
    have hjle : (j:ℝ) ≤ 2 := by
      have h3 : j < 3 := Finset.mem_range.1 hj3
      have : j ≤ 2 := by omega
      exact_mod_cast this
    linarith
  calc ∑ j ∈ Finset.range 3, ∑ k ∈ Finset.range p,
        blockIndic (cellSet [] (T + 1)) (gaussMap^[j + k] y)
      ≤ ∑ _j ∈ Finset.range 3, (blockCount (cellSet [] (T + 1)) p y + 2) :=
        Finset.sum_le_sum hj
    _ = 3 * blockCount (cellSet [] (T + 1)) p y + 6 := by
        simp [Finset.sum_const]; ring


/-- **The payoff.**  Under the chain's own second hypothesis `ImageTight`, the image orbit spends
an arbitrarily small fraction of its time near the reciprocals `1/k` — at a scale `η` that the
hypothesis itself chooses.  This is the de-circularised form of the directive's bootstrap: the
states at which bounded distortion fails are visited with negligible frequency. -/
theorem exists_nearInv_freq_le {y : ℝ} (hy : Irrational y) (hmem : y ∈ Set.Ioo (0:ℝ) 1)
    (htight : ImageTight y) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ p : ℕ in atTop, blockCount (nearInv η) p y / p ≤ ε := by
  classical
  obtain ⟨T₀, hT₀, hfreq⟩ := htight (ε / 6) (by linarith)
  set T := T₀ - 1 with hTdef
  have hT1 : 1 ≤ T := by omega
  have hTT : T + 1 = T₀ := by omega
  refine ⟨1 / (2 * ((T:ℝ) + 1) ^ 3), by positivity, ?_⟩
  have hbig : ∀ᶠ p : ℕ in atTop, (12:ℝ) / ε ≤ p := by
    obtain ⟨N, hN⟩ := exists_nat_gt ((12:ℝ) / ε)
    filter_upwards [eventually_ge_atTop N] with p hp
    have : (N:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
    linarith
  filter_upwards [hfreq, hbig, eventually_gt_atTop 0] with p hp hpbig hppos
  have hpR : (0:ℝ) < p := by exact_mod_cast hppos
  have hcount := blockCount_nearInv_le hy hmem hT1 p
  rw [hTT] at hcount
  rw [div_le_iff₀ hpR]
  have hp' : blockCount (cellSet [] T₀) p y ≤ (ε / 6) * p := by
    rw [div_le_iff₀ hpR] at hp; exact hp
  have h6 : (6:ℝ) ≤ (ε / 2) * p := by
    rw [div_le_iff₀ hε] at hpbig
    nlinarith
  nlinarith


/-- **The third digit is load-bearing.**  With only two bounded digits (`a₀ = a₁ = 1`, so
`T = 1`) the point `t = 1/(1+S)` can sit arbitrarily close to the reciprocal `1/2`: the
separation estimate is FALSE for two digits, whatever the constant. -/
theorem two_digits_insufficient {c : ℝ} (hc : 0 < c) :
    ∃ S : ℝ, 0 < S ∧ S < 1 ∧ 1 ≤ ((1:ℝ) + 1) * S ∧ |1 / (1 + S) - 1 / (2:ℝ)| < c := by
  set δ := min (1/2 : ℝ) c with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) hc
  have hδ2 : δ ≤ 1/2 := min_le_left _ _
  have hδc : δ ≤ c := min_le_right _ _
  refine ⟨1 - δ, by linarith, by linarith, by linarith, ?_⟩
  have hden : (0:ℝ) < 1 + (1 - δ) := by linarith
  have hne : (2 - δ) ≠ 0 := by intro h; linarith [hδ2]
  have hval : 1 / (1 + (1 - δ)) - 1 / (2:ℝ) = δ / (2 * (2 - δ)) := by
    rw [show (1:ℝ) + (1 - δ) = 2 - δ by ring]
    field_simp
    ring
  have hpos : (0:ℝ) ≤ δ / (2 * (2 - δ)) := by
    apply div_nonneg hδ0.le
    linarith
  rw [hval, abs_of_nonneg hpos]
  rw [div_lt_iff₀ (by linarith : (0:ℝ) < 2 * (2 - δ))]
  nlinarith


section Audit

#print axioms sep_arith
#print axioms dist_inv_ge_of_digits_le
#print axioms exists_large_digit_of_near_inv
#print axioms blockCount_nearInv_le
#print axioms exists_nearInv_freq_le
#print axioms two_digits_insufficient

end Audit

end NormalNumbers.VandeheyS7
