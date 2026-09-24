/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SwingC3Net
import NormalNumbers.SwingC3Split

/-!
# Leaf A of the rotation route, assembled

`SwingC3Net.lean` supplies six independent pieces; this file glues them into
`exists_rotationCover_core`, the arithmetic leaf of `SwingC3Rotation.lean`.

The construction, for a target arc of length `len`:

* pick `L` with `b·L + 2 < len·b^L` (`exists_L_growth`);
* set `W = L+1`, `K = (b−1)·L`, and take the minimal `P` holding exactly `K` primes in `(W, P]`
  (`exists_prime_window`), so `π(P) ≤ W + K = b·L + 1`;
* `Q = ∏_{p ≤ P} p`, `R = ∏_{p ≤ W} p`, and for each `k < b^L` steer the `K` primes of `(W,P]`
  into the window slots by the base-`b` digits of `k`, pinning `a ≡ 0 [MOD R]`;
* then `tailSmall P b (a k) = C + k·b^{−L} + ρ_k` with `0 ≤ ρ_k ≤ π(P)·b^{−L}/(b−1)`, and
  `exists_perturbed_grid_mem_Ico` turns that perturbed grid into a `len`-net.

Distinctness mod `Q` is free: `ω_{≤P}` is `Q`-periodic, so congruent classes have equal window
counts, hence equal digit vectors, hence equal `k`.
-/

open Finset Filter Topology

namespace NormalNumbers

/-! ### Base-`b` digits -/

lemma sum_digits_eq {b : ℕ} (hb : 2 ≤ b) : ∀ (L k : ℕ), k < b ^ L →
    ∑ j ∈ range L, (k / b ^ j % b) * b ^ j = k := by
  intro L
  induction L with
  | zero =>
      intro k hk
      rw [pow_zero] at hk
      simp only [range_zero, Finset.sum_empty]
      omega
  | succ L ih =>
      intro k hk
      have hkb : k / b < b ^ L := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        calc k < b ^ (L + 1) := hk
          _ = b ^ L * b := by ring
      have hIH := ih (k / b) hkb
      rw [Finset.sum_range_succ']
      have hrw : ∀ j : ℕ, (k / b ^ (j + 1) % b) * b ^ (j + 1)
          = (k / b / b ^ j % b) * b ^ j * b := by
        intro j
        rw [show b ^ (j + 1) = b * b ^ j by rw [pow_succ]; ring, ← Nat.div_div_eq_div_mul]
        ring
      simp only [hrw]
      rw [← Finset.sum_mul, hIH, pow_zero, Nat.div_one, mul_one]
      rw [mul_comm]
      exact Nat.div_add_mod k b

/-- The digit identity, read in the "most significant first" order used by the window slots. -/
lemma sum_digits_reflect {b : ℕ} (hb : 2 ≤ b) (L k : ℕ) (hk : k < b ^ L) :
    ∑ i ∈ range L, (k / b ^ (L - 1 - i) % b) * b ^ (L - 1 - i) = k := by
  have := Finset.sum_range_reflect (fun j => (k / b ^ j % b) * b ^ j) L
  rw [this]
  exact sum_digits_eq hb L k hk

/-- Same identity, as a real grid point: the window head runs over all multiples of `b^{-L}`. -/
lemma sum_digits_real {b : ℕ} (hb : 2 ≤ b) (L k : ℕ) (hk : k < b ^ L) :
    ∑ i ∈ range L, ((k / b ^ (L - 1 - i) % b : ℕ) : ℝ) / (b : ℝ) ^ (i + 1)
      = (k : ℝ) / (b : ℝ) ^ L := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by
    have : (0 : ℕ) < b := by omega
    exact_mod_cast this
  have hnat := sum_digits_reflect hb L k hk
  have hcast : ∑ i ∈ range L,
      ((k / b ^ (L - 1 - i) % b : ℕ) : ℝ) * (b : ℝ) ^ (L - 1 - i) = (k : ℝ) := by
    have := congrArg (fun t : ℕ => (t : ℝ)) hnat
    push_cast at this
    simpa using this
  rw [← hcast, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hiL : i < L := mem_range.1 hi
  have hpow : (b : ℝ) ^ (L - 1 - i) * (b : ℝ) ^ (i + 1) = (b : ℝ) ^ L := by
    rw [← pow_add]; congr 1; omega
  rw [div_eq_div_iff (by positivity) (by positivity), mul_assoc, hpow]

/-! ### `b^L` beats `b·L + 2` -/

lemma exists_L_growth {b : ℕ} (hb : 2 ≤ b) (len : ℝ) (hlen : 0 < len) :
    ∃ L : ℕ, ((b : ℝ) * L + 2) < len * (b : ℝ) ^ L := by
  have hb1 : (1 : ℝ) < (b : ℝ) := by
    have : (1 : ℕ) < b := by omega
    exact_mod_cast this
  have hb0 : (0 : ℝ) < (b : ℝ) := by linarith
  have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 hb1
  have h2 := tendsto_pow_const_div_const_pow_of_one_lt 0 hb1
  have hsum : Tendsto (fun n : ℕ => ((b : ℝ) * n + 2) / (b : ℝ) ^ n) atTop (𝓝 0) := by
    have hc := (h1.const_mul (b : ℝ)).add (h2.const_mul 2)
    simp only [mul_zero, add_zero] at hc
    refine hc.congr fun n => ?_
    have hne : ((b : ℝ) ^ n) ≠ 0 := by positivity
    field_simp
  obtain ⟨L, hL⟩ := (hsum.eventually_lt_const hlen).exists
  exact ⟨L, by rwa [div_lt_iff₀ (by positivity)] at hL⟩

/-! ### The steered class -/

/-- The constant part of the window count at slot `j`: the primes `≤ W` dividing `j`. -/
def slotConst (W j : ℕ) : ℕ := ((range (W + 1)).filter (fun p => p.Prime ∧ p ∣ j)).card

/-- **A steered class.**  With `S` the primes in `(L+1, P]` and `d` a vector of slot demands
fitting inside `S`, there is a residue `a` (pinned to be divisible by every prime `≤ L+1`)
whose window counts are the constants `slotConst` plus the demands. -/
theorem exists_steered_class (L P : ℕ) (d : ℕ → ℕ) (S : Finset ℕ)
    (hSdef : ∀ p, p ∈ S ↔ (L + 1 < p ∧ p ≤ P ∧ p.Prime)) (hLP : L + 1 ≤ P)
    (hcard : (∑ i ∈ range L, d i) ≤ S.card) :
    ∃ a : ℕ, ∀ j, 1 ≤ j → j ≤ L →
      omegaSmall P (a + j) = slotConst (L + 1) j + d (j - 1) := by
  classical
  obtain ⟨f, hfrange, hfcount⟩ := exists_slot_assignment L S d hcard
  set R : ℕ := ∏ p ∈ (range (L + 2)).filter Nat.Prime, p with hR
  have hR0 : 0 < R := by
    rw [hR]
    refine Finset.prod_pos fun p hp => ?_
    exact (Finset.mem_filter.1 hp).2.pos
  have hS : ∀ p ∈ S, p.Prime := fun p hp => ((hSdef p).1 hp).2.2
  have hSL : ∀ p ∈ S, L + 1 < p := fun p hp => ((hSdef p).1 hp).1
  have hcop : ∀ p ∈ S, ¬ p ∣ R := by
    intro p hp hdvd
    obtain ⟨q, hq, hpq⟩ := (Nat.Prime.prime (hS p hp)).exists_mem_finset_dvd hdvd
    simp only [Finset.mem_filter, mem_range] at hq
    have : p = q := ((Nat.prime_dvd_prime_iff_eq (hS p hp) hq.2).1 hpq)
    have := hSL p hp
    omega
  obtain ⟨a, ha0, hsteer⟩ := exists_crt_pattern_mod (L + 1) S hS hSL f
    (fun p hp => (hfrange p hp).1) (fun p hp => (hfrange p hp).2) R hR0 hcop 0
  have hRa : ∀ p, p ≤ L + 1 → p.Prime → p ∣ a := by
    intro p hp hpp
    have hpR : p ∣ R := by
      rw [hR]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨mem_range.2 (by omega), hpp⟩)
    have hRdvd : R ∣ a := by
      have : a ≡ 0 [MOD R] := ha0
      exact (Nat.modEq_zero_iff_dvd).1 this
    exact hpR.trans hRdvd
  refine ⟨a, fun j hj1 hjL => ?_⟩
  rw [omegaSmall_steered S hLP hSdef hRa hsteer hj1 (by omega),
    hfcount j hj1 hjL, slotConst]

/-! ### Leaf A -/

/-- **Leaf A, proved.**  The steering classes exist and their small-prime rotations form a
`len`-net of the circle. -/
theorem exists_rotationCover_core {b : ℕ} (hb : 2 ≤ b) (α len : ℝ) (hα : 0 ≤ α) (hlen : 0 < len)
    (hαlen : α + len ≤ 1) :
    ∃ (P Q M : ℕ) (a : ℕ → ℕ), 0 < Q ∧ 0 < M ∧
      (∀ p, p ≤ P → p.Prime → p ∣ Q) ∧
      (∀ p, p.Prime → p ∣ Q → p ≤ P) ∧
      (∀ k, k < M → ∀ k', k' < M → a k ≡ a k' [MOD Q] → k = k') ∧
      (∀ y : ℝ, ∃ k, k < M ∧
        Int.fract (tailSmall P b (a k) + y) ∈ Set.Ico α (α + len)) := by
  classical
  have hb0 : (0 : ℕ) < b := by omega
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb0
  have hb1R : (1 : ℝ) ≤ (b : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  obtain ⟨L, hL⟩ := exists_L_growth hb len hlen
  set W : ℕ := L + 1 with hW
  set K : ℕ := (b - 1) * L with hK
  obtain ⟨P, hWP, hPcard, hPpi⟩ := exists_prime_window W K
  set S : Finset ℕ := (Finset.Ioc W P).filter Nat.Prime with hS
  have hSdef : ∀ p, p ∈ S ↔ (W < p ∧ p ≤ P ∧ p.Prime) := by
    intro p
    simp only [hS, Finset.mem_filter, Finset.mem_Ioc]
    tauto
  have hScard : S.card = K := hPcard
  set M : ℕ := b ^ L with hM
  have hM0 : 0 < M := by rw [hM]; positivity
  set Q : ℕ := ∏ p ∈ (range (P + 1)).filter Nat.Prime, p with hQ
  have hQ0 : 0 < Q := by
    rw [hQ]; exact Finset.prod_pos fun p hp => (Finset.mem_filter.1 hp).2.pos
  have hQdvd : ∀ p, p ≤ P → p.Prime → p ∣ Q := by
    intro p hp hpp
    rw [hQ]; exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨mem_range.2 (by omega), hpp⟩)
  have hQle : ∀ p, p.Prime → p ∣ Q → p ≤ P := by
    intro p hpp hdvd
    rw [hQ] at hdvd
    obtain ⟨q, hq, hpq⟩ := (Nat.Prime.prime hpp).exists_mem_finset_dvd hdvd
    simp only [Finset.mem_filter, mem_range] at hq
    have : p = q := (Nat.prime_dvd_prime_iff_eq hpp hq.2).1 hpq
    omega
  -- the digit vector of `k`
  set dig : ℕ → ℕ → ℕ := fun k i => k / b ^ (L - 1 - i) % b with hdig
  have hdigfit : ∀ k, (∑ i ∈ range L, dig k i) ≤ S.card := by
    intro k
    rw [hScard, hK]
    calc (∑ i ∈ range L, dig k i) ≤ ∑ _i ∈ range L, (b - 1) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := Nat.mod_lt (k / b ^ (L - 1 - i)) hb0
          simp only [hdig]
          omega
      _ = (b - 1) * L := by rw [Finset.sum_const, card_range]; ring
  have hex : ∀ k : ℕ, ∃ a : ℕ, ∀ j, 1 ≤ j → j ≤ L →
      omegaSmall P (a + j) = slotConst W j + dig k (j - 1) := by
    intro k
    exact exists_steered_class L P (dig k) S hSdef hWP (hdigfit k)
  set a : ℕ → ℕ := fun k => Classical.choose (hex k) with ha
  have haspec : ∀ k j, 1 ≤ j → j ≤ L →
      omegaSmall P (a k + j) = slotConst W j + dig k (j - 1) :=
    fun k => Classical.choose_spec (hex k)
  -- injectivity mod `Q`
  have hinj : ∀ k, k < M → ∀ k', k' < M → a k ≡ a k' [MOD Q] → k = k' := by
    intro k hk k' hk' hmod
    have hd : ∀ i, i < L → dig k i = dig k' i := by
      intro i hi
      have h1 := haspec k (i + 1) (by omega) (by omega)
      have h2 := haspec k' (i + 1) (by omega) (by omega)
      have heq : omegaSmall P (a k + (i + 1)) = omegaSmall P (a k' + (i + 1)) :=
        omegaSmall_congr_of_modEq (by omega) (by omega) hQdvd (hmod.add_right _)
      simp only [Nat.add_sub_cancel] at h1 h2
      omega
    have e1 := sum_digits_reflect hb L k (by rw [← hM]; exact hk)
    have e2 := sum_digits_reflect hb L k' (by rw [← hM]; exact hk')
    rw [← e1, ← e2]
    exact Finset.sum_congr rfl fun i hi => by
      simp only [hdig] at hd; rw [hd i (mem_range.1 hi)]
  -- the window head: a grid point
  set C : ℝ := ∑ i ∈ range L, (slotConst W (i + 1) : ℝ) / (b : ℝ) ^ (i + 1) with hC
  have hhead : ∀ k, k < M →
      ∑ i ∈ range L, (omegaSmall P (a k + i + 1) : ℝ) / (b : ℝ) ^ (i + 1)
        = C + (k : ℝ) / (b : ℝ) ^ L := by
    intro k hk
    have : ∀ i ∈ range L, (omegaSmall P (a k + i + 1) : ℝ) / (b : ℝ) ^ (i + 1)
        = (slotConst W (i + 1) : ℝ) / (b : ℝ) ^ (i + 1)
          + ((dig k i : ℕ) : ℝ) / (b : ℝ) ^ (i + 1) := by
      intro i hi
      have hiL : i < L := mem_range.1 hi
      have h1 := haspec k (i + 1) (by omega) (by omega : i + 1 ≤ L)
      simp only [Nat.add_sub_cancel] at h1
      rw [show a k + i + 1 = a k + (i + 1) by ring, h1]
      push_cast
      ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← hC]
    congr 1
    exact sum_digits_real hb L k (by rw [← hM]; exact hk)
  -- the perturbation
  set ε : ℝ := (piCount P : ℝ) / ((b : ℝ) ^ L * ((b : ℝ) - 1)) with hε
  have hrem : ∀ k, ∃ r : ℝ, tailSmall P b (a k)
      = (∑ i ∈ range L, (omegaSmall P (a k + i + 1) : ℝ) / (b : ℝ) ^ (i + 1)) + r
      ∧ 0 ≤ r ∧ r ≤ ε := fun k => tailSmall_head_rem hb P (a k) L
  set ρ : ℕ → ℝ := fun k => Classical.choose (hrem k) with hρ
  have hρspec : ∀ k, tailSmall P b (a k)
      = (∑ i ∈ range L, (omegaSmall P (a k + i + 1) : ℝ) / (b : ℝ) ^ (i + 1)) + ρ k
      ∧ 0 ≤ ρ k ∧ ρ k ≤ ε := fun k => Classical.choose_spec (hrem k)
  -- the net inequality
  have hMR : ((M : ℕ) : ℝ) = (b : ℝ) ^ L := by rw [hM]; push_cast; ring
  have hkl : K + L = b * L := by
    rw [hK]
    cases b with
    | zero => omega
    | succ n => simp only [Nat.succ_sub_one]; ring
  have hpiR : (piCount P : ℝ) ≤ (b : ℝ) * L + 1 := by
    have hnat : piCount P ≤ b * L + 1 := by omega
    calc (piCount P : ℝ) ≤ ((b * L + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = (b : ℝ) * L + 1 := by push_cast; ring
  have hεle : ε ≤ ((b : ℝ) * L + 1) / (b : ℝ) ^ L := by
    rw [hε]
    have hpow : (0 : ℝ) < (b : ℝ) ^ L := by positivity
    rw [div_le_div_iff₀ (by positivity) hpow]
    have hnn : (0 : ℝ) ≤ (b : ℝ) * L + 1 := by positivity
    have s1 : (piCount P : ℝ) * (b : ℝ) ^ L ≤ ((b : ℝ) * L + 1) * (b : ℝ) ^ L := by
      exact mul_le_mul_of_nonneg_right hpiR hpow.le
    have s0 : (b : ℝ) ^ L ≤ (b : ℝ) ^ L * ((b : ℝ) - 1) := le_mul_of_one_le_right hpow.le hb1R
    have s2 : ((b : ℝ) * L + 1) * (b : ℝ) ^ L
        ≤ ((b : ℝ) * L + 1) * ((b : ℝ) ^ L * ((b : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left s0 hnn
    linarith
  have hnet : 1 / ((M : ℕ) : ℝ) + ε < len := by
    rw [hMR]
    have hpow : (0 : ℝ) < (b : ℝ) ^ L := by positivity
    have : 1 / (b : ℝ) ^ L + ((b : ℝ) * L + 1) / (b : ℝ) ^ L = ((b : ℝ) * L + 2) / (b : ℝ) ^ L := by
      field_simp; ring
    have hlt : ((b : ℝ) * L + 2) / (b : ℝ) ^ L < len := by
      rw [div_lt_iff₀ hpow]; linarith [hL]
    linarith
  refine ⟨P, Q, M, a, hQ0, hM0, hQdvd, hQle, hinj, ?_⟩
  intro y
  obtain ⟨k, hk, hmem⟩ := exists_perturbed_grid_mem_Ico hM0 (C + y) α len ε ρ
    (fun k => (hρspec k).2.1) (fun k => (hρspec k).2.2) hα hnet hαlen
  refine ⟨k, hk, ?_⟩
  have : C + y + (k : ℝ) / (M : ℕ) + ρ k = tailSmall P b (a k) + y := by
    rw [hMR, (hρspec k).1, hhead k hk]
    ring
  rwa [this] at hmem

end NormalNumbers
