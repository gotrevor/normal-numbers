/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.TwoPointMertensLower
import NormalNumbers.PrimeModelSqrtFresh

/-!
# Helpers for `ExplicitSparseNormal`: block structure and block masses

The explicit set `P` (`explicitSparseSet`, restated here as `sparseCond` to avoid a circular
import) meets the dyadic block `B_k = {p : ⌊log₂ ⌊log₂ p⌋⌋ = k}` in exactly the primes of
`(2^{2^k}, 2^{T_k}]`, `T_k = ⌈2^k (k+1)/k⌉` (`mem_block_iff`).

Mertens' **first** theorem with an `O(1)` error (`mertens_lower`, `mertens_upper`, already in the
repo) is all that is needed: on a window `(x, y]`, `1/p` is pinned between `(log p/p)/log y` and
`(log p/p)/log x`, and the window `log y/log x = T_k/2^k ∈ [1 + 1/k, 1 + 1/k + 2^{-k}]` has
log-width `≍ 2^k/k → ∞`, so the `O(1)` error is negligible.  Hence the block mass satisfies
`1/(2(k+1)) ≤ blockMass k ≤ 18/k` (for `k ≥ 9`, resp. `k ≥ 1`), with no Mertens-second input.
-/

open Finset Filter Topology

namespace NormalNumbers.PrimeModel.Explicit.Aux

/-- `⌈2^k (k+1)/k⌉`: the binary-length cutoff of block `k`. -/
def blockTop (k : ℕ) : ℕ := (2 ^ k * (k + 1) + k - 1) / k

/-- The rounding identity: `L k < 2^k (k+1)` iff `L < ⌈2^k (k+1)/k⌉`. -/
theorem mul_lt_iff_lt_blockTop {k : ℕ} (hk : 1 ≤ k) (L : ℕ) :
    L * k < 2 ^ k * (k + 1) ↔ L < blockTop k := by
  unfold blockTop
  rw [show L < (2 ^ k * (k + 1) + k - 1) / k ↔ L + 1 ≤ (2 ^ k * (k + 1) + k - 1) / k from
    Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le (by omega), add_mul, one_mul]
  omega

/-- `k · T_k ≥ 2^k (k+1)`. -/
theorem blockTop_mul_ge {k : ℕ} (hk : 1 ≤ k) : 2 ^ k * (k + 1) ≤ blockTop k * k := by
  unfold blockTop
  have := Nat.lt_div_mul_add (a := 2 ^ k * (k + 1) + k - 1) (b := k) (by omega)
  omega

/-- `k · T_k < 2^k (k+1) + k`. -/
theorem blockTop_mul_lt {k : ℕ} (hk : 1 ≤ k) : blockTop k * k < 2 ^ k * (k + 1) + k := by
  unfold blockTop
  have := Nat.div_mul_le_self (2 ^ k * (k + 1) + k - 1) k
  omega

/-- A prime is not a power `2^m` with `m ≥ 2`. -/
theorem prime_ne_two_pow {p m : ℕ} (hp : p.Prime) (hm : 2 ≤ m) : p ≠ 2 ^ m := by
  intro h
  have := (hp.pow_eq_iff (a := 2) (k := m)).1 h.symm
  omega

/-- The explicit condition, restated (definitionally `explicitSparseSet`). -/
def sparseCond (p : ℕ) : Prop :=
  1 ≤ Nat.log 2 (Nat.log 2 p) ∧
    Nat.log 2 p * Nat.log 2 (Nat.log 2 p) < 2 ^ Nat.log 2 (Nat.log 2 p) * (Nat.log 2 (Nat.log 2 p) + 1)

/-- **Exact interval form.**  For `k ≥ 1` and `p` prime: `p ∈ P` with scale `k` iff
`2^{2^k} < p ≤ 2^{T_k}`. -/
theorem mem_block_iff {k p : ℕ} (hk : 1 ≤ k) (hp : p.Prime) :
    (sparseCond p ∧ Nat.log 2 (Nat.log 2 p) = k) ↔ 2 ^ 2 ^ k < p ∧ p ≤ 2 ^ blockTop k := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have h2k : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  constructor
  · rintro ⟨⟨-, hlt⟩, hkk⟩
    rw [hkk] at hlt
    have hL := (Nat.log_eq_iff (Or.inl (by omega : k ≠ 0))).1 hkk
    have hL0 : Nat.log 2 p ≠ 0 := by omega
    refine ⟨?_, ?_⟩
    · have h1 : 2 ^ 2 ^ k ≤ p := Nat.pow_le_of_le_log hp0 hL.1
      have h2 := prime_ne_two_pow hp h2k
      omega
    · exact (Nat.lt_pow_of_log_lt (by norm_num) ((mul_lt_iff_lt_blockTop hk _).1 hlt)).le
  · rintro ⟨hlo, hhi⟩
    have hT : 2 ≤ blockTop k := by
      have := blockTop_mul_ge hk
      by_contra hc
      push Not at hc
      have : blockTop k * k ≤ 1 * k := Nat.mul_le_mul_right _ (by omega)
      have : 2 * k ≤ 2 ^ k * (k + 1) := by nlinarith
      omega
    have hlt : p < 2 ^ blockTop k := lt_of_le_of_ne hhi (prime_ne_two_pow hp hT)
    have hLT : Nat.log 2 p < blockTop k := Nat.log_lt_of_lt_pow hp0 hlt
    have hLk : Nat.log 2 p * k < 2 ^ k * (k + 1) := (mul_lt_iff_lt_blockTop hk _).2 hLT
    have hLlo : 2 ^ k ≤ Nat.log 2 p := Nat.le_log_of_pow_le (by norm_num) hlo.le
    have hLhi : Nat.log 2 p < 2 ^ (k + 1) := by
      have h1 : 2 ^ k * (k + 1) ≤ 2 ^ (k + 1) * k := by
        rw [pow_succ]; nlinarith
      exact Nat.lt_of_mul_lt_mul_right (lt_of_lt_of_le hLk h1)
    have hkk : Nat.log 2 (Nat.log 2 p) = k :=
      (Nat.log_eq_iff (Or.inl (by omega : k ≠ 0))).2 ⟨hLlo, hLhi⟩
    exact ⟨⟨by omega, by rw [hkk]; exact hLk⟩, hkk⟩

/-! ### Mertens on a window, and the block masses -/

open NormalNumbers.CastingOut

/-- Prime sums over `(a, b]` as a difference of prime sums over `[0, b]` and `[0, a]`. -/
theorem sum_Ioc_primes_eq (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ p ∈ (Ioc a b).filter Nat.Prime, f p =
      ∑ p ∈ primesLe b, f p - ∑ p ∈ primesLe a, f p := by
  unfold primesLe
  rw [sum_filter, sum_filter, sum_filter, range_eq_Ico, range_eq_Ico,
    ← sum_Ico_consecutive _ (Nat.zero_le (a + 1)) (by omega : a + 1 ≤ b + 1),
    Finset.Ico_add_one_add_one_eq_Ioc]
  ring

/-- Mertens' first theorem on a window (upper): `Σ_{a<p≤b} log p/p ≤ log b − log a + 9 + log 4`. -/
theorem mertens_Ioc_le {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log p / (p : ℝ) ≤
      Real.log b - Real.log a + (9 + Real.log 4) := by
  rw [sum_Ioc_primes_eq _ hab]
  have := mertens_upper b (by omega)
  have := mertens_lower a ha
  linarith

/-- Mertens' first theorem on a window (lower): `Σ_{a<p≤b} log p/p ≥ log b − log a − 9 − log 4`. -/
theorem mertens_Ioc_ge {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    Real.log b - Real.log a - (9 + Real.log 4) ≤
      ∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log p / (p : ℝ) := by
  rw [sum_Ioc_primes_eq _ hab]
  have := mertens_upper a ha
  have := mertens_lower b (by omega)
  linarith

/-- On `(a, b]` with `a ≥ 2`: `Σ 1/p ≤ (Σ log p/p) / log a`. -/
theorem recip_Ioc_le_div {a b : ℕ} (ha : 2 ≤ a) :
    ∑ p ∈ (Ioc a b).filter Nat.Prime, (1 : ℝ) / p ≤
      (∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log p / (p : ℝ)) / Real.log a := by
  have hla : 0 < Real.log a := Real.log_pos (by exact_mod_cast (by omega : 1 < a))
  rw [sum_div]
  refine sum_le_sum fun p hp => ?_
  have hpa : a < p := (mem_Ioc.1 (mem_filter.1 hp).1).1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hlp : Real.log a ≤ Real.log p :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < a)) (by exact_mod_cast hpa.le)
  rw [show Real.log p / p / Real.log a = (1 / p) * (Real.log p / Real.log a) by ring]
  exact le_mul_of_one_le_right (by positivity) ((one_le_div hla).2 hlp)

/-- On `(a, b]` with `b ≥ 2`: `(Σ log p/p) / log b ≤ Σ 1/p`. -/
theorem div_le_recip_Ioc {a b : ℕ} (hb : 2 ≤ b) :
    (∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log p / (p : ℝ)) / Real.log b ≤
      ∑ p ∈ (Ioc a b).filter Nat.Prime, (1 : ℝ) / p := by
  have hlb : 0 < Real.log b := Real.log_pos (by exact_mod_cast (by omega : 1 < b))
  rw [sum_div]
  refine sum_le_sum fun p hp => ?_
  have hpb : p ≤ b := (mem_Ioc.1 (mem_filter.1 hp).1).2
  have hpr := (mem_filter.1 hp).2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpr.pos
  have hlp : Real.log p ≤ Real.log b := Real.log_le_log hp0 (by exact_mod_cast hpb)
  rw [show Real.log p / p / Real.log b = (1 / p) * (Real.log p / Real.log b) by ring]
  exact mul_le_of_le_one_right (by positivity) ((div_le_one hlb).2 hlp)

/-- The primes of block `k` lying in `P`: `(2^{2^k}, 2^{T_k}]`. -/
def blockSet (k : ℕ) : Finset ℕ := (Ioc (2 ^ 2 ^ k) (2 ^ blockTop k)).filter Nat.Prime

/-- The reciprocal mass of block `k`. -/
noncomputable def blockMass (k : ℕ) : ℝ := ∑ p ∈ blockSet k, (1 : ℝ) / p

/-- `2^k ≤ T_k`. -/
theorem two_pow_le_blockTop {k : ℕ} (hk : 1 ≤ k) : 2 ^ k ≤ blockTop k := by
  have := blockTop_mul_ge hk
  by_contra hc
  push Not at hc
  have : blockTop k * k < 2 ^ k * k := Nat.mul_lt_mul_of_pos_right hc (by omega)
  nlinarith

/-- `log 2^{2^k} = 2^k log 2` and `log 2^{T} = T log 2`, as reals. -/
theorem log_two_pow_cast (m : ℕ) : Real.log ((2 ^ m : ℕ) : ℝ) = (m : ℝ) * Real.log 2 := by
  push_cast
  rw [Real.log_pow]

/-- **Block mass, upper bound.**  `blockMass k ≤ 18/k` for `k ≥ 1`. -/
theorem blockMass_le {k : ℕ} (hk : 1 ≤ k) : blockMass k ≤ 18 / k := by
  have hT := two_pow_le_blockTop hk
  have ha : 2 ≤ 2 ^ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_two_pow)
  have hab : 2 ^ 2 ^ k ≤ 2 ^ blockTop k := Nat.pow_le_pow_right (by norm_num) hT
  have h1 := recip_Ioc_le_div (b := 2 ^ blockTop k) ha
  have h2 := mertens_Ioc_le (by omega : 1 ≤ 2 ^ 2 ^ k) hab
  rw [log_two_pow_cast, log_two_pow_cast] at h2
  rw [log_two_pow_cast] at h1
  set S := ∑ p ∈ (Ioc (2 ^ 2 ^ k) (2 ^ blockTop k)).filter Nat.Prime, Real.log p / (p : ℝ)
  have hl := Real.log_two_gt_d9
  have hl' := Real.log_two_lt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hmul := blockTop_mul_lt hk
  have hku : (k : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast (Nat.lt_two_pow_self).le
  have hmulR : (blockTop k : ℝ) * k < (2 : ℝ) ^ k * (k + 1) + k := by exact_mod_cast hmul
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hTR : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
  rw [hTR] at h1 h2
  set u : ℝ := (2 : ℝ) ^ k
  set t : ℝ := (blockTop k : ℝ)
  set l := Real.log 2
  have hu0 : 0 < u := by positivity
  have hS : S * k ≤ 18 * (u * l) := by
    have : S ≤ (t - u) * l + 9 + 2 * l := by nlinarith
    have hSk : S * k ≤ ((t - u) * l + 9 + 2 * l) * k :=
      mul_le_mul_of_nonneg_right this (by linarith)
    nlinarith [mul_lt_mul_of_pos_right hmulR (by linarith : (0:ℝ) < l)]
  unfold blockMass blockSet
  refine h1.trans ?_
  rw [div_le_div_iff₀ (by positivity) (by linarith)]
  linarith

/-- `30 (k+1) ≤ 2^k` for `k ≥ 9`. -/
theorem thirty_mul_le_two_pow : ∀ k : ℕ, 9 ≤ k → 30 * (k + 1) ≤ 2 ^ k
  | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h | 7, h | 8, h => by omega
  | 9, _ => by norm_num
  | k + 10, _ => by
    have := thirty_mul_le_two_pow (k + 9) (by omega)
    rw [pow_succ]; omega

/-- **Block mass, lower bound.**  `1/(2(k+1)) ≤ blockMass k` for `k ≥ 9`. -/
theorem blockMass_ge {k : ℕ} (hk : 9 ≤ k) : 1 / (2 * ((k : ℝ) + 1)) ≤ blockMass k := by
  have hk1 : 1 ≤ k := by omega
  have hT := two_pow_le_blockTop hk1
  have hab : 2 ^ 2 ^ k ≤ 2 ^ blockTop k := Nat.pow_le_pow_right (by norm_num) hT
  have hb : 2 ≤ 2 ^ blockTop k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ blockTop k := Nat.pow_le_pow_right (by norm_num) (by
        have := Nat.one_le_two_pow (n := k); omega)
  have h1 := div_le_recip_Ioc (a := 2 ^ 2 ^ k) hb
  have h2 := mertens_Ioc_ge (Nat.one_le_two_pow) hab
  rw [log_two_pow_cast, log_two_pow_cast] at h2
  rw [log_two_pow_cast] at h1
  set S := ∑ p ∈ (Ioc (2 ^ 2 ^ k) (2 ^ blockTop k)).filter Nat.Prime, Real.log p / (p : ℝ)
  have hl := Real.log_two_gt_d9
  have hl' := Real.log_two_lt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hmulR : (2 : ℝ) ^ k * (k + 1) ≤ (blockTop k : ℝ) * k := by
    exact_mod_cast blockTop_mul_ge hk1
  have h30 : 30 * ((k : ℝ) + 1) ≤ (2 : ℝ) ^ k := by exact_mod_cast thirty_mul_le_two_pow k hk
  have hTu : (2 : ℝ) ^ k ≤ (blockTop k : ℝ) := by exact_mod_cast hT
  have hTR : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
  rw [hTR] at h2
  set u : ℝ := (2 : ℝ) ^ k
  set t : ℝ := (blockTop k : ℝ)
  set l := Real.log 2
  have hkR : (9 : ℝ) ≤ k := by exact_mod_cast hk
  have hu0 : 0 < u := by positivity
  have ht0 : 0 < t := by linarith
  -- `2 (k+1) S ≥ t l`
  have hS : t * l ≤ 2 * ((k : ℝ) + 1) * S := by
    have hS' : (t - u) * l - 9 - 2 * l ≤ S := by nlinarith
    have hk2 : (0 : ℝ) ≤ 2 * ((k : ℝ) + 1) := by positivity
    have := mul_le_mul_of_nonneg_left hS' hk2
    have htu : t ≤ (t - u) * ((k : ℝ) + 1) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right htu (by linarith : (0:ℝ) ≤ l),
      mul_le_mul_of_nonneg_right h30 (by linarith : (0:ℝ) ≤ l),
      mul_le_mul_of_nonneg_right hTu (by linarith : (0:ℝ) ≤ l)]
  unfold blockMass blockSet
  refine le_trans ?_ h1
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-! ### Assembly: divergence and vanishing fresh mass -/

/-- Membership in `blockSet k`: prime, in `P`, of scale `k`. -/
theorem mem_blockSet {k p : ℕ} (hk : 1 ≤ k) :
    p ∈ blockSet k ↔ p.Prime ∧ sparseCond p ∧ Nat.log 2 (Nat.log 2 p) = k := by
  unfold blockSet
  rw [mem_filter, mem_Ioc]
  constructor
  · rintro ⟨h, hp⟩
    exact ⟨hp, (mem_block_iff hk hp).2 h⟩
  · rintro ⟨hp, h⟩
    exact ⟨(mem_block_iff hk hp).1 h, hp⟩

/-- Distinct blocks are disjoint. -/
theorem blockSet_disjoint {k k' : ℕ} (hk : 1 ≤ k) (hk' : 1 ≤ k') (h : k ≠ k') :
    Disjoint (blockSet k) (blockSet k') := by
  rw [Finset.disjoint_left]
  intro p hp hp'
  exact h (((mem_blockSet hk).1 hp).2.2.symm.trans ((mem_blockSet hk').1 hp').2.2)

variable (S : ℕ → Prop) [DecidablePred S]

/-- **Divergence.**  Any `S` agreeing with `sparseCond` has `Σ_{p∈S} 1/p = ∞`. -/
theorem divergentRecip_of_iff (hS : ∀ p, S p ↔ sparseCond p) :
    NormalNumbers.G4Sparse.DivergentRecip S := by
  intro hsum
  set f : ℕ → ℝ := fun p => if p.Prime ∧ S p then (1 : ℝ) / p else 0 with hf
  have hf0 : ∀ p, 0 ≤ f p := fun p => by
    simp only [hf]; split_ifs <;> positivity
  have hpd : ∀ K : ℕ, ((Ico 9 K : Finset ℕ) : Set ℕ).PairwiseDisjoint blockSet := by
    intro K k hk k' hk' hne
    exact blockSet_disjoint (by simp at hk; omega) (by simp at hk'; omega) hne
  have hK : ∀ K : ℕ, ∑ k ∈ Ico 9 K, 1 / (2 * ((k : ℝ) + 1)) ≤ ∑' p, f p := by
    intro K
    calc ∑ k ∈ Ico 9 K, 1 / (2 * ((k : ℝ) + 1)) ≤ ∑ k ∈ Ico 9 K, blockMass k :=
          sum_le_sum fun k hk => blockMass_ge (mem_Ico.1 hk).1
      _ = ∑ p ∈ (Ico 9 K).biUnion blockSet, f p := by
          rw [sum_biUnion (hpd K)]
          refine sum_congr rfl fun k hk => ?_
          unfold blockMass
          refine sum_congr rfl fun p hp => ?_
          have := (mem_blockSet (by have := (mem_Ico.1 hk).1; omega)).1 hp
          simp only [hf, if_pos (And.intro this.1 ((hS p).2 this.2.1))]
      _ ≤ ∑' p, f p := hsum.sum_le_tsum _ (fun p _ => hf0 p)
  have htend := Real.tendsto_sum_range_one_div_nat_succ_atTop
  have hbd : ∀ K : ℕ, ∑ i ∈ range K, (1 / ((i : ℝ) + 1)) ≤
      ∑ i ∈ range 9, (1 / ((i : ℝ) + 1)) + 2 * ∑' p, f p := by
    intro K
    rcases le_or_gt K 9 with hK9 | hK9
    · have : ∑ i ∈ range K, (1 / ((i : ℝ) + 1)) ≤ ∑ i ∈ range 9, (1 / ((i : ℝ) + 1)) :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.2 hK9) (fun i _ _ => by positivity)
      have : 0 ≤ ∑' p, f p := tsum_nonneg hf0
      linarith
    · rw [range_eq_Ico, ← sum_Ico_consecutive _ (Nat.zero_le 9) hK9.le, ← range_eq_Ico]
      have h2 : ∑ i ∈ Ico 9 K, (1 / ((i : ℝ) + 1)) =
          2 * ∑ k ∈ Ico 9 K, 1 / (2 * ((k : ℝ) + 1)) := by
        rw [mul_sum]; refine sum_congr rfl fun i _ => ?_; field_simp
      have := hK K
      linarith
  obtain ⟨K, hK'⟩ := (htend.eventually_gt_atTop
    (∑ i ∈ range 9, (1 / ((i : ℝ) + 1)) + 2 * ∑' p, f p)).exists
  exact absurd (hbd K) (not_le.2 hK')

/-- Scale bookkeeping: a prime `p ∈ (√N, N]` of scale `k` has `k ∈ {m − 1, m}`,
`m = ⌊log₂ ⌊log₂ N⌋⌋`. -/
theorem scale_window {N p : ℕ} (hlo : Nat.sqrt N < p) (hhi : p ≤ N) :
    Nat.log 2 (Nat.log 2 N) ≤ Nat.log 2 (Nat.log 2 p) + 1 ∧
      Nat.log 2 (Nat.log 2 p) ≤ Nat.log 2 (Nat.log 2 N) := by
  refine ⟨?_, Nat.log_mono_right (Nat.log_mono_right hhi)⟩
  set L := Nat.log 2 p
  set k := Nat.log 2 L
  have hN : N < p * p := Nat.sqrt_lt.1 hlo
  have hp : p < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) p
  have hL : L < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) L
  have hN2 : N < 2 ^ (2 * L + 2) := by
    calc N < p * p := hN
      _ ≤ 2 ^ (L + 1) * 2 ^ (L + 1) := Nat.mul_le_mul hp.le hp.le
      _ = 2 ^ (2 * L + 2) := by rw [← pow_add]; ring_nf
  have hn : Nat.log 2 N < 2 * L + 2 := Nat.log_lt_of_lt_pow' (by omega) hN2
  have hn2 : Nat.log 2 N < 2 ^ (k + 2) := by rw [pow_succ]; omega
  have := Nat.log_lt_of_lt_pow' (by omega) hn2
  omega

/-- **Fresh-mass bound.**  For `m = ⌊log₂ ⌊log₂ N⌋⌋ ≥ 2`,
`Σ_{√N<p≤N, p∈S} 1/p ≤ 36/(m − 1)`. -/
theorem recipSumIoc_sqrt_le (hS : ∀ p, S p ↔ sparseCond p) {N : ℕ}
    (hm : 2 ≤ Nat.log 2 (Nat.log 2 N)) :
    NormalNumbers.G4Sparse.recipSumIoc S (Nat.sqrt N) N ≤
      36 / ((Nat.log 2 (Nat.log 2 N) : ℝ) - 1) := by
  set m := Nat.log 2 (Nat.log 2 N) with hmdef
  have hsub : (Ioc (Nat.sqrt N) N).filter (fun p => p.Prime ∧ S p) ⊆
      blockSet (m - 1) ∪ blockSet m := by
    intro p hp
    rw [mem_filter, mem_Ioc] at hp
    obtain ⟨⟨hlo, hhi⟩, hpr, hSp⟩ := hp
    have hc := (hS p).1 hSp
    obtain ⟨h1, h2⟩ := scale_window hlo hhi
    rw [← hmdef] at h1 h2
    have hk1 : 1 ≤ Nat.log 2 (Nat.log 2 p) := hc.1
    rcases (by omega : Nat.log 2 (Nat.log 2 p) = m - 1 ∨ Nat.log 2 (Nat.log 2 p) = m) with
      h | h
    · exact mem_union_left _ ((mem_blockSet (by omega)).2 ⟨hpr, hc, h⟩)
    · exact mem_union_right _ ((mem_blockSet (by omega)).2 ⟨hpr, hc, h⟩)
  have hdisj : Disjoint (blockSet (m - 1)) (blockSet m) :=
    blockSet_disjoint (by omega) (by omega) (by omega)
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hb1 := blockMass_le (k := m - 1) (by omega)
  have hb2 := blockMass_le (k := m) (by omega)
  rw [hcast] at hb1
  have hb2' : (18 : ℝ) / m ≤ 18 / ((m : ℝ) - 1) :=
    div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  unfold NormalNumbers.G4Sparse.recipSumIoc
  calc ∑ p ∈ (Ioc (Nat.sqrt N) N).filter (fun p => p.Prime ∧ S p), (1 : ℝ) / p
      ≤ ∑ p ∈ blockSet (m - 1) ∪ blockSet m, (1 : ℝ) / p :=
        sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
    _ = blockMass (m - 1) + blockMass m := by rw [sum_union hdisj]; rfl
    _ ≤ 36 / ((m : ℝ) - 1) := by
        have : (36 : ℝ) / ((m : ℝ) - 1) = 18 / ((m : ℝ) - 1) + 18 / ((m : ℝ) - 1) := by ring
        linarith

/-- **Vanishing `√N`-fresh mass.**  Any `S` agreeing with `sparseCond` has
`Σ_{√N<p≤N, p∈S} 1/p → 0`. -/
theorem sqrtFreshMassZero_of_iff (hS : ∀ p, S p ↔ sparseCond p) :
    NormalNumbers.PrimeModel.SqrtFresh.SqrtFreshMassZero S := by
  unfold NormalNumbers.PrimeModel.SqrtFresh.SqrtFreshMassZero
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hM⟩ := exists_nat_gt (36 / ε + 2)
  refine ⟨2 ^ 2 ^ M, fun N hN => ?_⟩
  have hm : M ≤ Nat.log 2 (Nat.log 2 N) :=
    Nat.le_log_of_pow_le (by norm_num) (Nat.le_log_of_pow_le (by norm_num) hN)
  have hM2 : (2 : ℝ) < M := by have : 0 < 36 / ε := by positivity
                               linarith
  have hM2' : 2 ≤ M := by exact_mod_cast hM2.le
  have hmR : (M : ℝ) ≤ Nat.log 2 (Nat.log 2 N) := by exact_mod_cast hm
  have hb := recipSumIoc_sqrt_le S hS (N := N) (by omega)
  have h0 : 0 ≤ NormalNumbers.G4Sparse.recipSumIoc S (Nat.sqrt N) N := by
    unfold NormalNumbers.G4Sparse.recipSumIoc
    exact sum_nonneg fun p _ => by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  refine lt_of_le_of_lt hb ?_
  rw [div_lt_iff₀ (by linarith)]
  have : 36 / ε < (M : ℝ) - 2 := by linarith
  rw [div_lt_iff₀ hε] at this
  nlinarith

end NormalNumbers.PrimeModel.Explicit.Aux
