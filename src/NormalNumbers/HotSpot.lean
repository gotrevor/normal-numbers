/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Sandwich
import NormalNumbers.Wall

/-!
# The strong hot spot lemma, elementarily

Bailey–Misiurewicz (2006): if every b-adic interval's orbit visit frequency
is eventually at most `C` times its length (one single constant `C`), then
`x` is normal in base `b`.  Their proof is ergodic (Vitali + Birkhoff);
mathlib has no pointwise ergodic theorem, so this file proves it by
elementary counting instead:

* Fix a target cell `[w/b^k, (w+1)/b^k)` and a large scale `K`.  Each orbit
  point `u j` sits in a unique scale-`K` cell `M j`; the `k`-subwords of the
  base-`b` expansion of `M j` (`subword`) predict the next `K - k` orbit
  points' scale-`k` cells (`subword_mem`), so the sliding-window count
  `occCount` of `w` in `M j` tallies target visits (`sum_occCount_orbit_*`).
* Among all `b^K` scale-`K` words, the second-moment (Chebyshev) bound
  `card_badSet_le` shows all but an `O(1/K)`-fraction are `ε`-*good*: their
  sliding count is within `ε` of the uniform value `(K-k+1)/b^k`.
* The hot-spot hypothesis applied at scale `K` makes the orbit's visits to
  the *bad* words eventually rare (`≤ C·|Bad|/b^K` per step), so almost all
  windows are good, and the target frequency is pinched at `1/b^k`
  (`tendsto_cell_of_visit_upper`).
* The b-adic sandwich (`equidistributed_of_badic`) and Wall's theorem
  finish (`isNormal_of_visit_upper_bound'`).

No measure theory, no character sums; the only analytic input is the
squeeze in `tendsto_cell_of_visit_upper`.
-/

namespace NormalNumbers

open Filter

/-! ### Counting scale-`K` words by their `k`-subwords -/

/-- The `k`-digit subword of the `K`-digit base-`b` word `m` starting at
(most-significant-first) position `i`: digits `i, …, i+k-1`. -/
def subword (b K k i m : ℕ) : ℕ := m / b ^ (K - i - k) % b ^ k

/-- The sliding-window count of the `k`-word `w` inside the `K`-word `m`. -/
def occCount (b K k w m : ℕ) : ℕ :=
  ((Finset.range (K - k + 1)).filter fun i => subword b K k i m = w).card

theorem occCount_le (b K k w m : ℕ) : occCount b K k w m ≤ K - k + 1 :=
  (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

/-- Quotient-remainder splitting of a divisibility-structured count:
`#{m < A·B : p (m / B)} = B · #{q < A : p q}`. -/
theorem card_filter_div (A B : ℕ) (hB : 0 < B) (p : ℕ → Prop) [DecidablePred p] :
    ((Finset.range (A * B)).filter fun m => p (m / B)).card
      = B * ((Finset.range A).filter p).card := by
  classical
  have key : ((Finset.range (A * B)).filter fun m => p (m / B)).card
      = (((Finset.range A).filter p) ×ˢ Finset.range B).card := by
    refine Finset.card_nbij' (fun m => (m / B, m % B)) (fun q => q.1 * B + q.2)
      ?_ ?_ ?_ ?_
    · intro m hm
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range,
        Finset.mem_product] at hm ⊢
      exact ⟨⟨Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hm.1), hm.2⟩,
        Nat.mod_lt _ hB⟩
    · intro q hq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range,
        Finset.mem_product] at hq ⊢
      obtain ⟨⟨h1, hp⟩, h2⟩ := hq
      have hdiv : (q.1 * B + q.2) / B = q.1 := by
        rw [mul_comm q.1 B, Nat.mul_add_div hB, Nat.div_eq_of_lt h2, add_zero]
      constructor
      · calc q.1 * B + q.2 < q.1 * B + B := by omega
          _ = (q.1 + 1) * B := by ring
          _ ≤ A * B := Nat.mul_le_mul_right B h1
      · rw [hdiv]; exact hp
    · intro m _
      show m / B * B + m % B = m
      rw [mul_comm (m / B) B, Nat.div_add_mod]
    · intro q hq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range,
        Finset.mem_product] at hq
      have hdiv : (q.1 * B + q.2) / B = q.1 := by
        rw [mul_comm q.1 B, Nat.mul_add_div hB, Nat.div_eq_of_lt hq.2, add_zero]
      have hmod : (q.1 * B + q.2) % B = q.2 := by
        rw [mul_comm q.1 B, Nat.mul_add_mod, Nat.mod_eq_of_lt hq.2]
      rw [Prod.ext_iff]
      exact ⟨hdiv, hmod⟩
  rw [key, Finset.card_product, Finset.card_range, mul_comm]

/-- `#{q < c·M : q % M = w} = c` for `w < M`. -/
theorem card_filter_mod (c M w : ℕ) (hw : w < M) :
    ((Finset.range (c * M)).filter fun q => q % M = w).card = c := by
  classical
  have hM : 0 < M := lt_of_le_of_lt (Nat.zero_le w) hw
  have key : ((Finset.range (c * M)).filter fun q => q % M = w).card
      = (Finset.range c).card := by
    refine Finset.card_nbij' (fun q => q / M) (fun t => t * M + w) ?_ ?_ ?_ ?_
    · intro q hq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hq ⊢
      exact Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hq.1)
    · intro t ht
      simp only [Finset.mem_coe, Finset.mem_range] at ht
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      constructor
      · calc t * M + w < t * M + M := by omega
          _ = (t + 1) * M := by ring
          _ ≤ c * M := Nat.mul_le_mul_right M ht
      · rw [mul_comm _ M, Nat.mul_add_mod, Nat.mod_eq_of_lt hw]
    · intro q hq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hq
      show q / M * M + w = q
      conv_rhs => rw [← Nat.div_add_mod q M]
      rw [hq.2, mul_comm (q / M) M]
    · intro t _
      show (t * M + w) / M = t
      rw [mul_comm t M, Nat.mul_add_div hM, Nat.div_eq_of_lt hw, add_zero]
  rw [key, Finset.card_range]

/-- Fixing the bottom `k` digits and a predicate on the rest:
`#{q < A·M : q % M = w ∧ p (q / M)} = #{r < A : p r}` for `w < M`. -/
theorem card_filter_mod_div (A M w : ℕ) (hw : w < M) (p : ℕ → Prop)
    [DecidablePred p] :
    ((Finset.range (A * M)).filter fun q => q % M = w ∧ p (q / M)).card
      = ((Finset.range A).filter p).card := by
  classical
  have hM : 0 < M := lt_of_le_of_lt (Nat.zero_le w) hw
  refine Finset.card_nbij' (fun q => q / M) (fun r => r * M + w) ?_ ?_ ?_ ?_
  · intro q hq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hq ⊢
    exact ⟨Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hq.1), hq.2.2⟩
  · intro r hr
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hr ⊢
    have hdiv : (r * M + w) / M = r := by
      rw [mul_comm r M, Nat.mul_add_div hM, Nat.div_eq_of_lt hw, add_zero]
    refine ⟨?_, ?_, ?_⟩
    · calc r * M + w < r * M + M := by omega
        _ = (r + 1) * M := by ring
        _ ≤ A * M := Nat.mul_le_mul_right M hr.1
    · rw [mul_comm _ M, Nat.mul_add_mod, Nat.mod_eq_of_lt hw]
    · rw [hdiv]; exact hr.2
  · intro q hq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hq
    show q / M * M + w = q
    conv_rhs => rw [← Nat.div_add_mod q M]
    rw [hq.2.1, mul_comm (q / M) M]
  · intro r _
    show (r * M + w) / M = r
    rw [mul_comm r M, Nat.mul_add_div hM, Nat.div_eq_of_lt hw, add_zero]

/-- Single-subword count: `#{m < b^K : subword i m = w} = b^(K-k)`. -/
theorem card_filter_subword (b K k i w : ℕ) (hb : 0 < b) (hw : w < b ^ k)
    (hik : i + k ≤ K) :
    ((Finset.range (b ^ K)).filter fun m => m / b ^ (K - i - k) % b ^ k = w).card
      = b ^ (K - k) := by
  classical
  have hs : K - i - k + k ≤ K := by omega
  set s := K - i - k with hs_def
  have hsplit : b ^ K = b ^ (K - s) * b ^ s := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit, card_filter_div _ _ (pow_pos hb _)
    (fun q => q % b ^ k = w)]
  have hsplit2 : b ^ (K - s) = b ^ (K - s - k) * b ^ k := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit2, card_filter_mod _ _ _ hw]
  rw [← pow_add]; congr 1; omega

/-- Disjoint-pair subword count: for `i + k ≤ i'` and `i' + k ≤ K`,
`#{m < b^K : subword i m = w ∧ subword i' m = w} = b^(K-2k)`. -/
theorem card_filter_subword_pair (b K k i i' w : ℕ) (hb : 0 < b)
    (hw : w < b ^ k) (hii : i + k ≤ i') (hik : i' + k ≤ K) :
    ((Finset.range (b ^ K)).filter fun m =>
      m / b ^ (K - i - k) % b ^ k = w ∧ m / b ^ (K - i' - k) % b ^ k = w).card
      = b ^ (K - 2 * k) := by
  classical
  -- positions from the bottom: t = K - i' - k  <  s = K - i - k, with t + k ≤ s
  set s := K - i - k with hs_def
  set t := K - i' - k with ht_def
  have hts : t + k ≤ s := by omega
  have hsK : s + k ≤ K := by omega
  -- split off the bottom t digits
  have hsplit : b ^ K = b ^ (K - t) * b ^ t := by rw [← pow_add]; congr 1; omega
  have hstep : ∀ m : ℕ, m / b ^ s = m / b ^ t / b ^ (s - t) := by
    intro m
    rw [Nat.div_div_eq_div_mul, ← pow_add]
    congr 2
    omega
  have hcongr : ((Finset.range (b ^ K)).filter fun m =>
        m / b ^ s % b ^ k = w ∧ m / b ^ t % b ^ k = w).card
      = ((Finset.range (b ^ (K - t) * b ^ t)).filter fun m =>
          (fun q => q % b ^ k = w ∧ (q / b ^ k) / b ^ (s - t - k) % b ^ k = w)
            (m / b ^ t)).card := by
    rw [← hsplit]
    congr 1
    apply Finset.filter_congr
    intro m _
    simp only [hstep m, eq_iff_iff]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h2, ?_⟩
      rw [Nat.div_div_eq_div_mul, ← pow_add]
      rw [show k + (s - t - k) = s - t by omega]
      exact h1
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h1⟩
      rw [Nat.div_div_eq_div_mul, ← pow_add] at h2
      rw [show k + (s - t - k) = s - t by omega] at h2
      exact h2
  have hdiv := card_filter_div (b ^ (K - t)) (b ^ t) (pow_pos hb _)
    (fun q => q % b ^ k = w ∧ (q / b ^ k) / b ^ (s - t - k) % b ^ k = w)
  have hmoddiv := card_filter_mod_div (b ^ (K - t - k)) (b ^ k) w hw
    (fun r => r / b ^ (s - t - k) % b ^ k = w)
  have hsplit2 : b ^ (K - t) = b ^ (K - t - k) * b ^ k := by
    rw [← pow_add]; congr 1; omega
  have hfin : ((Finset.range (b ^ (K - t - k))).filter
      fun r => r / b ^ (s - t - k) % b ^ k = w).card = b ^ (K - t - k - k) := by
    have h1 : s - t - k = (K - t - k) - i - k := by omega
    rw [h1]
    exact card_filter_subword b (K - t - k) k i w hb hw (by omega)
  rw [← hsplit2] at hmoddiv
  rw [hmoddiv, hfin] at hdiv
  rw [hcongr]
  refine hdiv.trans ?_
  rw [← pow_add]
  congr 1
  omega

/-! ### Moment bounds -/

/-- First moment: summed over all `b^K` scale-`K` words, the sliding count of
any fixed `k`-word `w` is exactly uniform. -/
theorem sum_occCount (b K k w : ℕ) (hb : 0 < b) (hw : w < b ^ k) (hk : k ≤ K) :
    ∑ m ∈ Finset.range (b ^ K), occCount b K k w m
      = (K - k + 1) * b ^ (K - k) := by
  classical
  have hinner : ∀ i ∈ Finset.range (K - k + 1),
      ((Finset.range (b ^ K)).filter
        fun m => m / b ^ (K - i - k) % b ^ k = w).card = b ^ (K - k) := by
    intro i hi
    simp only [Finset.mem_range] at hi
    exact card_filter_subword b K k i w hb hw (by omega)
  unfold occCount subword
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  calc ∑ i ∈ Finset.range (K - k + 1), ∑ m ∈ Finset.range (b ^ K),
        (if m / b ^ (K - i - k) % b ^ k = w then 1 else 0)
      = ∑ i ∈ Finset.range (K - k + 1), b ^ (K - k) :=
        Finset.sum_congr rfl fun i hi => by
          rw [← Finset.card_filter]; exact hinner i hi
    _ = (K - k + 1) * b ^ (K - k) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- Second moment bound (the Chebyshev numerator): the summed squared
sliding count is at most `N²·b^(K-2k) + 2k·N·b^(K-k)` with `N = K-k+1`. -/
theorem sum_occCount_sq_le (b K k w : ℕ) (hb : 0 < b) (hw : w < b ^ k)
    (hk : 2 * k ≤ K) (hk1 : 1 ≤ k) :
    ∑ m ∈ Finset.range (b ^ K), occCount b K k w m ^ 2
      ≤ (K - k + 1) ^ 2 * b ^ (K - 2 * k)
        + 2 * k * (K - k + 1) * b ^ (K - k) := by
  classical
  set N := K - k + 1 with hN
  -- expand the square into a double sum over offset pairs
  have hexp : ∀ m, occCount b K k w m ^ 2
      = ∑ i ∈ Finset.range N, ∑ i' ∈ Finset.range N,
          (if m / b ^ (K - i - k) % b ^ k = w
              ∧ m / b ^ (K - i' - k) % b ^ k = w then 1 else 0) := by
    intro m
    have h1 : occCount b K k w m = ∑ i ∈ Finset.range N,
        (if m / b ^ (K - i - k) % b ^ k = w then 1 else 0) := by
      unfold occCount subword
      rw [Finset.card_filter]
    rw [sq, h1, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
    by_cases hA : m / b ^ (K - i - k) % b ^ k = w <;>
      by_cases hB : m / b ^ (K - i' - k) % b ^ k = w <;>
      simp [hA, hB]
  -- swap sums: for each pair, the count of words satisfying both conditions
  have hswap : ∑ m ∈ Finset.range (b ^ K), occCount b K k w m ^ 2
      = ∑ i ∈ Finset.range N, ∑ i' ∈ Finset.range N,
          ((Finset.range (b ^ K)).filter fun m =>
            m / b ^ (K - i - k) % b ^ k = w
              ∧ m / b ^ (K - i' - k) % b ^ k = w).card := by
    simp_rw [hexp]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [Finset.card_filter]
  rw [hswap]
  -- bound each pair: far pairs contribute b^(K-2k), near pairs ≤ b^(K-k)
  have hsingle : ∀ i i' : ℕ, i < N →
      ((Finset.range (b ^ K)).filter fun m =>
        m / b ^ (K - i - k) % b ^ k = w
          ∧ m / b ^ (K - i' - k) % b ^ k = w).card ≤ b ^ (K - k) := by
    intro i i' hi
    calc ((Finset.range (b ^ K)).filter fun m =>
          m / b ^ (K - i - k) % b ^ k = w
            ∧ m / b ^ (K - i' - k) % b ^ k = w).card
        ≤ ((Finset.range (b ^ K)).filter fun m =>
            m / b ^ (K - i - k) % b ^ k = w).card :=
          Finset.card_le_card (Finset.monotone_filter_right _
            fun m _ hm => hm.1)
      _ = b ^ (K - k) := card_filter_subword b K k i w hb hw (by omega)
  have hfar : ∀ i i' : ℕ, i' < N → i + k ≤ i' →
      ((Finset.range (b ^ K)).filter fun m =>
        m / b ^ (K - i - k) % b ^ k = w
          ∧ m / b ^ (K - i' - k) % b ^ k = w).card = b ^ (K - 2 * k) :=
    fun i i' hi' hii => card_filter_subword_pair b K k i i' w hb hw hii
      (by omega)
  have hfar' : ∀ i i' : ℕ, i < N → i' + k ≤ i →
      ((Finset.range (b ^ K)).filter fun m =>
        m / b ^ (K - i - k) % b ^ k = w
          ∧ m / b ^ (K - i' - k) % b ^ k = w).card = b ^ (K - 2 * k) := by
    intro i i' hi hii
    rw [show ((Finset.range (b ^ K)).filter fun m =>
        m / b ^ (K - i - k) % b ^ k = w
          ∧ m / b ^ (K - i' - k) % b ^ k = w)
      = ((Finset.range (b ^ K)).filter fun m =>
        m / b ^ (K - i' - k) % b ^ k = w
          ∧ m / b ^ (K - i - k) % b ^ k = w) from
      Finset.filter_congr fun m _ => and_comm]
    exact card_filter_subword_pair b K k i' i w hb hw hii (by omega)
  -- pointwise bound by an if-expression, then sum the two classes
  have hbound : ∑ i ∈ Finset.range N, ∑ i' ∈ Finset.range N,
      ((Finset.range (b ^ K)).filter fun m =>
        m / b ^ (K - i - k) % b ^ k = w
          ∧ m / b ^ (K - i' - k) % b ^ k = w).card
      ≤ ∑ i ∈ Finset.range N, ∑ i' ∈ Finset.range N,
          (if i + k ≤ i' ∨ i' + k ≤ i then b ^ (K - 2 * k)
            else b ^ (K - k)) := by
    refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun i' hi' => ?_
    simp only [Finset.mem_range] at hi hi'
    by_cases hcase : i + k ≤ i' ∨ i' + k ≤ i
    · rcases hcase with h | h
      · rw [hfar i i' hi' h, if_pos (Or.inl h)]
      · rw [hfar' i i' hi h, if_pos (Or.inr h)]
    · rw [if_neg hcase]
      exact hsingle i i' hi
  refine hbound.trans ?_
  -- split: far terms ≤ N² · b^(K-2k); near terms ≤ 2k·N · b^(K-k)
  have hsplit : ∀ i ∈ Finset.range N,
      ∑ i' ∈ Finset.range N,
        (if i + k ≤ i' ∨ i' + k ≤ i then b ^ (K - 2 * k) else b ^ (K - k))
      ≤ N * b ^ (K - 2 * k) + 2 * k * b ^ (K - k) := by
    intro i _
    have hle : ∀ i' ∈ Finset.range N,
        (if i + k ≤ i' ∨ i' + k ≤ i then b ^ (K - 2 * k) else b ^ (K - k))
        ≤ b ^ (K - 2 * k)
          + (if i + k ≤ i' ∨ i' + k ≤ i then 0 else b ^ (K - k)) := by
      intro i' _
      by_cases hcase : i + k ≤ i' ∨ i' + k ≤ i <;> simp [hcase]
    refine (Finset.sum_le_sum hle).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      smul_eq_mul]
    gcongr
    -- near count: #{i' : ¬far} ≤ 2k
    have hnear : ((Finset.range N).filter
        fun i' => ¬(i + k ≤ i' ∨ i' + k ≤ i)).card ≤ 2 * k := by
      have hsub : ((Finset.range N).filter
          fun i' => ¬(i + k ≤ i' ∨ i' + k ≤ i))
          ⊆ Finset.Ico (i + 1 - k) (i + k) := by
        intro i' hi'
        simp only [Finset.mem_filter, Finset.mem_range, not_or, not_le] at hi'
        simp only [Finset.mem_Ico]
        omega
      calc ((Finset.range N).filter
            fun i' => ¬(i + k ≤ i' ∨ i' + k ≤ i)).card
          ≤ (Finset.Ico (i + 1 - k) (i + k)).card := Finset.card_le_card hsub
        _ = i + k - (i + 1 - k) := Nat.card_Ico _ _
        _ ≤ 2 * k := by omega
    calc ∑ i' ∈ Finset.range N,
          (if i + k ≤ i' ∨ i' + k ≤ i then 0 else b ^ (K - k))
        = ((Finset.range N).filter
            fun i' => ¬(i + k ≤ i' ∨ i' + k ≤ i)).card * b ^ (K - k) := by
          rw [Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const,
            smul_eq_mul, zero_add]
      _ ≤ 2 * k * b ^ (K - k) :=
          Nat.mul_le_mul_right _ hnear
  calc ∑ i ∈ Finset.range N, ∑ i' ∈ Finset.range N,
        (if i + k ≤ i' ∨ i' + k ≤ i then b ^ (K - 2 * k) else b ^ (K - k))
      ≤ ∑ _i ∈ Finset.range N,
          (N * b ^ (K - 2 * k) + 2 * k * b ^ (K - k)) :=
        Finset.sum_le_sum hsplit
    _ = N ^ 2 * b ^ (K - 2 * k) + 2 * k * N * b ^ (K - k) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
        ring

/-! ### The bad set and its size -/

/-- Scale-`K` words whose sliding count of `w` deviates from uniform by at
least `T` (measured as `|b^k·occ - N| ≥ T` with `N = K-k+1`). -/
noncomputable def badSet (b K k w T : ℕ) : Finset ℕ :=
  (Finset.range (b ^ K)).filter fun m =>
    (T : ℤ) ≤ |(b ^ k * occCount b K k w m : ℤ) - (K - k + 1 : ℕ)|

/-- Chebyshev: `T² · |Bad| ≤ 2k·N·b^(K+k)`. -/
theorem card_badSet_le (b K k w T : ℕ) (hb : 0 < b) (hw : w < b ^ k)
    (hk : 2 * k ≤ K) (hk1 : 1 ≤ k) :
    T ^ 2 * (badSet b K k w T).card ≤ 2 * k * (K - k + 1) * b ^ (K + k) := by
  classical
  set N := K - k + 1 with hN
  set f : ℕ → ℤ := fun m => (b : ℤ) ^ k * occCount b K k w m - N with hf
  -- total second moment of the deviation
  have hS1 : ((∑ m ∈ Finset.range (b ^ K), occCount b K k w m : ℕ) : ℤ)
      = (N : ℤ) * (b : ℤ) ^ (K - k) := by
    rw [sum_occCount b K k w hb hw (by omega)]; push_cast [hN]; ring
  have hS2 : ((∑ m ∈ Finset.range (b ^ K), occCount b K k w m ^ 2 : ℕ) : ℤ)
      ≤ (N : ℤ) ^ 2 * (b : ℤ) ^ (K - 2 * k)
        + 2 * k * N * (b : ℤ) ^ (K - k) := by
    have := sum_occCount_sq_le b K k w hb hw hk hk1
    calc ((∑ m ∈ Finset.range (b ^ K), occCount b K k w m ^ 2 : ℕ) : ℤ)
        ≤ ((N ^ 2 * b ^ (K - 2 * k) + 2 * k * N * b ^ (K - k) : ℕ) : ℤ) := by
          exact_mod_cast this
      _ = (N : ℤ) ^ 2 * (b : ℤ) ^ (K - 2 * k)
            + 2 * k * N * (b : ℤ) ^ (K - k) := by push_cast; ring
  have hsum : ∑ m ∈ Finset.range (b ^ K), f m ^ 2
      = ((b : ℤ) ^ k) ^ 2
          * ((∑ m ∈ Finset.range (b ^ K), occCount b K k w m ^ 2 : ℕ) : ℤ)
        - 2 * N * (b : ℤ) ^ k
            * ((∑ m ∈ Finset.range (b ^ K), occCount b K k w m : ℕ) : ℤ)
        + (N : ℤ) ^ 2 * ((b ^ K : ℕ) : ℤ) := by
    have hpt : ∀ m, f m ^ 2
        = ((b : ℤ) ^ k) ^ 2 * (occCount b K k w m : ℤ) ^ 2
          - 2 * N * (b : ℤ) ^ k * (occCount b K k w m : ℤ) + (N : ℤ) ^ 2 := by
      intro m
      simp only [hf]
      ring
    simp_rw [hpt]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  have hcast : ((b ^ K : ℕ) : ℤ) = (b : ℤ) ^ K := by push_cast; ring
  have hpow1 : ((b : ℤ) ^ k) ^ 2 * (b : ℤ) ^ (K - 2 * k) = (b : ℤ) ^ K := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  have hpow2 : ((b : ℤ) ^ k) ^ 2 * (b : ℤ) ^ (K - k) = (b : ℤ) ^ (K + k) := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  have hpow3 : (b : ℤ) ^ k * (b : ℤ) ^ (K - k) = (b : ℤ) ^ K := by
    rw [← pow_add]; congr 1; omega
  have hbk2 : (0 : ℤ) ≤ ((b : ℤ) ^ k) ^ 2 := by positivity
  have htotal : ∑ m ∈ Finset.range (b ^ K), f m ^ 2
      ≤ 2 * k * N * (b : ℤ) ^ (K + k) := by
    rw [hsum, hS1, hcast]
    have hmul := mul_le_mul_of_nonneg_left hS2 hbk2
    have hdist : ((b : ℤ) ^ k) ^ 2
        * ((N : ℤ) ^ 2 * (b : ℤ) ^ (K - 2 * k)
            + 2 * k * N * (b : ℤ) ^ (K - k))
        = (N : ℤ) ^ 2 * (b : ℤ) ^ K + 2 * k * N * (b : ℤ) ^ (K + k) := by
      linear_combination (N : ℤ) ^ 2 * hpow1 + 2 * (k : ℤ) * (N : ℤ) * hpow2
    have hB : 2 * (N : ℤ) * (b : ℤ) ^ k * ((N : ℤ) * (b : ℤ) ^ (K - k))
        = 2 * (N : ℤ) ^ 2 * (b : ℤ) ^ K := by
      linear_combination 2 * (N : ℤ) ^ 2 * hpow3
    linarith [hmul, hdist, hB]
  -- Chebyshev: every bad word contributes at least T² to the second moment
  have hcheb : (T : ℤ) ^ 2 * ((badSet b K k w T).card : ℤ)
      ≤ ∑ m ∈ Finset.range (b ^ K), f m ^ 2 := by
    have h1 : ∀ m ∈ badSet b K k w T, (T : ℤ) ^ 2 ≤ f m ^ 2 := by
      intro m hm
      have hmem := Finset.mem_filter.mp hm
      have habs : (T : ℤ) ≤ |f m| := hmem.2
      calc (T : ℤ) ^ 2 ≤ |f m| ^ 2 := by
            rw [sq, sq]
            exact mul_self_le_mul_self (Int.natCast_nonneg T) habs
        _ = f m ^ 2 := sq_abs _
    calc (T : ℤ) ^ 2 * ((badSet b K k w T).card : ℤ)
        = ∑ _m ∈ badSet b K k w T, (T : ℤ) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ m ∈ badSet b K k w T, f m ^ 2 := Finset.sum_le_sum h1
      _ ≤ ∑ m ∈ Finset.range (b ^ K), f m ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun m _ _ => sq_nonneg _
  have hfin : (T : ℤ) ^ 2 * ((badSet b K k w T).card : ℤ)
      ≤ 2 * k * N * (b : ℤ) ^ (K + k) := hcheb.trans htotal
  exact_mod_cast hfin

end NormalNumbers
