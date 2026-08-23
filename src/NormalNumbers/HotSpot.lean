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

/-! ### Orbit points and b-adic cells -/

/-- Membership in the scale-`k` cell `[w/b^k, (w+1)/b^k)` is exactly
`⌊y·b^k⌋₊ = w` (for `y ≥ 0`, `b > 0`). -/
theorem mem_cell_iff_floor (b k w : ℕ) (hb : 0 < b) {y : ℝ} (hy : 0 ≤ y) :
    y ∈ Set.Ico ((w : ℝ) / (b : ℝ) ^ k) ((w + 1 : ℝ) / (b : ℝ) ^ k)
      ↔ ⌊y * (b : ℝ) ^ k⌋₊ = w := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hbk : (0 : ℝ) < (b : ℝ) ^ k := by positivity
  rw [Set.mem_Ico, Nat.floor_eq_iff (mul_nonneg hy hbk.le)]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(div_le_iff₀ hbk).mp h1, ?_⟩
    rw [lt_div_iff₀ hbk] at h2
    linarith
  · rintro ⟨h1, h2⟩
    exact ⟨(div_le_iff₀ hbk).mpr h1, (lt_div_iff₀ hbk).mpr (by linarith)⟩

/-- The orbit advances by iterating `y ↦ {b·y}`. -/
theorem orbit_add (b : ℕ) (x : ℝ) (j i : ℕ) :
    orbit b x (j + i) = Int.fract (orbit b x j * (b : ℝ) ^ i) := by
  unfold orbit
  have h : Int.fract (x * (b : ℝ) ^ j) * (b : ℝ) ^ i
      = x * (b : ℝ) ^ (j + i) - ((⌊x * (b : ℝ) ^ j⌋ * (b ^ i : ℤ) : ℤ) : ℝ) := by
    rw [Int.fract]
    push_cast
    ring
  rw [h, Int.fract_sub_intCast]

/-- The index of the scale-`K` cell containing the `j`-th orbit point. -/
noncomputable def cellAt (b : ℕ) (x : ℝ) (K j : ℕ) : ℕ :=
  ⌊orbit b x j * (b : ℝ) ^ K⌋₊

theorem cellAt_lt (b : ℕ) (hb : 0 < b) (x : ℝ) (K j : ℕ) :
    cellAt b x K j < b ^ K := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hbk : (0 : ℝ) < (b : ℝ) ^ K := by positivity
  have h1 : orbit b x j < 1 := Int.fract_lt_one _
  have h0 : 0 ≤ orbit b x j := Int.fract_nonneg _
  unfold cellAt
  rw [Nat.floor_lt (mul_nonneg h0 hbk.le)]
  calc orbit b x j * (b : ℝ) ^ K < 1 * (b : ℝ) ^ K := by
        exact mul_lt_mul_of_pos_right h1 hbk
    _ = ((b ^ K : ℕ) : ℝ) := by push_cast; ring

theorem orbit_mem_cellAt (b : ℕ) (hb : 0 < b) (x : ℝ) (K j : ℕ) :
    orbit b x j ∈ Set.Ico ((cellAt b x K j : ℝ) / (b : ℝ) ^ K)
      ((cellAt b x K j + 1 : ℝ) / (b : ℝ) ^ K) :=
  (mem_cell_iff_floor b K (cellAt b x K j) hb (Int.fract_nonneg _)).mpr rfl

/-- **Subword localization**: the scale-`k` cell of the orbit point `i`
steps later is read off the `K`-digit expansion of the current scale-`K`
cell index (as long as the lookahead stays inside the window:
`i + k ≤ K`). -/
theorem subword_cellAt (b : ℕ) (hb : 0 < b) (x : ℝ) (K k i j : ℕ)
    (hik : i + k ≤ K) :
    subword b K k i (cellAt b x K j) = ⌊orbit b x (j + i) * (b : ℝ) ^ k⌋₊ := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  set m := cellAt b x K j with hm_def
  set y := orbit b x j with hy_def
  have hy0 : 0 ≤ y := Int.fract_nonneg _
  have hycell := orbit_mem_cellAt b hb x K j
  rw [← hm_def, ← hy_def] at hycell
  -- decompose the cell index at the split point K - i
  set a := m / b ^ (K - i) with ha_def
  set r := m % b ^ (K - i) with hr_def
  have hBpos : (0 : ℕ) < b ^ (K - i) := pow_pos hb _
  have hr_lt : r < b ^ (K - i) := Nat.mod_lt _ hBpos
  have hm_eq : m = a * b ^ (K - i) + r := by
    rw [ha_def, hr_def, mul_comm]
    exact (Nat.div_add_mod m (b ^ (K - i))).symm
  -- real-arithmetic: y·bⁱ − a lies in the r-cell at scale K−i
  have hpowKi : (b : ℝ) ^ K = (b : ℝ) ^ (K - i) * (b : ℝ) ^ i := by
    rw [← pow_add]; congr 1; omega
  have hbKi : (0 : ℝ) < (b : ℝ) ^ (K - i) := by positivity
  have hbi : (0 : ℝ) < (b : ℝ) ^ i := by positivity
  have h1 : (a : ℝ) + (r : ℝ) / (b : ℝ) ^ (K - i) ≤ y * (b : ℝ) ^ i := by
    have := hycell.1
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (b : ℝ) ^ K)] at this
    have hcast : (m : ℝ) = a * (b : ℝ) ^ (K - i) + r := by
      rw [hm_eq]; push_cast; ring
    rw [hcast, hpowKi] at this
    rw [← sub_nonneg]
    have hexp : y * (b : ℝ) ^ i - ((a : ℝ) + (r : ℝ) / (b : ℝ) ^ (K - i))
        = (y * ((b : ℝ) ^ (K - i) * (b : ℝ) ^ i)
            - ((a : ℝ) * (b : ℝ) ^ (K - i) + (r : ℝ)))
          / (b : ℝ) ^ (K - i) := by
      field_simp
      try ring
    rw [hexp]
    exact div_nonneg (by linarith) hbKi.le
  have h2 : y * (b : ℝ) ^ i < (a : ℝ) + ((r : ℝ) + 1) / (b : ℝ) ^ (K - i) := by
    have := hycell.2
    rw [lt_div_iff₀ (by positivity : (0:ℝ) < (b : ℝ) ^ K)] at this
    have hcast : (m : ℝ) + 1 = a * (b : ℝ) ^ (K - i) + ((r : ℝ) + 1) := by
      rw [hm_eq]; push_cast; ring
    rw [hcast, hpowKi] at this
    rw [← sub_neg]
    have hexp : y * (b : ℝ) ^ i - ((a : ℝ) + ((r : ℝ) + 1) / (b : ℝ) ^ (K - i))
        = (y * ((b : ℝ) ^ (K - i) * (b : ℝ) ^ i)
            - ((a : ℝ) * (b : ℝ) ^ (K - i) + ((r : ℝ) + 1)))
          / (b : ℝ) ^ (K - i) := by
      field_simp
      try ring
    rw [hexp]
    exact div_neg_of_neg_of_pos (by linarith) hbKi
  -- hence the fractional part is exactly y·bⁱ − a
  have hfrac : Int.fract (y * (b : ℝ) ^ i) = y * (b : ℝ) ^ i - a := by
    have hmem : y * (b : ℝ) ^ i - a ∈ Set.Ico (0 : ℝ) 1 := by
      constructor
      · have : (0 : ℝ) ≤ (r : ℝ) / (b : ℝ) ^ (K - i) := by positivity
        linarith
      · have hr1 : ((r : ℝ) + 1) / (b : ℝ) ^ (K - i) ≤ 1 := by
          rw [div_le_one hbKi]
          have : (r : ℕ) + 1 ≤ b ^ (K - i) := hr_lt
          exact_mod_cast this
        linarith
    have hsub : Int.fract (y * (b : ℝ) ^ i - ((a : ℤ) : ℝ))
        = Int.fract (y * (b : ℝ) ^ i) := Int.fract_sub_intCast _ _
    have : Int.fract (y * (b : ℝ) ^ i - ((a : ℤ) : ℝ))
        = y * (b : ℝ) ^ i - a := by
      rw [Int.fract_eq_self.mpr (by push_cast at hmem ⊢; exact hmem)]
      push_cast
      ring
    rw [← hsub, this]
  -- the shifted orbit point sits in the subword's scale-k cell
  set w' := r / b ^ (K - i - k) with hw'_def
  have hw'_lt : w' < b ^ k := by
    rw [hw'_def]
    have hsplit : b ^ (K - i) = b ^ (K - i - k) * b ^ k := by
      rw [← pow_add]; congr 1; omega
    rw [Nat.div_lt_iff_lt_mul (pow_pos hb _)]
    calc r < b ^ (K - i) := hr_lt
      _ = b ^ k * b ^ (K - i - k) := by rw [← pow_add]; congr 1; omega
  have hr_lb : w' * b ^ (K - i - k) ≤ r := Nat.div_mul_le_self r _
  have hr_ub : r + 1 ≤ (w' + 1) * b ^ (K - i - k) := by
    have h1 : b ^ (K - i - k) * w' + r % b ^ (K - i - k) = r := by
      rw [hw'_def]
      exact Nat.div_add_mod r (b ^ (K - i - k))
    have h2 : r % b ^ (K - i - k) < b ^ (K - i - k) :=
      Nat.mod_lt _ (pow_pos hb _)
    have h3 : (w' + 1) * b ^ (K - i - k)
        = b ^ (K - i - k) * w' + b ^ (K - i - k) := by ring
    linarith
  have horbit : orbit b x (j + i) ∈ Set.Ico ((w' : ℝ) / (b : ℝ) ^ k)
      ((w' + 1 : ℝ) / (b : ℝ) ^ k) := by
    rw [orbit_add, ← hy_def, hfrac]
    have hbik : (0 : ℝ) < (b : ℝ) ^ (K - i - k) := by positivity
    have hsplitR : (b : ℝ) ^ (K - i) = (b : ℝ) ^ k * (b : ℝ) ^ (K - i - k) := by
      rw [← pow_add]; congr 1; omega
    constructor
    · calc (w' : ℝ) / (b : ℝ) ^ k
          = ((w' : ℝ) * (b : ℝ) ^ (K - i - k)) / (b : ℝ) ^ (K - i) := by
            rw [hsplitR]; field_simp; try ring
        _ ≤ (r : ℝ) / (b : ℝ) ^ (K - i) := by
            apply div_le_div_of_nonneg_right _ hbKi.le
            exact_mod_cast hr_lb
        _ ≤ y * (b : ℝ) ^ i - a := by linarith
    · calc y * (b : ℝ) ^ i - a
          < ((r : ℝ) + 1) / (b : ℝ) ^ (K - i) := by linarith
        _ ≤ (((w' : ℝ) + 1) * (b : ℝ) ^ (K - i - k)) / (b : ℝ) ^ (K - i) := by
            apply div_le_div_of_nonneg_right _ hbKi.le
            exact_mod_cast hr_ub
        _ = ((w' : ℝ) + 1) / (b : ℝ) ^ k := by
            rw [hsplitR]; field_simp; try ring
  have hnn : (0 : ℝ) ≤ orbit b x (j + i) := Int.fract_nonneg _
  have hfloor := (mem_cell_iff_floor b k w' hb hnn).mp horbit
  rw [hfloor, hw'_def, hr_def]
  -- finally, w' is the subword of m
  unfold subword
  have hsplit : b ^ (K - i) = b ^ (K - i - k) * b ^ k := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit, Nat.mod_mul_right_div_self]

/-! ### The sliding double count -/

/-- The sliding count inside the current scale-`K` cell tallies the next
`K - k + 1` orbit points' scale-`k` cells. -/
theorem occCount_cellAt (b : ℕ) (hb : 0 < b) (x : ℝ) (K k w j : ℕ)
    (hkK : k ≤ K) :
    occCount b K k w (cellAt b x K j)
      = ((Finset.range (K - k + 1)).filter
          fun i => ⌊orbit b x (j + i) * (b : ℝ) ^ k⌋₊ = w).card := by
  unfold occCount
  congr 1
  apply Finset.filter_congr
  intro i hi
  simp only [Finset.mem_range] at hi
  rw [subword_cellAt b hb x K k i j (by omega)]

/-- Visits to the scale-`k` cell of `w` are floor matches. -/
theorem visitCount_eq_card_floor (b : ℕ) (hb : 0 < b) (x : ℝ) (k w n : ℕ) :
    visitCount (orbit b x) ((w : ℝ) / (b : ℝ) ^ k) ((w + 1 : ℝ) / (b : ℝ) ^ k) n
      = ((Finset.range n).filter
          fun t => ⌊orbit b x t * (b : ℝ) ^ k⌋₊ = w).card := by
  classical
  unfold visitCount
  congr 1
  apply Finset.filter_congr
  intro t _
  exact mem_cell_iff_floor b k w hb (Int.fract_nonneg _)

/-- Summed sliding counts along the orbit are the pair count of hits. -/
theorem sum_occCount_cellAt_eq (b : ℕ) (hb : 0 < b) (x : ℝ) (K k w n : ℕ)
    (hkK : k ≤ K) :
    ∑ j ∈ Finset.range n, occCount b K k w (cellAt b x K j)
      = ((Finset.range n ×ˢ Finset.range (K - k + 1)).filter
          fun p => ⌊orbit b x (p.1 + p.2) * (b : ℝ) ^ k⌋₊ = w).card := by
  classical
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [occCount_cellAt b hb x K k w j hkK, Finset.card_filter]

/-- Sliding upper bound: pair hits inject into (hit time, offset). -/
theorem sum_occCount_cellAt_le (b : ℕ) (hb : 0 < b) (x : ℝ) (K k w n : ℕ)
    (hkK : k ≤ K) :
    ∑ j ∈ Finset.range n, occCount b K k w (cellAt b x K j)
      ≤ ((Finset.range (n + (K - k))).filter
            fun t => ⌊orbit b x t * (b : ℝ) ^ k⌋₊ = w).card
          * (K - k + 1) := by
  classical
  rw [sum_occCount_cellAt_eq b hb x K k w n hkK]
  have hcp : (((Finset.range (n + (K - k))).filter
        fun t => ⌊orbit b x t * (b : ℝ) ^ k⌋₊ = w)
          ×ˢ Finset.range (K - k + 1)).card
      = ((Finset.range (n + (K - k))).filter
          fun t => ⌊orbit b x t * (b : ℝ) ^ k⌋₊ = w).card * (K - k + 1) := by
    rw [Finset.card_product, Finset.card_range]
  rw [← hcp]
  apply Finset.card_le_card_of_injOn
    (fun p : ℕ × ℕ => (p.1 + p.2, p.2))
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range] at hp ⊢
    exact ⟨⟨by omega, hp.2⟩, hp.1.2⟩
  · intro p hp q hq heq
    simp only [Prod.mk.injEq] at heq
    have : p.1 = q.1 := by omega
    exact Prod.ext this heq.2

/-- Sliding lower bound: every hit at time `≥ K - k` owns all
`K - k + 1` offsets. -/
theorem le_sum_occCount_cellAt (b : ℕ) (hb : 0 < b) (x : ℝ) (K k w n : ℕ)
    (hkK : k ≤ K) :
    ((Finset.Ico (K - k) n).filter
        fun t => ⌊orbit b x t * (b : ℝ) ^ k⌋₊ = w).card * (K - k + 1)
      ≤ ∑ j ∈ Finset.range n, occCount b K k w (cellAt b x K j) := by
  classical
  rw [sum_occCount_cellAt_eq b hb x K k w n hkK]
  have hcp : (((Finset.Ico (K - k) n).filter
        fun t => ⌊orbit b x t * (b : ℝ) ^ k⌋₊ = w)
          ×ˢ Finset.range (K - k + 1)).card
      = ((Finset.Ico (K - k) n).filter
          fun t => ⌊orbit b x t * (b : ℝ) ^ k⌋₊ = w).card * (K - k + 1) := by
    rw [Finset.card_product, Finset.card_range]
  rw [← hcp]
  apply Finset.card_le_card_of_injOn
    (fun p : ℕ × ℕ => (p.1 - p.2, p.2))
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Ico, Finset.mem_range] at hp ⊢
    obtain ⟨⟨⟨h1, h2⟩, hQ⟩, h3⟩ := hp
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [show p.1 - p.2 + p.2 = p.1 by omega]
    exact hQ
  · intro p hp q hq heq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Ico, Finset.mem_range] at hp hq
    simp only [Prod.mk.injEq] at heq
    have : p.1 = q.1 := by omega
    exact Prod.ext this heq.2

/-- Truncating the count range costs at most the truncation length. -/
theorem card_filter_range_le_add (Q : ℕ → Prop) [DecidablePred Q] (n c : ℕ) :
    ((Finset.range (n + c)).filter Q).card
      ≤ ((Finset.range n).filter Q).card + c := by
  classical
  have hsub : (Finset.range (n + c)).filter Q
      ⊆ (Finset.range n).filter Q ∪ Finset.Ico n (n + c) := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union,
      Finset.mem_Ico] at ht ⊢
    rcases lt_or_ge t n with h | h
    · exact Or.inl ⟨h, ht.2⟩
    · exact Or.inr ⟨h, ht.1⟩
  calc ((Finset.range (n + c)).filter Q).card
      ≤ ((Finset.range n).filter Q ∪ Finset.Ico n (n + c)).card :=
        Finset.card_le_card hsub
    _ ≤ ((Finset.range n).filter Q).card + (Finset.Ico n (n + c)).card :=
        Finset.card_union_le _ _
    _ = ((Finset.range n).filter Q).card + c := by rw [Nat.card_Ico]; omega

/-- Dually, the head of the range holds at most `c` of the count. -/
theorem card_filter_range_le_Ico_add (Q : ℕ → Prop) [DecidablePred Q] (n c : ℕ) :
    ((Finset.range n).filter Q).card
      ≤ ((Finset.Ico c n).filter Q).card + c := by
  classical
  have hsub : (Finset.range n).filter Q
      ⊆ (Finset.Ico c n).filter Q ∪ Finset.range c := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union,
      Finset.mem_Ico] at ht ⊢
    rcases lt_or_ge t c with h | h
    · exact Or.inr h
    · exact Or.inl ⟨⟨h, ht.1⟩, ht.2⟩
  calc ((Finset.range n).filter Q).card
      ≤ ((Finset.Ico c n).filter Q ∪ Finset.range c).card :=
        Finset.card_le_card hsub
    _ ≤ ((Finset.Ico c n).filter Q).card + (Finset.range c).card :=
        Finset.card_union_le _ _
    _ = ((Finset.Ico c n).filter Q).card + c := by rw [Finset.card_range]

/-! ### Visits through the good/bad decomposition -/

/-- Visits to a set of scale-`K` cells, summed cell by cell. -/
theorem card_cellAt_mem (b : ℕ) (hb : 0 < b) (x : ℝ) (K n : ℕ) (S : Finset ℕ) :
    ((Finset.range n).filter fun j => cellAt b x K j ∈ S).card
      = ∑ m ∈ S, visitCount (orbit b x)
          ((m : ℝ) / (b : ℝ) ^ K) ((m + 1 : ℝ) / (b : ℝ) ^ K) n := by
  classical
  have hv : ∀ m : ℕ, visitCount (orbit b x) ((m : ℝ) / (b : ℝ) ^ K)
      ((m + 1 : ℝ) / (b : ℝ) ^ K) n
      = ((Finset.range n).filter fun j => cellAt b x K j = m).card :=
    fun m => visitCount_eq_card_floor b hb x K m n
  simp_rw [hv, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_ite_eq S (cellAt b x K j) (fun _ => 1)]

/-- A `k ≤ K` window is never bad about its own count: cells outside
`badSet` have sliding count within `T` of uniform.  Upper counting bound:
`b^k·N·A(n) ≤ n·(N+T) + Bad·b^k·N + b^k·N·(K−k)`. -/
theorem cell_visits_upper (b : ℕ) (hb : 0 < b) (x : ℝ) (K k w T n : ℕ)
    (hkK : k ≤ K) :
    b ^ k * ((K - k + 1) * visitCount (orbit b x)
        ((w : ℝ) / (b : ℝ) ^ k) ((w + 1 : ℝ) / (b : ℝ) ^ k) n)
      ≤ n * ((K - k + 1) + T)
        + ((Finset.range n).filter
            fun j => cellAt b x K j ∈ badSet b K k w T).card
          * (b ^ k * (K - k + 1))
        + b ^ k * ((K - k + 1) * (K - k)) := by
  classical
  set N := K - k + 1 with hN
  set Q : ℕ → Prop := fun t => ⌊orbit b x t * (b : ℝ) ^ k⌋₊ = w with hQ
  set F : ℕ → ℕ := fun n => ((Finset.range n).filter Q).card with hF
  set Sn := ∑ j ∈ Finset.range n, occCount b K k w (cellAt b x K j) with hSn
  have hA : visitCount (orbit b x) ((w : ℝ) / (b : ℝ) ^ k)
      ((w + 1 : ℝ) / (b : ℝ) ^ k) n = F n :=
    visitCount_eq_card_floor b hb x k w n
  -- sliding lower: N·F(n) ≤ S(n) + N·(K−k)
  have hslide : N * F n ≤ Sn + N * (K - k) := by
    have h1 := le_sum_occCount_cellAt b hb x K k w n hkK
    have h2 := card_filter_range_le_Ico_add Q n (K - k)
    calc N * F n ≤ N * (((Finset.Ico (K - k) n).filter Q).card + (K - k)) :=
          Nat.mul_le_mul_left N h2
      _ = ((Finset.Ico (K - k) n).filter Q).card * N + N * (K - k) := by ring
      _ ≤ Sn + N * (K - k) := Nat.add_le_add_right h1 _
  -- good/bad split of b^k·S(n)
  set P : ℕ → Prop := fun j => cellAt b x K j ∈ badSet b K k w T with hP
  have hsplit : b ^ k * Sn ≤ n * (N + T)
      + ((Finset.range n).filter P).card * (b ^ k * N) := by
    have hgb : (∑ j ∈ (Finset.range n).filter P,
          b ^ k * occCount b K k w (cellAt b x K j))
        + (∑ j ∈ (Finset.range n).filter (fun j => ¬ P j),
            b ^ k * occCount b K k w (cellAt b x K j))
        = b ^ k * Sn := by
      rw [hSn, Finset.mul_sum]
      exact Finset.sum_filter_add_sum_filter_not (Finset.range n) P _
    -- bad part: the trivial bound occCount ≤ N
    have hbad : ∑ j ∈ (Finset.range n).filter P,
          b ^ k * occCount b K k w (cellAt b x K j)
        ≤ ((Finset.range n).filter P).card * (b ^ k * N) := by
      have := Finset.sum_le_card_nsmul ((Finset.range n).filter P)
        (fun j => b ^ k * occCount b K k w (cellAt b x K j)) (b ^ k * N)
        (fun j _ => Nat.mul_le_mul_left _ (occCount_le b K k w _))
      simpa [smul_eq_mul] using this
    -- good part: sliding count within T of uniform
    have hgood : ∑ j ∈ (Finset.range n).filter (fun j => ¬ P j),
          b ^ k * occCount b K k w (cellAt b x K j)
        ≤ n * (N + T) := by
      have hpt : ∀ j ∈ (Finset.range n).filter (fun j => ¬ P j),
          b ^ k * occCount b K k w (cellAt b x K j) ≤ N + T := by
        intro j hj
        rw [Finset.mem_filter] at hj
        have hnb : cellAt b x K j ∉ badSet b K k w T := hj.2
        rw [badSet, Finset.mem_filter, not_and] at hnb
        have habs := hnb (Finset.mem_range.mpr (cellAt_lt b hb x K j))
        rw [not_le] at habs
        have h1 : ((b ^ k * occCount b K k w (cellAt b x K j) : ℕ) : ℤ)
            - (N : ℤ) < T := by
          calc ((b ^ k * occCount b K k w (cellAt b x K j) : ℕ) : ℤ) - (N : ℤ)
              ≤ |((b : ℤ) ^ k * occCount b K k w (cellAt b x K j) : ℤ)
                  - ((K - k + 1 : ℕ) : ℤ)| := by
                rw [← hN]
                push_cast
                exact le_abs_self _
            _ < T := habs
        have h2 : b ^ k * occCount b K k w (cellAt b x K j) < N + T := by
          exact_mod_cast (by linarith :
            ((b ^ k * occCount b K k w (cellAt b x K j) : ℕ) : ℤ)
              < (N : ℤ) + T)
        omega
      have := Finset.sum_le_card_nsmul _ _ _ hpt
      have hcard : ((Finset.range n).filter (fun j => ¬ P j)).card ≤ n := by
        calc ((Finset.range n).filter (fun j => ¬ P j)).card
            ≤ (Finset.range n).card := Finset.card_filter_le _ _
          _ = n := Finset.card_range n
      calc ∑ j ∈ (Finset.range n).filter (fun j => ¬ P j),
            b ^ k * occCount b K k w (cellAt b x K j)
          ≤ ((Finset.range n).filter (fun j => ¬ P j)).card * (N + T) := by
            simpa [smul_eq_mul] using this
        _ ≤ n * (N + T) := Nat.mul_le_mul_right _ hcard
    omega
  -- assemble
  rw [hA]
  calc b ^ k * (N * F n) ≤ b ^ k * (Sn + N * (K - k)) :=
        Nat.mul_le_mul_left _ hslide
    _ = b ^ k * Sn + b ^ k * (N * (K - k)) := by ring
    _ ≤ n * (N + T) + ((Finset.range n).filter P).card * (b ^ k * N)
          + b ^ k * (N * (K - k)) := by omega

/-- Lower counting bound:
`n·(N−T) ≤ b^k·N·(A(n) + (K−k)) + Bad·(N−T)` (ℕ-truncated `N−T`). -/
theorem cell_visits_lower (b : ℕ) (hb : 0 < b) (x : ℝ) (K k w T n : ℕ)
    (hkK : k ≤ K) :
    n * ((K - k + 1) - T)
      ≤ b ^ k * ((K - k + 1) * (visitCount (orbit b x)
          ((w : ℝ) / (b : ℝ) ^ k) ((w + 1 : ℝ) / (b : ℝ) ^ k) n + (K - k)))
        + ((Finset.range n).filter
            fun j => cellAt b x K j ∈ badSet b K k w T).card
          * ((K - k + 1) - T) := by
  classical
  set N := K - k + 1 with hN
  set Q : ℕ → Prop := fun t => ⌊orbit b x t * (b : ℝ) ^ k⌋₊ = w with hQ
  set F : ℕ → ℕ := fun n => ((Finset.range n).filter Q).card with hF
  set Sn := ∑ j ∈ Finset.range n, occCount b K k w (cellAt b x K j) with hSn
  set P : ℕ → Prop := fun j => cellAt b x K j ∈ badSet b K k w T with hP
  have hA : visitCount (orbit b x) ((w : ℝ) / (b : ℝ) ^ k)
      ((w + 1 : ℝ) / (b : ℝ) ^ k) n = F n :=
    visitCount_eq_card_floor b hb x k w n
  -- sliding upper: S(n) ≤ N·(F(n) + (K−k))
  have hslide : Sn ≤ (F n + (K - k)) * N := by
    have h1 := sum_occCount_cellAt_le b hb x K k w n hkK
    have h2 := card_filter_range_le_add Q n (K - k)
    calc Sn ≤ ((Finset.range (n + (K - k))).filter Q).card * N := h1
      _ ≤ (F n + (K - k)) * N := Nat.mul_le_mul_right N h2
  -- every good step carries at least N − T sliding hits (scaled by b^k)
  have hgood : ∀ j ∈ (Finset.range n).filter (fun j => ¬ P j),
      N - T ≤ b ^ k * occCount b K k w (cellAt b x K j) := by
    intro j hj
    rw [Finset.mem_filter] at hj
    have hnb : cellAt b x K j ∉ badSet b K k w T := hj.2
    rw [badSet, Finset.mem_filter, not_and] at hnb
    have habs := hnb (Finset.mem_range.mpr (cellAt_lt b hb x K j))
    rw [not_le] at habs
    have h1 : (N : ℤ) - (b ^ k * occCount b K k w (cellAt b x K j) : ℕ)
        < T := by
      calc (N : ℤ) - ((b ^ k * occCount b K k w (cellAt b x K j) : ℕ) : ℤ)
          ≤ |((b : ℤ) ^ k * occCount b K k w (cellAt b x K j) : ℤ)
              - ((K - k + 1 : ℕ) : ℤ)| := by
            rw [← hN, abs_sub_comm]
            push_cast
            exact le_abs_self _
        _ < T := habs
    have h2 : (N : ℤ) < (b ^ k * occCount b K k w (cellAt b x K j) : ℕ) + T := by
      linarith
    have h3 : N < b ^ k * occCount b K k w (cellAt b x K j) + T := by
      exact_mod_cast h2
    omega
  -- sum the good bound
  have hsum : ((Finset.range n).filter (fun j => ¬ P j)).card * (N - T)
      ≤ b ^ k * Sn := by
    calc ((Finset.range n).filter (fun j => ¬ P j)).card * (N - T)
        = ∑ _j ∈ (Finset.range n).filter (fun j => ¬ P j), (N - T) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ j ∈ (Finset.range n).filter (fun j => ¬ P j),
            b ^ k * occCount b K k w (cellAt b x K j) :=
          Finset.sum_le_sum hgood
      _ ≤ ∑ j ∈ Finset.range n,
            b ^ k * occCount b K k w (cellAt b x K j) :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = b ^ k * Sn := by rw [hSn, Finset.mul_sum]
  -- the two filters partition range n
  have hpart : ((Finset.range n).filter P).card
      + ((Finset.range n).filter (fun j => ¬ P j)).card = n := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_range]
  -- assemble
  rw [hA]
  have hchain : ((Finset.range n).filter (fun j => ¬ P j)).card * (N - T)
      ≤ b ^ k * ((F n + (K - k)) * N) := by
    calc ((Finset.range n).filter (fun j => ¬ P j)).card * (N - T)
        ≤ b ^ k * Sn := hsum
      _ ≤ b ^ k * ((F n + (K - k)) * N) := Nat.mul_le_mul_left _ hslide
  have hexpand : n * (N - T)
      = ((Finset.range n).filter P).card * (N - T)
        + ((Finset.range n).filter (fun j => ¬ P j)).card * (N - T) := by
      rw [← Nat.add_mul, hpart]
  calc n * (N - T)
      = ((Finset.range n).filter P).card * (N - T)
        + ((Finset.range n).filter (fun j => ¬ P j)).card * (N - T) := hexpand
    _ ≤ ((Finset.range n).filter P).card * (N - T)
        + b ^ k * ((F n + (K - k)) * N) := by omega
    _ = b ^ k * (N * (F n + (K - k)))
        + ((Finset.range n).filter P).card * (N - T) := by ring

/-! ### The squeeze: cell frequencies converge to cell length -/

set_option maxHeartbeats 1000000 in
/-- **Core of the hot-spot lemma**: a uniform eventual upper bound `C/bᴷ`
on every scale-`K` cell's visit frequency forces every fixed cell's
frequency to converge to its exact length `1/bᵏ`. -/
theorem tendsto_cell_of_visit_upper (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (C : ℝ)
    (h : ∀ K m : ℕ, m < b ^ K → ∀ᶠ n in atTop,
      (visitCount (orbit b x) ((m : ℝ) / (b : ℝ) ^ K)
          ((m + 1 : ℝ) / (b : ℝ) ^ K) n : ℝ) / n ≤ C / (b : ℝ) ^ K)
    (k w : ℕ) (hk1 : 1 ≤ k) (hw : w < b ^ k) :
    Tendsto (fun n => (visitCount (orbit b x) ((w : ℝ) / (b : ℝ) ^ k)
        ((w + 1 : ℝ) / (b : ℝ) ^ k) n : ℝ) / n) atTop
      (nhds (1 / (b : ℝ) ^ k)) := by
  classical
  have hb0 : (0 : ℕ) < b := by omega
  have hbR : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hbk : (0 : ℝ) < (b : ℝ) ^ k := by positivity
  have hbk1 : (1 : ℝ) ≤ (b : ℝ) ^ k := one_le_pow₀ hbR.le
  -- the constant is at least 1 (apply the hypothesis to the unit cell)
  have hC1 : (1 : ℝ) ≤ C := by
    have h00 := h 0 0 (by norm_num)
    obtain ⟨n, hn1, hnC⟩ := ((eventually_ge_atTop 1).and h00).exists
    have hv : visitCount (orbit b x) (((0 : ℕ) : ℝ) / (b : ℝ) ^ 0)
        ((((0 : ℕ) : ℝ) + 1) / (b : ℝ) ^ 0) n = n := by
      unfold visitCount
      rw [Finset.filter_true_of_mem, Finset.card_range]
      intro t _
      simp only [pow_zero, Nat.cast_zero, zero_div, Set.mem_Ico]
      constructor
      · exact Int.fract_nonneg _
      · rw [zero_add, div_one]
        exact Int.fract_lt_one _
    rw [hv] at hnC
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [div_self hn0.ne', pow_zero, div_one] at hnC
    exact hnC
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC1
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ := ε / 5 with hδdef
  have hδ : 0 < δ := by positivity
  -- choose the window size K
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt
    (max ((2 * k * C) / δ ^ 3) (1 / (δ * (b : ℝ) ^ k)))
  set K := max (2 * k) (N₀ + k) with hKdef
  set N := K - k + 1 with hNdef
  have hk2K : 2 * k ≤ K := le_max_left _ _
  have hkK : k ≤ K := by omega
  have hN₀N : N₀ ≤ N := by
    have : N₀ + k ≤ K := le_max_right _ _
    omega
  have hN1 : 1 ≤ N := by omega
  have hNR : (0 : ℝ) < (N : ℕ) := by exact_mod_cast hN1
  have hNge : (N₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN₀N
  have hNbig : max ((2 * k * C) / δ ^ 3) (1 / (δ * (b : ℝ) ^ k)) < (N : ℝ) :=
    lt_of_lt_of_le hN₀ hNge
  have hc3 : 2 * k * C ≤ δ ^ 3 * N := by
    have h1 : (2 * k * C) / δ ^ 3 < (N : ℝ) :=
      lt_of_le_of_lt (le_max_left _ _) hNbig
    have hδ3 : (0 : ℝ) < δ ^ 3 := by positivity
    rw [div_lt_iff₀ hδ3] at h1
    linarith
  have hc2 : 1 ≤ δ * ((N : ℝ) * (b : ℝ) ^ k) := by
    have h1 : 1 / (δ * (b : ℝ) ^ k) < (N : ℝ) :=
      lt_of_le_of_lt (le_max_right _ _) hNbig
    have hpos : (0 : ℝ) < δ * (b : ℝ) ^ k := by positivity
    rw [div_lt_iff₀ hpos] at h1
    linarith [h1]
  -- the deviation threshold
  set T := ⌈δ * ((N : ℝ) * (b : ℝ) ^ k)⌉₊ with hTdef
  have hT_lb : δ * ((N : ℝ) * (b : ℝ) ^ k) ≤ (T : ℝ) := Nat.le_ceil _
  have hT_ub : (T : ℝ) ≤ 2 * δ * ((N : ℝ) * (b : ℝ) ^ k) := by
    have := Nat.ceil_lt_add_one
      (by positivity : (0:ℝ) ≤ δ * ((N : ℝ) * (b : ℝ) ^ k))
    have h2 : (T : ℝ) < δ * ((N : ℝ) * (b : ℝ) ^ k) + 1 := this
    nlinarith [hc2]
  have hT1 : 1 ≤ T := by
    rw [hTdef, Nat.one_le_ceil_iff]
    positivity
  clear_value T
  clear_value N
  clear_value K
  -- the bad-set is small (Chebyshev)
  have hbadcard : ((badSet b K k w T).card : ℝ) * ((T : ℝ) ^ 2)
      ≤ 2 * k * (N : ℝ) * (b : ℝ) ^ (K + k) := by
    have := card_badSet_le b K k w T hb0 hw hk2K hk1
    rw [← hNdef] at this
    calc ((badSet b K k w T).card : ℝ) * ((T : ℝ) ^ 2)
        = ((T ^ 2 * (badSet b K k w T).card : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((2 * k * N * b ^ (K + k) : ℕ) : ℝ) := by exact_mod_cast this
      _ = 2 * k * (N : ℝ) * (b : ℝ) ^ (K + k) := by push_cast; ring
  -- key consequence: total bad-cell frequency is at most δ
  have hkey : ((badSet b K k w T).card : ℝ) * (C / (b : ℝ) ^ K) ≤ δ := by
    have hbK : (0 : ℝ) < (b : ℝ) ^ K := by positivity
    have hgoal : ((badSet b K k w T).card : ℝ) * C ≤ δ * (b : ℝ) ^ K := by
        have hT2 : (δ * ((N : ℝ) * (b : ℝ) ^ k)) ^ 2 ≤ (T : ℝ) ^ 2 := by
          have h0 : (0:ℝ) ≤ δ * ((N : ℝ) * (b : ℝ) ^ k) := by positivity
          exact pow_le_pow_left₀ h0 hT_lb 2
        have hcard0 : (0 : ℝ) ≤ ((badSet b K k w T).card : ℝ) :=
          Nat.cast_nonneg _
        have hE : ((badSet b K k w T).card : ℝ)
            * (δ ^ 2 * (N : ℝ) ^ 2 * ((b : ℝ) ^ k) ^ 2)
            ≤ 2 * k * (N : ℝ) * (b : ℝ) ^ (K + k) := by
          calc ((badSet b K k w T).card : ℝ)
              * (δ ^ 2 * (N : ℝ) ^ 2 * ((b : ℝ) ^ k) ^ 2)
              = ((badSet b K k w T).card : ℝ)
                  * (δ * ((N : ℝ) * (b : ℝ) ^ k)) ^ 2 := by ring
            _ ≤ ((badSet b K k w T).card : ℝ) * (T : ℝ) ^ 2 :=
                mul_le_mul_of_nonneg_left hT2 hcard0
            _ ≤ 2 * k * (N : ℝ) * (b : ℝ) ^ (K + k) := hbadcard
        have hpow : (b : ℝ) ^ (K + k) = (b : ℝ) ^ K * (b : ℝ) ^ k := pow_add _ _ _
        -- multiply the target by the positive quantity δ²·N·b^{2k} and compare
        have hmulpos : (0 : ℝ) < δ ^ 2 * (N : ℝ) * ((b : ℝ) ^ k) ^ 2 := by
          positivity
        refine le_of_mul_le_mul_right ?_ hmulpos
        calc ((badSet b K k w T).card : ℝ) * C
              * (δ ^ 2 * (N : ℝ) * ((b : ℝ) ^ k) ^ 2)
            = C / (N : ℝ) * (((badSet b K k w T).card : ℝ)
                * (δ ^ 2 * (N : ℝ) ^ 2 * ((b : ℝ) ^ k) ^ 2)) := by
              field_simp
              try ring
          _ ≤ C / (N : ℝ) * (2 * k * (N : ℝ) * (b : ℝ) ^ (K + k)) := by
              apply mul_le_mul_of_nonneg_left hE
              positivity
          _ = 2 * k * C * ((b : ℝ) ^ K * (b : ℝ) ^ k) := by
              rw [hpow]
              field_simp
              try ring
          _ ≤ δ ^ 3 * (N : ℝ) * ((b : ℝ) ^ K * (b : ℝ) ^ k) := by
              apply mul_le_mul_of_nonneg_right hc3
              positivity
          _ ≤ δ * (b : ℝ) ^ K * (δ ^ 2 * (N : ℝ) * ((b : ℝ) ^ k) ^ 2) := by
              have hsq : (b : ℝ) ^ k ≤ ((b : ℝ) ^ k) ^ 2 := by
                nlinarith [hbk1, hbk]
              nlinarith [mul_le_mul_of_nonneg_left hsq
                (by positivity : (0 : ℝ) ≤ δ ^ 3 * (N : ℝ) * (b : ℝ) ^ K)]
    calc ((badSet b K k w T).card : ℝ) * (C / (b : ℝ) ^ K)
        = ((badSet b K k w T).card : ℝ) * C / (b : ℝ) ^ K := by ring
      _ ≤ δ * (b : ℝ) ^ K / (b : ℝ) ^ K :=
          div_le_div_of_nonneg_right hgoal hbK.le
      _ = δ := by field_simp
  -- eventual facts
  have hE1 : ∀ᶠ n in atTop, ∀ m ∈ badSet b K k w T,
      (visitCount (orbit b x) ((m : ℝ) / (b : ℝ) ^ K)
        ((m + 1 : ℝ) / (b : ℝ) ^ K) n : ℝ) / n ≤ C / (b : ℝ) ^ K := by
    rw [eventually_all_finset]
    intro m hm
    have hmlt : m < b ^ K := by
      have := Finset.mem_filter.mp hm
      exact Finset.mem_range.mp this.1
    exact h K m hmlt
  have hE2 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  have hE3 : ∀ᶠ n : ℕ in atTop, ((K : ℝ)) / n < δ :=
    (tendsto_const_div_atTop_nhds_zero_nat (K : ℝ)).eventually_lt_const hδ
  have hev : ∀ᶠ n in atTop, dist ((visitCount (orbit b x)
      ((w : ℝ) / (b : ℝ) ^ k) ((w + 1 : ℝ) / (b : ℝ) ^ k) n : ℝ) / n)
      (1 / (b : ℝ) ^ k) < ε := by
    filter_upwards [hE1, hE2, hE3] with n hbadv hn1 hKn
    set An := (visitCount (orbit b x) ((w : ℝ) / (b : ℝ) ^ k)
      ((w + 1 : ℝ) / (b : ℝ) ^ k) n : ℕ) with hAndef
    set Bn := ((Finset.range n).filter
      fun j => cellAt b x K j ∈ badSet b K k w T).card with hBndef
    clear_value An Bn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    -- bad visits are rare
    have hBn : (Bn : ℝ) ≤ δ * n := by
      have hident := card_cellAt_mem b hb0 x K n (badSet b K k w T)
      have hsum : (Bn : ℝ) / n = ∑ m ∈ badSet b K k w T,
          (visitCount (orbit b x) ((m : ℝ) / (b : ℝ) ^ K)
            ((m + 1 : ℝ) / (b : ℝ) ^ K) n : ℝ) / n := by
        rw [hBndef, hident]
        push_cast
        rw [Finset.sum_div]
      have hle : (Bn : ℝ) / n ≤ ((badSet b K k w T).card : ℝ)
          * (C / (b : ℝ) ^ K) := by
        rw [hsum]
        calc ∑ m ∈ badSet b K k w T,
              (visitCount (orbit b x) ((m : ℝ) / (b : ℝ) ^ K)
                ((m + 1 : ℝ) / (b : ℝ) ^ K) n : ℝ) / n
            ≤ ∑ _m ∈ badSet b K k w T, C / (b : ℝ) ^ K :=
              Finset.sum_le_sum hbadv
          _ = ((badSet b K k w T).card : ℝ) * (C / (b : ℝ) ^ K) := by
              rw [Finset.sum_const, nsmul_eq_mul]
      have : (Bn : ℝ) / n ≤ δ := hle.trans hkey
      rw [div_le_iff₀ hn0] at this
      linarith
    have hKn' : (K : ℝ) ≤ δ * n := by
      rw [div_lt_iff₀ hn0] at hKn
      linarith
    -- cast the two counting bounds
    have hup := cell_visits_upper b hb0 x K k w T n hkK
    have hlo := cell_visits_lower b hb0 x K k w T n hkK
    rw [← hNdef, ← hAndef, ← hBndef] at hup hlo
    have hupR : (b : ℝ) ^ k * ((N : ℝ) * An)
        ≤ n * ((N : ℝ) + T) + Bn * ((b : ℝ) ^ k * N)
          + (b : ℝ) ^ k * ((N : ℝ) * (K - k : ℕ)) := by
      exact_mod_cast hup
    have hKkR : ((K - k : ℕ) : ℝ) ≤ (K : ℝ) := by
      have : K - k ≤ K := Nat.sub_le _ _
      exact_mod_cast this
    -- upper estimate on the frequency
    have hTle : (T : ℝ) * n ≤ 2 * δ * ((N : ℝ) * (b : ℝ) ^ k) * n :=
      mul_le_mul_of_nonneg_right hT_ub hn0.le
    have hKle : (b : ℝ) ^ k * ((N : ℝ) * ((K - k : ℕ) : ℝ))
        ≤ (b : ℝ) ^ k * ((N : ℝ) * (δ * n)) := by
      apply mul_le_mul_of_nonneg_left _ hbk.le
      exact mul_le_mul_of_nonneg_left (hKkR.trans hKn') hNR.le
    have hfreq_ub : (An : ℝ) / n - 1 / (b : ℝ) ^ k ≤ 4 * δ := by
      rw [sub_le_iff_le_add, div_le_iff₀ hn0]
      have hbkN : (0 : ℝ) < (b : ℝ) ^ k * N := by positivity
      refine le_of_mul_le_mul_right ?_ hbkN
      have hRHS : (4 * δ + 1 / (b : ℝ) ^ k) * n * ((b : ℝ) ^ k * N)
          = 4 * δ * n * ((b : ℝ) ^ k * (N : ℝ)) + n * N := by
        field_simp
        try ring
      rw [hRHS]
      have hBnle : (Bn : ℝ) * ((b : ℝ) ^ k * N) ≤ δ * n * ((b : ℝ) ^ k * N) := by
        apply mul_le_mul_of_nonneg_right hBn
        positivity
      linarith [hupR, hTle, hBnle, hKle]
    -- lower estimate on the frequency
    have hfreq_lb : 1 / (b : ℝ) ^ k - (An : ℝ) / n ≤ 4 * δ := by
      by_cases hTN : N ≤ T
      · -- degenerate: the cell is already shorter than the tolerance
        have h1 : (N : ℝ) ≤ (T : ℝ) := by exact_mod_cast hTN
        have h2 : (1 : ℝ) / (b : ℝ) ^ k ≤ 2 * δ := by
          have := hT_ub
          have hN' : (0 : ℝ) < (N : ℝ) := hNR
          rw [div_le_iff₀ hbk]
          nlinarith [h1, hT_ub, hNR]
        have h3 : (0 : ℝ) ≤ (An : ℝ) / n := by positivity
        linarith
      · push_neg at hTN
        have hcast : ((N - T : ℕ) : ℝ) = (N : ℝ) - T := by
          rw [Nat.cast_sub hTN.le]
        have hloR : n * ((N : ℝ) - T)
            ≤ (b : ℝ) ^ k * ((N : ℝ) * (An + ((K - k : ℕ) : ℝ)))
              + Bn * ((N : ℝ) - T) := by
          rw [← hcast]
          exact_mod_cast hlo
        rw [sub_le_iff_le_add, ← sub_le_iff_le_add']
        rw [le_div_iff₀ hn0]
        have hbkN : (0 : ℝ) < (b : ℝ) ^ k * N := by positivity
        refine le_of_mul_le_mul_right ?_ hbkN
        have hLHS : (1 / (b : ℝ) ^ k - 4 * δ) * n * ((b : ℝ) ^ k * N)
            = n * N - 4 * δ * n * ((b : ℝ) ^ k * (N : ℝ)) := by
          field_simp
          try ring
        rw [hLHS]
        have hBnle : (Bn : ℝ) * ((N : ℝ) - T) ≤ (Bn : ℝ) * N := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          have : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg _
          linarith
        have hBnle2 : (Bn : ℝ) * (N : ℝ) ≤ δ * n * ((b : ℝ) ^ k * (N : ℝ)) := by
          calc (Bn : ℝ) * (N : ℝ) ≤ δ * n * N :=
              mul_le_mul_of_nonneg_right hBn hNR.le
            _ ≤ δ * n * ((b : ℝ) ^ k * (N : ℝ)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              nlinarith [hNR, hbk1]
        have hBnT : (0 : ℝ) ≤ (Bn : ℝ) * T := by positivity
        linarith [hloR, hTle, hBnle2, hKle, hBnT]
    -- combine
    rw [Real.dist_eq, abs_sub_lt_iff]
    constructor
    · calc (An : ℝ) / n - 1 / (b : ℝ) ^ k ≤ 4 * δ := hfreq_ub
        _ < 5 * δ := by linarith
        _ = ε := by rw [hδdef]; ring
    · calc 1 / (b : ℝ) ^ k - (An : ℝ) / n ≤ 4 * δ := hfreq_lb
        _ < 5 * δ := by linarith
        _ = ε := by rw [hδdef]; ring
  exact Filter.eventually_atTop.mp hev

/-- The hot-spot lemma, orbit form: uniform eventual b-adic upper bounds
give equidistribution of the orbit. -/
theorem equidistributed_orbit_of_visit_upper (b : ℕ) (hb : 2 ≤ b) (x : ℝ)
    (C : ℝ)
    (h : ∀ K m : ℕ, m < b ^ K → ∀ᶠ n in atTop,
      (visitCount (orbit b x) ((m : ℝ) / (b : ℝ) ^ K)
          ((m + 1 : ℝ) / (b : ℝ) ^ K) n : ℝ) / n ≤ C / (b : ℝ) ^ K) :
    Equidistributed (orbit b x) :=
  equidistributed_of_badic b hb _ fun k hk m hm =>
    tendsto_cell_of_visit_upper b hb x C h k m hk hm

end NormalNumbers
