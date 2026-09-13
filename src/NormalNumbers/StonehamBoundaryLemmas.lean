import Mathlib

/-!
# Elementary 2-adic lemmas for the Stoneham boundary campaign

Helper module for `StonehamBoundary.lean` (brief: BRIEF-stoneham-boundary-2026-09-13.md).

* `three_pow_two_pow_modEq`: `3^(2^r) ≡ 1 + 2^(r+2) [ZMOD 2^(r+3)]` for `r ≥ 1`
  (squaring lift), hence `3^(2^r) ≡ 1 [ZMOD 2^(r+2)]`.
* `stoneham_f_add_two_pow`: the block map `f k = 3^k − k` satisfies
  `f (k + 2^r) ≡ f k − 2^r [ZMOD 2^(r+2)]`, which drives both the residue
  surjectivity lift and the periodicity mod `2^r`.
* `exponent_residue_aux`: surjectivity of `f` on residues mod `2^r`.
* `three_pow_grid_aux`: every `a ≡ 1 (mod 8)`, `a < 2^c`, is `3^e mod 2^c`.
-/

namespace NormalNumbers

/-- Squaring lift: `x ≡ 1 + 2^m (mod 2^(m+1))` with `m ≥ 2` gives
`x² ≡ 1 + 2^(m+1) (mod 2^(m+2))`. -/
theorem sq_lift_two_adic (m : ℕ) (hm : 2 ≤ m) (x : ℤ)
    (hx : x ≡ 1 + 2 ^ m [ZMOD 2 ^ (m + 1)]) :
    x ^ 2 ≡ 1 + 2 ^ (m + 1) [ZMOD 2 ^ (m + 2)] := by
  rw [Int.modEq_iff_dvd] at hx ⊢
  obtain ⟨t, ht⟩ := hx
  have h2m : (2 : ℤ) ^ m = 4 * 2 ^ (m - 2) := by
    rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  set z : ℤ := 2 ^ (m - 2) with hz
  have e1 : (2 : ℤ) ^ (m + 1) = 8 * z := by rw [pow_succ, h2m]; ring
  have e2 : (2 : ℤ) ^ (m + 2) = 16 * z := by rw [pow_succ, e1]; ring
  rw [e1, h2m] at ht
  rw [e2, e1]
  have hx' : x = 1 + 4 * z - 8 * z * t := by linarith
  refine ⟨-z + (1 + 4 * z) * t - 4 * z * t ^ 2, ?_⟩
  rw [hx']; ring

/-- `3^(2^r) ≡ 1 + 2^(r+2) (mod 2^(r+3))` for `r ≥ 1`. -/
theorem three_pow_two_pow_modEq (r : ℕ) (hr : 1 ≤ r) :
    (3 : ℤ) ^ (2 ^ r) ≡ 1 + 2 ^ (r + 2) [ZMOD 2 ^ (r + 3)] := by
  induction r, hr using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have h := sq_lift_two_adic (k + 2) (by omega) _ ih
    have hsq : (3 : ℤ) ^ (2 ^ (k + 1)) = ((3 : ℤ) ^ (2 ^ k)) ^ 2 := by
      rw [pow_succ, pow_mul]
    rw [show k + 2 + 1 = k + 1 + 2 by ring, show k + 2 + 2 = k + 1 + 3 by ring] at h
    rwa [hsq]

/-- `3^(2^r) ≡ 1 (mod 2^(r+2))` for `r ≥ 1`. -/
theorem three_pow_two_pow_modEq_one (r : ℕ) (hr : 1 ≤ r) :
    (3 : ℤ) ^ (2 ^ r) ≡ 1 [ZMOD 2 ^ (r + 2)] := by
  have h := (three_pow_two_pow_modEq r hr).of_dvd (pow_dvd_pow 2 (by omega : r + 2 ≤ r + 3))
  refine h.trans ?_
  rw [Int.modEq_iff_dvd]
  exact ⟨-1, by ring⟩

/-- The block map `f k = 3^k − k` drops by exactly `2^r` (mod `2^(r+2)`) under `k ↦ k + 2^r`. -/
theorem stoneham_f_add_two_pow (r : ℕ) (hr : 1 ≤ r) (k : ℕ) :
    (3 : ℤ) ^ (k + 2 ^ r) - ((k + 2 ^ r : ℕ) : ℤ)
      ≡ ((3 : ℤ) ^ k - (k : ℤ)) - 2 ^ r [ZMOD 2 ^ (r + 2)] := by
  have h := three_pow_two_pow_modEq_one r hr
  rw [Int.modEq_iff_dvd] at h ⊢
  obtain ⟨t, ht⟩ := h
  refine ⟨3 ^ k * t, ?_⟩
  push_cast
  rw [pow_add]
  linear_combination (3 : ℤ) ^ k * ht

/-- Periodicity: `f (k + m·2^r) ≡ f k (mod 2^r)` for `r ≥ 1`. -/
theorem stoneham_f_periodic (r : ℕ) (hr : 1 ≤ r) (k m : ℕ) :
    (3 : ℤ) ^ (k + m * 2 ^ r) - ((k + m * 2 ^ r : ℕ) : ℤ)
      ≡ (3 : ℤ) ^ k - (k : ℤ) [ZMOD 2 ^ r] := by
  have h1 : (3 : ℤ) ^ (2 ^ r) ≡ 1 [ZMOD 2 ^ r] :=
    (three_pow_two_pow_modEq_one r hr).of_dvd (pow_dvd_pow 2 (by omega))
  have h2 : (3 : ℤ) ^ (k + m * 2 ^ r) ≡ 3 ^ k [ZMOD 2 ^ r] := by
    rw [pow_add, pow_mul']
    calc (3 : ℤ) ^ k * ((3 : ℤ) ^ (2 ^ r)) ^ m ≡ 3 ^ k * 1 ^ m [ZMOD 2 ^ r] :=
          (h1.pow m).mul_left _
      _ = 3 ^ k := by ring
  have h3 : ((k + m * 2 ^ r : ℕ) : ℤ) ≡ (k : ℤ) [ZMOD 2 ^ r] := by
    rw [Int.modEq_iff_dvd]; push_cast; exact ⟨-m, by ring⟩
  exact h2.sub h3

/-- Surjectivity of the block map on residues mod `2^r`, with a witness below `2^r`. -/
theorem exponent_residue_aux (r : ℕ) :
    ∀ a : ℤ, ∃ k : ℕ, k < 2 ^ r ∧ (3 : ℤ) ^ k - (k : ℤ) ≡ a [ZMOD 2 ^ r] := by
  induction r with
  | zero =>
    intro a
    exact ⟨0, by norm_num, by simpa using Int.modEq_one⟩
  | succ r ih =>
    intro a
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · rcases Int.emod_two_eq_zero_or_one a with h | h
      · exact ⟨1, by norm_num, by unfold Int.ModEq; norm_num [h]⟩
      · exact ⟨0, by norm_num, by unfold Int.ModEq; norm_num [h]⟩
    · obtain ⟨k, hk, hfk⟩ := ih a
      obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.1 hfk
      rcases Int.emod_two_eq_zero_or_one t with h | h
      · refine ⟨k, by rw [pow_succ]; omega, ?_⟩
        rw [Int.modEq_iff_dvd, ht, pow_succ]
        exact mul_dvd_mul_left _ (Int.dvd_of_emod_eq_zero h)
      · refine ⟨k + 2 ^ r, by rw [pow_succ]; omega, ?_⟩
        have hlift := (stoneham_f_add_two_pow r hr k).of_dvd
          (pow_dvd_pow 2 (by omega : r + 1 ≤ r + 2))
        refine hlift.trans ?_
        rw [Int.modEq_iff_dvd]
        obtain ⟨s, hs⟩ : (2 : ℤ) ∣ t + 1 := Int.dvd_of_emod_eq_zero (by omega)
        exact ⟨s, by rw [pow_succ]; linear_combination ht + 2 ^ r * hs⟩

/-- `3^(2^(c-2)) ≡ 1 + 2^c (mod 2^(c+1))` for `c ≥ 3`. -/
theorem three_pow_half_period (c : ℕ) (hc : 3 ≤ c) :
    (3 : ℤ) ^ (2 ^ (c - 2)) ≡ 1 + 2 ^ c [ZMOD 2 ^ (c + 1)] := by
  have h := three_pow_two_pow_modEq (c - 2) (by omega)
  rwa [show c - 2 + 2 = c by omega, show c - 2 + 3 = c + 1 by omega] at h

/-- Grid lemma (integer form): every `a ≡ 1 (mod 8)` is a power of `3` mod `2^c`, `c ≥ 3`. -/
theorem three_pow_grid_aux (c : ℕ) (hc : 3 ≤ c) :
    ∀ a : ℤ, a % 8 = 1 → ∃ e : ℕ, (3 : ℤ) ^ e ≡ a [ZMOD 2 ^ c] := by
  induction c, hc using Nat.le_induction with
  | base =>
    intro a ha
    refine ⟨0, ?_⟩
    unfold Int.ModEq; norm_num; omega
  | succ c hc ih =>
    intro a ha
    obtain ⟨e, he⟩ := ih a ha
    obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.1 he
    rcases Int.emod_two_eq_zero_or_one t with h | h
    · refine ⟨e, ?_⟩
      rw [Int.modEq_iff_dvd, ht, pow_succ]
      exact mul_dvd_mul_left _ (Int.dvd_of_emod_eq_zero h)
    · refine ⟨e + 2 ^ (c - 2), ?_⟩
      have hhalf := three_pow_half_period c hc
      -- 3^e is odd
      have hodd : (3 : ℤ) ^ e % 2 = 1 :=
        Int.odd_iff.mp ((by decide : Odd (3 : ℤ)).pow)
      obtain ⟨s, hs⟩ : (2 : ℤ) ∣ t + 1 := Int.dvd_of_emod_eq_zero (by omega)
      obtain ⟨w, hw⟩ : (2 : ℤ) ∣ 3 ^ e - 1 := Int.dvd_of_emod_eq_zero (by omega)
      obtain ⟨q, hq⟩ := Int.modEq_iff_dvd.1 hhalf
      have h3 : (3 : ℤ) ^ (2 ^ (c - 2)) = 1 + 2 ^ c - 2 ^ (c + 1) * q := by linarith
      rw [Int.modEq_iff_dvd, pow_add (3 : ℤ), h3]
      -- a - 3^e (1 + 2^c - 2^(c+1) q)
      --   = (a - 3^e) - 3^e 2^c + 3^e 2^(c+1) q
      --   = 2^c t - 3^e 2^c + ... = 2^c (t - 3^e) + ...
      -- t - 3^e = (t + 1) - (3^e - 1) - 2 = 2s - 2w - 2
      refine ⟨s - w - 1 + 3 ^ e * q, ?_⟩
      rw [pow_succ]
      linear_combination ht + 2 ^ c * hs - 2 ^ c * hw

end NormalNumbers
