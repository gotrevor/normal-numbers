/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.MahlerFamilyI

/-!
# Family II: `M(p,1) > (⌊p/2⌋² − 2)/3` for EVERY odd `p ≥ 17` 🧮

Family I (`MahlerFamilyI.lean`) closes its cycle with one junction
`1 → −1` and needs `−1 ∈ ⟨−3⟩ ⊂ (ℤ/D)^×`, `D = (p+3)/2`.  For the other
residues a second junction returns: the family-I junction **scaled by 3**,
`T₀' = 3/D + 6/(pD)`, digit `5`, lands on `−3 = p mod D`, which is in the
orbit of `1`; and its source `3 ∈ −⟨−3⟩` is in the orbit of `−1`.  So

    1 ⟶(junction 1) −1 ⟶(far cycle) 3c₋₂ ⟶(junction 2) −3 ⟶(far cycle) c₋₂

closes for every `p` with `p^e ≡ 1 (mod D)`, `e ≥ 3` — every prime `p ≥ 17`.
The near states of junction 2 are `3×` those of junction 1, so its digit
conditions are the family-I keys at channel `3m`: the bound is
`M = (n² − 2)/3`, `n = ⌊p/2⌋`, i.e. **`M(p,1) ≥ p²/12 − O(p)` for every
prime `p ≥ 17`** — the uniform quadratic prime lower bound
(`mahler_lower_bound_prime_family_II`).  The exact two-junction bottleneck is
measured in `experiments/mahler_two_junction_scan.py`.

The slack is `8/E` (junction 2 carries `δ = 6p`).
-/

namespace NormalNumbers.Adder.FamilyII

open NormalNumbers NormalNumbers.Mahler NormalNumbers.Adder.FamilyI

/-! ### States -/

section cert

variable (p e : ℕ)

/-- `c₃ = 3c₋₁ mod D`, the residue of `N₋₁'`. -/
def c3 : ℕ := 3 * cm1 p e % D p
/-- `c₂ = 3c₋₂ mod D`, the far state feeding junction 2. -/
def c2 : ℕ := 3 * cm2 p e % D p

/-- The far state `F_{c mod D}`. -/
def far (c : ℕ) : Fin (D p + 4) := ⟨c % D p, by have := Nat.mod_lt c (D_pos p); omega⟩
def nm1 : Fin (D p + 4) := ⟨D p, by omega⟩
def n0 : Fin (D p + 4) := ⟨D p + 1, by omega⟩
def nm1' : Fin (D p + 4) := ⟨D p + 2, by omega⟩
def n0' : Fin (D p + 4) := ⟨D p + 3, by omega⟩

/-- Tail numerators over `E = p³D`. -/
def num (s : Fin (D p + 4)) : ℕ :=
  if s.1 < D p then s.1 * p ^ 3
  else if s.1 = D p then (cm1 p e * p ^ 2 + 2) * p
  else if s.1 = D p + 1 then (p + 2) * p ^ 2
  else if s.1 = D p + 2 then (c3 p e * p ^ 2 + 6) * p
  else 3 * (p + 2) * p ^ 2

/-- The emitted digits. -/
def dig (s : Fin (D p + 4)) : ℕ :=
  if s.1 < D p then s.1 * p / D p
  else if s.1 = D p then cm1 p e * p / D p
  else if s.1 = D p + 1 then 1
  else if s.1 = D p + 2 then c3 p e * p / D p
  else 5

/-- Successors: the far cycle and the two junctions. -/
def nxt (s : Fin (D p + 4)) : List (Fin (D p + 4)) :=
  if s.1 < D p then
    [far p (s.1 * p)] ++ (if s.1 = cm2 p e then [nm1 p] else [])
      ++ (if s.1 = c2 p e then [nm1' p] else [])
  else if s.1 = D p then [n0 p]
  else if s.1 = D p + 1 then [far p (D p - 1)]
  else if s.1 = D p + 2 then [n0' p]
  else [far p (D p - 3)]

/-- The family-II numerator certificate (slack `8/E`). -/
def cert : NumCert p where
  n := D p + 4
  num := num p e
  dig := dig p e
  nxt := nxt p e
  E := E p
  σ := 8

theorem far_mod (c : ℕ) : far p (c % D p) = far p c := by
  unfold far; exact Fin.ext (Nat.mod_mod _ _)
theorem far_val (c : ℕ) : (far p c).1 = c % D p := rfl

theorem num_far (c : ℕ) : num p e (far p c) = (c % D p) * p ^ 3 := by
  simp [num, far_val, Nat.mod_lt _ (D_pos p)]
theorem dig_far (c : ℕ) : dig p e (far p c) = (c % D p) * p / D p := by
  simp [dig, far_val, Nat.mod_lt _ (D_pos p)]
theorem num_nm1 : num p e (nm1 p) = (cm1 p e * p ^ 2 + 2) * p := by simp [num, nm1]
theorem dig_nm1 : dig p e (nm1 p) = cm1 p e * p / D p := by simp [dig, nm1]
theorem num_n0 : num p e (n0 p) = (p + 2) * p ^ 2 := by simp [num, n0]
theorem dig_n0 : dig p e (n0 p) = 1 := by simp [dig, n0]
theorem num_nm1' : num p e (nm1' p) = (c3 p e * p ^ 2 + 6) * p := by simp [num, nm1']
theorem dig_nm1' : dig p e (nm1' p) = c3 p e * p / D p := by simp [dig, nm1']
theorem num_n0' : num p e (n0' p) = 3 * (p + 2) * p ^ 2 := by simp [num, n0']
theorem dig_n0' : dig p e (n0' p) = 5 := by simp [dig, n0']

theorem nxt_nm1 : nxt p e (nm1 p) = [n0 p] := by simp [nxt, nm1]
theorem nxt_n0 : nxt p e (n0 p) = [far p (D p - 1)] := by simp [nxt, n0]
theorem nxt_nm1' : nxt p e (nm1' p) = [n0' p] := by simp [nxt, nm1']
theorem nxt_n0' : nxt p e (n0' p) = [far p (D p - 3)] := by simp [nxt, n0']

theorem far_mul_far (c : ℕ) : far p (c % D p * p) = far p (c * p) := by
  unfold far; apply Fin.ext; simp [Nat.mul_mod]

theorem nxt_far (c : ℕ) : nxt p e (far p c) =
    [far p (c % D p * p)] ++ (if c % D p = cm2 p e then [nm1 p] else [])
      ++ (if c % D p = c2 p e then [nm1' p] else []) := by
  have hlt : (far p c).1 < D p := Nat.mod_lt _ (D_pos p)
  unfold nxt; rw [if_pos hlt]; rfl

/-- The far cycle edge is always present. -/
theorem far_mul_mem (c : ℕ) : far p (c * p) ∈ nxt p e (far p c) := by
  rw [nxt_far, far_mul_far]; simp

/-- Junction 1 is available at `F_{c₋₂}`. -/
theorem nm1_mem : nm1 p ∈ nxt p e (far p (cm2 p e)) := by
  have hc : cm2 p e < D p := Nat.mod_lt _ (D_pos p)
  rw [nxt_far, Nat.mod_eq_of_lt hc, if_pos rfl]; simp

/-- Junction 2 is available at `F_{c₂}`. -/
theorem nm1'_mem : nm1' p ∈ nxt p e (far p (c2 p e)) := by
  have hc : c2 p e < D p := Nat.mod_lt _ (D_pos p)
  rw [nxt_far, Nat.mod_eq_of_lt hc]
  by_cases hj : c2 p e = cm2 p e <;> simp [hj]

/-- Every state is one of five kinds. -/
theorem state_cases (s : Fin (D p + 4)) :
    (∃ c, c < D p ∧ s = far p c) ∨ s = nm1 p ∨ s = n0 p ∨ s = nm1' p ∨ s = n0' p := by
  have hs := s.2
  rcases Nat.lt_or_ge s.1 (D p) with hlt | hge
  · left; exact ⟨s.1, hlt, Fin.ext (by rw [far_val, Nat.mod_eq_of_lt hlt])⟩
  · right
    rcases Nat.lt_or_ge s.1 (D p + 1) with h1 | h1
    · left; exact Fin.ext (by unfold nm1; simp; omega)
    rcases Nat.lt_or_ge s.1 (D p + 2) with h2 | h2
    · right; left; exact Fin.ext (by unfold n0; simp; omega)
    rcases Nat.lt_or_ge s.1 (D p + 3) with h3 | h3
    · right; right; left; exact Fin.ext (by unfold nm1'; simp; omega)
    · right; right; right; exact Fin.ext (by unfold n0'; simp; omega)

/-- The six edge types. -/
theorem mem_nxt {s s' : Fin (D p + 4)} (hs' : s' ∈ nxt p e s) :
    (∃ c, c < D p ∧ s = far p c ∧ s' = far p (c * p)) ∨
    (s = far p (cm2 p e) ∧ s' = nm1 p) ∨
    (s = far p (c2 p e) ∧ s' = nm1' p) ∨
    (s = nm1 p ∧ s' = n0 p) ∨ (s = n0 p ∧ s' = far p (D p - 1)) ∨
    (s = nm1' p ∧ s' = n0' p) ∨ (s = n0' p ∧ s' = far p (D p - 3)) := by
  rcases state_cases p s with ⟨c, hc, rfl⟩ | rfl | rfl | rfl | rfl
  · rw [nxt_far, Nat.mod_eq_of_lt hc] at hs'
    simp only [List.mem_append, List.mem_singleton] at hs'
    rcases hs' with (rfl | h) | h
    · left; exact ⟨c, hc, rfl, rfl⟩
    · split_ifs at h with hj
      · simp only [List.mem_singleton] at h
        right; left; exact ⟨by rw [hj], h⟩
      · simp at h
    · split_ifs at h with hj
      · simp only [List.mem_singleton] at h
        right; right; left; exact ⟨by rw [hj], h⟩
      · simp at h
  · rw [nxt_nm1, List.mem_singleton] at hs'; right; right; right; left; exact ⟨rfl, hs'⟩
  · rw [nxt_n0, List.mem_singleton] at hs'; right; right; right; right; left; exact ⟨rfl, hs'⟩
  · rw [nxt_nm1', List.mem_singleton] at hs'
    right; right; right; right; right; left; exact ⟨rfl, hs'⟩
  · rw [nxt_n0', List.mem_singleton] at hs'
    right; right; right; right; right; right; exact ⟨rfl, hs'⟩

end cert

/-! ### The bound `M = (n² − 2)/3` and the extra keys -/

/-- The family-II channel bound. -/
def bound (p : ℕ) : ℕ := (((p - 1) / 2) ^ 2 - 2) / 3

section edges

variable {p e : ℕ} (h : Hyp p e)
include h

theorem three_mul_le (m : ℕ) (hm : m ≤ bound p) : 3 * m ≤ ((p - 1) / 2) ^ 2 - 2 := by
  unfold bound at hm
  have := Nat.mul_le_mul_left 3 hm
  have := Nat.mul_div_le (((p - 1) / 2) ^ 2 - 2) 3
  omega

theorem c3_lt : c3 p e < D p := Nat.mod_lt _ (D_pos p)
theorem c2_lt : c2 p e < D p := Nat.mod_lt _ (D_pos p)

/-- `c₃ · p ≡ 3 (mod D)`. -/
theorem c3_mul : c3 p e * p % D p = 3 := by
  have hD := D_pos p
  have h3 : 3 < D p := by have := h.ge; unfold D; omega
  unfold c3
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, mul_assoc, Nat.mul_mod, h.cm1_mul, mul_one,
    Nat.mod_mod, Nat.mod_eq_of_lt h3]

/-- `c₂ · p ≡ c₃ (mod D)`. -/
theorem c2_mul : c2 p e * p % D p = c3 p e := by
  unfold c2 c3
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, mul_assoc, Nat.mul_mod, h.cm2_mul]
  conv_rhs => rw [Nat.mul_mod, Nat.mod_eq_of_lt h.cm1_lt]

/-- The junction-2 edge carries `6pm`; needs `6m < p²`. -/
theorem key_junction2 (m : ℕ) (hm : 6 * m < p ^ 2) :
    p * (m * (c2 p e * p ^ 3) % E p) + m * (6 * p) < (p - 1) * E p := by
  unfold E
  rw [show m * (c2 p e * p ^ 3) = p ^ 3 * (m * c2 p e) by ring, Nat.mul_mod_mul_left]
  have hr : m * c2 p e % D p ≤ D p - 1 := Nat.le_sub_one_of_lt (Nat.mod_lt _ (D_pos p))
  obtain ⟨n, hn, rfl, hD⟩ := h.params
  rw [hD] at hr ⊢
  rw [show 2 * n + 1 - 1 = 2 * n by omega]
  have hp3 : 0 < (2 * n + 1) ^ 3 := by positivity
  calc (2 * n + 1) * ((2 * n + 1) ^ 3 * (m * c2 (2 * n + 1) e % (n + 2))) + m * (6 * (2 * n + 1))
      ≤ (2 * n + 1) * ((2 * n + 1) ^ 3 * (n + 1)) + m * (6 * (2 * n + 1)) := by gcongr; omega
    _ < 2 * n * ((2 * n + 1) ^ 3 * (n + 2)) := by nlinarith

/-- The residue of `N₋₁'` at channel `m` is that of `N₋₁` at channel `3m`. -/
theorem res_nm1' (m : ℕ) :
    m * ((c3 p e * p ^ 2 + 6) * p) % E p = 3 * m * ((cm1 p e * p ^ 2 + 2) * p) % E p := by
  have hdm := Nat.div_add_mod (3 * cm1 p e) (D p)
  have hc3 : 3 * cm1 p e % D p = c3 p e := rfl
  rw [hc3] at hdm
  have : 3 * m * ((cm1 p e * p ^ 2 + 2) * p)
      = m * ((c3 p e * p ^ 2 + 6) * p) + (m * (3 * cm1 p e / D p)) * E p := by
    unfold E
    calc 3 * m * ((cm1 p e * p ^ 2 + 2) * p) = m * ((3 * cm1 p e) * p ^ 3 + 6 * p) := by ring
      _ = m * ((D p * (3 * cm1 p e / D p) + c3 p e) * p ^ 3 + 6 * p) := by rw [hdm]
      _ = _ := by ring
  rw [this, Nat.add_mul_mod_self_right]

theorem dig_lt (s : Fin (D p + 4)) : dig p e s < p := by
  have hD := D_pos p
  have hp := h.ge
  have key : ∀ c, c < D p → c * p / D p < p := by
    intro c hc
    rw [Nat.div_lt_iff_lt_mul hD, mul_comm p]
    exact Nat.mul_lt_mul_of_pos_right hc (by omega)
  rcases state_cases p s with ⟨c, hc, rfl⟩ | rfl | rfl | rfl | rfl
  · rw [dig_far, Nat.mod_eq_of_lt hc]; exact key c hc
  · rw [dig_nm1]; exact key _ h.cm1_lt
  · rw [dig_n0]; omega
  · rw [dig_nm1']; exact key _ (c3_lt h)
  · rw [dig_n0']; omega

theorem dig_le (s : Fin (D p + 4)) : dig p e s ≤ p - 2 := by
  have hD := D_pos p
  have hp := h.ge
  have key : ∀ c, c < D p → c * p / D p ≤ p - 2 := by
    intro c hc
    rw [Nat.div_le_iff_le_mul_add_pred hD]
    have : c * p ≤ (D p - 1) * p := Nat.mul_le_mul_right _ (by omega)
    have h2 : (D p - 1) * p ≤ D p * (p - 2) + (D p - 1) := by
      obtain ⟨n, hn, rfl, hD⟩ := h.params
      rw [hD, show n + 2 - 1 = n + 1 by omega, show 2 * n + 1 - 2 = 2 * n - 1 by omega]
      obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
      rw [show 2 * (t + 1) - 1 = 2 * t + 1 by omega]; nlinarith
    exact le_trans this h2
  rcases state_cases p s with ⟨c, hc, rfl⟩ | rfl | rfl | rfl | rfl
  · rw [dig_far, Nat.mod_eq_of_lt hc]; exact key c hc
  · rw [dig_nm1]; exact key _ h.cm1_lt
  · rw [dig_n0]; omega
  · rw [dig_nm1']; exact key _ (c3_lt h)
  · rw [dig_n0']; omega

theorem num_add_eight_le (s : Fin (D p + 4)) : num p e s + 8 ≤ E p := by
  have hc := h.cm1_lt
  have hc3 := c3_lt h
  unfold E
  have key : ∀ c, c < D p → ∀ t, t + 8 ≤ p ^ 3 → c * p ^ 3 + t ≤ p ^ 3 * D p := by
    intro c hc t ht
    have : (c + 1) * p ^ 3 ≤ D p * p ^ 3 := Nat.mul_le_mul_right _ hc
    nlinarith
  have hp3 : 17 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left h.ge 3
  have hp2 : 17 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left h.ge 2
  have hpp : p ^ 3 = p ^ 2 * p := by ring
  have hD4 : 4 ≤ D p := by have := h.ge; unfold D; omega
  rcases state_cases p s with ⟨c, hc, rfl⟩ | rfl | rfl | rfl | rfl
  · rw [num_far, Nat.mod_eq_of_lt hc]; exact key c hc 8 (by omega)
  · rw [num_nm1, show (cm1 p e * p ^ 2 + 2) * p + 8 = cm1 p e * p ^ 3 + (2 * p + 8) by ring]
    exact key _ hc _ (by nlinarith)
  · rw [num_n0]
    have : 2 * p ^ 3 ≤ p ^ 3 * D p := by nlinarith
    nlinarith
  · rw [num_nm1', show (c3 p e * p ^ 2 + 6) * p + 8 = c3 p e * p ^ 3 + (6 * p + 8) by ring]
    exact key _ hc3 _ (by nlinarith)
  · rw [num_n0']
    have : 4 * p ^ 3 ≤ p ^ 3 * D p := by nlinarith
    nlinarith

/-- Every edge: `dig·E + num' = p·num + δ`, `δ ∈ {0, 2p, 6p}`, with its digit
condition for `m ≤ bound p`. -/
theorem edge_data {s s' : Fin (D p + 4)} (hs' : s' ∈ nxt p e s) :
    ∃ δ, δ + 8 < 8 * p ∧ dig p e s * E p + num p e s' = p * num p e s + δ ∧
      ∀ m, m ≤ bound p → p * (m * num p e s % E p) + m * δ < (p - 1) * E p := by
  have hD := D_pos p
  have hp := h.ge
  have hm3 : ∀ m, m ≤ bound p → m ≤ ((p - 1) / 2) ^ 2 - 2 := fun m hm => by
    have := three_mul_le h m hm; omega
  rcases mem_nxt p e hs' with ⟨c, hc, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- far → far
    refine ⟨0, by omega, ?_, ?_⟩
    · rw [dig_far, num_far, num_far, Nat.mod_eq_of_lt hc]
      unfold E
      calc c * p / D p * (p ^ 3 * D p) + c * p % D p * p ^ 3
          = p ^ 3 * (D p * (c * p / D p) + c * p % D p) := by ring
        _ = p ^ 3 * (c * p) := by rw [Nat.div_add_mod]
        _ = p * (c * p ^ 3) + 0 := by ring
    · intro m _
      rw [num_far, Nat.mod_eq_of_lt hc, mul_zero, add_zero]
      exact key_far h c m hc
  · -- junction 1
    have hc2 := h.cm2_lt
    have hmul := h.cm2_mul
    refine ⟨2 * p, by omega, ?_, ?_⟩
    · rw [dig_far, num_far, num_nm1, Nat.mod_eq_of_lt hc2]
      unfold E
      have hdm := Nat.div_add_mod (cm2 p e * p) (D p)
      rw [hmul] at hdm
      calc cm2 p e * p / D p * (p ^ 3 * D p) + (cm1 p e * p ^ 2 + 2) * p
          = p ^ 3 * (D p * (cm2 p e * p / D p) + cm1 p e) + 2 * p := by ring
        _ = p ^ 3 * (cm2 p e * p) + 2 * p := by rw [hdm]
        _ = p * (cm2 p e * p ^ 3) + 2 * p := by ring
    · intro m hm
      rw [num_far, Nat.mod_eq_of_lt hc2]
      apply key_junction h
      have := three_mul_le h m hm
      obtain ⟨n, hn, rfl, hD⟩ := h.params
      rw [show (2 * n + 1 - 1) / 2 = n by omega] at this
      have h4 : 4 ≤ n ^ 2 := by nlinarith
      have h2 : 3 * m + 2 ≤ n ^ 2 := by omega
      nlinarith
  · -- junction 2
    have hc2 := c2_lt h
    have hmul := c2_mul h
    refine ⟨6 * p, by omega, ?_, ?_⟩
    · rw [dig_far, num_far, num_nm1', Nat.mod_eq_of_lt hc2]
      unfold E
      have hdm := Nat.div_add_mod (c2 p e * p) (D p)
      rw [hmul] at hdm
      calc c2 p e * p / D p * (p ^ 3 * D p) + (c3 p e * p ^ 2 + 6) * p
          = p ^ 3 * (D p * (c2 p e * p / D p) + c3 p e) + 6 * p := by ring
        _ = p ^ 3 * (c2 p e * p) + 6 * p := by rw [hdm]
        _ = p * (c2 p e * p ^ 3) + 6 * p := by ring
    · intro m hm
      rw [num_far, Nat.mod_eq_of_lt hc2]
      apply key_junction2 h
      have := three_mul_le h m hm
      obtain ⟨n, hn, rfl, hD⟩ := h.params
      rw [show (2 * n + 1 - 1) / 2 = n by omega] at this
      have h4 : 4 ≤ n ^ 2 := by nlinarith
      have h2 : 3 * m + 2 ≤ n ^ 2 := by omega
      nlinarith
  · -- `N₋₁ → N₀`
    have hmul := h.cm1_mul
    refine ⟨0, by omega, ?_, ?_⟩
    · rw [dig_nm1, num_nm1, num_n0]
      unfold E
      have hdm := Nat.div_add_mod (cm1 p e * p) (D p)
      rw [hmul] at hdm
      calc cm1 p e * p / D p * (p ^ 3 * D p) + (p + 2) * p ^ 2
          = p ^ 3 * (D p * (cm1 p e * p / D p) + 1) + 2 * p ^ 2 := by ring
        _ = p ^ 3 * (cm1 p e * p) + 2 * p ^ 2 := by rw [hdm]
        _ = p * ((cm1 p e * p ^ 2 + 2) * p) + 0 := by ring
    · intro m hm
      rw [num_nm1, mul_zero, add_zero]
      exact key_nm1 h m (hm3 m hm)
  · -- `N₀ → F_{D−1}`
    refine ⟨0, by omega, ?_, ?_⟩
    · rw [dig_n0, num_n0, num_far, Nat.mod_eq_of_lt (by omega)]
      unfold E
      obtain ⟨n, hn, rfl, hD⟩ := h.params
      rw [hD, show n + 2 - 1 = n + 1 by omega]; ring
    · intro m hm
      rw [num_n0, mul_zero, add_zero]
      exact key_n0 h m (hm3 m hm)
  · -- `N₋₁' → N₀'`
    have hmul := c3_mul h
    refine ⟨0, by omega, ?_, ?_⟩
    · rw [dig_nm1', num_nm1', num_n0']
      unfold E
      have hdm := Nat.div_add_mod (c3 p e * p) (D p)
      rw [hmul] at hdm
      calc c3 p e * p / D p * (p ^ 3 * D p) + 3 * (p + 2) * p ^ 2
          = p ^ 3 * (D p * (c3 p e * p / D p) + 3) + 6 * p ^ 2 := by ring
        _ = p ^ 3 * (c3 p e * p) + 6 * p ^ 2 := by rw [hdm]
        _ = p * ((c3 p e * p ^ 2 + 6) * p) + 0 := by ring
    · intro m hm
      rw [num_nm1', mul_zero, add_zero, res_nm1' h]
      exact key_nm1 h (3 * m) (three_mul_le h m hm)
  · -- `N₀' → F_{D−3}`
    refine ⟨0, by omega, ?_, ?_⟩
    · rw [dig_n0', num_n0', num_far, Nat.mod_eq_of_lt (by omega)]
      unfold E
      obtain ⟨n, hn, rfl, hD⟩ := h.params
      rw [hD, show n + 2 - 3 = n - 1 by omega]
      obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
      rw [Nat.add_sub_cancel]; ring
    · intro m hm
      rw [num_n0', mul_zero, add_zero, show m * (3 * (p + 2) * p ^ 2) = 3 * m * ((p + 2) * p ^ 2) by ring]
      exact key_n0 h (3 * m) (three_mul_le h m hm)

/-- Every state has an outgoing edge, hence the `δ = 0`-type bound
`p·((m·num) mod E) < (p−1)E`; then `(m·num) mod E + 8m < E`. -/
theorem res_add_lt (s : Fin (D p + 4)) (m : ℕ) (hm : m ≤ bound p) :
    m * num p e s % E p + 8 * m < E p := by
  have hp := h.p_pos
  -- an edge out of `s`
  have hout : ∃ s', s' ∈ nxt p e s := by
    rcases state_cases p s with ⟨c, hc, rfl⟩ | rfl | rfl | rfl | rfl
    · exact ⟨_, far_mul_mem p e c⟩
    · exact ⟨n0 p, by rw [nxt_nm1]; simp⟩
    · exact ⟨far p (D p - 1), by rw [nxt_n0]; simp⟩
    · exact ⟨n0' p, by rw [nxt_nm1']; simp⟩
    · exact ⟨far p (D p - 3), by rw [nxt_n0']; simp⟩
  obtain ⟨s', hs'⟩ := hout
  obtain ⟨δ, _, _, hkey⟩ := edge_data h hs'
  have hk := hkey m hm
  have h8 : 8 * m < p ^ 2 * D p := by
    have := three_mul_le h m hm
    obtain ⟨n, hn, rfl, hD⟩ := h.params
    rw [show (2 * n + 1 - 1) / 2 = n by omega] at this
    rw [hD]
    have h4 : 4 ≤ n ^ 2 := by nlinarith
    have h2 : 3 * m + 2 ≤ n ^ 2 := by omega
    nlinarith [Nat.zero_le (n ^ 3), Nat.zero_le (n ^ 2)]
  have hE : E p = p * (p ^ 2 * D p) := by unfold E; ring
  by_contra hcon
  push Not at hcon
  have : p * E p ≤ p * (m * num p e s % E p + 8 * m) := Nat.mul_le_mul_left _ hcon
  have h5 : p * (8 * m) < E p := by rw [hE]; nlinarith
  have h6 : (p - 1) * E p + E p = p * E p := by
    rcases Nat.exists_eq_add_of_le hp with ⟨t, ht⟩; rw [ht]; simp; ring
  nlinarith

/-- **The family-II certificate is good** for `M = (n² − 2)/3`. -/
theorem good : (cert p e).Good (bound p) where
  E_pos := h.E_pos
  σ_pos := by show 0 < 8; norm_num
  dig_lt := fun s => dig_lt h s
  num_le := fun s => num_add_eight_le h s
  edge := fun s s' hs' => by
    obtain ⟨δ, hδ, hV, hk⟩ := edge_data h hs'
    exact ⟨δ, by show δ + 8 < 8 * p; omega, hV, hk⟩
  res := fun s m hm => res_add_lt h s m hm

theorem valid : (cert p e).toCert.Valid (bound p) [p - 1] := NumCert.valid h.two_le (good h)

theorem not_hiMax_of_edge {s s' : Fin (D p + 4)} (hs' : s' ∈ nxt p e s) :
    ¬ (cert p e).toCert.HiMax s s' :=
  NumCert.not_hiMax_of_edge h.two_le (good h) hs'

end edges

/-! ### The closed walks -/

/-- The two-junction walk, period `2e + 2`:
`F_{c₋₂}, N₋₁, N₀, F_{−1}, F_{−p}, …, F_{−p^(e−1)} = F_{c₂}, N₋₁', N₀', F_p, …, F_{p^(e−3)}`. -/
def walkA (p e : ℕ) (i : ℕ) : Fin (D p + 4) :=
  if i = 0 then far p (cm2 p e) else if i = 1 then nm1 p else if i = 2 then n0 p
  else if i < e + 3 then far p ((D p - 1) * p ^ (i - 3))
  else if i = e + 3 then nm1' p else if i = e + 4 then n0' p
  else far p (p ^ (i - e - 4))

/-- The pure far cycle from `F_{c₋₂}`. -/
def walkB (p e : ℕ) (i : ℕ) : Fin (D p + 4) := far p (p ^ (e - 2 + i))

section walks

variable {p e : ℕ} (h : Hyp p e) (he : 3 ≤ e)

theorem walkA_zero : walkA p e 0 = far p (cm2 p e) := by simp [walkA]
theorem walkA_one : walkA p e 1 = nm1 p := by simp [walkA]
theorem walkA_two : walkA p e 2 = n0 p := by simp [walkA]
theorem walkA_far1 (i : ℕ) (h3 : 3 ≤ i) (hi : i < e + 3) :
    walkA p e i = far p ((D p - 1) * p ^ (i - 3)) := by
  unfold walkA
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos hi]
theorem walkA_e3 : walkA p e (e + 3) = nm1' p := by
  unfold walkA
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
theorem walkA_e4 : walkA p e (e + 4) = n0' p := by
  unfold walkA
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos rfl]
theorem walkA_far2 (i : ℕ) (hi : e + 5 ≤ i) : walkA p e i = far p (p ^ (i - e - 4)) := by
  unfold walkA
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega)]

theorem far_pow_succ (j : ℕ) : far p (p ^ (j + 1)) = far p (p ^ j * p) := by rw [pow_succ]

theorem far_cm2 : far p (cm2 p e) = far p (p ^ (e - 2)) := by unfold cm2; exact far_mod p _

include h

/-- `(D−1)·p ≡ 3 (mod D)`. -/
theorem Dm1_mul : (D p - 1) * p % D p = 3 := by
  obtain ⟨n, hn, rfl, hD⟩ := h.params
  rw [hD, show n + 2 - 1 = n + 1 by omega,
    show (n + 1) * (2 * n + 1) = 3 + (n + 2) * (2 * n - 1) by
      obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
      rw [show 2 * (t + 1) - 1 = 2 * t + 1 by omega]; ring,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- `p ≡ D − 3 (mod D)`. -/
theorem p_mod : p % D p = D p - 3 := by
  obtain ⟨n, hn, rfl, hD⟩ := h.params
  rw [hD, show 2 * n + 1 = (n - 1) + (n + 2) by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]; omega

/-- `F_{(D−1)p^(e−1)} = F_{c₂}`. -/
theorem far_c2 : far p ((D p - 1) * p ^ (e - 1)) = far p (c2 p e) := by
  have he2 := h.two_le_e
  apply Fin.ext
  rw [far_val, far_val, c2, Nat.mod_mod, cm2, show e - 1 = (e - 2) + 1 by omega, pow_succ,
    show (D p - 1) * (p ^ (e - 2) * p) = ((D p - 1) * p) * p ^ (e - 2) by ring, Nat.mul_mod,
    Dm1_mul h]

theorem dig_top : dig p e (far p (D p - 1)) = p - 2 := by
  rw [dig_far]
  obtain ⟨n, hn, rfl, hD⟩ := h.params
  rw [hD, show n + 2 - 1 = n + 1 by omega, Nat.mod_eq_of_lt (by omega),
    show 2 * n + 1 - 2 = 2 * n - 1 by omega]
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
  rw [show 2 * (t + 1) - 1 = 2 * t + 1 by omega]
  apply Nat.div_eq_of_lt_le <;> nlinarith

theorem dig_p : dig p e (far p p) = p - 6 := by
  rw [dig_far, p_mod h]
  obtain ⟨n, hn, rfl, hD⟩ := h.params
  rw [hD]
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 8 := ⟨n - 8, by omega⟩
  rw [show t + 8 + 2 - 3 = t + 7 by omega, show 2 * (t + 8) + 1 - 6 = 2 * t + 11 by omega]
  apply Nat.div_eq_of_lt_le <;> nlinarith

include he

theorem walkA_closed :
    walkA p e 0 = far p (cm2 p e) ∧
    (∀ i, i + 1 < 2 * e + 2 → walkA p e (i + 1) ∈ nxt p e (walkA p e i)) ∧
    far p (cm2 p e) ∈ nxt p e (walkA p e (2 * e + 2 - 1)) := by
  have hD := D_pos p
  refine ⟨walkA_zero, ?_, ?_⟩
  · intro i hi
    rcases i with _ | _ | _ | i
    · rw [walkA_zero, walkA_one]; exact nm1_mem p e
    · rw [walkA_one, walkA_two, nxt_nm1]; simp
    · rw [walkA_two, walkA_far1 3 le_rfl (by omega), nxt_n0]; simp
    · -- `i + 3 → i + 4`
      rcases Nat.lt_or_ge (i + 4) (e + 3) with h1 | h1
      · rw [walkA_far1 (i + 3) (by omega) (by omega), walkA_far1 (i + 4) (by omega) h1,
          show i + 4 - 3 = (i + 3 - 3) + 1 by omega, pow_succ, ← mul_assoc]
        exact far_mul_mem p e _
      rcases Nat.lt_or_ge (i + 4) (e + 4) with h2 | h2
      · have he3 : i + 4 = e + 3 := by omega
        rw [walkA_far1 (i + 3) (by omega) (by omega), he3, walkA_e3,
          show i + 3 - 3 = e - 1 by omega, far_c2 h]
        exact nm1'_mem p e
      rcases Nat.lt_or_ge (i + 4) (e + 5) with h3 | h3
      · have he4 : i + 4 = e + 4 := by omega
        rw [he4, show i + 3 = e + 3 by omega, walkA_e3, walkA_e4, nxt_nm1']; simp
      rcases Nat.lt_or_ge (i + 4) (e + 6) with h4 | h4
      · have he5 : i + 4 = e + 5 := by omega
        rw [he5, show i + 3 = e + 4 by omega, walkA_e4, walkA_far2 (e + 5) le_rfl, nxt_n0',
          show e + 5 - e - 4 = 1 by omega, pow_one]
        have : far p p = far p (D p - 3) := by
          apply Fin.ext; rw [far_val, far_val, p_mod h, Nat.mod_eq_of_lt (by omega)]
        rw [this]; simp
      · rw [walkA_far2 (i + 3) (by omega), walkA_far2 (i + 4) (by omega),
          show i + 4 - e - 4 = (i + 3 - e - 4) + 1 by omega, far_pow_succ]
        exact far_mul_mem p e _
  · rcases Nat.lt_or_ge e 4 with h3 | h4
    · -- `e = 3`: the last state is `N₀'`, whose successor `F_{D−3} = F_p = F_{c₋₂}`
      have he3 : e = 3 := by omega
      subst he3
      rw [show 2 * 3 + 2 - 1 = 3 + 4 by rfl, walkA_e4, nxt_n0']
      have : far p (cm2 p 3) = far p (D p - 3) := by
        apply Fin.ext
        rw [far_val, far_val, cm2, Nat.mod_mod, show 3 - 2 = 1 by rfl, pow_one, p_mod h,
          Nat.mod_eq_of_lt (by omega)]
      rw [this]; simp
    · rw [show 2 * e + 2 - 1 = 2 * e + 1 by omega, walkA_far2 (2 * e + 1) (by omega),
        show 2 * e + 1 - e - 4 = e - 3 by omega]
      have : far p (cm2 p e) = far p (p ^ (e - 3) * p) := by
        rw [far_cm2, ← pow_succ, show e - 3 + 1 = e - 2 by omega]
      rw [this]; exact far_mul_mem p e _

theorem walkB_closed (L : ℕ) (hL : L = (2 * e + 2) * e) :
    walkB p e 0 = far p (cm2 p e) ∧
    (∀ i, walkB p e (i + 1) ∈ nxt p e (walkB p e i)) ∧
    far p (cm2 p e) ∈ nxt p e (walkB p e (L - 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold walkB; rw [add_zero, far_cm2]
  · intro i; unfold walkB; rw [← add_assoc, far_pow_succ]; exact far_mul_mem p e _
  · unfold walkB
    have hL1 : 1 ≤ L := by rw [hL]; nlinarith
    have : far p (cm2 p e) = far p (p ^ (e - 2 + (L - 1)) * p) := by
      rw [far_cm2, ← pow_succ]
      apply Fin.ext
      rw [far_val, far_val, show e - 2 + (L - 1) + 1 = (e - 2) + (2 * e + 2) * e by omega,
        h.pow_add_mul_e]
    rw [this]; exact far_mul_mem p e _

/-- The witness pair: the two-junction walk repeated `e` times against the far cycle. -/
theorem witness (L : ℕ) (hL : L = (2 * e + 2) * e) (hL0 : 0 < L) :
    (cert p e).toCert.WitnessPair L (fun i : Fin L => walkA p e (i.1 % (2 * e + 2)))
      (fun i : Fin L => walkB p e i.1) hL0 (far p (cm2 p e)) := by
  have hp := h.ge
  have hL8 : 8 ≤ L := by rw [hL]; nlinarith
  obtain ⟨hA0, hAstep, hAclose⟩ := walkA_closed h he
  obtain ⟨hB0, hBstep, hBclose⟩ := walkB_closed h he L hL
  refine ⟨?_, ⟨hB0, fun j _ => hBstep j.1, hBclose⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact EscapeCert.isClosedWalk_periodic (C := (cert p e).toCert) (walkA p e) (2 * e + 2)
      (by omega) _ hA0 hAstep hAclose L e (by rw [hL, mul_comm]) (by omega) hL0
  · refine ⟨⟨0, by omega⟩, ?_⟩
    show dig p e (walkA p e (0 % (2 * e + 2))) ≠ p - 1
    have := dig_le h (walkA p e (0 % (2 * e + 2))); omega
  · refine ⟨⟨0, by omega⟩, ?_⟩
    show dig p e (walkB p e 0) ≠ p - 1
    have := dig_le h (walkB p e 0); omega
  · refine ⟨⟨2, by omega⟩, show 2 + 1 < L by omega, ?_⟩
    simp only [Nat.mod_eq_of_lt (show 2 < 2 * e + 2 by omega),
      Nat.mod_eq_of_lt (show 2 + 1 < 2 * e + 2 by omega)]
    exact not_hiMax_of_edge h (hAstep 2 (by omega))
  · refine ⟨⟨0, by omega⟩, show 0 + 1 < L by omega, ?_⟩
    exact not_hiMax_of_edge h (hBstep 0)
  · refine ⟨⟨3, by omega⟩, ?_⟩
    simp only [NumCert.toCert, cert, Nat.mod_eq_of_lt (show 3 < 2 * e + 2 by omega)]
    rw [walkA_far1 3 le_rfl (by omega), Nat.sub_self, pow_zero, mul_one, dig_top h]
    have hv : walkB p e 3 = far p p := by
      unfold walkB; apply Fin.ext
      rw [far_val, far_val, show e - 2 + 3 = 1 + e by omega, h.pow_add_e, pow_one]
    rw [hv, dig_p h]; omega

end walks

/-! ### The theorem -/

/-- **Family II: `M(p,1) > (⌊p/2⌋² − 2)/3` for every odd `p ≥ 17`** with
`p^e ≡ 1 (mod (p+3)/2)` for some `e ≥ 3` (every prime `p ≥ 17`, by Euler). -/
theorem mahler_lower_bound_family_II (p e : ℕ) (h : Hyp p e) (he : 3 ≤ e) :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ (((p - 1) / 2) ^ 2 - 2) / 3 →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt p ((m : ℝ) * α) [p - 1] n := by
  have hL0 : 0 < (2 * e + 2) * e := by positivity
  exact (cert p e).toCert.escape_mahler_lower_bound h.two_le _ [p - 1] (valid h)
    _ _ _ hL0 _ (witness h he _ rfl hL0)

/-- **The uniform quadratic prime lower bound.**  For every prime `p ≥ 17`,
`M(p,1) > (⌊p/2⌋² − 2)/3`, i.e. `M(p,1) ≥ p²/12 − O(p)`.  The exponent is
`e = 3·φ(D)` with `D = (p+3)/2` (Euler's theorem). -/
theorem mahler_lower_bound_prime_family_II (p : ℕ) (hp : p.Prime) (h17 : 17 ≤ p) :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ (((p - 1) / 2) ^ 2 - 2) / 3 →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt p ((m : ℝ) * α) [p - 1] n := by
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h2 | h2
    · omega
    · exact h2
  have hD : D p = (p + 3) / 2 := by unfold D; omega
  have hDpos : 0 < D p := D_pos p
  have hDlt : D p < p := by unfold D; omega
  have hcop : Nat.Coprime p (D p) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt hDpos hDlt)
  have htot : p ^ Nat.totient (D p) % D p = 1 := by
    have := Nat.ModEq.pow_totient hcop
    unfold Nat.ModEq at this
    rw [this, Nat.mod_eq_of_lt (by unfold D at *; omega)]
  have hφ : 0 < Nat.totient (D p) := Nat.totient_pos.2 hDpos
  refine mahler_lower_bound_family_II p (3 * Nat.totient (D p)) ⟨hodd, h17, ?_, by omega⟩ (by omega)
  rw [pow_mul', Nat.pow_mod, htot, one_pow, Nat.mod_eq_of_lt (by unfold D at *; omega)]

/-- **`M(29,1) ≥ 65`** from family II (`29 ≡ −1 (mod 16)` fails: `−1 ∉ ⟨−3⟩ (mod 16)`,
so family I does not apply; `⌊29/2⌋² = 196`, `(196 − 2)/3 = 64`). -/
theorem mahler_lower_bound_base29' :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ 64 →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt 29 ((m : ℝ) * α) [28] n :=
  mahler_lower_bound_prime_family_II 29 (by norm_num) (by norm_num)

end NormalNumbers.Adder.FamilyII
