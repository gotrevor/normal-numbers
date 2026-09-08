/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.MahlerDriftOne

/-!
# Two junctions over one background: the offset 2-cycle 🧮

`MahlerBackgroundCert.lean` closes a single junction `F_{c₀} → N₋₁ → N₀ → F_land`
back into the orbit of `c₀`, which for a drift-one junction (landing `−c₂`) forces
`−1 ∈ ⟨p⟩ (mod D)` — the arithmetic crux of `MahlerDriftOne.lean`.

This file closes **two** drift-one junctions against each other.  A junction of
offset `b` has source `c₂ = −b/(p+1)` and landing `−c₂ = b/(p+1)`; a second junction
of offset `b'` has source `−b'/(p+1)`.  The first lands in the orbit of the second's
source iff `−b'/b ∈ ⟨p⟩ (mod D)`, and then the second automatically lands back in the
orbit of the first's source (the condition is its own inverse).  At `p ≡ −b'/b`, i.e.
`D ∣ bp + b'`, this is a **closed form**: e.g. `D = (p+2)/3` with `(b, b') = (2, 4)`
for every prime `p ≡ 7 (mod 12)`.  The orbit condition `−1 ∈ ⟨p⟩` disappears.

The certificate: far states `F_c` (`c < D`), and two near chains `N₋₁, N₀` (offset
`b`, source `c₀`) and `N₋₁', N₀'` (offset `b'`, source `c₀'`), slack `σ = 2(b+b')`.
Validity is the two `Keys` of `MahlerBackgroundCert` plus one slack bound; the
per-channel keys are supplied by `DriftOneB.keys` for every channel below
`min(p(p−D), (b−1)pD − D)/b` and the same for `b'`.
-/

namespace NormalNumbers.Adder.Background.Two

open NormalNumbers NormalNumbers.Mahler NormalNumbers.Adder.Background

/-! ### States -/

section states

variable (p D c₀ b c₀' b' : ℕ)

/-- Far state `F_c`, index `c mod D`. -/
def far (c : ℕ) : Fin (D + 4) := ⟨c % D % (D + 4), Nat.mod_lt _ (by omega)⟩
def nm1 : Fin (D + 4) := ⟨D, by omega⟩
def n0 : Fin (D + 4) := ⟨D + 1, by omega⟩
def nm1' : Fin (D + 4) := ⟨D + 2, by omega⟩
def n0' : Fin (D + 4) := ⟨D + 3, by omega⟩

variable {D}

theorem far_val (c : ℕ) (hD : 0 < D) : (far D c).1 = c % D := by
  unfold far; simp only; exact Nat.mod_eq_of_lt (by have := Nat.mod_lt c hD; omega)

theorem far_congr {c c' : ℕ} (h : c % D = c' % D) : far D c = far D c' := by
  unfold far; simp only [Fin.mk.injEq]; rw [h]

theorem far_mod (c : ℕ) : far D (c % D) = far D c := far_congr (Nat.mod_mod _ _)

variable (D)

/-- Tail numerators over `E = p³D`. -/
def num (s : Fin (D + 4)) : ℕ :=
  if s.1 < D then s.1 * p ^ 3
  else if s.1 = D then (c₁ p D c₀ * p ^ 2 + b) * p
  else if s.1 = D + 1 then (c₂ p D c₀ * p + b) * p ^ 2
  else if s.1 = D + 2 then (c₁ p D c₀' * p ^ 2 + b') * p
  else (c₂ p D c₀' * p + b') * p ^ 2

/-- The emitted digits. -/
def dig (s : Fin (D + 4)) : ℕ :=
  if s.1 < D then s.1 * p / D
  else if s.1 = D then c₁ p D c₀ * p / D
  else if s.1 = D + 1 then (c₂ p D c₀ * p + b) / D
  else if s.1 = D + 2 then c₁ p D c₀' * p / D
  else (c₂ p D c₀' * p + b') / D

/-- Successors: the far cycle plus the two junctions. -/
def nxt (s : Fin (D + 4)) : List (Fin (D + 4)) :=
  if s.1 < D then
    [far D (s.1 * p)] ++ (if s.1 = c₀ % D then [nm1 D] else [])
      ++ (if s.1 = c₀' % D then [nm1' D] else [])
  else if s.1 = D then [n0 D]
  else if s.1 = D + 1 then [far D (c₂ p D c₀ * p + b)]
  else if s.1 = D + 2 then [n0' D]
  else [far D (c₂ p D c₀' * p + b')]

/-- The two-junction numerator certificate, slack `σ = 2(b + b')`. -/
def cert : NumCert p where
  n := D + 4
  num := num p D c₀ b c₀' b'
  dig := dig p D c₀ b c₀' b'
  nxt := nxt p D c₀ b c₀' b'
  E := E p D
  σ := 2 * (b + b')

variable {p D c₀ b c₀' b'}

theorem num_far (c : ℕ) (hD : 0 < D) : num p D c₀ b c₀' b' (far D c) = (c % D) * p ^ 3 := by
  unfold num; rw [far_val c hD]; rw [if_pos (Nat.mod_lt _ hD)]
theorem dig_far (c : ℕ) (hD : 0 < D) : dig p D c₀ b c₀' b' (far D c) = (c % D) * p / D := by
  unfold dig; rw [far_val c hD]; rw [if_pos (Nat.mod_lt _ hD)]
theorem num_nm1 : num p D c₀ b c₀' b' (nm1 D) = (c₁ p D c₀ * p ^ 2 + b) * p := by
  unfold num nm1; simp
theorem dig_nm1 : dig p D c₀ b c₀' b' (nm1 D) = c₁ p D c₀ * p / D := by
  unfold dig nm1; simp
theorem num_n0 : num p D c₀ b c₀' b' (n0 D) = (c₂ p D c₀ * p + b) * p ^ 2 := by
  unfold num n0; simp
theorem dig_n0 : dig p D c₀ b c₀' b' (n0 D) = (c₂ p D c₀ * p + b) / D := by
  unfold dig n0; simp
theorem num_nm1' : num p D c₀ b c₀' b' (nm1' D) = (c₁ p D c₀' * p ^ 2 + b') * p := by
  unfold num nm1'; simp
theorem dig_nm1' : dig p D c₀ b c₀' b' (nm1' D) = c₁ p D c₀' * p / D := by
  unfold dig nm1'; simp
theorem num_n0' : num p D c₀ b c₀' b' (n0' D) = (c₂ p D c₀' * p + b') * p ^ 2 := by
  unfold num n0'; simp
theorem dig_n0' : dig p D c₀ b c₀' b' (n0' D) = (c₂ p D c₀' * p + b') / D := by
  unfold dig n0'; simp

theorem nxt_far (c : ℕ) (hD : 0 < D) :
    nxt p D c₀ b c₀' b' (far D c) =
      [far D (c % D * p)] ++ (if c % D = c₀ % D then [nm1 D] else [])
        ++ (if c % D = c₀' % D then [nm1' D] else []) := by
  unfold nxt; rw [far_val c hD, if_pos (Nat.mod_lt _ hD)]
theorem nxt_nm1 : nxt p D c₀ b c₀' b' (nm1 D) = [n0 D] := by unfold nxt nm1; simp
theorem nxt_n0 : nxt p D c₀ b c₀' b' (n0 D) = [far D (c₂ p D c₀ * p + b)] := by
  unfold nxt n0; simp
theorem nxt_nm1' : nxt p D c₀ b c₀' b' (nm1' D) = [n0' D] := by unfold nxt nm1'; simp
theorem nxt_n0' : nxt p D c₀ b c₀' b' (n0' D) = [far D (c₂ p D c₀' * p + b')] := by
  unfold nxt n0'; simp

theorem far_mul_mem (c : ℕ) (hD : 0 < D) :
    far D (c * p) ∈ nxt p D c₀ b c₀' b' (far D c) := by
  rw [nxt_far (c₀ := c₀) (b := b) (c₀' := c₀') (b' := b') c hD]
  have e : far D (c % D * p) = far D (c * p) := far_congr (by simp [Nat.mul_mod])
  simp [e]

theorem nm1_mem (hD : 0 < D) : nm1 D ∈ nxt p D c₀ b c₀' b' (far D c₀) := by
  rw [nxt_far (c₀ := c₀) (b := b) (c₀' := c₀') (b' := b') c₀ hD, if_pos rfl]; simp

theorem nm1'_mem (hD : 0 < D) : nm1' D ∈ nxt p D c₀ b c₀' b' (far D c₀') := by
  rw [nxt_far (c₀ := c₀) (b := b) (c₀' := c₀') (b' := b') c₀' hD]
  rw [if_pos rfl]; simp

/-- Every state is far or one of the four near states. -/
theorem state_cases (s : Fin (D + 4)) :
    (∃ c, c < D ∧ s = far D c) ∨ s = nm1 D ∨ s = n0 D ∨ s = nm1' D ∨ s = n0' D := by
  rcases Nat.lt_or_ge s.1 D with hlt | hge
  · left
    refine ⟨s.1, hlt, Fin.ext ?_⟩
    rw [far_val s.1 (by omega), Nat.mod_eq_of_lt hlt]
  · right
    have hs := s.2
    rcases (show s.1 = D ∨ s.1 = D + 1 ∨ s.1 = D + 2 ∨ s.1 = D + 3 by omega) with h | h | h | h
    · left; exact Fin.ext (by unfold nm1; simp; omega)
    · right; left; exact Fin.ext (by unfold n0; simp; omega)
    · right; right; left; exact Fin.ext (by unfold nm1'; simp; omega)
    · right; right; right; exact Fin.ext (by unfold n0'; simp; omega)

/-- The six edge types. -/
theorem mem_nxt (hD : 0 < D) {s s' : Fin (D + 4)} (hs' : s' ∈ nxt p D c₀ b c₀' b' s) :
    (∃ c, c < D ∧ s = far D c ∧ s' = far D (c * p)) ∨
    (s = far D c₀ ∧ s' = nm1 D) ∨ (s = nm1 D ∧ s' = n0 D) ∨
    (s = n0 D ∧ s' = far D (c₂ p D c₀ * p + b)) ∨
    (s = far D c₀' ∧ s' = nm1' D) ∨ (s = nm1' D ∧ s' = n0' D) ∨
    (s = n0' D ∧ s' = far D (c₂ p D c₀' * p + b')) := by
  rcases state_cases s with ⟨c, hc, rfl⟩ | rfl | rfl | rfl | rfl
  · rw [nxt_far (c₀ := c₀) (b := b) (c₀' := c₀') (b' := b') c hD, Nat.mod_eq_of_lt hc] at hs'
    simp only [List.append_assoc, List.mem_append, List.mem_singleton] at hs'
    rcases hs' with rfl | hs' | hs'
    · left; exact ⟨c, hc, rfl, rfl⟩
    · split_ifs at hs' with hj
      · simp only [List.mem_singleton] at hs'
        right; left
        exact ⟨far_congr (by rw [Nat.mod_eq_of_lt hc, hj]), hs'⟩
      · simp at hs'
    · split_ifs at hs' with hj
      · simp only [List.mem_singleton] at hs'
        right; right; right; right; left
        exact ⟨far_congr (by rw [Nat.mod_eq_of_lt hc, hj]), hs'⟩
      · simp at hs'
  · rw [nxt_nm1, List.mem_singleton] at hs'
    right; right; left; exact ⟨rfl, hs'⟩
  · rw [nxt_n0, List.mem_singleton] at hs'
    right; right; right; left; exact ⟨rfl, hs'⟩
  · rw [nxt_nm1', List.mem_singleton] at hs'
    right; right; right; right; right; left; exact ⟨rfl, hs'⟩
  · rw [nxt_n0', List.mem_singleton] at hs'
    right; right; right; right; right; right; exact ⟨rfl, hs'⟩

end states

/-! ### Validity -/

section good

variable {p D c₀ b c₀' b' M : ℕ}

/-- The residue bound from the digit bound: `pX < (p−1)E` and `σm < p²D` give
`X + σm < E`. -/
theorem res_of_dig (hp : 0 < p) {X σ m : ℕ} (hX : p * X < (p - 1) * E p D)
    (hσ : σ * m < p ^ 2 * D) : X + σ * m < E p D := by
  have e1 : (p - 1) * E p D + E p D = p * E p D := by
    rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ hp)]
  have e2 : p * (p ^ 2 * D) = E p D := by unfold E; ring
  have h1 : p * (σ * m) < p * (p ^ 2 * D) := Nat.mul_lt_mul_of_pos_left hσ hp
  have h2 : p * (X + σ * m) < p * E p D := by
    rw [Nat.mul_add]; omega
  exact Nat.lt_of_mul_lt_mul_left h2

theorem dig_lt (h : Hyp p D b) (h' : Hyp p D b') (s : Fin (D + 4)) :
    dig p D c₀ b c₀' b' s < p := by
  have hD := h.hD
  have hbp := h.b_lt
  have hbp' := h'.b_lt
  have key : ∀ c : ℕ, c < D → c * p / D < p := by
    intro c hc
    rw [Nat.div_lt_iff_lt_mul hD, mul_comm p]
    exact Nat.mul_lt_mul_of_pos_right hc (by omega)
  have key2 : ∀ c x : ℕ, c < D → x < p → (c * p + x) / D < p := by
    intro c x hc hx
    rw [Nat.div_lt_iff_lt_mul hD]
    have h1 : c * p + p ≤ D * p := by
      have := Nat.mul_le_mul_right p (show c + 1 ≤ D by omega)
      rw [Nat.add_mul, one_mul] at this; exact this
    have e : D * p = p * D := by ring
    omega
  rcases state_cases s with ⟨c, hc, rfl⟩ | rfl | rfl | rfl | rfl
  · rw [dig_far c hD, Nat.mod_eq_of_lt hc]; exact key c hc
  · rw [dig_nm1]; exact key _ (c₁_lt hD)
  · rw [dig_n0]; exact key2 _ _ (c₂_lt hD) hbp
  · rw [dig_nm1']; exact key _ (c₁_lt hD)
  · rw [dig_n0']; exact key2 _ _ (c₂_lt hD) hbp'

theorem num_add_le (h : Hyp p D b) (h' : Hyp p D b') (s : Fin (D + 4)) :
    num p D c₀ b c₀' b' s + 2 * (b + b') ≤ E p D := by
  have hD := h.hD
  have hp := h.hp
  have hbp : b + 1 < p := by have := h.hbD; have := h.hD; omega
  have hbp' : b' + 1 < p := by have := h'.hbD; have := h'.hD; omega
  have key : ∀ c : ℕ, c < D → ∀ x : ℕ, x ≤ p ^ 3 → c * p ^ 3 + x ≤ E p D := by
    intro c hc x hx
    unfold E
    have h1 : c * p ^ 3 + p ^ 3 ≤ D * p ^ 3 := by
      have := Nat.mul_le_mul_right (p ^ 3) (show c + 1 ≤ D by omega)
      rw [Nat.add_mul, one_mul] at this; exact this
    have e : D * p ^ 3 = p ^ 3 * D := by ring
    omega
  -- `β·x + 2(b + b') ≤ p³` for `β ∈ {b, b'}`, `x ≤ p²`
  have hcase : ∀ β x : ℕ, β + 1 < p → x ≤ p ^ 2 → β * x + 2 * (b + b') ≤ p ^ 3 := by
    intro β x hβ hx
    have h1 : β * x ≤ (p - 2) * p ^ 2 := Nat.mul_le_mul (by omega) hx
    have h2 : (p - 2) * p ^ 2 + 2 * p ^ 2 = p ^ 3 := by
      rw [Nat.sub_mul, Nat.sub_add_cancel (by nlinarith)]; ring
    have h3 : 2 * (b + b') ≤ 2 * p ^ 2 := by nlinarith
    omega
  rcases state_cases s with ⟨c, hc, rfl⟩ | rfl | rfl | rfl | rfl
  · rw [num_far c hD, Nat.mod_eq_of_lt hc]
    exact key c hc _ (by have := hcase b 0 hbp (by positivity); simpa using this)
  · rw [num_nm1]
    have e0 : (c₁ p D c₀ * p ^ 2 + b) * p = c₁ p D c₀ * p ^ 3 + b * p := by ring
    rw [e0, add_assoc]
    exact key _ (c₁_lt hD) _ (hcase b p hbp (by nlinarith))
  · rw [num_n0]
    have e0 : (c₂ p D c₀ * p + b) * p ^ 2 = c₂ p D c₀ * p ^ 3 + b * p ^ 2 := by ring
    rw [e0, add_assoc]
    exact key _ (c₂_lt hD) _ (hcase b (p ^ 2) hbp le_rfl)
  · rw [num_nm1']
    have e0 : (c₁ p D c₀' * p ^ 2 + b') * p = c₁ p D c₀' * p ^ 3 + b' * p := by ring
    rw [e0, add_assoc]
    exact key _ (c₁_lt hD) _ (hcase b' p hbp' (by nlinarith))
  · rw [num_n0']
    have e0 : (c₂ p D c₀' * p + b') * p ^ 2 = c₂ p D c₀' * p ^ 3 + b' * p ^ 2 := by ring
    rw [e0, add_assoc]
    exact key _ (c₂_lt hD) _ (hcase b' (p ^ 2) hbp' le_rfl)

/-- The numerator identity and digit key of the junction edge `F_{c₀} → N₋₁`
(generic in the junction). -/
theorem junction_edge (h : Hyp p D b) (K : Keys p D c₀ b M) :
    dig p D c₀ b c₀' b' (far D c₀) * E p D + (c₁ p D c₀ * p ^ 2 + b) * p
        = p * num p D c₀ b c₀' b' (far D c₀) + b * p ∧
      ∀ m, m ≤ M → p * (m * num p D c₀ b c₀' b' (far D c₀) % E p D) + m * (b * p)
        < (p - 1) * E p D := by
  have hD := h.hD
  constructor
  · rw [dig_far c₀ hD, num_far c₀ hD]
    unfold E c₁
    have hmm : c₀ * p % D = c₀ % D * p % D := by simp [Nat.mul_mod]
    have hdm := Nat.div_add_mod (c₀ % D * p) D
    rw [← hmm] at hdm
    calc c₀ % D * p / D * (p ^ 3 * D) + (c₀ * p % D * p ^ 2 + b) * p
        = p ^ 3 * (D * (c₀ % D * p / D) + c₀ * p % D) + b * p := by ring
      _ = p ^ 3 * (c₀ % D * p) + b * p := by rw [hdm]
      _ = p * (c₀ % D * p ^ 3) + b * p := by ring
  · intro m hm
    rw [num_far c₀ hD]
    have e : m * (c₀ % D * p ^ 3) % E p D = m * (c₀ * p ^ 3) % E p D := by
      unfold E
      rw [show m * (c₀ % D * p ^ 3) = p ^ 3 * (m * (c₀ % D)) by ring,
        show m * (c₀ * p ^ 3) = p ^ 3 * (m * c₀) by ring,
        Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
    rw [e]
    exact key_jump h K.keyJ m hm

/-- `N₋₁ → N₀` numerator identity (generic). -/
theorem chain_identity (c₀ b : ℕ) :
    c₁ p D c₀ * p / D * E p D + (c₂ p D c₀ * p + b) * p ^ 2
      = p * ((c₁ p D c₀ * p ^ 2 + b) * p) + 0 := by
  unfold E c₂ c₁
  have hmm : c₀ * p ^ 2 % D = c₀ * p % D * p % D := by
    rw [show c₀ * p ^ 2 = c₀ * p * p by ring]; simp [Nat.mul_mod]
  have hdm := Nat.div_add_mod (c₀ * p % D * p) D
  rw [← hmm] at hdm
  calc c₀ * p % D * p / D * (p ^ 3 * D) + (c₀ * p ^ 2 % D * p + b) * p ^ 2
      = p ^ 3 * (D * (c₀ * p % D * p / D) + c₀ * p ^ 2 % D) + b * p ^ 2 := by ring
    _ = p ^ 3 * (c₀ * p % D * p) + b * p ^ 2 := by rw [hdm]
    _ = p * ((c₀ * p % D * p ^ 2 + b) * p) + 0 := by ring

/-- `N₀ → F_land` numerator identity (generic). -/
theorem land_identity (c₀ b : ℕ) :
    (c₂ p D c₀ * p + b) / D * E p D + (c₂ p D c₀ * p + b) % D * p ^ 3
      = p * ((c₂ p D c₀ * p + b) * p ^ 2) + 0 := by
  unfold E
  calc (c₂ p D c₀ * p + b) / D * (p ^ 3 * D) + (c₂ p D c₀ * p + b) % D * p ^ 3
      = p ^ 3 * (D * ((c₂ p D c₀ * p + b) / D) + (c₂ p D c₀ * p + b) % D) := by ring
    _ = p ^ 3 * (c₂ p D c₀ * p + b) := by rw [Nat.div_add_mod]
    _ = p * ((c₂ p D c₀ * p + b) * p ^ 2) + 0 := by ring

theorem edge_data (h : Hyp p D b) (h' : Hyp p D b') (K : Keys p D c₀ b M)
    (K' : Keys p D c₀' b' M) {s s' : Fin (D + 4)} (hs' : s' ∈ nxt p D c₀ b c₀' b' s) :
    ∃ δ, (δ = 0 ∨ δ = b * p ∨ δ = b' * p) ∧
      dig p D c₀ b c₀' b' s * E p D + num p D c₀ b c₀' b' s'
        = p * num p D c₀ b c₀' b' s + δ ∧
      ∀ m, m ≤ M → p * (m * num p D c₀ b c₀' b' s % E p D) + m * δ < (p - 1) * E p D := by
  have hD := h.hD
  rcases mem_nxt hD hs' with ⟨c, hc, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨0, Or.inl rfl, ?_, ?_⟩
    · rw [dig_far c hD, num_far c hD, num_far (c₀ := c₀) (b := b) (c₀' := c₀') (b' := b')
        (c * p) hD, Nat.mod_eq_of_lt hc]
      unfold E
      calc c * p / D * (p ^ 3 * D) + c * p % D * p ^ 3
          = p ^ 3 * (D * (c * p / D) + c * p % D) := by ring
        _ = p ^ 3 * (c * p) := by rw [Nat.div_add_mod]
        _ = p * (c * p ^ 3) + 0 := by ring
    · intro m _
      rw [num_far c hD, Nat.mod_eq_of_lt hc, mul_zero, add_zero]
      exact key_far h c m
  · obtain ⟨h1, h2⟩ := junction_edge (c₀' := c₀') (b' := b') h K
    exact ⟨b * p, Or.inr (Or.inl rfl), by rw [num_nm1]; exact h1, h2⟩
  · refine ⟨0, Or.inl rfl, ?_, ?_⟩
    · rw [dig_nm1, num_nm1, num_n0]; exact chain_identity c₀ b
    · intro m hm
      rw [num_nm1, mul_zero, add_zero]
      exact key_nm1 h m (K.keyA m hm)
  · refine ⟨0, Or.inl rfl, ?_, ?_⟩
    · rw [dig_n0, num_n0, num_far (c₀ := c₀) (b := b) (c₀' := c₀') (b' := b') _ hD]
      exact land_identity c₀ b
    · intro m hm
      rw [num_n0, mul_zero, add_zero]
      exact key_n0 h m (K.keyB m hm)
  · obtain ⟨h1, h2⟩ := junction_edge (c₀' := c₀) (b' := b) h' K'
    refine ⟨b' * p, Or.inr (Or.inr rfl), ?_, ?_⟩
    · rw [num_nm1']
      have e1 : dig p D c₀ b c₀' b' (far D c₀') = dig p D c₀' b' c₀ b (far D c₀') := by
        rw [dig_far _ hD, dig_far _ hD]
      have e2 : num p D c₀ b c₀' b' (far D c₀') = num p D c₀' b' c₀ b (far D c₀') := by
        rw [num_far _ hD, num_far _ hD]
      rw [e1, e2]; exact h1
    · have e2 : num p D c₀ b c₀' b' (far D c₀') = num p D c₀' b' c₀ b (far D c₀') := by
        rw [num_far _ hD, num_far _ hD]
      rw [e2]; exact h2
  · refine ⟨0, Or.inl rfl, ?_, ?_⟩
    · rw [dig_nm1', num_nm1', num_n0']; exact chain_identity c₀' b'
    · intro m hm
      rw [num_nm1', mul_zero, add_zero]
      exact key_nm1 h' m (K'.keyA m hm)
  · refine ⟨0, Or.inl rfl, ?_, ?_⟩
    · rw [dig_n0', num_n0', num_far (c₀ := c₀) (b := b) (c₀' := c₀') (b' := b') _ hD]
      exact land_identity c₀' b'
    · intro m hm
      rw [num_n0', mul_zero, add_zero]
      exact key_n0 h' m (K'.keyB m hm)

/-- Every state has the digit key with `δ = 0` (used for the residue bound). -/
theorem dig_key (h : Hyp p D b) (h' : Hyp p D b') (K : Keys p D c₀ b M)
    (K' : Keys p D c₀' b' M) (s : Fin (D + 4)) (m : ℕ) (hm : m ≤ M) :
    p * (m * num p D c₀ b c₀' b' s % E p D) < (p - 1) * E p D := by
  have hD := h.hD
  rcases state_cases s with ⟨c, hc, rfl⟩ | rfl | rfl | rfl | rfl
  · rw [num_far c hD, Nat.mod_eq_of_lt hc]; simpa using key_far h c m
  · rw [num_nm1]; exact key_nm1 h m (K.keyA m hm)
  · rw [num_n0]; exact key_n0 h m (K.keyB m hm)
  · rw [num_nm1']; exact key_nm1 h' m (K'.keyA m hm)
  · rw [num_n0']; exact key_n0 h' m (K'.keyB m hm)

/-- **The two-junction certificate is good** up to channel `M`. -/
theorem good (h : Hyp p D b) (h' : Hyp p D b') (K : Keys p D c₀ b M)
    (K' : Keys p D c₀' b' M) (hσ : 2 * (b + b') * M < p ^ 2 * D) :
    (cert p D c₀ b c₀' b').Good M where
  E_pos := h.E_pos
  σ_pos := by have := h.hb; show 0 < 2 * (b + b'); omega
  dig_lt := fun s => dig_lt h h' s
  num_le := fun s => num_add_le h h' s
  edge := fun s s' hs' => by
    obtain ⟨δ, hδ, hV, hk⟩ := edge_data h h' K K' hs'
    refine ⟨δ, ?_, hV, hk⟩
    have h3 := h.hp
    have hb := h.hb
    have hb' := h'.hb
    show δ + 2 * (b + b') < 2 * (b + b') * p
    rcases hδ with rfl | rfl | rfl <;> nlinarith
  res := fun s m hm => by
    have hp : 0 < p := by have := h.hp; omega
    exact res_of_dig hp (dig_key h h' K K' s m hm)
      (lt_of_le_of_lt (Nat.mul_le_mul_left _ hm) hσ)

theorem valid (h : Hyp p D b) (h' : Hyp p D b') (K : Keys p D c₀ b M)
    (K' : Keys p D c₀' b' M) (hσ : 2 * (b + b') * M < p ^ 2 * D) :
    (cert p D c₀ b c₀' b').toCert.Valid M [p - 1] :=
  NumCert.valid h.two_le (good h h' K K' hσ)

theorem not_hiMax_of_edge (h : Hyp p D b) (h' : Hyp p D b') (K : Keys p D c₀ b M)
    (K' : Keys p D c₀' b' M) (hσ : 2 * (b + b') * M < p ^ 2 * D)
    {s s' : Fin (D + 4)} (hs' : s' ∈ nxt p D c₀ b c₀' b' s) :
    ¬ (cert p D c₀ b c₀' b').toCert.HiMax s s' :=
  NumCert.not_hiMax_of_edge h.two_le (good h h' K K' hσ) hs'

end good

/-! ### Closure and the two walks -/

/-- Closure data: `p^e ≡ 1 (mod D)`; junction 1 lands on `c₀'p^j`, junction 2 lands on
`c₀p^j'`; and the first landing differs from `c₀p³`. -/
structure Closure (p D c₀ b c₀' b' e j j' : ℕ) : Prop where
  hD2 : 2 ≤ D
  he : 0 < e
  hj : j < e
  hj' : j' < e
  hpow : p ^ e % D = 1
  hland : (c₂ p D c₀ * p + b) % D = c₀' * p ^ j % D
  hland' : (c₂ p D c₀' * p + b') % D = c₀ * p ^ j' % D
  hne : c₀' * p ^ j % D ≠ c₀ * p ^ 3 % D

/-- The period of the junction walk: `T = e − j + 3` far-or-near steps to reach
`F_{c₀'}`, then `3 + (e − j')` more. -/
def T (e j : ℕ) : ℕ := e - j + 3
def per (e j j' : ℕ) : ℕ := T e j + 3 + (e - j')

/-- The walk through both junctions. -/
def walkA (p D c₀ c₀' e j j' : ℕ) (i : ℕ) : Fin (D + 4) :=
  if i = 0 then far D c₀ else if i = 1 then nm1 D else if i = 2 then n0 D
  else if i ≤ T e j then far D (c₀' * p ^ (j + (i - 3)))
  else if i = T e j + 1 then nm1' D else if i = T e j + 2 then n0' D
  else far D (c₀ * p ^ (j' + (i - T e j - 3)))

/-- The pure far cycle from `F_{c₀}`. -/
def walkB (p D c₀ : ℕ) (i : ℕ) : Fin (D + 4) := far D (c₀ * p ^ i)

section walks

variable {p D c₀ b c₀' b' M e j j' : ℕ}

theorem walkA_zero : walkA p D c₀ c₀' e j j' 0 = far D c₀ := by simp [walkA]
theorem walkA_one : walkA p D c₀ c₀' e j j' 1 = nm1 D := by simp [walkA]
theorem walkA_two : walkA p D c₀ c₀' e j j' 2 = n0 D := by simp [walkA]
theorem walkA_mid (i : ℕ) (hi : 3 ≤ i) (hi' : i ≤ T e j) :
    walkA p D c₀ c₀' e j j' i = far D (c₀' * p ^ (j + (i - 3))) := by
  unfold walkA; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos hi']
theorem walkA_T1 : walkA p D c₀ c₀' e j j' (T e j + 1) = nm1' D := by
  unfold walkA; simp [T]
theorem walkA_T2 : walkA p D c₀ c₀' e j j' (T e j + 2) = n0' D := by
  unfold walkA; simp [T]
theorem walkA_late (i : ℕ) (hi : T e j + 3 ≤ i) :
    walkA p D c₀ c₀' e j j' i = far D (c₀ * p ^ (j' + (i - T e j - 3))) := by
  unfold walkA
  have h3 : 3 ≤ T e j := by unfold T; omega
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega)]

theorem far_pow_e (hpow : p ^ e % D = 1) (c : ℕ) : far D (c * p ^ e) = far D c :=
  far_congr (by rw [Nat.mul_mod, hpow, mul_one, Nat.mod_mod])

theorem far_pow_mul_e (hpow : p ^ e % D = 1) (hD2 : 2 ≤ D) (c t : ℕ) :
    far D (c * p ^ (e * t)) = far D c :=
  far_congr (by rw [Nat.mul_mod, pow_mul_e hpow hD2 t, mul_one, Nat.mod_mod])

/-- The junction walk is closed with period `per e j j'`. -/
theorem walkA_closed (h : Hyp p D b) (C : Closure p D c₀ b c₀' b' e j j') :
    walkA p D c₀ c₀' e j j' 0 = far D c₀ ∧
    (∀ i, i + 1 < per e j j' →
      walkA p D c₀ c₀' e j j' (i + 1) ∈ nxt p D c₀ b c₀' b' (walkA p D c₀ c₀' e j j' i)) ∧
    far D c₀ ∈ nxt p D c₀ b c₀' b' (walkA p D c₀ c₀' e j j' (per e j j' - 1)) := by
  have hD := h.hD
  have hj := C.hj
  have hj' := C.hj'
  have he := C.he
  have hT : T e j = e - j + 3 := rfl
  have hper : per e j j' = T e j + 3 + (e - j') := rfl
  refine ⟨walkA_zero, ?_, ?_⟩
  · intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ (3 ≤ i ∧ i + 1 ≤ T e j) ∨ i = T e j ∨
        i = T e j + 1 ∨ i = T e j + 2 ∨ T e j + 3 ≤ i by omega)
      with rfl | rfl | rfl | ⟨h3, hiT⟩ | rfl | rfl | rfl | hlate
    · rw [walkA_zero, walkA_one]; exact nm1_mem hD
    · rw [walkA_one, walkA_two, nxt_nm1]; simp
    · rw [walkA_two, walkA_mid 3 le_rfl (by omega), nxt_n0]
      have ee : far D (c₀' * p ^ (j + (3 - 3))) = far D (c₂ p D c₀ * p + b) := by
        simp only [Nat.sub_self, add_zero]
        exact (far_congr C.hland).symm
      rw [ee]; simp
    · rw [walkA_mid i h3 (by omega), walkA_mid (i + 1) (by omega) hiT,
        show j + (i + 1 - 3) = (j + (i - 3)) + 1 by omega, pow_succ, ← mul_assoc]
      exact far_mul_mem _ hD
    · rw [walkA_mid (T e j) (by omega) le_rfl, walkA_T1,
        show j + (T e j - 3) = e by omega, far_pow_e C.hpow]
      exact nm1'_mem hD
    · rw [walkA_T1, walkA_T2, nxt_nm1']; simp
    · rw [walkA_T2, walkA_late (T e j + 3) le_rfl, nxt_n0']
      have ee : far D (c₀ * p ^ (j' + (T e j + 3 - T e j - 3))) =
          far D (c₂ p D c₀' * p + b') := by
        rw [show T e j + 3 - T e j - 3 = 0 by omega, add_zero]
        exact (far_congr C.hland').symm
      rw [ee]; simp
    · rw [walkA_late i hlate, walkA_late (i + 1) (by omega),
        show j' + (i + 1 - T e j - 3) = (j' + (i - T e j - 3)) + 1 by omega, pow_succ,
        ← mul_assoc]
      exact far_mul_mem _ hD
  · have hge : T e j + 3 ≤ per e j j' - 1 := by omega
    rw [walkA_late _ hge, show j' + (per e j j' - 1 - T e j - 3) = e - 1 by omega]
    have e1 : far D c₀ = far D (c₀ * p ^ (e - 1) * p) := by
      rw [mul_assoc, ← pow_succ, show e - 1 + 1 = e by omega]
      exact (far_pow_e C.hpow c₀).symm
    rw [e1]; exact far_mul_mem _ hD

theorem walkB_closed (h : Hyp p D b) (C : Closure p D c₀ b c₀' b' e j j') (L : ℕ)
    (hL : L = e * per e j j') :
    walkB p D c₀ 0 = far D c₀ ∧
    (∀ i, walkB p D c₀ (i + 1) ∈ nxt p D c₀ b c₀' b' (walkB p D c₀ i)) ∧
    far D c₀ ∈ nxt p D c₀ b c₀' b' (walkB p D c₀ (L - 1)) := by
  have hD := h.hD
  have he := C.he
  have hper : 1 ≤ per e j j' := by unfold per T; omega
  have hL1 : 1 ≤ L := by rw [hL]; nlinarith
  refine ⟨by simp [walkB], ?_, ?_⟩
  · intro i; unfold walkB; rw [pow_succ, ← mul_assoc]; exact far_mul_mem _ hD
  · unfold walkB
    have e1 : far D c₀ = far D (c₀ * p ^ (L - 1) * p) := by
      rw [mul_assoc, ← pow_succ, show L - 1 + 1 = L by omega, hL]
      exact (far_pow_mul_e C.hpow C.hD2 c₀ _).symm
    rw [e1]; exact far_mul_mem _ hD

theorem dig_far_le (h : Hyp p D b) (c : ℕ) : dig p D c₀ b c₀' b' (far D c) ≤ p - 2 := by
  have := Background.dig_far_le (c₀ := c₀) h c
  rwa [Background.dig_far c h.hD, ← dig_far (c₀ := c₀) (b := b) (c₀' := c₀') (b' := b') c h.hD]
    at this

theorem dig_far_ne (h : Hyp p D b) {x y : ℕ} (hxy : x % D ≠ y % D) :
    dig p D c₀ b c₀' b' (far D x) ≠ dig p D c₀ b c₀' b' (far D y) := by
  have := Background.dig_far_ne (c₀ := c₀) (b := b) h hxy
  rwa [Background.dig_far x h.hD, Background.dig_far y h.hD,
    ← dig_far (c₀ := c₀) (b := b) (c₀' := c₀') (b' := b') x h.hD,
    ← dig_far (c₀ := c₀) (b := b) (c₀' := c₀') (b' := b') y h.hD] at this

theorem witness (h : Hyp p D b) (h' : Hyp p D b') (K : Keys p D c₀ b M)
    (K' : Keys p D c₀' b' M) (hσ : 2 * (b + b') * M < p ^ 2 * D)
    (C : Closure p D c₀ b c₀' b' e j j') (L : ℕ) (hL : L = e * per e j j') (hL0 : 0 < L) :
    (cert p D c₀ b c₀' b').toCert.WitnessPair L
      (fun i : Fin L => walkA p D c₀ c₀' e j j' (i.1 % per e j j'))
      (fun i : Fin L => walkB p D c₀ i.1) hL0 (far D c₀) := by
  have hD := h.hD
  have hp := h.hp
  have hj := C.hj
  have he := C.he
  have hl4 : 4 ≤ per e j j' := by unfold per T; omega
  have hL4 : 4 ≤ L := by rw [hL]; nlinarith
  obtain ⟨hA0, hAstep, hAclose⟩ := walkA_closed h C
  obtain ⟨hB0, hBstep, hBclose⟩ := walkB_closed h C L hL
  refine ⟨?_, ⟨hB0, fun i _ => hBstep i.1, hBclose⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact EscapeCert.isClosedWalk_periodic (C := (cert p D c₀ b c₀' b').toCert)
      (walkA p D c₀ c₀' e j j') (per e j j') (by omega) _ hA0 hAstep hAclose L e hL
      (by omega) hL0
  · refine ⟨⟨0, by omega⟩, ?_⟩
    show dig p D c₀ b c₀' b' (walkA p D c₀ c₀' e j j' (0 % per e j j')) ≠ p - 1
    rw [Nat.zero_mod, walkA_zero]
    have := dig_far_le (c₀ := c₀) (b := b) (c₀' := c₀') (b' := b') h c₀
    omega
  · refine ⟨⟨0, by omega⟩, ?_⟩
    show dig p D c₀ b c₀' b' (walkB p D c₀ 0) ≠ p - 1
    unfold walkB
    have := dig_far_le (c₀ := c₀) (b := b) (c₀' := c₀') (b' := b') h (c₀ * p ^ 0)
    omega
  · refine ⟨⟨0, by omega⟩, show 0 + 1 < L by omega, ?_⟩
    simp only [Nat.zero_mod, Nat.mod_eq_of_lt (show 0 + 1 < per e j j' by omega)]
    exact not_hiMax_of_edge h h' K K' hσ (hAstep 0 (by omega))
  · refine ⟨⟨0, by omega⟩, show 0 + 1 < L by omega, ?_⟩
    exact not_hiMax_of_edge h h' K K' hσ (hBstep 0)
  · refine ⟨⟨3, by omega⟩, ?_⟩
    show dig p D c₀ b c₀' b' (walkA p D c₀ c₀' e j j' (3 % per e j j'))
      ≠ dig p D c₀ b c₀' b' (walkB p D c₀ 3)
    rw [Nat.mod_eq_of_lt (show 3 < per e j j' by omega), walkA_mid 3 le_rfl (by unfold T; omega)]
    unfold walkB
    simp only [Nat.sub_self, add_zero]
    exact dig_far_ne h C.hne

end walks

/-! ### The theorem -/

/-- **The two-junction background theorem.** -/
theorem mahler_lower_bound_two_junction (p D c₀ b c₀' b' M e j j' : ℕ)
    (h : Hyp p D b) (h' : Hyp p D b') (K : Keys p D c₀ b M) (K' : Keys p D c₀' b' M)
    (hσ : 2 * (b + b') * M < p ^ 2 * D) (C : Closure p D c₀ b c₀' b' e j j') :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ M →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt p ((m : ℝ) * α) [p - 1] n := by
  have he := C.he
  have hper : 0 < per e j j' := by unfold per T; omega
  have hL0 : 0 < e * per e j j' := by positivity
  exact (cert p D c₀ b c₀' b').toCert.escape_mahler_lower_bound h.two_le _ [p - 1]
    (valid h h' K K' hσ) _ _ _ hL0 _ (witness h h' K K' hσ C _ rfl hL0)

/-! ### The offset 2-cycle: closure from `D ∣ bp + b'` -/

section cycle

variable {p D c₀ b c₀' b' : ℕ}

/-- A junction source of offset `b` exists whenever `gcd(D, p(p+1)) = 1`:
`c₀ = (D − b mod D)·(p²(p+1))⁻¹`. -/
theorem exists_source (p D b : ℕ) (hD : 1 < D) (hcop : Nat.Coprime D (p * (p + 1))) :
    ∃ c₀, (c₂ p D c₀ * (p + 1) + b) % D = 0 := by
  have hcop' : Nat.Coprime (p ^ 2 * (p + 1)) D := by
    have h1 : Nat.Coprime (p * (p + 1)) D := hcop.symm
    have hp : Nat.Coprime p D := Nat.Coprime.coprime_mul_right h1
    have hp1 : Nat.Coprime (p + 1) D := Nat.Coprime.coprime_mul_left h1
    exact Nat.Coprime.mul_left (hp.pow_left 2) hp1
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop' hD
  refine ⟨(D - b % D) * u, ?_⟩
  have hu' : ((p ^ 2 * (p + 1) * u : ℕ) : ZMod D) = 1 := by
    rw [show (1 : ZMod D) = ((1 : ℕ) : ZMod D) by simp, ZMod.natCast_eq_natCast_iff', hu,
      Nat.mod_eq_of_lt hD]
  have hDZ : ((D - b % D : ℕ) : ZMod D) = -(b : ZMod D) := by
    rw [Nat.cast_sub (Nat.mod_lt _ (by omega)).le, ZMod.natCast_self, zero_sub]
    congr 1
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_mod]
  have hc : ((c₂ p D ((D - b % D) * u) : ℕ) : ZMod D)
      = (((D - b % D) * u * p ^ 2 : ℕ) : ZMod D) := by
    rw [ZMod.natCast_eq_natCast_iff']; unfold c₂; simp
  have goal : ((c₂ p D ((D - b % D) * u) * (p + 1) + b : ℕ) : ZMod D) = 0 := by
    push_cast
    rw [hc]
    push_cast
    rw [hDZ]
    push_cast at hu'
    linear_combination (-(b : ZMod D)) * hu'
  rw [ZMod.natCast_eq_zero_iff] at goal
  exact Nat.mod_eq_zero_of_dvd goal

/-- The closure of the 2-cycle: junction 1 lands on `c₀'p`, junction 2 on `c₀p³`. -/
theorem closure_of_cycle (hD3 : 3 ≤ D) (hcopP : Nat.Coprime p D)
    (hcopP1 : Nat.Coprime (p + 1) D) (hbD : ¬ D ∣ b)
    (hc : (c₂ p D c₀ * (p + 1) + b) % D = 0) (hc' : (c₂ p D c₀' * (p + 1) + b') % D = 0)
    (hcyc : (b * p + b') % D = 0) :
    Closure p D c₀ b c₀' b' (4 * Nat.totient D) 1 3 where
  hD2 := by omega
  he := by have := Nat.totient_pos.2 (show 0 < D by omega); omega
  hj := by have := Nat.totient_pos.2 (show 0 < D by omega); omega
  hj' := by have := Nat.totient_pos.2 (show 0 < D by omega); omega
  hpow := by
    have htot : p ^ Nat.totient D % D = 1 := by
      have := Nat.ModEq.pow_totient hcopP
      unfold Nat.ModEq at this
      rw [this, Nat.mod_eq_of_lt (by omega)]
    rw [pow_mul', Nat.pow_mod, htot, one_pow, Nat.mod_eq_of_lt (by omega)]
  hland := by
    -- in `ZMod D`: `c₂' = −c₂p` from the cycle, then cancel `p`
    have hcZ : ((c₂ p D c₀ : ℕ) : ZMod D) * ((p : ZMod D) + 1) = -(b : ZMod D) := by
      have h1 : (((c₂ p D c₀ * (p + 1) + b : ℕ)) : ZMod D) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]; exact Nat.dvd_of_mod_eq_zero hc
      push_cast at h1; linear_combination h1
    have hcZ' : ((c₂ p D c₀' : ℕ) : ZMod D) * ((p : ZMod D) + 1) = -(b' : ZMod D) := by
      have h1 : (((c₂ p D c₀' * (p + 1) + b' : ℕ)) : ZMod D) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]; exact Nat.dvd_of_mod_eq_zero hc'
      push_cast at h1; linear_combination h1
    have hcycZ : (b : ZMod D) * p + b' = 0 := by
      have h1 : (((b * p + b' : ℕ)) : ZMod D) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]; exact Nat.dvd_of_mod_eq_zero hcyc
      push_cast at h1; exact h1
    have hc2 : ((c₂ p D c₀ : ℕ) : ZMod D) = (c₀ : ZMod D) * (p : ZMod D) ^ 2 :=
      DriftOne.c₂_cast (p := p) (D := D) (c₀ := c₀)
    have hc2' : ((c₂ p D c₀' : ℕ) : ZMod D) = (c₀' : ZMod D) * (p : ZMod D) ^ 2 :=
      DriftOne.c₂_cast (p := p) (D := D) (c₀ := c₀')
    set u1 := ZMod.unitOfCoprime (p + 1) hcopP1 with hu1
    set u := ZMod.unitOfCoprime p hcopP with hu
    have hu1v : (u1 : ZMod D) = (p : ZMod D) + 1 := by rw [hu1, ZMod.coe_unitOfCoprime]; push_cast; rfl
    have huv : (u : ZMod D) = (p : ZMod D) := by rw [hu, ZMod.coe_unitOfCoprime]
    -- `(p+1)·(c₂' + c₂ p) = −b' − b p = 0`
    have h1 : ((c₂ p D c₀' : ℕ) : ZMod D) = -((c₂ p D c₀ : ℕ) : ZMod D) * p := by
      have : (u1 : ZMod D) * ((c₂ p D c₀' : ℕ) : ZMod D)
          = (u1 : ZMod D) * (-((c₂ p D c₀ : ℕ) : ZMod D) * p) := by
        rw [hu1v]; linear_combination hcZ' + (p : ZMod D) * hcZ - hcycZ
      exact (Units.mul_right_inj u1).mp this
    -- `c₀' p² = −c₂ p`, cancel `p`: `c₀' p = −c₂ = c₂ p + b`
    have h2 : (c₀' : ZMod D) * p = ((c₂ p D c₀ : ℕ) : ZMod D) * p + b := by
      have : (u : ZMod D) * ((c₀' : ZMod D) * p)
          = (u : ZMod D) * (((c₂ p D c₀ : ℕ) : ZMod D) * p + b) := by
        rw [huv]; linear_combination -hc2' + h1 - (p : ZMod D) * hcZ
      exact (Units.mul_right_inj u).mp this
    have : (((c₂ p D c₀ * p + b : ℕ)) : ZMod D) = ((c₀' * p ^ 1 : ℕ) : ZMod D) := by
      push_cast; rw [pow_one, h2]
    rwa [ZMod.natCast_eq_natCast_iff'] at this
  hland' := by
    have hcZ' : ((c₂ p D c₀' : ℕ) : ZMod D) * ((p : ZMod D) + 1) = -(b' : ZMod D) := by
      have h1 : (((c₂ p D c₀' * (p + 1) + b' : ℕ)) : ZMod D) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]; exact Nat.dvd_of_mod_eq_zero hc'
      push_cast at h1; linear_combination h1
    have hcycZ : (b : ZMod D) * p + b' = 0 := by
      have h1 : (((b * p + b' : ℕ)) : ZMod D) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]; exact Nat.dvd_of_mod_eq_zero hcyc
      push_cast at h1; exact h1
    have hcZ : ((c₂ p D c₀ : ℕ) : ZMod D) * ((p : ZMod D) + 1) = -(b : ZMod D) := by
      have h1 : (((c₂ p D c₀ * (p + 1) + b : ℕ)) : ZMod D) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]; exact Nat.dvd_of_mod_eq_zero hc
      push_cast at h1; linear_combination h1
    have hc2 : ((c₂ p D c₀ : ℕ) : ZMod D) = (c₀ : ZMod D) * (p : ZMod D) ^ 2 :=
      DriftOne.c₂_cast (p := p) (D := D) (c₀ := c₀)
    have hc2' : ((c₂ p D c₀' : ℕ) : ZMod D) = (c₀' : ZMod D) * (p : ZMod D) ^ 2 :=
      DriftOne.c₂_cast (p := p) (D := D) (c₀ := c₀')
    set u1 := ZMod.unitOfCoprime (p + 1) hcopP1 with hu1
    have hu1v : (u1 : ZMod D) = (p : ZMod D) + 1 := by rw [hu1, ZMod.coe_unitOfCoprime]; push_cast; rfl
    have h1 : ((c₂ p D c₀' : ℕ) : ZMod D) = -((c₂ p D c₀ : ℕ) : ZMod D) * p := by
      have : (u1 : ZMod D) * ((c₂ p D c₀' : ℕ) : ZMod D)
          = (u1 : ZMod D) * (-((c₂ p D c₀ : ℕ) : ZMod D) * p) := by
        rw [hu1v]; linear_combination hcZ' + (p : ZMod D) * hcZ - hcycZ
      exact (Units.mul_right_inj u1).mp this
    -- `c₂' p + b' = −c₂' = c₂ p = c₀ p³`
    have : (((c₂ p D c₀' * p + b' : ℕ)) : ZMod D) = ((c₀ * p ^ 3 : ℕ) : ZMod D) := by
      push_cast
      linear_combination hcZ' - h1 + (p : ZMod D) * hc2
    rwa [ZMod.natCast_eq_natCast_iff'] at this
  hne := by
    intro heq
    have hcZ : ((c₂ p D c₀ : ℕ) : ZMod D) * ((p : ZMod D) + 1) = -(b : ZMod D) := by
      have h1 : (((c₂ p D c₀ * (p + 1) + b : ℕ)) : ZMod D) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]; exact Nat.dvd_of_mod_eq_zero hc
      push_cast at h1; linear_combination h1
    have hcZ' : ((c₂ p D c₀' : ℕ) : ZMod D) * ((p : ZMod D) + 1) = -(b' : ZMod D) := by
      have h1 : (((c₂ p D c₀' * (p + 1) + b' : ℕ)) : ZMod D) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]; exact Nat.dvd_of_mod_eq_zero hc'
      push_cast at h1; linear_combination h1
    have hcycZ : (b : ZMod D) * p + b' = 0 := by
      have h1 : (((b * p + b' : ℕ)) : ZMod D) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]; exact Nat.dvd_of_mod_eq_zero hcyc
      push_cast at h1; exact h1
    have hc2 : ((c₂ p D c₀ : ℕ) : ZMod D) = (c₀ : ZMod D) * (p : ZMod D) ^ 2 :=
      DriftOne.c₂_cast (p := p) (D := D) (c₀ := c₀)
    have hc2' : ((c₂ p D c₀' : ℕ) : ZMod D) = (c₀' : ZMod D) * (p : ZMod D) ^ 2 :=
      DriftOne.c₂_cast (p := p) (D := D) (c₀ := c₀')
    set u1 := ZMod.unitOfCoprime (p + 1) hcopP1 with hu1
    set u := ZMod.unitOfCoprime p hcopP with hu
    have hu1v : (u1 : ZMod D) = (p : ZMod D) + 1 := by rw [hu1, ZMod.coe_unitOfCoprime]; push_cast; rfl
    have huv : (u : ZMod D) = (p : ZMod D) := by rw [hu, ZMod.coe_unitOfCoprime]
    have h1 : ((c₂ p D c₀' : ℕ) : ZMod D) = -((c₂ p D c₀ : ℕ) : ZMod D) * p := by
      have : (u1 : ZMod D) * ((c₂ p D c₀' : ℕ) : ZMod D)
          = (u1 : ZMod D) * (-((c₂ p D c₀ : ℕ) : ZMod D) * p) := by
        rw [hu1v]; linear_combination hcZ' + (p : ZMod D) * hcZ - hcycZ
      exact (Units.mul_right_inj u1).mp this
    have heqZ : ((c₀' * p ^ 1 : ℕ) : ZMod D) = ((c₀ * p ^ 3 : ℕ) : ZMod D) := by
      rwa [ZMod.natCast_eq_natCast_iff']
    push_cast at heqZ
    -- `c₀' p = −c₂`, `c₀ p³ = c₂ p`: so `c₂ (p + 1) = 0`, i.e. `b = 0` in `ZMod D`
    have h3 : (u : ZMod D) * ((c₀' : ZMod D) * p) = (u : ZMod D) * (-((c₂ p D c₀ : ℕ) : ZMod D)) := by
      rw [huv]; linear_combination -hc2' + h1
    have h4 : (c₀' : ZMod D) * p = -((c₂ p D c₀ : ℕ) : ZMod D) := (Units.mul_right_inj u).mp h3
    have hb0 : ((b : ℕ) : ZMod D) = 0 := by
      linear_combination hcZ - h4 + heqZ - (p : ZMod D) * hc2
    rw [ZMod.natCast_eq_zero_iff] at hb0
    exact hbD hb0

/-- **The offset 2-cycle theorem.**  For a prime `p`, background `D ≥ 3` coprime to
`p(p+1)`, two offsets `b ≠ b'` dividing `p + 1`, coprime to `D`, with `b + D < p`,
`b' + D < p`, and the cycle condition `D ∣ bp + b'`, every channel `M` with
`bM < p(p−D)`, `bM + D < (b−1)pD`, the same for `b'`, and `2(b+b')M < p²D`, is
digit-`p−1`-free for a common irrational.  No orbit condition on `−1`. -/
theorem mahler_lower_bound_two_cycle (p D b b' M : ℕ) (hp : p.Prime) (hD3 : 3 ≤ D)
    (hb : 2 ≤ b) (hb' : 2 ≤ b') (hbD : b + D < p) (hb'D : b' + D < p)
    (hbp : b ∣ p + 1) (hb'p : b' ∣ p + 1) (hcopb : Nat.Coprime b D) (hcopb' : Nat.Coprime b' D)
    (hcopP1 : Nat.Coprime (p + 1) D) (hcyc : (b * p + b') % D = 0)
    (hM0 : 0 < M) (hMA : b * M < p * (p - D)) (hMB : b * M + D < (b - 1) * p * D)
    (hMA' : b' * M < p * (p - D)) (hMB' : b' * M + D < (b' - 1) * p * D)
    (hσ : 2 * (b + b') * M < p ^ 2 * D) :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ M →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt p ((m : ℝ) * α) [p - 1] n := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hcopP : Nat.Coprime p D :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  have hcopD : Nat.Coprime D (p * (p + 1)) := Nat.Coprime.mul_right hcopP.symm hcopP1.symm
  obtain ⟨c₀, hc⟩ := exists_source p D b (by omega) hcopD
  obtain ⟨c₀', hc'⟩ := exists_source p D b' (by omega) hcopD
  have h1 : DriftOneB p D c₀ b := ⟨hp3, hD3, hb, hbD, hbp, hcopb, hc⟩
  have h1' : DriftOneB p D c₀' b' := ⟨hp3, hD3, hb', hb'D, hb'p, hcopb', hc'⟩
  have hbD' : ¬ D ∣ b := fun hd => by
    have := Nat.Coprime.eq_one_of_dvd hcopb.symm hd
    omega
  exact mahler_lower_bound_two_junction p D c₀ b c₀' b' M _ 1 3 h1.toHyp h1'.toHyp
    (h1.keys M hM0 hMA hMB) (h1'.keys M hM0 hMA' hMB') hσ
    (closure_of_cycle hD3 hcopP hcopP1 hbD' hc hc' hcyc)

end cycle

/-! ### A closed-form class: `p ≡ 7 (mod 12)` -/

/-- **`M(p,1) ≥ p(p−1)/6` for every prime `p ≡ 7 (mod 12)`, `p ≥ 19`.**  Background
`D = (p+2)/3`, offsets `2` and `4` (both divide `p + 1` since `4 ∣ p + 1`), cycle
`2p + 4 = 6D`.  No orbit condition: the `−1 ∈ ⟨p⟩` hypothesis of family I and the
`exists_prime_nonresidue` sorry of `MahlerDriftOne.lean` are both absent.  The constant
is `1/6 = (2/3)·(1/4)`, twice family II's `1/12`. -/
theorem mahler_lower_bound_prime_seven_mod_twelve (p : ℕ) (hp : p.Prime) (h7 : p % 12 = 7)
    (h19 : 19 ≤ p) :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ p * (p - 1) / 6 - 1 →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt p ((m : ℝ) * α) [p - 1] n := by
  obtain ⟨k, rfl⟩ : ∃ k, p = 12 * k + 7 := ⟨p / 12, by omega⟩
  have hk : 1 ≤ k := by omega
  have hM : (12 * k + 7) * (12 * k + 7 - 1) / 6 - 1 = 24 * k ^ 2 + 26 * k + 6 := by
    rw [show 12 * k + 7 - 1 = 12 * k + 6 by omega,
      show (12 * k + 7) * (12 * k + 6) = 6 * (24 * k ^ 2 + 26 * k + 7) by ring,
      Nat.mul_div_cancel_left _ (by norm_num)]
    omega
  rw [hM]
  have hsub : 12 * k + 7 - (4 * k + 3) = 8 * k + 4 := by omega
  have hcop2 : Nat.Coprime 2 (4 * k + 3) := by
    rw [Nat.Coprime, Nat.gcd_rec, show (4 * k + 3) % 2 = 1 by omega]; norm_num
  have hcopP1 : Nat.Coprime (12 * k + 7 + 1) (4 * k + 3) := by
    have hg := Nat.gcd_dvd_left (12 * k + 7 + 1) (4 * k + 3)
    have hg' := Nat.gcd_dvd_right (12 * k + 7 + 1) (4 * k + 3)
    have h3 : Nat.gcd (12 * k + 7 + 1) (4 * k + 3) ∣ 3 * (4 * k + 3) := Dvd.dvd.mul_left hg' 3
    have h4 := Nat.dvd_sub h3 hg
    rw [show 3 * (4 * k + 3) - (12 * k + 7 + 1) = 1 by omega] at h4
    exact Nat.dvd_one.mp h4
  refine mahler_lower_bound_two_cycle (12 * k + 7) (4 * k + 3) 2 4 (24 * k ^ 2 + 26 * k + 6)
    hp (by omega) (by norm_num) (by norm_num) (by omega) (by omega)
    ⟨6 * k + 4, by ring⟩ ⟨3 * k + 2, by ring⟩ hcop2
    (by have := hcop2.pow_left 2; simpa using this) hcopP1
    (Nat.mod_eq_zero_of_dvd ⟨6, by ring⟩) (by positivity) ?_ ?_ ?_ ?_ ?_
  · rw [hsub]; nlinarith
  · norm_num; nlinarith
  · rw [hsub]; nlinarith
  · norm_num; nlinarith
  · nlinarith

end NormalNumbers.Adder.Background.Two
