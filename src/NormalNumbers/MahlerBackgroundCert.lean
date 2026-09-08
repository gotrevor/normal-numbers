/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.MahlerNumCert

/-!
# The background certificate: one junction over an arbitrary `1/D` 🧮

`MahlerFamilyI.lean` hard-wires the background `D = (p+3)/2`, the junction offset
`b = 2` and the junction source `c₀ = p^(e−2)`.  This file frees all three.

For any odd `p`, any `D < p` with `b + D < p`, and any `c₀`, put
`c₁ = c₀p mod D`, `c₂ = c₀p² mod D` and `E = p³D`.  The states are

* far `F_c` (`c < D`): tail `c/D`, numerator `c·p³`, digit `⌊cp/D⌋`,
  edge `F_c → F_{cp mod D}`;
* `N₋₁`: numerator `(c₁p² + b)·p`  (tail `c₁/D + b/(p²D)`), digit `⌊c₁p/D⌋`;
* `N₀`: numerator `(c₂p + b)·p²`  (tail `c₂/D + b/(pD)`), digit `⌊(c₂p+b)/D⌋`,
  landing on `F_{(c₂p + b) mod D}`;

with the single junction edge `F_{c₀} → N₋₁` carrying `δ = b·p`, and slack
`σ = 2b` (so `δ + σ < σp` for every `p > 2`).  Every far state is free: only
`D < p` is used.  Validity to channel `M` reduces to **two** arithmetic keys,

* `keyA` : `p²·(m·c₁ mod D) + m·b < (p−1)·pD`   — the state `N₋₁`;
* `keyB` : `m·(c₂p + b) mod pD < (p−1)·D`       — the state `N₀`;

plus two size conditions (`keyJ` for the junction edge, `keyR` for the carry
slack).  `keyA` bites only when `m·c₁ ≡ −1 (mod D)`, and `keyB` only when
`m·c₂ + ⌊mb/p⌋ ≡ −1 (mod D)`; the review lap of 2026-09-08 shows that the
second is a linear drift `w ≡ w₀ + g·v (mod bD)` with `w₀ = −b·c₂⁻¹`,
`g = w₀ − p`, and that `g = 1` — the optimal drift — happens exactly when
`−1 ∈ ⟨p⟩ (mod D)`, which is family I's hypothesis.  See `PENDING_WORK.md`.

The closed walk is `F_{c₀} → N₋₁ → N₀ → F_{c₀p^j} → ⋯ → F_{c₀p^(e−1)} → F_{c₀}`
against the pure far cycle, where `p^e ≡ 1 (mod D)` and the landing residue is
`c₀p^j`; they differ at position `3` as soon as `c₀p^j ≢ c₀p³ (mod D)`.
-/

namespace NormalNumbers.Adder.Background

open NormalNumbers NormalNumbers.Mahler

/-! ### Parameters -/

/-- The common denominator of all tail intervals, `p³D`. -/
def E (p D : ℕ) : ℕ := p ^ 3 * D
/-- `c₁ = c₀p mod D`, the residue of `N₋₁`. -/
def c₁ (p D c₀ : ℕ) : ℕ := c₀ * p % D
/-- `c₂ = c₀p² mod D`, the residue of `N₀`. -/
def c₂ (p D c₀ : ℕ) : ℕ := c₀ * p ^ 2 % D

/-- The shape hypotheses: `p ≥ 3`, `0 < D`, `0 < b` and `b + D < p`. -/
structure Hyp (p D b : ℕ) : Prop where
  hp : 3 ≤ p
  hD : 0 < D
  hb : 0 < b
  hbD : b + D < p

namespace Hyp

variable {p D b : ℕ} (h : Hyp p D b)
include h

theorem two_le : 2 ≤ p := by have := h.hp; omega
theorem D_lt : D < p := by have := h.hbD; have := h.hb; omega
theorem b_lt : b < p := by have := h.hbD; have := h.hD; omega
theorem E_pos : 0 < E p D := by
  unfold E; have := h.hp; have := h.hD; positivity

end Hyp

/-- The four arithmetic keys certifying channels `1 … M`. -/
structure Keys (p D c₀ b M : ℕ) : Prop where
  posM : 0 < M
  keyA : ∀ m, m ≤ M → p ^ 2 * (m * c₁ p D c₀ % D) + m * b < (p - 1) * (p * D)
  keyB : ∀ m, m ≤ M → m * (c₂ p D c₀ * p + b) % (p * D) < (p - 1) * D
  keyJ : b * M + p ^ 2 * D < p ^ 3
  keyR : 2 * b * M < p ^ 2 * D

/-! ### A little `Nat` arithmetic -/

theorem sub_one_mul_add (p X : ℕ) (hp : 1 ≤ p) : (p - 1) * X + X = p * X := by
  obtain ⟨t, rfl⟩ : ∃ t, p = t + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel]; ring

/-! ### States -/

/-- The far state `F_{c mod D}`. -/
def far (D c : ℕ) : Fin (D + 2) := ⟨c % D % (D + 2), Nat.mod_lt _ (by omega)⟩
/-- The near state `N₋₁`. -/
def nm1 (D : ℕ) : Fin (D + 2) := ⟨D, by omega⟩
/-- The near state `N₀`. -/
def n0 (D : ℕ) : Fin (D + 2) := ⟨D + 1, by omega⟩

theorem far_val (D c : ℕ) (hD : 0 < D) : (far D c).1 = c % D := by
  have h := Nat.mod_lt c hD
  simp only [far]
  exact Nat.mod_eq_of_lt (by omega)

theorem far_congr (D : ℕ) {c c' : ℕ} (h : c % D = c' % D) : far D c = far D c' := by
  simp only [far, h]

theorem far_mod (D c : ℕ) : far D (c % D) = far D c := far_congr D (Nat.mod_mod _ _)

section states

variable (p D c₀ b : ℕ)

/-- Tail numerators over `E = p³D`. -/
def num (s : Fin (D + 2)) : ℕ :=
  if s.1 < D then s.1 * p ^ 3
  else if s.1 = D then (c₁ p D c₀ * p ^ 2 + b) * p
  else (c₂ p D c₀ * p + b) * p ^ 2

/-- The emitted digits. -/
def dig (s : Fin (D + 2)) : ℕ :=
  if s.1 < D then s.1 * p / D
  else if s.1 = D then c₁ p D c₀ * p / D
  else (c₂ p D c₀ * p + b) / D

/-- Successors: the far cycle plus the junction `F_{c₀} → N₋₁ → N₀ → F_land`. -/
def nxt (s : Fin (D + 2)) : List (Fin (D + 2)) :=
  if s.1 < D then
    (if s.1 = c₀ % D then [far D (s.1 * p), nm1 D] else [far D (s.1 * p)])
  else if s.1 = D then [n0 D] else [far D (c₂ p D c₀ * p + b)]

/-- The background numerator certificate, slack `σ = 2b`. -/
def cert : NumCert p where
  n := D + 2
  num := num p D c₀ b
  dig := dig p D c₀ b
  nxt := nxt p D c₀ b
  E := E p D
  σ := 2 * b

variable {p D c₀ b}

theorem num_far (c : ℕ) (hD : 0 < D) : num p D c₀ b (far D c) = (c % D) * p ^ 3 := by
  have hv := far_val D c hD
  unfold num
  rw [if_pos (by rw [hv]; exact Nat.mod_lt _ hD), hv]

theorem dig_far (c : ℕ) (hD : 0 < D) : dig p D c₀ b (far D c) = (c % D) * p / D := by
  have hv := far_val D c hD
  unfold dig
  rw [if_pos (by rw [hv]; exact Nat.mod_lt _ hD), hv]

theorem num_nm1 : num p D c₀ b (nm1 D) = (c₁ p D c₀ * p ^ 2 + b) * p := by
  unfold num nm1; simp

theorem dig_nm1 : dig p D c₀ b (nm1 D) = c₁ p D c₀ * p / D := by
  unfold dig nm1; simp

theorem num_n0 : num p D c₀ b (n0 D) = (c₂ p D c₀ * p + b) * p ^ 2 := by
  unfold num n0; simp

theorem dig_n0 : dig p D c₀ b (n0 D) = (c₂ p D c₀ * p + b) / D := by
  unfold dig n0; simp

theorem nxt_far (c : ℕ) (hD : 0 < D) :
    nxt p D c₀ b (far D c) =
      if c % D = c₀ % D then [far D (c % D * p), nm1 D] else [far D (c % D * p)] := by
  have hv := far_val D c hD
  unfold nxt
  rw [if_pos (by rw [hv]; exact Nat.mod_lt _ hD), hv]

theorem nxt_nm1 : nxt p D c₀ b (nm1 D) = [n0 D] := by unfold nxt nm1; simp

theorem nxt_n0 : nxt p D c₀ b (n0 D) = [far D (c₂ p D c₀ * p + b)] := by
  unfold nxt n0; simp

/-- The far edge is always available. -/
theorem far_mul_mem (c : ℕ) (hD : 0 < D) :
    far D (c * p) ∈ nxt p D c₀ b (far D c) := by
  rw [nxt_far (c₀ := c₀) (b := b) c hD]
  have e : far D (c % D * p) = far D (c * p) := far_congr D (by simp [Nat.mul_mod])
  split_ifs <;> simp [e]

/-- Every state is a far state, `N₋₁` or `N₀`. -/
theorem state_cases (s : Fin (D + 2)) :
    (∃ c, c < D ∧ s = far D c) ∨ s = nm1 D ∨ s = n0 D := by
  rcases Nat.lt_or_ge s.1 D with hlt | hge
  · left
    refine ⟨s.1, hlt, Fin.ext ?_⟩
    rw [far_val D s.1 (by omega), Nat.mod_eq_of_lt hlt]
  · right
    have hs := s.2
    rcases Nat.lt_or_ge s.1 (D + 1) with h1 | h1
    · left; exact Fin.ext (by unfold nm1; simp; omega)
    · right; exact Fin.ext (by unfold n0; simp; omega)

/-- The four edge types. -/
theorem mem_nxt (hD : 0 < D) {s s' : Fin (D + 2)} (hs' : s' ∈ nxt p D c₀ b s) :
    (∃ c, c < D ∧ s = far D c ∧ s' = far D (c * p)) ∨
    (s = far D c₀ ∧ s' = nm1 D) ∨
    (s = nm1 D ∧ s' = n0 D) ∨ (s = n0 D ∧ s' = far D (c₂ p D c₀ * p + b)) := by
  rcases state_cases s with ⟨c, hc, rfl⟩ | rfl | rfl
  · rw [nxt_far (c₀ := c₀) (b := b) c hD, Nat.mod_eq_of_lt hc] at hs'
    split_ifs at hs' with hj
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs'
      rcases hs' with rfl | rfl
      · left; exact ⟨c, hc, rfl, rfl⟩
      · right; left
        exact ⟨far_congr D (by rw [Nat.mod_eq_of_lt hc, hj]), rfl⟩
    · simp only [List.mem_singleton] at hs'
      left; exact ⟨c, hc, rfl, hs'⟩
  · rw [nxt_nm1, List.mem_singleton] at hs'
    right; right; left; exact ⟨rfl, hs'⟩
  · rw [nxt_n0, List.mem_singleton] at hs'
    right; right; right; exact ⟨rfl, hs'⟩

end states

/-! ### The digit and carry conditions -/

section keys

variable {p D c₀ b M : ℕ}

theorem c₁_lt (hD : 0 < D) : c₁ p D c₀ < D := Nat.mod_lt _ hD
theorem c₂_lt (hD : 0 < D) : c₂ p D c₀ < D := Nat.mod_lt _ hD

/-- `p·r < (p−1)·D` for `r < D < p` — the only fact far states need. -/
theorem far_core (h : Hyp p D b) (r : ℕ) (hr : r < D) : p * r < (p - 1) * D := by
  have hD := h.hD
  have hDp := h.D_lt
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := h.hp; omega⟩
  simp only [Nat.add_sub_cancel]
  have h1 : q * r + q ≤ q * D := by
    have := Nat.mul_le_mul_left q (show r + 1 ≤ D by omega)
    rw [Nat.mul_add, mul_one] at this; exact this
  have e : (q + 1) * r = q * r + r := by ring
  omega

/-- **Far states** are unconditionally safe. -/
theorem key_far (h : Hyp p D b) (c m : ℕ) :
    p * (m * (c * p ^ 3) % E p D) < (p - 1) * E p D := by
  have hD := h.hD
  have hp := h.hp
  unfold E
  rw [show m * (c * p ^ 3) = p ^ 3 * (m * c) by ring, Nat.mul_mod_mul_left]
  have hcore := far_core h (m * c % D) (Nat.mod_lt _ hD)
  have hp3 : 0 < p ^ 3 := by positivity
  calc p * (p ^ 3 * (m * c % D)) = p ^ 3 * (p * (m * c % D)) := by ring
    _ < p ^ 3 * ((p - 1) * D) := Nat.mul_lt_mul_of_pos_left hcore hp3
    _ = (p - 1) * (p ^ 3 * D) := by ring

theorem pow_two_D_le (h : Hyp p D b) : p ^ 2 * D ≤ p ^ 3 := by
  have := h.D_lt
  calc p ^ 2 * D ≤ p ^ 2 * p := Nat.mul_le_mul_left _ (le_of_lt this)
    _ = p ^ 3 := by ring

/-- **The far carry bound**. -/
theorem res_far (h : Hyp p D b) (hR : 2 * b * M < p ^ 2 * D) (c m : ℕ) (hm : m ≤ M) :
    m * (c * p ^ 3) % E p D + 2 * b * m < E p D := by
  have hD := h.hD
  have hp := h.hp
  unfold E
  rw [show m * (c * p ^ 3) = p ^ 3 * (m * c) by ring, Nat.mul_mod_mul_left]
  have hr : m * c % D + 1 ≤ D := Nat.mod_lt _ hD
  have h1 : p ^ 3 * (m * c % D) + p ^ 3 ≤ p ^ 3 * D := by
    have := Nat.mul_le_mul_left (p ^ 3) hr
    rw [Nat.mul_add, mul_one] at this; exact this
  have h2 : 2 * b * m < p ^ 3 :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ hm) (lt_of_lt_of_le hR (pow_two_D_le h))
  omega

/-- **The junction edge** out of `F_{c₀}` carries `δ = bp`. -/
theorem key_jump (h : Hyp p D b) (hJ : b * M + p ^ 2 * D < p ^ 3) (m : ℕ) (hm : m ≤ M) :
    p * (m * (c₀ * p ^ 3) % E p D) + m * (b * p) < (p - 1) * E p D := by
  have hD := h.hD
  have hp := h.hp
  unfold E
  rw [show m * (c₀ * p ^ 3) = p ^ 3 * (m * c₀) by ring, Nat.mul_mod_mul_left]
  have hr : m * c₀ % D + 1 ≤ D := Nat.mod_lt _ hD
  have hK : b * m + p ^ 2 * D < p ^ 3 :=
    lt_of_le_of_lt (by have := Nat.mul_le_mul_left b hm; omega) hJ
  have h1 : p ^ 4 * (m * c₀ % D) + p ^ 4 ≤ p ^ 4 * D := by
    have := Nat.mul_le_mul_left (p ^ 4) hr
    rw [Nat.mul_add, mul_one] at this; exact this
  have h2 : b * m * p + p ^ 3 * D < p ^ 4 := by
    have hmul := Nat.mul_lt_mul_of_pos_right hK (show 0 < p by omega)
    calc b * m * p + p ^ 3 * D = (b * m + p ^ 2 * D) * p := by ring
      _ < p ^ 3 * p := hmul
      _ = p ^ 4 := by ring
  have e3 : (p - 1) * (p ^ 3 * D) + p ^ 3 * D = p ^ 4 * D := by
    rw [sub_one_mul_add _ _ (by omega)]; ring
  have e1 : p * (p ^ 3 * (m * c₀ % D)) = p ^ 4 * (m * c₀ % D) := by ring
  have e2 : m * (b * p) = b * m * p := by ring
  omega

/-- The residue of `N₋₁`: `m·num mod E = p³·(m·c₁ mod D) + mbp`. -/
theorem nm1_mod (h : Hyp p D b) (m : ℕ)
    (hA : p ^ 2 * (m * c₁ p D c₀ % D) + m * b < (p - 1) * (p * D)) :
    m * ((c₁ p D c₀ * p ^ 2 + b) * p) % E p D
      = p ^ 3 * (m * c₁ p D c₀ % D) + m * b * p := by
  have hD := h.hD
  have hp := h.hp
  set c := c₁ p D c₀ with hc
  set r := m * c % D with hr
  set u := m * c / D with hu
  have hsplit : m * c = D * u + r := (Nat.div_add_mod _ _).symm
  have hnum : m * ((c * p ^ 2 + b) * p) = (p ^ 3 * r + m * b * p) + (p ^ 3 * D) * u := by
    have e : m * ((c * p ^ 2 + b) * p) = p ^ 3 * (m * c) + m * b * p := by ring
    rw [e, hsplit]; ring
  have hmul : p * (p ^ 2 * r + m * b) < p * ((p - 1) * (p * D)) :=
    Nat.mul_lt_mul_of_pos_left hA (by omega)
  have e1 : p * (p ^ 2 * r + m * b) = p ^ 3 * r + m * b * p := by ring
  have e2 : p * ((p - 1) * (p * D)) = (p - 1) * (p ^ 2 * D) := by ring
  have e3 : (p - 1) * (p ^ 2 * D) + p ^ 2 * D = p ^ 3 * D := by
    rw [sub_one_mul_add _ _ (by omega)]; ring
  have hpos : 0 < p ^ 2 * D := by positivity
  have hlt : p ^ 3 * r + m * b * p < p ^ 3 * D := by omega
  unfold E
  rw [hnum, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- **The state `N₋₁`**: exactly `keyA`. -/
theorem key_nm1 (h : Hyp p D b) (m : ℕ)
    (hA : p ^ 2 * (m * c₁ p D c₀ % D) + m * b < (p - 1) * (p * D)) :
    p * (m * ((c₁ p D c₀ * p ^ 2 + b) * p) % E p D) < (p - 1) * E p D := by
  have hp := h.hp
  rw [nm1_mod h m hA]
  unfold E
  calc p * (p ^ 3 * (m * c₁ p D c₀ % D) + m * b * p)
      = p ^ 2 * (p ^ 2 * (m * c₁ p D c₀ % D) + m * b) := by ring
    _ < p ^ 2 * ((p - 1) * (p * D)) := Nat.mul_lt_mul_of_pos_left hA (by positivity)
    _ = (p - 1) * (p ^ 3 * D) := by ring

theorem res_nm1 (h : Hyp p D b) (hR : 2 * b * M < p ^ 2 * D) (m : ℕ)
    (hA : p ^ 2 * (m * c₁ p D c₀ % D) + m * b < (p - 1) * (p * D)) (hm : m ≤ M) :
    m * ((c₁ p D c₀ * p ^ 2 + b) * p) % E p D + 2 * b * m < E p D := by
  have hp := h.hp
  rw [nm1_mod h m hA]
  have hmul : p * (p ^ 2 * (m * c₁ p D c₀ % D) + m * b) < p * ((p - 1) * (p * D)) :=
    Nat.mul_lt_mul_of_pos_left hA (by omega)
  have e1 : p * (p ^ 2 * (m * c₁ p D c₀ % D) + m * b)
      = p ^ 3 * (m * c₁ p D c₀ % D) + m * b * p := by ring
  have e2 : p * ((p - 1) * (p * D)) = (p - 1) * (p ^ 2 * D) := by ring
  have e3 : (p - 1) * (p ^ 2 * D) + p ^ 2 * D = p ^ 3 * D := by
    rw [sub_one_mul_add _ _ (by omega)]; ring
  have h2 : 2 * b * m ≤ 2 * b * M := Nat.mul_le_mul_left _ hm
  unfold E
  omega

/-- The residue of `N₀`: `m·num mod E = p²·(m(c₂p+b) mod pD)`. -/
theorem n0_mod (m : ℕ) :
    m * ((c₂ p D c₀ * p + b) * p ^ 2) % E p D
      = p ^ 2 * (m * (c₂ p D c₀ * p + b) % (p * D)) := by
  unfold E
  rw [show m * ((c₂ p D c₀ * p + b) * p ^ 2) = p ^ 2 * (m * (c₂ p D c₀ * p + b)) by ring,
    show p ^ 3 * D = p ^ 2 * (p * D) by ring, Nat.mul_mod_mul_left]

/-- **The state `N₀`**: exactly `keyB`. -/
theorem key_n0 (h : Hyp p D b) (m : ℕ)
    (hB : m * (c₂ p D c₀ * p + b) % (p * D) < (p - 1) * D) :
    p * (m * ((c₂ p D c₀ * p + b) * p ^ 2) % E p D) < (p - 1) * E p D := by
  have hp := h.hp
  rw [n0_mod]
  unfold E
  calc p * (p ^ 2 * (m * (c₂ p D c₀ * p + b) % (p * D)))
      = p ^ 3 * (m * (c₂ p D c₀ * p + b) % (p * D)) := by ring
    _ < p ^ 3 * ((p - 1) * D) := Nat.mul_lt_mul_of_pos_left hB (by positivity)
    _ = (p - 1) * (p ^ 3 * D) := by ring

theorem res_n0 (h : Hyp p D b) (hR : 2 * b * M < p ^ 2 * D) (m : ℕ)
    (hB : m * (c₂ p D c₀ * p + b) % (p * D) < (p - 1) * D) (hm : m ≤ M) :
    m * ((c₂ p D c₀ * p + b) * p ^ 2) % E p D + 2 * b * m < E p D := by
  have hp := h.hp
  rw [n0_mod]
  have h1 : p ^ 2 * (m * (c₂ p D c₀ * p + b) % (p * D)) ≤ p ^ 2 * ((p - 1) * D) :=
    Nat.mul_le_mul_left _ (by omega)
  have e2 : p ^ 2 * ((p - 1) * D) = (p - 1) * (p ^ 2 * D) := by ring
  have e3 : (p - 1) * (p ^ 2 * D) + p ^ 2 * D = p ^ 3 * D := by
    rw [sub_one_mul_add _ _ (by omega)]; ring
  have h2 : 2 * b * m ≤ 2 * b * M := Nat.mul_le_mul_left _ hm
  unfold E
  omega

end keys

/-! ### The certificate is good -/

section good

variable {p D c₀ b M : ℕ}

theorem dig_lt (h : Hyp p D b) (s : Fin (D + 2)) : dig p D c₀ b s < p := by
  have hD := h.hD
  have hbp := h.b_lt
  rcases state_cases s with ⟨c, hc, rfl⟩ | rfl | rfl
  · rw [dig_far c hD, Nat.mod_eq_of_lt hc, Nat.div_lt_iff_lt_mul hD, mul_comm p]
    exact Nat.mul_lt_mul_of_pos_right hc (by omega)
  · rw [dig_nm1, Nat.div_lt_iff_lt_mul hD, mul_comm p]
    exact Nat.mul_lt_mul_of_pos_right (c₁_lt hD) (by omega)
  · rw [dig_n0, Nat.div_lt_iff_lt_mul hD]
    have hc := c₂_lt (p := p) (c₀ := c₀) hD
    have h1 : c₂ p D c₀ * p + p ≤ D * p := by
      have := Nat.mul_le_mul_right p (show c₂ p D c₀ + 1 ≤ D by omega)
      rw [Nat.add_mul, one_mul] at this; exact this
    have e : D * p = p * D := by ring
    omega

theorem num_add_le (h : Hyp p D b) (s : Fin (D + 2)) :
    num p D c₀ b s + 2 * b ≤ E p D := by
  have hD := h.hD
  have hp := h.hp
  have hbp := h.b_lt
  have hb2 : b + 2 ≤ p := by have := h.hbD; have := h.hD; omega
  have hc1 := c₁_lt (p := p) (c₀ := c₀) hD
  have hc2 := c₂_lt (p := p) (c₀ := c₀) hD
  have key : ∀ c : ℕ, c < D → ∀ x : ℕ, x ≤ p ^ 3 → c * p ^ 3 + x ≤ E p D := by
    intro c hc x hx
    unfold E
    have h1 : c * p ^ 3 + p ^ 3 ≤ D * p ^ 3 := by
      have := Nat.mul_le_mul_right (p ^ 3) (show c + 1 ≤ D by omega)
      rw [Nat.add_mul, one_mul] at this; exact this
    have e : D * p ^ 3 = p ^ 3 * D := by ring
    omega
  obtain ⟨t, rfl⟩ : ∃ t, p = t + 3 := ⟨p - 3, by omega⟩
  have hbb : b ≤ t + 1 := by omega
  have hcase : ∀ x : ℕ, x ≤ (t + 3) ^ 2 → b * x + 2 * b ≤ (t + 3) ^ 3 := by
    intro x hx
    have h1 : b * x + 2 * b = b * (x + 2) := by ring
    have h2 : b * (x + 2) ≤ (t + 1) * (x + 2) := Nat.mul_le_mul_right _ hbb
    have h3 : (t + 1) * (x + 2) ≤ (t + 1) * ((t + 3) ^ 2 + 2) :=
      Nat.mul_le_mul_left _ (by omega)
    have h4 : (t + 1) * ((t + 3) ^ 2 + 2) ≤ (t + 3) ^ 3 := by nlinarith
    omega
  rcases state_cases s with ⟨c, hc, rfl⟩ | rfl | rfl
  · rw [num_far c hD, Nat.mod_eq_of_lt hc]
    have h0 := hcase 0 (by positivity)
    exact key c hc (2 * b) (by simpa using h0)
  · rw [num_nm1]
    have e0 : (c₁ (t + 3) D c₀ * (t + 3) ^ 2 + b) * (t + 3)
        = c₁ (t + 3) D c₀ * (t + 3) ^ 3 + b * (t + 3) := by ring
    rw [e0, add_assoc]
    exact key _ hc1 _ (hcase (t + 3) (by nlinarith))
  · rw [num_n0]
    have e0 : (c₂ (t + 3) D c₀ * (t + 3) + b) * (t + 3) ^ 2
        = c₂ (t + 3) D c₀ * (t + 3) ^ 3 + b * (t + 3) ^ 2 := by ring
    rw [e0, add_assoc]
    exact key _ hc2 _ (hcase ((t + 3) ^ 2) le_rfl)

/-- Every edge: `dig s · E + num s' = p · num s + δ`, `δ ∈ {0, bp}`, plus the
digit condition on every channel `m ≤ M`. -/
theorem edge_data (h : Hyp p D b) (K : Keys p D c₀ b M)
    {s s' : Fin (D + 2)} (hs' : s' ∈ nxt p D c₀ b s) :
    ∃ δ, δ ≤ b * p ∧ dig p D c₀ b s * E p D + num p D c₀ b s' = p * num p D c₀ b s + δ ∧
      ∀ m, m ≤ M → p * (m * num p D c₀ b s % E p D) + m * δ < (p - 1) * E p D := by
  have hD := h.hD
  have hp := h.hp
  rcases mem_nxt hD hs' with ⟨c, hc, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨0, by omega, ?_, ?_⟩
    · rw [dig_far c hD, num_far c hD, num_far (c₀ := c₀) (b := b) (c * p) hD,
        Nat.mod_eq_of_lt hc]
      unfold E
      calc c * p / D * (p ^ 3 * D) + c * p % D * p ^ 3
          = p ^ 3 * (D * (c * p / D) + c * p % D) := by ring
        _ = p ^ 3 * (c * p) := by rw [Nat.div_add_mod]
        _ = p * (c * p ^ 3) + 0 := by ring
    · intro m _
      rw [num_far c hD, Nat.mod_eq_of_lt hc, mul_zero, add_zero]
      exact key_far h c m
  · -- the junction `F_{c₀} → N₋₁`
    refine ⟨b * p, le_rfl, ?_, ?_⟩
    · rw [dig_far c₀ hD, num_far c₀ hD, num_nm1]
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
  · -- `N₋₁ → N₀`
    refine ⟨0, by omega, ?_, ?_⟩
    · rw [dig_nm1, num_nm1, num_n0]
      unfold E c₂ c₁
      have hmm : c₀ * p ^ 2 % D = c₀ * p % D * p % D := by
        rw [show c₀ * p ^ 2 = c₀ * p * p by ring]; simp [Nat.mul_mod]
      have hdm := Nat.div_add_mod (c₀ * p % D * p) D
      rw [← hmm] at hdm
      calc c₀ * p % D * p / D * (p ^ 3 * D) + (c₀ * p ^ 2 % D * p + b) * p ^ 2
          = p ^ 3 * (D * (c₀ * p % D * p / D) + c₀ * p ^ 2 % D) + b * p ^ 2 := by ring
        _ = p ^ 3 * (c₀ * p % D * p) + b * p ^ 2 := by rw [hdm]
        _ = p * ((c₀ * p % D * p ^ 2 + b) * p) + 0 := by ring
    · intro m hm
      rw [num_nm1, mul_zero, add_zero]
      exact key_nm1 h m (K.keyA m hm)
  · -- `N₀ → F_land`
    refine ⟨0, by omega, ?_, ?_⟩
    · rw [dig_n0, num_n0, num_far (c₀ := c₀) (b := b) _ hD]
      unfold E
      calc (c₂ p D c₀ * p + b) / D * (p ^ 3 * D) + (c₂ p D c₀ * p + b) % D * p ^ 3
          = p ^ 3 * (D * ((c₂ p D c₀ * p + b) / D) + (c₂ p D c₀ * p + b) % D) := by ring
        _ = p ^ 3 * (c₂ p D c₀ * p + b) := by rw [Nat.div_add_mod]
        _ = p * ((c₂ p D c₀ * p + b) * p ^ 2) + 0 := by ring
    · intro m hm
      rw [num_n0, mul_zero, add_zero]
      exact key_n0 h m (K.keyB m hm)

theorem res_all (h : Hyp p D b) (K : Keys p D c₀ b M) (s : Fin (D + 2)) (m : ℕ)
    (hm : m ≤ M) : m * num p D c₀ b s % E p D + 2 * b * m < E p D := by
  have hD := h.hD
  rcases state_cases s with ⟨c, hc, rfl⟩ | rfl | rfl
  · rw [num_far c hD]; exact res_far h K.keyR _ m hm
  · rw [num_nm1]; exact res_nm1 h K.keyR m (K.keyA m hm) hm
  · rw [num_n0]; exact res_n0 h K.keyR m (K.keyB m hm) hm

/-- **The background certificate is good** up to channel `M`. -/
theorem good (h : Hyp p D b) (K : Keys p D c₀ b M) : (cert p D c₀ b).Good M where
  E_pos := h.E_pos
  σ_pos := by have := h.hb; show 0 < 2 * b; omega
  dig_lt := fun s => dig_lt h s
  num_le := fun s => num_add_le h s
  edge := fun s s' hs' => by
    obtain ⟨δ, hδ, hV, hk⟩ := edge_data h K hs'
    refine ⟨δ, ?_, hV, hk⟩
    have h3 := h.hp
    have hb := h.hb
    show δ + 2 * b < 2 * b * p
    nlinarith
  res := fun s m hm => res_all h K s m hm

theorem valid (h : Hyp p D b) (K : Keys p D c₀ b M) :
    (cert p D c₀ b).toCert.Valid M [p - 1] :=
  NumCert.valid h.two_le (good h K)

theorem not_hiMax_of_edge (h : Hyp p D b) (K : Keys p D c₀ b M)
    {s s' : Fin (D + 2)} (hs' : s' ∈ nxt p D c₀ b s) :
    ¬ (cert p D c₀ b).toCert.HiMax s s' :=
  NumCert.not_hiMax_of_edge h.two_le (good h K) hs'

end good

/-! ### Closure and the two walks -/

/-- Closure data: `p^e ≡ 1 (mod D)`, the landing residue is `c₀p^j` with `j < e`,
and the landing differs from `c₀p³` — so the two walks separate at position `3`. -/
structure Closure (p D c₀ b e j : ℕ) : Prop where
  hD2 : 2 ≤ D
  he : 0 < e
  hj : j < e
  hpow : p ^ e % D = 1
  hland : (c₂ p D c₀ * p + b) % D = c₀ * p ^ j % D
  hne : c₀ * p ^ j % D ≠ c₀ * p ^ 3 % D

/-- The junction walk `F_{c₀} → N₋₁ → N₀ → F_{c₀p^j} → ⋯`. -/
def walkA (p D c₀ j : ℕ) (i : ℕ) : Fin (D + 2) :=
  if i = 0 then far D c₀ else if i = 1 then nm1 D else if i = 2 then n0 D
  else far D (c₀ * p ^ (j + (i - 3)))

/-- The pure far cycle from `F_{c₀}`. -/
def walkB (p D c₀ : ℕ) (i : ℕ) : Fin (D + 2) := far D (c₀ * p ^ i)

section walks

variable {p D c₀ b M e j : ℕ}

theorem walkA_zero : walkA p D c₀ j 0 = far D c₀ := by simp [walkA]
theorem walkA_one : walkA p D c₀ j 1 = nm1 D := by simp [walkA]
theorem walkA_two : walkA p D c₀ j 2 = n0 D := by simp [walkA]

theorem walkA_ge (i : ℕ) (hi : 3 ≤ i) :
    walkA p D c₀ j i = far D (c₀ * p ^ (j + (i - 3))) := by
  unfold walkA; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem pow_mul_e (hpow : p ^ e % D = 1) (hD2 : 2 ≤ D) (t : ℕ) : p ^ (e * t) % D = 1 := by
  induction t with
  | zero => simpa using Nat.mod_eq_of_lt (show 1 < D by omega)
  | succ t ih =>
    rw [Nat.mul_succ, pow_add, Nat.mul_mod, ih, hpow, one_mul,
      Nat.mod_eq_of_lt (show 1 < D by omega)]

theorem far_pow_e (hpow : p ^ e % D = 1) (c : ℕ) : far D (c * p ^ e) = far D c := by
  exact far_congr D (by rw [Nat.mul_mod, hpow, mul_one, Nat.mod_mod])

theorem far_pow_mul_e (hpow : p ^ e % D = 1) (hD2 : 2 ≤ D) (c t : ℕ) :
    far D (c * p ^ (e * t)) = far D c :=
  far_congr D (by rw [Nat.mul_mod, pow_mul_e hpow hD2 t, mul_one, Nat.mod_mod])

/-- The junction walk is closed, with period `ℓ = e − j + 3`. -/
theorem walkA_closed (h : Hyp p D b) (C : Closure p D c₀ b e j) :
    walkA p D c₀ j 0 = far D c₀ ∧
    (∀ i, i + 1 < e - j + 3 → walkA p D c₀ j (i + 1) ∈ nxt p D c₀ b (walkA p D c₀ j i)) ∧
    far D c₀ ∈ nxt p D c₀ b (walkA p D c₀ j (e - j + 3 - 1)) := by
  have hD := h.hD
  have hj := C.hj
  refine ⟨walkA_zero, ?_, ?_⟩
  · intro i hi
    match i with
    | 0 =>
      rw [walkA_zero, walkA_one, nxt_far (c₀ := c₀) (b := b) c₀ hD, if_pos rfl]; simp
    | 1 => rw [walkA_one, walkA_two, nxt_nm1]; simp
    | 2 =>
      rw [walkA_two, walkA_ge 3 le_rfl, nxt_n0]
      have ee : far D (c₀ * p ^ (j + (3 - 3))) = far D (c₂ p D c₀ * p + b) := by
        simp only [Nat.sub_self, add_zero]
        exact (far_congr D C.hland).symm
      rw [ee]; simp
    | (i + 3) =>
      rw [walkA_ge (i + 3) (by omega), walkA_ge (i + 3 + 1) (by omega),
        show i + 3 + 1 - 3 = (i + 3 - 3) + 1 by omega, ← add_assoc, pow_succ, ← mul_assoc]
      exact far_mul_mem _ hD
  · have hge : 3 ≤ e - j + 3 - 1 := by omega
    rw [walkA_ge _ hge, show j + (e - j + 3 - 1 - 3) = e - 1 by omega]
    have e1 : far D c₀ = far D (c₀ * p ^ (e - 1) * p) := by
      rw [mul_assoc, ← pow_succ, show e - 1 + 1 = e by have := C.he; omega]
      exact (far_pow_e C.hpow c₀).symm
    rw [e1]; exact far_mul_mem _ hD

/-- The far cycle is closed for any length divisible by `e`. -/
theorem walkB_closed (h : Hyp p D b) (C : Closure p D c₀ b e j) (L : ℕ)
    (hL : L = e * (e - j + 3)) :
    walkB p D c₀ 0 = far D c₀ ∧
    (∀ i, walkB p D c₀ (i + 1) ∈ nxt p D c₀ b (walkB p D c₀ i)) ∧
    far D c₀ ∈ nxt p D c₀ b (walkB p D c₀ (L - 1)) := by
  have hD := h.hD
  have hj := C.hj
  have he := C.he
  have hL1 : 1 ≤ L := by rw [hL]; nlinarith
  refine ⟨by simp [walkB], ?_, ?_⟩
  · intro i; unfold walkB; rw [pow_succ, ← mul_assoc]; exact far_mul_mem _ hD
  · unfold walkB
    have e1 : far D c₀ = far D (c₀ * p ^ (L - 1) * p) := by
      rw [mul_assoc, ← pow_succ, show L - 1 + 1 = L by omega, hL]
      exact (far_pow_mul_e C.hpow C.hD2 c₀ _).symm
    rw [e1]; exact far_mul_mem _ hD

/-! ### Digits along the walks -/

theorem dig_far_le (h : Hyp p D b) (c : ℕ) : dig p D c₀ b (far D c) ≤ p - 2 := by
  have hD := h.hD
  have hDp := h.D_lt
  have hp := h.hp
  rw [dig_far c hD, Nat.div_le_iff_le_mul_add_pred hD]
  have hr : c % D + 1 ≤ D := Nat.mod_lt _ hD
  have h1 : c % D * p + p ≤ D * p := by
    have := Nat.mul_le_mul_right p hr
    rw [Nat.add_mul, one_mul] at this; exact this
  have h2 : D * (p - 2) + (D - 1) + (D + 1) = D * p := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
    have e : D * (q + 2) = D * q + 2 * D := by ring
    simp only [Nat.add_sub_cancel]
    omega
  omega

/-- `c ↦ ⌊cp/D⌋` is injective on residues, because `D < p`. -/
theorem dig_far_ne (h : Hyp p D b) {x y : ℕ} (hxy : x % D ≠ y % D) :
    dig p D c₀ b (far D x) ≠ dig p D c₀ b (far D y) := by
  have hD := h.hD
  have hDp := h.D_lt
  rw [dig_far x hD, dig_far y hD]
  have key : ∀ u v : ℕ, u < v → u * p / D < v * p / D := by
    intro u v huv
    have h1 : u * p + D ≤ v * p := by
      have := Nat.mul_le_mul_right p (show u + 1 ≤ v by omega)
      rw [Nat.add_mul, one_mul] at this
      omega
    have h2 : u * p / D + 1 ≤ v * p / D := by
      calc u * p / D + 1 = (u * p + D) / D := (Nat.add_div_right _ hD).symm
        _ ≤ v * p / D := Nat.div_le_div_right h1
    omega
  rcases Nat.lt_trichotomy (x % D) (y % D) with hlt | heq | hgt
  · exact ne_of_lt (key _ _ hlt)
  · exact absurd heq hxy
  · exact ne_of_gt (key _ _ hgt)

/-! ### The witness pair -/

theorem witness (h : Hyp p D b) (K : Keys p D c₀ b M) (C : Closure p D c₀ b e j)
    (L : ℕ) (hL : L = e * (e - j + 3)) (hL0 : 0 < L) :
    (cert p D c₀ b).toCert.WitnessPair L
      (fun i : Fin L => walkA p D c₀ j (i.1 % (e - j + 3)))
      (fun i : Fin L => walkB p D c₀ i.1) hL0 (far D c₀) := by
  have hD := h.hD
  have hp := h.hp
  have hj := C.hj
  have he := C.he
  have hl4 : 4 ≤ e - j + 3 := by omega
  have hL4 : 4 ≤ L := by rw [hL]; nlinarith
  obtain ⟨hA0, hAstep, hAclose⟩ := walkA_closed h C
  obtain ⟨hB0, hBstep, hBclose⟩ := walkB_closed h C L hL
  refine ⟨?_, ⟨hB0, fun i _ => hBstep i.1, hBclose⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact EscapeCert.isClosedWalk_periodic (C := (cert p D c₀ b).toCert)
      (walkA p D c₀ j) (e - j + 3) (by omega) _ hA0 hAstep hAclose L e hL (by omega) hL0
  · refine ⟨⟨0, by omega⟩, ?_⟩
    show dig p D c₀ b (walkA p D c₀ j (0 % (e - j + 3))) ≠ p - 1
    rw [Nat.zero_mod, walkA_zero]
    have := dig_far_le (c₀ := c₀) (b := b) h c₀
    omega
  · refine ⟨⟨0, by omega⟩, ?_⟩
    show dig p D c₀ b (walkB p D c₀ 0) ≠ p - 1
    unfold walkB
    have := dig_far_le (c₀ := c₀) (b := b) h (c₀ * p ^ 0)
    omega
  · refine ⟨⟨0, by omega⟩, show 0 + 1 < L by omega, ?_⟩
    simp only [Nat.zero_mod, Nat.mod_eq_of_lt (show 0 + 1 < e - j + 3 by omega)]
    exact not_hiMax_of_edge h K (hAstep 0 (by omega))
  · refine ⟨⟨0, by omega⟩, show 0 + 1 < L by omega, ?_⟩
    exact not_hiMax_of_edge h K (hBstep 0)
  · refine ⟨⟨3, by omega⟩, ?_⟩
    show dig p D c₀ b (walkA p D c₀ j (3 % (e - j + 3))) ≠ dig p D c₀ b (walkB p D c₀ 3)
    rw [Nat.mod_eq_of_lt (show 3 < e - j + 3 by omega), walkA_ge 3 le_rfl]
    unfold walkB
    simp only [Nat.sub_self, add_zero]
    exact dig_far_ne h C.hne

end walks

/-! ### The theorem -/

/-- **The background certificate theorem.**  For any base `p ≥ 3`, background
`1/D` with `b + D < p`, junction source `c₀`, closing data `(e, j)` and channel
keys up to `M`, there is an irrational `α` with no digit `p − 1` in `m·α` for
every `1 ≤ m ≤ M`; hence `M(p,1) > M`.

Family I (`MahlerFamilyI.lean`) is the instance `D = (p+3)/2`, `b = 2`,
`c₀ = p^(e−2)`, `M = ⌊p/2⌋² − 2`, whose closure `j` exists exactly when
`−1 ∈ ⟨p⟩ (mod D)`.  Freeing `D` and `c₀` is what breaks the factor `3` of
`MahlerFamilyII.lean`: measured, `M/⌊p/2⌋² ≥ 0.88` at every prime `17 … 127`
(`experiments/mahler_onejunction_scan.py`). -/
theorem mahler_lower_bound_background (p D c₀ b M e j : ℕ)
    (h : Hyp p D b) (K : Keys p D c₀ b M) (C : Closure p D c₀ b e j) :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ M →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt p ((m : ℝ) * α) [p - 1] n := by
  have he := C.he
  have hL0 : 0 < e * (e - j + 3) := by positivity
  exact (cert p D c₀ b).toCert.escape_mahler_lower_bound h.two_le _ [p - 1] (valid h K)
    _ _ _ hL0 _ (witness h K C _ rfl hL0)

/-! ### Instances beyond family II -/

set_option maxRecDepth 200000

/-- **`M(29,1) ≥ 180`.**  Background `1/11`, junction source `c₀ = 9`, offset
`b = 3`, closing after `e = 10` far steps with landing `c₀p⁷`.  Family I does not
apply at `29` (`−1 ∉ ⟨29⟩ mod 16`) and family II gives only `M(29,1) ≥ 65`;
`⌊29/2⌋² = 196`, so this is `0.913·⌊p/2⌋²`. -/
theorem mahler_lower_bound_base29_background :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ 179 →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt 29 ((m : ℝ) * α) [28] n :=
  mahler_lower_bound_background 29 11 9 3 179 10 7
    ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
    ⟨by norm_num, by decide, by decide, by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel,
      by decide +kernel⟩

/-- **`M(71,1) ≥ 1080`.**  Background `1/41`, `c₀ = 4`, `b = 2`, `e = 40`,
landing `c₀p²²`.  Family I does not apply at `71`; family II gives `M(71,1) ≥ 408`.
`⌊71/2⌋² = 1225`, so this is `0.881·⌊p/2⌋²` — the worst ratio of the whole scan
`17 ≤ p ≤ 127`. -/
theorem mahler_lower_bound_base71_background :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ 1079 →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt 71 ((m : ℝ) * α) [70] n :=
  mahler_lower_bound_background 71 41 4 2 1079 40 22
    ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
    ⟨by norm_num, by decide, by decide, by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel,
      by decide +kernel⟩

end NormalNumbers.Adder.Background
