/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderEscapeCert

/-!
# Numerator certificates: escape certificates with a common denominator 🧮

A **numerator certificate** is an escape certificate (`AdderEscapeCert.lean`)
in which every tail interval is `[num s / E, (num s + σ) / E]` for a common
denominator `E` and a common slack `σ`, and the carries are `⌊m · num s / E⌋`.
Validity for the single-digit block `[p − 1]` then reduces to integer data
(`NumCert.Good`):

* `dig s < p` and `num s + σ ≤ E`;
* every edge `s → s'` satisfies `dig s · E + num s' = p · num s + δ` with
  `δ + σ < σ p`, together with the **digit condition**
  `p · ((m · num s) mod E) + m δ < (p − 1) E` for every channel `m ≤ M`;
* the **carry condition** `(m · num s) mod E + σ m < E` for every `m ≤ M`.

`NumCert.valid` turns this into `EscapeCert.Valid M [p−1]`, and
`NumCert.not_hiMax_of_edge` shows no edge is `hi`-extremal (so mixing is
automatic for any path).  `MahlerFamilyI.lean` and `MahlerFamilyII.lean` are
instances.
-/

namespace NormalNumbers.Adder

open NormalNumbers NormalNumbers.Mahler

/-- A numerator certificate for base `p`. -/
structure NumCert (p : ℕ) where
  n : ℕ
  num : Fin n → ℕ
  dig : Fin n → ℕ
  nxt : Fin n → List (Fin n)
  E : ℕ
  σ : ℕ

namespace NumCert

variable {p : ℕ} (C : NumCert p)

/-- The underlying escape certificate. -/
def toCert : EscapeCert p where
  n := C.n
  a := C.dig
  next := C.nxt
  lo := fun s => (C.num s : ℚ) / C.E
  hi := fun s => ((C.num s : ℚ) + C.σ) / C.E
  c := fun s m => m * C.num s / C.E

/-- The integer data certifying validity up to channel `M`. -/
structure Good (M : ℕ) : Prop where
  E_pos : 0 < C.E
  σ_pos : 0 < C.σ
  dig_lt : ∀ s, C.dig s < p
  num_le : ∀ s, C.num s + C.σ ≤ C.E
  edge : ∀ s, ∀ s' ∈ C.nxt s, ∃ δ, δ + C.σ < C.σ * p ∧
    C.dig s * C.E + C.num s' = p * C.num s + δ ∧
    ∀ m, m ≤ M → p * (m * C.num s % C.E) + m * δ < (p - 1) * C.E
  res : ∀ s, ∀ m, m ≤ M → m * C.num s % C.E + C.σ * m < C.E

variable {C} {M : ℕ} (hp : 2 ≤ p) (G : C.Good M)
include hp G

theorem valid_intervals : ∀ s, 0 ≤ C.toCert.lo s ∧ C.toCert.lo s ≤ C.toCert.hi s ∧
    C.toCert.hi s ≤ 1 := by
  intro s
  have hE : (0 : ℚ) < C.E := by exact_mod_cast G.E_pos
  simp only [toCert]
  refine ⟨by positivity, ?_, ?_⟩
  · gcongr; linarith [show (0 : ℚ) ≤ C.σ by positivity]
  · rw [div_le_one hE]
    have := G.num_le s
    exact_mod_cast this

theorem valid_edges : ∀ s, ∀ s' ∈ C.toCert.next s,
    C.toCert.lo s ≤ (C.toCert.a s + C.toCert.lo s') / p ∧
    (C.toCert.a s + C.toCert.hi s') / p ≤ C.toCert.hi s := by
  intro s s' hs'
  obtain ⟨δ, hδ, hV, _⟩ := G.edge s s' hs'
  have hE : (0 : ℚ) < C.E := by exact_mod_cast G.E_pos
  have hpQ : (0 : ℚ) < p := by exact_mod_cast (by omega : 0 < p)
  have hVQ : (C.dig s : ℚ) * C.E + C.num s' = p * C.num s + δ := by exact_mod_cast hV
  have hδQ : (δ : ℚ) + C.σ < C.σ * p := by exact_mod_cast hδ
  simp only [toCert]
  have h1 : (C.dig s : ℚ) + (C.num s' : ℚ) / C.E = ((p : ℚ) * C.num s + δ) / C.E := by
    rw [← hVQ]; field_simp
  have h2 : (C.dig s : ℚ) + ((C.num s' : ℚ) + C.σ) / C.E
      = ((p : ℚ) * C.num s + δ + C.σ) / C.E := by
    rw [← hVQ]; field_simp; ring
  constructor
  · rw [le_div_iff₀ hpQ, h1, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hE]
    have : (0 : ℚ) ≤ δ := by positivity
    nlinarith
  · rw [div_le_iff₀ hpQ, h2, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hE]
    nlinarith

/-- No edge is `hi`-extremal: the slack `σ/E` is never exhausted (`δ + σ < σ p`). -/
theorem not_hiMax_of_edge {s s' : Fin C.n} (hs' : s' ∈ C.nxt s) : ¬ C.toCert.HiMax s s' := by
  intro hmax
  obtain ⟨δ, hδ, hV, _⟩ := G.edge s s' hs'
  have hE : (0 : ℚ) < C.E := by exact_mod_cast G.E_pos
  have hpQ : (0 : ℚ) < p := by exact_mod_cast (by omega : 0 < p)
  have hVQ : (C.dig s : ℚ) * C.E + C.num s' = p * C.num s + δ := by exact_mod_cast hV
  have hδQ : (δ : ℚ) + C.σ < C.σ * p := by exact_mod_cast hδ
  have h2 : (C.dig s : ℚ) + ((C.num s' : ℚ) + C.σ) / C.E
      = ((p : ℚ) * C.num s + δ + C.σ) / C.E := by
    rw [← hVQ]; field_simp; ring
  unfold EscapeCert.HiMax at hmax
  simp only [toCert] at hmax
  rw [h2, div_div, div_eq_div_iff (by positivity) (by positivity)] at hmax
  nlinarith

theorem valid_carry : ∀ m, m ≤ M → ∀ s,
    (C.toCert.c s m : ℚ) ≤ m * C.toCert.lo s ∧
    m * C.toCert.hi s ≤ C.toCert.c s m + 1 := by
  intro m hm s
  have hE : (0 : ℚ) < C.E := by exact_mod_cast G.E_pos
  have hres := G.res s m hm
  have hdm := Nat.div_add_mod (m * C.num s) C.E
  simp only [toCert]
  constructor
  · calc ((m * C.num s / C.E : ℕ) : ℚ) ≤ ((m * C.num s : ℕ) : ℚ) / (C.E : ℚ) := Nat.cast_div_le
      _ = m * ((C.num s : ℚ) / C.E) := by push_cast; ring
  · have hN : m * (C.num s + C.σ) ≤ (m * C.num s / C.E + 1) * C.E := by nlinarith
    rw [mul_div_assoc', div_le_iff₀ hE]
    exact_mod_cast hN

/-- The channel digit on an edge, as a single quotient below `p − 1`. -/
theorem chDigit_eq {s s' : Fin C.n} (hs' : s' ∈ C.nxt s) (m : ℕ) (hm : m ≤ M) :
    ∃ x, x < p - 1 ∧
      m * C.dig s + m * C.num s' / C.E = x + p * (m * C.num s / C.E) ∧
      C.toCert.chDigit m s s' = x := by
  obtain ⟨δ, _, hV, hkey⟩ := G.edge s s' hs'
  have hEn := G.E_pos
  have hp0 : 0 < p := by omega
  have hdm := Nat.div_add_mod (m * C.num s) C.E
  have hk := hkey m hm
  set c := m * C.num s / C.E with hc
  set r := m * C.num s % C.E with hr
  have hsplit : m * (C.dig s * C.E + C.num s') = (p * r + m * δ) + (p * c) * C.E := by
    rw [hV]
    calc m * (p * C.num s + δ) = p * (m * C.num s) + m * δ := by ring
      _ = p * (C.E * c + r) + m * δ := by rw [hdm]
      _ = (p * r + m * δ) + (p * c) * C.E := by ring
  have hX : m * C.dig s + m * C.num s' / C.E = (p * r + m * δ) / C.E + p * c := by
    rw [← Nat.mul_add_div hEn, show C.E * (m * C.dig s) + m * C.num s'
      = m * (C.dig s * C.E + C.num s') by ring, hsplit, Nat.add_mul_div_right _ _ hEn]
  have hx : (p * r + m * δ) / C.E < p - 1 := by
    rw [Nat.div_lt_iff_lt_mul hEn]; exact hk
  refine ⟨(p * r + m * δ) / C.E, hx, hX, ?_⟩
  unfold EscapeCert.chDigit
  simp only [toCert]
  rw [hX, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem valid_recursion : ∀ m, m ≤ M → ∀ s, ∀ s' ∈ C.toCert.next s,
    C.toCert.c s m = (m * C.toCert.a s + C.toCert.c s' m) / p := by
  intro m hm s s' hs'
  obtain ⟨x, hx, hX, _⟩ := chDigit_eq hp G hs' m hm
  have hp0 : 0 < p := by omega
  simp only [toCert]
  rw [hX, Nat.add_mul_div_left _ _ hp0, Nat.div_eq_of_lt (show x < p by omega), zero_add]

theorem valid_block : ∀ m, 1 ≤ m → m ≤ M →
    ∀ σ : Fin ([p - 1].length + 1) → Fin C.toCert.n,
    (∀ i : Fin [p - 1].length, σ i.succ ∈ C.toCert.next (σ i.castSucc)) →
    List.ofFn (fun i : Fin [p - 1].length =>
      C.toCert.chDigit m (σ i.castSucc) (σ i.succ)) ≠ [p - 1] := by
  intro m _ hm σ hσ
  have hedge : σ 1 ∈ C.nxt (σ 0) := hσ 0
  obtain ⟨x, hx, _, hch⟩ := chDigit_eq hp G hedge m hm
  simp only [List.length_singleton, List.ofFn_succ, List.ofFn_zero, ne_eq, List.cons.injEq,
    and_true]
  show ¬ C.toCert.chDigit m (σ 0) (σ 1) = p - 1
  rw [hch]; omega

/-- **Validity of a good numerator certificate.** -/
theorem valid : C.toCert.Valid M [p - 1] :=
  ⟨fun s => G.dig_lt s, valid_intervals hp G, valid_edges hp G, valid_carry hp G,
    valid_recursion hp G, valid_block hp G⟩

end NumCert

/-- Periodic extension of a closed sequence is a closed walk. -/
theorem EscapeCert.isClosedWalk_periodic {g : ℕ} {C : EscapeCert g} (A : ℕ → Fin C.n) (ℓ : ℕ)
    (hℓ : 0 < ℓ) (s₀ : Fin C.n) (h0 : A 0 = s₀)
    (hstep : ∀ i, i + 1 < ℓ → A (i + 1) ∈ C.next (A i)) (hclose : s₀ ∈ C.next (A (ℓ - 1)))
    (L N : ℕ) (hL : L = N * ℓ) (hN : 0 < N) (hL0 : 0 < L) :
    C.IsClosedWalk L s₀ hL0 (fun i : Fin L => A (i.1 % ℓ)) := by
  refine ⟨by simp [h0], ?_, ?_⟩
  · intro j hj
    simp only
    have hmd := Nat.mod_add_div j.1 ℓ
    have hlt := Nat.mod_lt j.1 hℓ
    rcases Nat.lt_or_ge (j.1 % ℓ + 1) ℓ with hin | hout
    · rw [show j.1 + 1 = (j.1 % ℓ + 1) + ℓ * (j.1 / ℓ) by omega, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hin]
      exact hstep _ hin
    · have he : j.1 % ℓ = ℓ - 1 := by omega
      rw [show j.1 + 1 = ℓ * (j.1 / ℓ + 1) by rw [Nat.mul_add, mul_one]; omega,
        Nat.mul_mod_right, h0, he]
      exact hclose
  · simp only
    have h1 : ℓ * (N - 1) = N * ℓ - ℓ := by rw [Nat.mul_sub_one, mul_comm]
    have h2 : ℓ ≤ N * ℓ := Nat.le_mul_of_pos_left _ hN
    rw [show L - 1 = (ℓ - 1) + ℓ * (N - 1) by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by omega)]
    exact hclose

end NormalNumbers.Adder
