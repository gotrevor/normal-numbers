/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.MahlerNumCert

/-!
# The run+jump chain: `M(p,1) ≥ b(p − b − 1)` 🧮

Every background certificate so far (`MahlerFamilyI/II`, `MahlerBackgroundCert`,
`MahlerTwoJunction`, `MahlerFareyJunction`) uses one or two backgrounds.  The
2026-09-08 reflection lap mapped the whole space and found the unique *free*
skeleton: the descending run of **consecutive integers**

    p − b,  p − b − 1,  …,  b + 1,  b

closed by the single jump `b → p − b`.  In the model of `PENDING_WORK.md`
§Reflection 2026-09-08 — backgrounds `D`, junction `D → D'` costing `D'(p − D)`,
vertex condition `−D_prev/D_next ∈ ⟨p⟩ (mod D)` — every vertex of this cycle is
free except the bottom one:

* interior `D` (`prev = D+1 ≡ 1`, `next = D−1 ≡ −1`): the condition is `p^f ≡ 1`;
* the top `D = p − b` (`p ≡ b`, `prev = b ≡ p`, `next ≡ −1`): `p^f ≡ p`, `f = 1`;
* the bottom `D = b` (`prev = b+1 ≡ 1`, `next = p−b ≡ p`): `p^{f+1} ≡ −1 (mod b)`
  — **the only arithmetic condition in the whole construction.**

The bottleneck is `min_D (D−1)(p−D)` over the run, attained at both ends and
equal to `b(p − b − 1)`, so

> **`M(p,1) ≥ b(p − b − 1)` whenever `3 ≤ b < p/2` and `−1 ∈ ⟨p⟩ (mod b)`.**

`−1 ∈ ⟨p⟩ (mod b)` is FREE when `b ∣ p + 1` (then `p ≡ −1`), which gives the two
unconditional corollaries `b = (p+1)/3` (constant `2/9`) and `b = (p+1)/4`
(constant `3/16`), covering every prime `p ≢ 1 (mod 12)`.

Validated before formalising: 2512 `(p,b)` pairs over primes `11 … 397`, zero
mismatches (`experiments/mahler_runjump.py`), and the model itself reproduces the
exact census (`experiments/mahler_bg_cycle_model.py`).

## Why this file does NOT go through `NumCert`

A numerator certificate needs ONE common denominator `E` for every state.  Here
there are `Θ(p)` backgrounds, so `E` would be `p · lcm(b … p−b)` and the junction
perturbations `1/(p D D')` would be enormous multiples of `1/E`, breaking the
`δ < (p−1)σ` slack budget.  Instead this file instantiates `EscapeCert` directly
with **rational intervals of per-background width**

    wid i = 1/(p · Dh i · Dn i),

which is exactly the scale at which the junction perturbation is absorbed.
-/

namespace NormalNumbers.Adder.RunJump

open NormalNumbers NormalNumbers.Mahler

/-! ### The backgrounds -/

/-- The background at index `i`: `Dh b i = b + i`.  With `p = 2b + L` the run is
`i = L` (`Dh = p − b`) down to `i = 0` (`Dh = b`). -/
def Dh (b i : ℕ) : ℕ := b + i

/-- The index of the next background in the cycle: `i ↦ i − 1` along the run, and
the closing jump `0 ↦ L`. -/
def nx (L i : ℕ) : ℕ := if i = 0 then L else i - 1

/-- The background the junction at `i` lands in. -/
def Dn (b L i : ℕ) : ℕ := Dh b (nx L i)

theorem Dh_pos {b : ℕ} (hb : 0 < b) (i : ℕ) : 0 < Dh b i := by unfold Dh; omega

theorem nx_le {L i : ℕ} (hi : i ≤ L) : nx L i ≤ L := by unfold nx; split <;> omega

theorem Dn_pos {b : ℕ} (hb : 0 < b) (L i : ℕ) : 0 < Dn b L i := Dh_pos hb _

theorem Dh_le {b L i : ℕ} (hi : i ≤ L) : Dh b i ≤ b + L := by unfold Dh; omega

theorem Dn_le {b L i : ℕ} (hi : i ≤ L) : Dn b L i ≤ b + L := Dh_le (nx_le hi)

/-! ### The certificate data -/

/-- The per-junction data of a run+jump cycle in base `p`.

* `al i` is the **departure** residue in background `Dh i`;
* `cj i` is the **injection source** (`p · cj ≡ al`);
* `ap i` is the **landing** residue in `Dn i`;
* `dj i` is the digit emitted by the junction.

The single identity `key` says the landing is EXACT; reducing it mod `Dh i` gives
the departure condition `p · al · Dn ≡ −1`, and mod `Dn i` the landing condition
`ap · Dh ≡ 1`. -/
structure Data (p b L : ℕ) where
  al : ℕ → ℕ
  cj : ℕ → ℕ
  ap : ℕ → ℕ
  dj : ℕ → ℕ

/-- The hypotheses making `Data` a valid run+jump cycle. -/
structure Hyp (p b L : ℕ) (D : Data p b L) : Prop where
  hb : 3 ≤ b
  hL : 1 ≤ L
  hp : p = 2 * b + L
  al_lt : ∀ i, i ≤ L → D.al i < Dh b i
  cj_lt : ∀ i, i ≤ L → D.cj i < Dh b i
  ap_lt : ∀ i, i ≤ L → D.ap i < Dn b L i
  dj_lt : ∀ i, i ≤ L → D.dj i < p
  inj : ∀ i, i ≤ L → D.cj i * p % Dh b i = D.al i
  key : ∀ i, i ≤ L →
    p * D.al i * Dn b L i + 1 = D.ap i * Dh b i + D.dj i * (Dh b i * Dn b L i)

/-! ### States

`S = (L+1)·p + (L+1)`.  A **far** state `(i, a)` with `i ≤ L` sits at index
`i·p + a` and carries the value `a/Dh i`; a **junction** state `J i` sits at index
`(L+1)·p + i`.  Since every background is `< p`, `s.1 / p` decodes the kind:
`≤ L` means far (with `i = s.1/p`, `a = s.1 % p`), `= L+1` means the junction
`J (s.1 % p)`.  Indices whose residue exceeds the background are harmless
aliases: every definition reduces `s.1 % p` mod `Dh`. -/

/-- The number of states. -/
def S (p _b L : ℕ) : ℕ := (L + 1) * p + (L + 1)

theorem S_pos (p b L : ℕ) : 0 < S p b L := by unfold S; omega

/-- The far state `(i, a)`, value `(a mod Dh i)/Dh i`. -/
def far (p b L i a : ℕ) : Fin (S p b L) :=
  ⟨(i % (L + 1) * p + a % Dh b (i % (L + 1)) % p) % S p b L,
    Nat.mod_lt _ (S_pos p b L)⟩

/-- The junction state `J i`. -/
def jn (p b L i : ℕ) : Fin (S p b L) := ⟨((L + 1) * p + i % (L + 1)) % S p b L,
  Nat.mod_lt _ (S_pos p b L)⟩

variable {p b L : ℕ}

/-- Decoded index of a state. -/
def ix (s : Fin (S p b L)) : ℕ := s.1 / p

/-- Decoded residue of a state. -/
def rs (s : Fin (S p b L)) : ℕ := s.1 % p

/-! ### The certificate -/

variable (p b L)

/-- The half-width of the tail interval at background `i`. -/
def wid (i : ℕ) : ℚ := 1 / ((p : ℚ) * Dh b i * Dn b L i)

variable {p b L}

/-- Emitted digits. -/
def dig (D : Data p b L) (s : Fin (S p b L)) : ℕ :=
  if ix s ≤ L then rs s % Dh b (ix s) * p / Dh b (ix s) else D.dj (rs s)

/-- Tail-interval left endpoints. -/
def lop (D : Data p b L) (s : Fin (S p b L)) : ℚ :=
  if ix s ≤ L then ((rs s % Dh b (ix s) : ℕ) : ℚ) / (Dh b (ix s) : ℚ)
  else ((D.al (rs s) : ℚ) * (p : ℚ) * (Dn b L (rs s) : ℚ) + 1)
        / ((p : ℚ) * (Dh b (rs s) : ℚ) * (Dn b L (rs s) : ℚ))

/-- Tail-interval right endpoints. -/
def hip (D : Data p b L) (s : Fin (S p b L)) : ℚ :=
  lop D s + (if ix s ≤ L then wid p b L (ix s) else wid p b L (nx L (rs s)) / (p : ℚ))

/-- Carries. -/
def cc (D : Data p b L) (s : Fin (S p b L)) (m : ℕ) : ℕ :=
  if ix s ≤ L then m * (rs s % Dh b (ix s)) / Dh b (ix s)
  else m * (D.al (rs s) * p * Dn b L (rs s) + 1) / (p * Dh b (rs s) * Dn b L (rs s))

/-- Successors: the far cycle, the injections, the landings. -/
def nxt (D : Data p b L) (s : Fin (S p b L)) : List (Fin (S p b L)) :=
  if ix s ≤ L then
    [far p b L (ix s) (rs s % Dh b (ix s) * p)] ++
      (if rs s % Dh b (ix s) = D.cj (ix s) then [jn p b L (ix s)] else [])
  else [far p b L (nx L (rs s)) (D.ap (rs s))]

/-! ### Decoding -/

/-- Division with remainder, in the form the state encoding needs. -/
theorem dm {i r q : ℕ} (hq : 0 < q) (hr : r < q) :
    (i * q + r) / q = i ∧ (i * q + r) % q = r := by
  have e : i * q + r = r + q * i := by ring
  refine ⟨?_, ?_⟩
  · rw [e, Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt hr, zero_add]
  · rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]

section decode

variable (hb : 3 ≤ b) (hp : p = 2 * b + L)
include hb hp

theorem p_pos : 0 < p := by omega

theorem Dh_lt_p {i : ℕ} (hi : i ≤ L) : Dh b i < p := by unfold Dh; omega

theorem Dn_lt_p {i : ℕ} (hi : i ≤ L) : Dn b L i < p := Dh_lt_p hb hp (nx_le hi)

theorem rs_lt_p {i a : ℕ} (hi : i ≤ L) : a % Dh b i < p :=
  lt_of_lt_of_le (Nat.mod_lt _ (Dh_pos (by omega) i)) (le_of_lt (Dh_lt_p hb hp hi))

theorem far_val {i a : ℕ} (hi : i ≤ L) : (far p b L i a).1 = i * p + a % Dh b i := by
  have hr := rs_lt_p hb hp (i := i) (a := a) hi
  have hmod : i % (L + 1) = i := Nat.mod_eq_of_lt (by omega)
  have hlt : i * p + a % Dh b i < S p b L := by
    have h1 : i * p + p ≤ (L + 1) * p := by
      have := Nat.mul_le_mul_right p (show i + 1 ≤ L + 1 by omega)
      simpa [Nat.add_mul] using this
    unfold S; omega
  show (i % (L + 1) * p + a % Dh b (i % (L + 1)) % p) % S p b L = i * p + a % Dh b i
  rw [hmod, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hlt]

theorem ix_far {i a : ℕ} (hi : i ≤ L) : ix (far p b L i a) = i := by
  unfold ix; rw [far_val hb hp hi]; exact (dm (p_pos hb hp) (rs_lt_p hb hp hi)).1

theorem rs_far {i a : ℕ} (hi : i ≤ L) : rs (far p b L i a) = a % Dh b i := by
  unfold rs; rw [far_val hb hp hi]; exact (dm (p_pos hb hp) (rs_lt_p hb hp hi)).2

omit hb hp in
theorem jn_val {i : ℕ} (hi : i ≤ L) : (jn p b L i).1 = (L + 1) * p + i := by
  have hmod : i % (L + 1) = i := Nat.mod_eq_of_lt (by omega)
  show ((L + 1) * p + i % (L + 1)) % S p b L = (L + 1) * p + i
  rw [hmod, Nat.mod_eq_of_lt (by unfold S; omega)]

theorem ix_jn {i : ℕ} (hi : i ≤ L) : ix (jn p b L i) = L + 1 := by
  unfold ix; rw [jn_val hi]; exact (dm (p_pos hb hp) (show i < p by omega)).1

theorem rs_jn {i : ℕ} (hi : i ≤ L) : rs (jn p b L i) = i := by
  unfold rs; rw [jn_val hi]; exact (dm (p_pos hb hp) (show i < p by omega)).2

/-- Every state is far (index `≤ L`) or a junction (index `L+1`, residue `≤ L`). -/
theorem state_cases (s : Fin (S p b L)) : ix s ≤ L ∨ (ix s = L + 1 ∧ rs s ≤ L) := by
  have hS := s.2
  have hp0 : 0 < p := by omega
  have hdm := Nat.div_add_mod s.1 p
  have hmlt := Nat.mod_lt s.1 hp0
  unfold S at hS
  rcases Nat.lt_or_ge (s.1 / p) (L + 1) with h | h
  · exact Or.inl (by unfold ix; omega)
  · right
    have hcomm2 : s.1 / p * p = p * (s.1 / p) := by ring
    have hge : (L + 1) * p ≤ s.1 / p * p := Nat.mul_le_mul_right p h
    have hne : s.1 / p = L + 1 := by
      by_contra hc
      have h2 : L + 2 ≤ s.1 / p := by omega
      have : (L + 2) * p ≤ s.1 / p * p := Nat.mul_le_mul_right p h2
      have hexp : (L + 2) * p = (L + 1) * p + p := by ring
      omega
    refine ⟨hne, ?_⟩
    unfold rs
    rw [hne] at hdm
    have hcomm : p * (L + 1) = (L + 1) * p := by ring
    omega

end decode

/-- The run+jump escape certificate. -/
def cert (D : Data p b L) : EscapeCert p where
  n := S p b L
  a := dig D
  next := nxt D
  lo := lop D
  hi := hip D
  c := cc D

/-! ### Validity

`M(p,1) ≥ b(p − b − 1)`, i.e. every channel `M < b·(b + L − 1)` (note `p − b = b + L`).
The six `EscapeCert.Valid` components are proved separately below. -/

section valid

variable {D : Data p b L} (h : Hyp p b L D) {M : ℕ} (hM : M < b * (b + L - 1))
include h

theorem hb' : 3 ≤ b := h.hb
theorem hp' : p = 2 * b + L := h.hp

/-- Reduced residue of a far state, as a natural `< Dh`. -/
theorem rsr_lt (s : Fin (S p b L)) (hs : ix s ≤ L) : rs s % Dh b (ix s) < Dh b (ix s) := by
  have hb3 : 3 ≤ b := h.hb
  exact Nat.mod_lt _ (Dh_pos (by omega) _)

/-- **Digits are legal.** -/
theorem dig_lt (s : Fin (S p b L)) : dig D s < p := by
  have hb3 : 3 ≤ b := h.hb
  have hpe : p = 2 * b + L := h.hp
  unfold dig
  rcases state_cases h.hb h.hp s with hs | ⟨hs, hr⟩
  · rw [if_pos hs]
    have hD := Dh_pos (show 0 < b by omega) (ix s)
    have := rsr_lt h s hs
    rw [Nat.div_lt_iff_lt_mul hD]
    calc rs s % Dh b (ix s) * p < Dh b (ix s) * p :=
          Nat.mul_lt_mul_of_lt_of_le this (le_refl p) (by omega)
      _ = p * Dh b (ix s) := by ring
  · rw [if_neg (by omega)]
    exact h.dj_lt _ hr

omit h in
/-- `Dh` and `Dn` are at least `b` and at most `b + L`. -/
theorem Dh_bounds (i : ℕ) (hi : i ≤ L) : b ≤ Dh b i ∧ Dh b i ≤ b + L := by
  unfold Dh; omega

omit h in
theorem Dn_bounds (i : ℕ) (hi : i ≤ L) : b ≤ Dn b L i ∧ Dn b L i ≤ b + L := by
  unfold Dn Dh; have := nx_le hi; omega

theorem intervals (s : Fin (S p b L)) :
    0 ≤ lop D s ∧ lop D s ≤ hip D s ∧ hip D s ≤ 1 := by
  have hb3 : 3 ≤ b := h.hb
  have hpe : p = 2 * b + L := h.hp
  have hL1 : 1 ≤ L := h.hL
  have hp0 : 0 < p := by omega
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hp0
  rcases state_cases hb3 hpe s with hs | ⟨hs, hr⟩
  · -- far state
    have hdb := Dh_bounds (b := b) (L := L) (ix s) hs
    have hdnb := Dn_bounds (b := b) (L := L) (ix s) hs
    have hd0 : 0 < Dh b (ix s) := by omega
    have hdn0 : 0 < Dn b L (ix s) := by omega
    have hdQ : (0 : ℚ) < (Dh b (ix s) : ℚ) := by exact_mod_cast hd0
    have hdnQ : (0 : ℚ) < (Dn b L (ix s) : ℚ) := by exact_mod_cast hdn0
    have hr1 : rs s % Dh b (ix s) < Dh b (ix s) := Nat.mod_lt _ hd0
    have hlo : lop D s = ((rs s % Dh b (ix s) : ℕ) : ℚ) / (Dh b (ix s) : ℚ) := by
      unfold lop; rw [if_pos hs]
    have hwi : hip D s = lop D s + 1 / ((p : ℚ) * Dh b (ix s) * Dn b L (ix s)) := by
      unfold hip wid; rw [if_pos hs]
    have hpos : (0 : ℚ) < 1 / ((p : ℚ) * Dh b (ix s) * Dn b L (ix s)) := by positivity
    refine ⟨by rw [hlo]; positivity, by rw [hwi]; linarith, ?_⟩
    rw [hwi, hlo]
    have hcomb : ((rs s % Dh b (ix s) : ℕ) : ℚ) / (Dh b (ix s) : ℚ)
          + 1 / ((p : ℚ) * Dh b (ix s) * Dn b L (ix s))
        = (((rs s % Dh b (ix s) : ℕ) : ℚ) * p * Dn b L (ix s) + 1)
          / ((p : ℚ) * Dh b (ix s) * Dn b L (ix s)) := by
      field_simp
    rw [hcomb, div_le_one (by positivity)]
    have hpdn : 1 ≤ p * Dn b L (ix s) := Nat.mul_pos hp0 hdn0
    have hnat : rs s % Dh b (ix s) * p * Dn b L (ix s) + 1
        ≤ p * Dh b (ix s) * Dn b L (ix s) := by
      have h1 : (rs s % Dh b (ix s) + 1) * (p * Dn b L (ix s))
          ≤ Dh b (ix s) * (p * Dn b L (ix s)) := Nat.mul_le_mul hr1 (le_refl _)
      have h2 : (rs s % Dh b (ix s) + 1) * (p * Dn b L (ix s))
          = rs s % Dh b (ix s) * p * Dn b L (ix s) + p * Dn b L (ix s) := by ring
      have h3 : Dh b (ix s) * (p * Dn b L (ix s)) = p * Dh b (ix s) * Dn b L (ix s) := by ring
      omega
    calc ((rs s % Dh b (ix s) : ℕ) : ℚ) * p * Dn b L (ix s) + 1
        = ((rs s % Dh b (ix s) * p * Dn b L (ix s) + 1 : ℕ) : ℚ) := by push_cast; ring
      _ ≤ ((p * Dh b (ix s) * Dn b L (ix s) : ℕ) : ℚ) := by exact_mod_cast hnat
      _ = (p : ℚ) * Dh b (ix s) * Dn b L (ix s) := by push_cast; ring
  · -- junction state
    have hdb := Dh_bounds (b := b) (L := L) (rs s) hr
    have hdnb := Dn_bounds (b := b) (L := L) (rs s) hr
    have hd'b := Dh_bounds (b := b) (L := L) (nx L (rs s)) (nx_le hr)
    have hdn'b := Dn_bounds (b := b) (L := L) (nx L (rs s)) (nx_le hr)
    have ha := h.al_lt (rs s) hr
    have hd0 : 0 < Dh b (rs s) := by omega
    have hdn0 : 0 < Dn b L (rs s) := by omega
    have hdQ : (0 : ℚ) < (Dh b (rs s) : ℚ) := by exact_mod_cast hd0
    have hdnQ : (0 : ℚ) < (Dn b L (rs s) : ℚ) := by exact_mod_cast hdn0
    have hd'Q : (0 : ℚ) < (Dh b (nx L (rs s)) : ℚ) := by exact_mod_cast (show 0 < Dh b (nx L (rs s)) by omega)
    have hdn'Q : (0 : ℚ) < (Dn b L (nx L (rs s)) : ℚ) := by
      exact_mod_cast (show 0 < Dn b L (nx L (rs s)) by omega)
    have hlo : lop D s
        = ((D.al (rs s) : ℚ) * p * Dn b L (rs s) + 1)
          / ((p : ℚ) * Dh b (rs s) * Dn b L (rs s)) := by
      unfold lop; rw [if_neg (by omega)]
    have hwi : hip D s = lop D s
        + 1 / ((p : ℚ) * Dh b (nx L (rs s)) * Dn b L (nx L (rs s))) / (p : ℚ) := by
      unfold hip wid; rw [if_neg (by omega)]
    have hpos : (0 : ℚ)
        < 1 / ((p : ℚ) * Dh b (nx L (rs s)) * Dn b L (nx L (rs s))) / (p : ℚ) := by positivity
    refine ⟨by rw [hlo]; positivity, by rw [hwi]; linarith, ?_⟩
    rw [hwi, hlo]
    have hcomb : ((D.al (rs s) : ℚ) * p * Dn b L (rs s) + 1)
            / ((p : ℚ) * Dh b (rs s) * Dn b L (rs s))
          + 1 / ((p : ℚ) * Dh b (nx L (rs s)) * Dn b L (nx L (rs s))) / (p : ℚ)
        = (((D.al (rs s) : ℚ) * p * Dn b L (rs s) + 1)
              * ((p : ℚ) * Dh b (nx L (rs s)) * Dn b L (nx L (rs s)))
            + (Dh b (rs s) : ℚ) * Dn b L (rs s))
          / (((p : ℚ) * Dh b (rs s) * Dn b L (rs s))
              * ((p : ℚ) * Dh b (nx L (rs s)) * Dn b L (nx L (rs s)))) := by
      field_simp
    rw [hcomb, div_le_one (by positivity)]
    -- the natural-number core
    set A := D.al (rs s) with hA
    set d := Dh b (rs s) with hd
    set dn := Dn b L (rs s) with hdn
    set P := p * Dh b (nx L (rs s)) * Dn b L (nx L (rs s)) with hP
    have hpdn : 1 ≤ p * dn := Nat.mul_pos hp0 hdn0
    obtain ⟨u, hu⟩ : ∃ u, p * dn = u + 1 := ⟨p * dn - 1, by omega⟩
    have hPb : p * (b * b) ≤ P := by
      rw [hP]
      calc p * (b * b) = p * b * b := by ring
        _ ≤ p * Dh b (nx L (rs s)) * b := Nat.mul_le_mul_right b (Nat.mul_le_mul_left p hd'b.1)
        _ ≤ p * Dh b (nx L (rs s)) * Dn b L (nx L (rs s)) := Nat.mul_le_mul_left _ hdn'b.1
    have hpdn21 : 21 ≤ p * dn := by nlinarith [hdnb.1, hb3, hpe, hL1]
    have hstep : p * d * dn ≤ u * P := by
      have c1 : d * dn ≤ (b + L) * dn := Nat.mul_le_mul_right dn hdb.2
      have c2 : (b + L) * dn ≤ p * dn := Nat.mul_le_mul_right dn (by omega)
      have c3 : p * dn ≤ 9 * u := by omega
      have c4 : 9 * u ≤ b * b * u := Nat.mul_le_mul_right u (by nlinarith)
      have c5 : d * dn ≤ b * b * u := by omega
      calc p * d * dn = p * (d * dn) := by ring
        _ ≤ p * (b * b * u) := Nat.mul_le_mul_left p c5
        _ = p * (b * b) * u := by ring
        _ ≤ P * u := Nat.mul_le_mul_right u hPb
        _ = u * P := by ring
    have hmid : A * p * dn + u + 1 ≤ p * d * dn := by
      have e1 : (A + 1) * (p * dn) ≤ d * (p * dn) := Nat.mul_le_mul ha (le_refl _)
      have e2 : (A + 1) * (p * dn) = A * p * dn + p * dn := by ring
      have e3 : d * (p * dn) = p * d * dn := by ring
      omega
    have hnat : (A * p * dn + 1) * P + p * d * dn ≤ (p * d * dn) * P := by
      have hfin : (A * p * dn + u + 1) * P ≤ (p * d * dn) * P := Nat.mul_le_mul_right P hmid
      have hexp : (A * p * dn + u + 1) * P = (A * p * dn + 1) * P + u * P := by ring
      omega
    have hnat' : (A * p * dn + 1) * P + d * dn ≤ (p * d * dn) * P := by
      have : d * dn ≤ p * d * dn := by
        calc d * dn = 1 * (d * dn) := by ring
          _ ≤ p * (d * dn) := Nat.mul_le_mul_right _ hp0
          _ = p * d * dn := by ring
      omega
    have hPQ : (P : ℚ) = (p : ℚ) * Dh b (nx L (rs s)) * Dn b L (nx L (rs s)) := by
      rw [hP]; push_cast; ring
    rw [← hPQ]
    calc ((A : ℚ) * p * dn + 1) * (P : ℚ) + (d : ℚ) * dn
        = (((A * p * dn + 1) * P + d * dn : ℕ) : ℚ) := by push_cast; ring
      _ ≤ (((p * d * dn) * P : ℕ) : ℚ) := by exact_mod_cast hnat'
      _ = ((p : ℚ) * d * dn) * (P : ℚ) := by push_cast; ring

theorem edges (s : Fin (S p b L)) (s' : Fin (S p b L)) (hs' : s' ∈ nxt D s) :
    lop D s ≤ ((dig D s : ℚ) + lop D s') / p ∧
      ((dig D s : ℚ) + hip D s') / p ≤ hip D s := by
  sorry

include hM in
theorem carries (m : ℕ) (hm : m ≤ M) (s : Fin (S p b L)) :
    ((cc D s m : ℕ) : ℚ) ≤ m * lop D s ∧ m * hip D s ≤ (cc D s m : ℚ) + 1 := by
  sorry

include hM in
theorem recursion (m : ℕ) (hm : m ≤ M) (s s' : Fin (S p b L)) (hs' : s' ∈ nxt D s) :
    cc D s m = (m * dig D s + cc D s' m) / p := by
  sorry

include hM in
theorem block (m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ M) (s s' : Fin (S p b L)) (hs' : s' ∈ nxt D s) :
    (m * dig D s + cc D s' m) % p ≠ p - 1 := by
  sorry

include hM in
/-- **The run+jump certificate is valid up to `M < b(p − b − 1)`.** -/
theorem valid : (cert D).Valid M [p - 1] := by
  refine ⟨dig_lt h, intervals h, ?_, ?_, ?_, ?_⟩
  · intro s s' hs'; exact edges h s s' hs'
  · intro m hm s; exact carries h hM m hm s
  · intro m hm s s' hs'; exact recursion h hM m hm s s' hs'
  · intro m hm1 hm σ hσ
    have hedge : σ 1 ∈ nxt D (σ 0) := hσ 0
    simp only [List.length_singleton, List.ofFn_succ, List.ofFn_zero, ne_eq, List.cons.injEq,
      and_true]
    show ¬ (cert D).chDigit m (σ 0) (σ 1) = p - 1
    unfold EscapeCert.chDigit
    exact block h hM m hm1 hm _ _ hedge

end valid

end NormalNumbers.Adder.RunJump
