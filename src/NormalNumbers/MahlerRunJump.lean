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

/-! ### The generic edge

Every edge `s → s'` of the certificate has the shape: `lo s = N/E`, `lo s' = N'/E'`
with **local** denominators `E`, `E'`, the carries are `⌊m N / E⌋`, and the digit `d`
satisfies the exact integer identity

    d · E · E' + N' · E = p · N · E' + δ          (`δ ≥ 0`)

— the per-edge, two-denominator form of `NumCert.Good.edge`.  The six validity
components are consequences of this identity plus two inequalities:
the **block** inequality `p · (m N mod E) · E' + m δ + E E' < p E E'` and the
**carry** inequality `(m N mod E) + m · w · E ≤ E`. -/

section generic

variable {E E' N N' d δ : ℕ}

theorem gen_lo (hE : 0 < E) (hE' : 0 < E') (hp : 0 < p)
    (hV : d * E * E' + N' * E = p * N * E' + δ) :
    (N : ℚ) / E ≤ ((d : ℚ) + (N' : ℚ) / E') / p := by
  have hEQ : (0 : ℚ) < E := by exact_mod_cast hE
  have hE'Q : (0 : ℚ) < E' := by exact_mod_cast hE'
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hp
  have hVQ : (d : ℚ) * E * E' + N' * E = p * N * E' + δ := by exact_mod_cast hV
  have h1 : ((d : ℚ) + (N' : ℚ) / E') / p = ((p : ℚ) * N * E' + δ) / (E * E' * p) := by
    rw [← hVQ]; field_simp
  have h2 : (N : ℚ) / E = ((p : ℚ) * N * E') / (E * E' * p) := by field_simp
  rw [h1, h2]
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith [show (0 : ℚ) ≤ δ by positivity]

theorem gen_hi (hE : 0 < E) (hE' : 0 < E') (hp : 0 < p)
    (hV : d * E * E' + N' * E = p * N * E' + δ) {w w' : ℚ}
    (hw : (δ : ℚ) / (E * E') + w' ≤ p * w) :
    ((d : ℚ) + ((N' : ℚ) / E' + w')) / p ≤ (N : ℚ) / E + w := by
  have hEQ : (0 : ℚ) < E := by exact_mod_cast hE
  have hE'Q : (0 : ℚ) < E' := by exact_mod_cast hE'
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hp
  have hVQ : (d : ℚ) * E * E' + N' * E = p * N * E' + δ := by exact_mod_cast hV
  have h1 : (d : ℚ) + (N' : ℚ) / E' = p * ((N : ℚ) / E) + (δ : ℚ) / (E * E') := by
    have e1 : (d : ℚ) + (N' : ℚ) / E' = ((d : ℚ) * E * E' + N' * E) / (E * E') := by
      field_simp
    rw [e1, hVQ]; field_simp
  rw [div_le_iff₀ hpQ, ← add_assoc, h1]
  nlinarith

theorem gen_carry_lo (m : ℕ) : ((m * N / E : ℕ) : ℚ) ≤ m * ((N : ℚ) / E) := by
  calc ((m * N / E : ℕ) : ℚ) ≤ ((m * N : ℕ) : ℚ) / (E : ℚ) := Nat.cast_div_le
    _ = m * ((N : ℚ) / E) := by push_cast; ring

theorem gen_carry_hi (hE : 0 < E) (m : ℕ) {w : ℚ}
    (hc : ((m * N % E : ℕ) : ℚ) + m * w * E ≤ E) :
    m * ((N : ℚ) / E + w) ≤ ((m * N / E : ℕ) : ℚ) + 1 := by
  have hEQ : (0 : ℚ) < E := by exact_mod_cast hE
  have hdm : (E : ℚ) * ((m * N / E : ℕ) : ℚ) + ((m * N % E : ℕ) : ℚ) = m * N := by
    exact_mod_cast Nat.div_add_mod (m * N) E
  have h1 : (m : ℚ) * ((N : ℚ) / E + w)
      = ((m * N / E : ℕ) : ℚ) + (((m * N % E : ℕ) : ℚ) + m * w * E) / E := by
    field_simp; linarith
  rw [h1]
  have : (((m * N % E : ℕ) : ℚ) + m * w * E) / E ≤ 1 := by
    rw [div_le_one hEQ]; exact hc
  linarith

/-- The two-denominator form of `NumCert.chDigit_eq`: the channel digit as a quotient. -/
theorem gen_x (hE : 0 < E) (hE' : 0 < E')
    (hV : d * E * E' + N' * E = p * N * E' + δ) (m : ℕ) :
    m * d + m * N' / E' = (p * (m * N % E) * E' + m * δ) / (E * E') + p * (m * N / E) := by
  have hEE : 0 < E * E' := Nat.mul_pos hE hE'
  have hdm := Nat.div_add_mod (m * N) E
  have hdm' := Nat.div_add_mod (m * N') E'
  set c := m * N / E with hc
  set r := m * N % E with hr
  set c' := m * N' / E' with hc'
  set r' := m * N' % E' with hr'
  have hr'lt : r' < E' := Nat.mod_lt _ hE'
  have hVm : m * (d * E * E') + m * N' * E = p * (m * N) * E' + m * δ := by
    calc m * (d * E * E') + m * N' * E = m * (d * E * E' + N' * E) := by ring
      _ = m * (p * N * E' + δ) := by rw [hV]
      _ = p * (m * N) * E' + m * δ := by ring
  rw [← hdm, ← hdm'] at hVm
  have hsplit : (E * E') * (m * d + c') + r' * E = (E * E') * (p * c) + (p * r * E' + m * δ) := by
    linear_combination hVm
  have hlt : r' * E < E * E' := by
    calc r' * E < E' * E := Nat.mul_lt_mul_of_pos_right hr'lt hE
      _ = E * E' := by ring
  calc m * d + c' = ((E * E') * (m * d + c') + r' * E) / (E * E') := by
        rw [Nat.mul_add_div hEE, Nat.div_eq_of_lt hlt, add_zero]
    _ = ((E * E') * (p * c) + (p * r * E' + m * δ)) / (E * E') := by rw [hsplit]
    _ = (p * r * E' + m * δ) / (E * E') + p * c := by
        rw [Nat.mul_add_div hEE, add_comm]

theorem gen_rec (hE : 0 < E) (hE' : 0 < E') (hp : 0 < p)
    (hV : d * E * E' + N' * E = p * N * E' + δ) (m : ℕ)
    (hblk : p * (m * N % E) * E' + m * δ + E * E' < p * (E * E')) :
    m * N / E = (m * d + m * N' / E') / p := by
  have hEE : 0 < E * E' := Nat.mul_pos hE hE'
  rw [gen_x hE hE' hV m]
  have hx : (p * (m * N % E) * E' + m * δ) / (E * E') < p := by
    rw [Nat.div_lt_iff_lt_mul hEE]; omega
  rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hx, zero_add]

theorem gen_block (hE : 0 < E) (hE' : 0 < E') (hp : 0 < p)
    (hV : d * E * E' + N' * E = p * N * E' + δ) (m : ℕ)
    (hblk : p * (m * N % E) * E' + m * δ + E * E' < p * (E * E')) :
    (m * d + m * N' / E') % p ≠ p - 1 := by
  have hEE : 0 < E * E' := Nat.mul_pos hE hE'
  rw [gen_x hE hE' hV m]
  have hx : (p * (m * N % E) * E' + m * δ) / (E * E') < p - 1 := by
    rw [Nat.div_lt_iff_lt_mul hEE]
    have : (p - 1) * (E * E') + E * E' = p * (E * E') := by
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      rw [Nat.add_sub_cancel]; ring
    omega
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  omega

end generic

/-! ### Local numerator data of a state -/

/-- Local denominator: `Dh i` at a far state, `p · Dh i · Dn i` at the junction `J i`. -/
def En (s : Fin (S p b L)) : ℕ :=
  if ix s ≤ L then Dh b (ix s) else p * Dh b (rs s) * Dn b L (rs s)

/-- Local numerator. -/
def Nn (D : Data p b L) (s : Fin (S p b L)) : ℕ :=
  if ix s ≤ L then rs s % Dh b (ix s) else D.al (rs s) * p * Dn b L (rs s) + 1

/-- Interval width. -/
def wd (s : Fin (S p b L)) : ℚ :=
  if ix s ≤ L then wid p b L (ix s) else wid p b L (nx L (rs s)) / (p : ℚ)

theorem lop_eq (D : Data p b L) (s : Fin (S p b L)) : lop D s = (Nn D s : ℚ) / (En s : ℚ) := by
  unfold lop Nn En; split_ifs <;> push_cast <;> ring

theorem hip_eq (D : Data p b L) (s : Fin (S p b L)) : hip D s = lop D s + wd s := by
  unfold hip wd; rfl

theorem cc_eq (D : Data p b L) (s : Fin (S p b L)) (m : ℕ) : cc D s m = m * Nn D s / En s := by
  unfold cc Nn En; split_ifs <;> rfl

section decode2

variable (hb : 3 ≤ b) (hp : p = 2 * b + L)
include hb hp

theorem En_pos (s : Fin (S p b L)) : 0 < En s := by
  unfold En; split_ifs
  · exact Dh_pos (by omega) _
  · exact Nat.mul_pos (Nat.mul_pos (by omega) (Dh_pos (by omega) _)) (Dn_pos (by omega) _ _)

omit hb hp in
theorem En_far {s : Fin (S p b L)} (hs : ix s ≤ L) : En s = Dh b (ix s) := by
  unfold En; rw [if_pos hs]

omit hb hp in
theorem Nn_far {D : Data p b L} {s : Fin (S p b L)} (hs : ix s ≤ L) :
    Nn D s = rs s % Dh b (ix s) := by
  unfold Nn; rw [if_pos hs]

omit hb hp in
theorem wd_far {s : Fin (S p b L)} (hs : ix s ≤ L) : wd s = wid p b L (ix s) := by
  unfold wd; rw [if_pos hs]

omit hb hp in
theorem dig_far {D : Data p b L} {s : Fin (S p b L)} (hs : ix s ≤ L) :
    dig D s = rs s % Dh b (ix s) * p / Dh b (ix s) := by
  unfold dig; rw [if_pos hs]

omit hb hp in
theorem En_jn {s : Fin (S p b L)} (hs : ix s = L + 1) :
    En s = p * Dh b (rs s) * Dn b L (rs s) := by
  unfold En; rw [if_neg (by omega)]

omit hb hp in
theorem Nn_jn {D : Data p b L} {s : Fin (S p b L)} (hs : ix s = L + 1) :
    Nn D s = D.al (rs s) * p * Dn b L (rs s) + 1 := by
  unfold Nn; rw [if_neg (by omega)]

omit hb hp in
theorem wd_jn {s : Fin (S p b L)} (hs : ix s = L + 1) :
    wd s = wid p b L (nx L (rs s)) / (p : ℚ) := by
  unfold wd; rw [if_neg (by omega)]

omit hb hp in
theorem dig_jn {D : Data p b L} {s : Fin (S p b L)} (hs : ix s = L + 1) :
    dig D s = D.dj (rs s) := by
  unfold dig; rw [if_neg (by omega)]

/-- The three edge types. -/
theorem nxt_cases {D : Data p b L} {s s' : Fin (S p b L)} (hs' : s' ∈ nxt D s) :
    (ix s ≤ L ∧ s' = far p b L (ix s) (rs s % Dh b (ix s) * p)) ∨
    (ix s ≤ L ∧ rs s % Dh b (ix s) = D.cj (ix s) ∧ s' = jn p b L (ix s)) ∨
    (ix s = L + 1 ∧ rs s ≤ L ∧ s' = far p b L (nx L (rs s)) (D.ap (rs s))) := by
  unfold nxt at hs'
  rcases state_cases hb hp s with hs | ⟨hs, hr⟩
  · rw [if_pos hs] at hs'
    simp only [List.singleton_append, List.mem_cons] at hs'
    rcases hs' with h1 | h1
    · exact Or.inl ⟨hs, h1⟩
    · split_ifs at h1 with hc
      · simp only [List.mem_singleton] at h1
        exact Or.inr (Or.inl ⟨hs, hc, h1⟩)
      · simp at h1
  · rw [if_neg (by omega)] at hs'
    simp only [List.mem_singleton] at hs'
    exact Or.inr (Or.inr ⟨hs, hr, hs'⟩)

end decode2

/-! ### Validity

`M(p,1) ≥ b(p − b − 1)`, i.e. every channel `M < b·(b + L − 1)` (note `p − b = b + L`).
The six `EscapeCert.Valid` components are proved separately below. -/

section valid

variable {D : Data p b L} (h : Hyp p b L D) {M : ℕ} (hM : M < b * (b + L - 1))
include h

theorem hb' : 3 ≤ b := h.hb
theorem hp' : p = 2 * b + L := h.hp

/-- Reduced residue of a far state, as a natural `< Dh`. -/
theorem rsr_lt (s : Fin (S p b L)) (_hs : ix s ≤ L) : rs s % Dh b (ix s) < Dh b (ix s) := by
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

/-! ### The numeric core -/

omit h in
/-- **The junction cost.**  `Dn i · (p − Dh i) ≥ b (b + L − 1)` along the whole run, with
equality at both ends (`i = 1` and `i = L`); the closing jump (`i = 0`) costs `(b+L)²`. -/
theorem cost_ge (hb : 3 ≤ b) (hL : 1 ≤ L) (hp : p = 2 * b + L) (i : ℕ) (hi : i ≤ L) :
    b * (b + L - 1) + Dn b L i * Dh b i ≤ p * Dn b L i := by
  unfold Dn Dh nx
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  rw [show b + (L' + 1) - 1 = b + L' by omega]
  split_ifs with h0
  · subst h0; subst hp; nlinarith
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [show j + 1 - 1 = j by omega]
    have hj : j * (j + 1) ≤ j * (L' + 1) := Nat.mul_le_mul_left j (by omega)
    subst hp; nlinarith

omit h in
/-- The junction residue: `m · (al p Dn + 1) mod (p Dh Dn) = p Dn (m al mod Dh) + m` when
`m < p Dn` (no overflow). -/
theorem jmod {al Dh Dn m : ℕ} (hDh : 0 < Dh) (hm : m < p * Dn) :
    m * (al * p * Dn + 1) % (p * Dh * Dn) = p * Dn * (m * al % Dh) + m := by
  have hdm := Nat.div_add_mod (m * al) Dh
  have hρ : m * al % Dh < Dh := Nat.mod_lt _ hDh
  set q := m * al / Dh
  set ρ := m * al % Dh
  have e : m * (al * p * Dn + 1) = (p * Dh * Dn) * q + (p * Dn * ρ + m) := by
    linear_combination (p * Dn) * hdm.symm
  have hlt : p * Dn * ρ + m < p * Dh * Dn := by
    have : p * Dn * (ρ + 1) ≤ p * Dn * Dh := Nat.mul_le_mul_left _ hρ
    nlinarith
  rw [e, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]

include hM in
theorem m_lt_pb {m : ℕ} (hm : m ≤ M) : m < p * b := by
  have hb3 : 3 ≤ b := h.hb
  have hpe : p = 2 * b + L := h.hp
  have : b * (b + L - 1) ≤ p * b := by
    calc b * (b + L - 1) ≤ b * p := Nat.mul_le_mul_left b (by omega)
      _ = p * b := by ring
  omega

include hM in
theorem m_cost {m : ℕ} (hm : m ≤ M) {i : ℕ} (hi : i ≤ L) :
    m + Dn b L i * Dh b i < p * Dn b L i := by
  have := cost_ge h.hb h.hL h.hp i hi
  omega

include hM in
/-- **Every edge is a generic edge**: the exact identity, the width inequality and the
block inequality. -/
theorem edge_data (s s' : Fin (S p b L)) (hs' : s' ∈ nxt D s) : ∃ δ,
    dig D s * En s * En s' + Nn D s' * En s = p * Nn D s * En s' + δ ∧
    (δ : ℚ) / (En s * En s') + wd s' ≤ p * wd s ∧
    ∀ m, m ≤ M → p * (m * Nn D s % En s) * En s' + m * δ + En s * En s' < p * (En s * En s') := by
  have hb3 : 3 ≤ b := h.hb
  have hpe : p = 2 * b + L := h.hp
  have hL1 : 1 ≤ L := h.hL
  have hp0 : 0 < p := by omega
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hp0
  rcases nxt_cases hb3 hpe hs' with ⟨hs, rfl⟩ | ⟨hs, hcj, rfl⟩ | ⟨hs, hr, rfl⟩
  · -- far → far
    set i := ix s with hi
    set r := rs s % Dh b i with hr
    have hd0 : 0 < Dh b i := Dh_pos (by omega) i
    have hdp : Dh b i < p := Dh_lt_p hb3 hpe hs
    have hix : ix (far p b L i (r * p)) = i := ix_far hb3 hpe hs
    have hrs : rs (far p b L i (r * p)) = r * p % Dh b i := rs_far hb3 hpe hs
    have hs2 : ix (far p b L i (r * p)) ≤ L := by rw [hix]; exact hs
    rw [En_far hs, En_far hs2, Nn_far hs, Nn_far hs2, wd_far hs, wd_far hs2, dig_far hs, hix, hrs,
      Nat.mod_mod, ← hr]
    refine ⟨0, ?_, ?_, ?_⟩
    · have := Nat.div_add_mod (r * p) (Dh b i)
      linear_combination (Dh b i) * this
    · have hw : (0 : ℚ) < wid p b L i := by
        have hdQ : (0 : ℚ) < Dh b i := by exact_mod_cast hd0
        have hdnQ : (0 : ℚ) < Dn b L i := by exact_mod_cast (Dn_pos (show 0 < b by omega) L i)
        unfold wid; exact div_pos one_pos (mul_pos (mul_pos hpQ hdQ) hdnQ)
      have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast hp0
      push_cast; rw [zero_div, zero_add]; nlinarith
    · intro m _
      have hρ : m * r % Dh b i + 1 ≤ Dh b i := Nat.mod_lt _ hd0
      have h1 : p * Dh b i * (m * r % Dh b i + 1) ≤ p * Dh b i * Dh b i := Nat.mul_le_mul_left _ hρ
      have h2 : Dh b i * Dh b i < p * Dh b i := Nat.mul_lt_mul_of_pos_right hdp hd0
      linarith
  · -- injection: far → junction
    set i := ix s with hi
    have hd0 : 0 < Dh b i := Dh_pos (by omega) i
    have hdn0 : 0 < Dn b L i := Dn_pos (by omega) L i
    have hdb := Dh_bounds (b := b) (L := L) i hs
    have hdnb := Dn_bounds (b := b) (L := L) i hs
    have hd'b := Dh_bounds (b := b) (L := L) (nx L i) (nx_le hs)
    have hdn'b := Dn_bounds (b := b) (L := L) (nx L i) (nx_le hs)
    have hix : ix (jn p b L i) = L + 1 := ix_jn hb3 hpe hs
    have hrs : rs (jn p b L i) = i := rs_jn hb3 hpe hs
    rw [En_far hs, En_jn hix, Nn_far hs, Nn_jn hix, wd_far hs, wd_jn hix,
      dig_far hs, hrs, hcj]
    refine ⟨Dh b i, ?_, ?_, ?_⟩
    · have hdm := Nat.div_add_mod (D.cj i * p) (Dh b i)
      rw [h.inj i hs] at hdm
      linear_combination (Dh b i * p * Dn b L i) * hdm
    · -- width: `p Dh' Dn' + Dh Dn ≤ p² Dh' Dn'`
      set d' := Dh b (nx L i) with hd'
      set dn' := Dn b L (nx L i) with hdn'
      have hnat : p * d' * dn' + Dh b i * Dn b L i ≤ p * p * d' * dn' := by
        obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
        have h9 : 9 ≤ d' * dn' := by nlinarith
        have hA : Dh b i * Dn b L i ≤ p * p := Nat.mul_le_mul (by omega) (by omega)
        have hB : p * (q + 1) ≤ p * (q * 9) := Nat.mul_le_mul_left p (by omega)
        have hC : p * q * 9 ≤ p * q * (d' * dn') := Nat.mul_le_mul_left _ h9
        calc p * d' * dn' + Dh b i * Dn b L i ≤ p * d' * dn' + p * (q * 9) := by
              rw [← hq] at hB; omega
          _ ≤ p * d' * dn' + p * q * (d' * dn') := by nlinarith
          _ = p * (q + 1) * d' * dn' := by ring
          _ = p * p * d' * dn' := by rw [← hq]
      have hdQ : (0 : ℚ) < Dh b i := by exact_mod_cast hd0
      have hdnQ : (0 : ℚ) < Dn b L i := by exact_mod_cast hdn0
      have hd'Q : (0 : ℚ) < d' := by exact_mod_cast (show 0 < d' by omega)
      have hdn'Q : (0 : ℚ) < dn' := by exact_mod_cast (show 0 < dn' by omega)
      unfold wid
      have e1 : (Dh b i : ℚ) / ((Dh b i : ℕ) * (p * Dh b i * Dn b L i : ℕ) : ℚ)
            + 1 / ((p : ℚ) * d' * dn') / p
          = ((p * d' * dn' + Dh b i * Dn b L i : ℕ) : ℚ)
            / ((p : ℚ) * p * Dh b i * Dn b L i * d' * dn') := by
        push_cast; field_simp; try ring
      have e2 : (p : ℚ) * (1 / ((p : ℚ) * Dh b i * Dn b L i))
          = ((p * p * d' * dn' : ℕ) : ℚ) / ((p : ℚ) * p * Dh b i * Dn b L i * d' * dn') := by
        push_cast; field_simp; try ring
      rw [e1, e2]
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hnat
    · intro m hm
      have hcost := m_cost h hM hm hs
      have hρ : m * D.cj i % Dh b i + 1 ≤ Dh b i := Nat.mod_lt _ hd0
      set ρ := m * D.cj i % Dh b i
      have h1 : p * p * Dn b L i * Dh b i * (ρ + 1) ≤ p * p * Dn b L i * Dh b i * Dh b i :=
        Nat.mul_le_mul_left _ hρ
      have h2 : (m + Dn b L i * Dh b i) * (p * Dh b i) < p * Dn b L i * (p * Dh b i) :=
        Nat.mul_lt_mul_of_pos_right hcost (Nat.mul_pos hp0 hd0)
      have h3 : m * Dh b i ≤ p * m * Dh b i := Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left m hp0)
      linarith
  · -- junction → far
    set i := rs s with hi
    have hd0 : 0 < Dh b i := Dh_pos (by omega) i
    have hdn0 : 0 < Dn b L i := Dn_pos (by omega) L i
    have hnx : nx L i ≤ L := nx_le hr
    have hap : D.ap i < Dh b (nx L i) := h.ap_lt i hr
    have hix : ix (far p b L (nx L i) (D.ap i)) = nx L i := ix_far hb3 hpe hnx
    have hrs : rs (far p b L (nx L i) (D.ap i)) = D.ap i % Dh b (nx L i) := rs_far hb3 hpe hnx
    have hs2 : ix (far p b L (nx L i) (D.ap i)) ≤ L := by rw [hix]; exact hnx
    rw [En_jn hs, En_far hs2, Nn_jn hs, Nn_far hs2, wd_jn hs, wd_far hs2,
      dig_jn hs, hix, hrs, Nat.mod_mod, Nat.mod_eq_of_lt hap]
    have hDn : Dh b (nx L i) = Dn b L i := rfl
    rw [hDn, ← hi]
    refine ⟨0, ?_, ?_, ?_⟩
    · have hk := h.key i hr
      linear_combination (p * Dn b L i) * hk.symm
    · push_cast; rw [zero_div, zero_add, mul_div_cancel₀ _ hpQ.ne']
    · intro m hm
      have hcost := m_cost h hM hm hr
      have hmlt : m < p * Dn b L i := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hcost
      rw [jmod hd0 hmlt]
      have hρ : m * D.al i % Dh b i + 1 ≤ Dh b i := Nat.mod_lt _ hd0
      set ρ := m * D.al i % Dh b i
      have h1 : p * Dn b L i * (ρ + 1) * (p * Dn b L i) ≤ p * Dn b L i * Dh b i * (p * Dn b L i) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hρ)
      have h2 : (m + Dn b L i * Dh b i) * (p * Dn b L i) < p * Dn b L i * (p * Dn b L i) :=
        Nat.mul_lt_mul_of_pos_right hcost (Nat.mul_pos hp0 hdn0)
      linarith

include hM in
/-- **The carry inequality** at every state. -/
theorem carry_data (s : Fin (S p b L)) (m : ℕ) (hm : m ≤ M) :
    ((m * Nn D s % En s : ℕ) : ℚ) + m * wd s * En s ≤ En s := by
  have hb3 : 3 ≤ b := h.hb
  have hpe : p = 2 * b + L := h.hp
  have hL1 : 1 ≤ L := h.hL
  have hp0 : 0 < p := by omega
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hp0
  have hpb := m_lt_pb h hM hm
  rcases state_cases hb3 hpe s with hs | ⟨hs, hr⟩
  · set i := ix s with hi
    have hd0 : 0 < Dh b i := Dh_pos (by omega) i
    have hdn0 : 0 < Dn b L i := Dn_pos (by omega) L i
    have hdnb := Dn_bounds (b := b) (L := L) i hs
    rw [En_far hs, Nn_far hs, wd_far hs]
    have hρ : m * (rs s % Dh b i) % Dh b i + 1 ≤ Dh b i := Nat.mod_lt _ hd0
    have hρQ : ((m * (rs s % Dh b i) % Dh b i : ℕ) : ℚ) + 1 ≤ Dh b i := by exact_mod_cast hρ
    have hdQ : (0 : ℚ) < Dh b i := by exact_mod_cast hd0
    have hdnQ : (0 : ℚ) < Dn b L i := by exact_mod_cast hdn0
    have e : (m : ℚ) * wid p b L i * Dh b i = m / ((p : ℚ) * Dn b L i) := by
      unfold wid; field_simp
    have hm1 : (m : ℚ) / ((p : ℚ) * Dn b L i) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : m ≤ p * Dn b L i := by nlinarith
      exact_mod_cast this
    rw [e]; linarith
  · set i := rs s with hi
    have hd0 : 0 < Dh b i := Dh_pos (by omega) i
    have hdn0 : 0 < Dn b L i := Dn_pos (by omega) L i
    have hnx : nx L i ≤ L := nx_le hr
    have hd'b := Dh_bounds (b := b) (L := L) (nx L i) hnx
    have hdn'b := Dn_bounds (b := b) (L := L) (nx L i) hnx
    have hcost := m_cost h hM hm hr
    have hmlt : m < p * Dn b L i := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hcost
    rw [En_jn hs, Nn_jn hs, wd_jn hs, jmod hd0 hmlt]
    have hρ : m * D.al i % Dh b i + 1 ≤ Dh b i := Nat.mod_lt _ hd0
    set ρ := m * D.al i % Dh b i
    set d' := Dh b (nx L i) with hd'
    set dn' := Dn b L (nx L i) with hdn'
    set X := p * d' * dn' with hX
    have hnat : (p * Dn b L i * ρ + m) * X + m * (Dh b i * Dn b L i)
        ≤ (p * Dh b i * Dn b L i) * X := by
      have h1 : p * Dn b L i * (ρ + 1) * X ≤ p * Dn b L i * Dh b i * X :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hρ)
      have h2 : (m + Dn b L i * Dh b i) * X ≤ p * Dn b L i * X :=
        Nat.mul_le_mul_right _ hcost.le
      have hmX : m ≤ X := by
        have h1 : p * b ≤ p * d' := Nat.mul_le_mul_left p hd'b.1
        have h2 : p * d' ≤ p * d' * dn' := Nat.le_mul_of_pos_right _ (by omega)
        omega
      have h3 : m * (Dh b i * Dn b L i) ≤ X * (Dh b i * Dn b L i) := Nat.mul_le_mul_right _ hmX
      nlinarith
    have hX0 : 0 < X := Nat.mul_pos (Nat.mul_pos hp0 (by omega)) (by omega)
    have hXQ : (0 : ℚ) < X := by exact_mod_cast hX0
    have hdQ : (0 : ℚ) < Dh b i := by exact_mod_cast hd0
    have hdnQ : (0 : ℚ) < Dn b L i := by exact_mod_cast hdn0
    have hXQ' : (X : ℚ) = (p : ℚ) * d' * dn' := by rw [hX]; push_cast; ring
    unfold wid
    rw [← hXQ']
    have e : ((p * Dn b L i * ρ + m : ℕ) : ℚ) + m * (1 / (X : ℚ) / p) * ((p * Dh b i * Dn b L i : ℕ) : ℚ)
        = (((p * Dn b L i * ρ + m) * X + m * (Dh b i * Dn b L i) : ℕ) : ℚ) / (X : ℚ) := by
      push_cast; field_simp; try ring
    rw [e, div_le_iff₀ hXQ]
    exact_mod_cast hnat

include hM in
theorem edges (s : Fin (S p b L)) (s' : Fin (S p b L)) (hs' : s' ∈ nxt D s) :
    lop D s ≤ ((dig D s : ℚ) + lop D s') / p ∧
      ((dig D s : ℚ) + hip D s') / p ≤ hip D s := by
  obtain ⟨δ, hV, hw, _⟩ := edge_data h hM s s' hs'
  have hp0 : 0 < p := by have := h.hb; have := h.hp; omega
  rw [hip_eq, hip_eq, lop_eq, lop_eq]
  exact ⟨gen_lo (En_pos h.hb h.hp s) (En_pos h.hb h.hp s') hp0 hV,
    gen_hi (En_pos h.hb h.hp s) (En_pos h.hb h.hp s') hp0 hV hw⟩

include hM in
theorem carries (m : ℕ) (hm : m ≤ M) (s : Fin (S p b L)) :
    ((cc D s m : ℕ) : ℚ) ≤ m * lop D s ∧ m * hip D s ≤ (cc D s m : ℚ) + 1 := by
  rw [cc_eq, hip_eq, lop_eq]
  exact ⟨gen_carry_lo m, gen_carry_hi (En_pos h.hb h.hp s) m (carry_data h hM s m hm)⟩

include hM in
theorem recursion (m : ℕ) (hm : m ≤ M) (s s' : Fin (S p b L)) (hs' : s' ∈ nxt D s) :
    cc D s m = (m * dig D s + cc D s' m) / p := by
  obtain ⟨δ, hV, _, hblk⟩ := edge_data h hM s s' hs'
  have hp0 : 0 < p := by have := h.hb; have := h.hp; omega
  rw [cc_eq, cc_eq]
  exact gen_rec (En_pos h.hb h.hp s) (En_pos h.hb h.hp s') hp0 hV m (hblk m hm)

include hM in
theorem block (m : ℕ) (_hm1 : 1 ≤ m) (hm : m ≤ M) (s s' : Fin (S p b L)) (hs' : s' ∈ nxt D s) :
    (m * dig D s + cc D s' m) % p ≠ p - 1 := by
  obtain ⟨δ, hV, _, hblk⟩ := edge_data h hM s s' hs'
  have hp0 : 0 < p := by have := h.hb; have := h.hp; omega
  rw [cc_eq]
  exact gen_block (En_pos h.hb h.hp s) (En_pos h.hb h.hp s') hp0 hV m (hblk m hm)

include hM in
/-- **The run+jump certificate is valid up to `M < b(p − b − 1)`.** -/
theorem valid : (cert D).Valid M [p - 1] := by
  refine ⟨dig_lt h, intervals h, ?_, ?_, ?_, ?_⟩
  · intro s s' hs'; exact edges h hM s s' hs'
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
