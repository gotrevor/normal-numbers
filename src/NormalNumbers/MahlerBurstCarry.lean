/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.MahlerBurstDigit

/-!
# Carry normalization: every burst digit as an explicit integer recursion 🧮

`MahlerBurstDigit.lean` identifies the window digit at position `i` with the
digit `bgDigit` emitted by the long addition "background `b` plus `m B`".  That
is still a *computation* in `m` and `B`.  This file makes it an **algebraic
identity, uniform in `g`**.

Any integer-coefficient expansion `N = Σ_{j<D} F_j g^j` (the `F_j` may be
negative or exceed `g`) has base-`g` digits given by *carry normalization*:

    G_0 = F_0,   G_{j+1} = F_{j+1} + ⌊G_j / g⌋,   digit_j(N) = G_j mod g

(`carryG`, `digit_of_carry`).  For the `a = 2` family with `Q = (g−1)/2`,
`m = Q u + r`, and a burst written with arbitrary integer digits
`B = Σ e_j g^j`, the number whose digits the certificate inspects is

    2r·S_D + m·B = Σ_j (2r + e_j m) g^j,

so (`bgDigit_family`) position `i` emits `G_i mod g` with `F_j = 2r + e_j m`.
The point: with `e_j m = e_j (Q u + r)` and `2Q = g − 1`, every `F_j` is an
affine form in `(u, r)` plus a multiple of `g` that passes into the next carry,
so each position is an **affine congruence in `(u, r)` with a bounded carry** —
the shape a uniform-in-`g` proof needs.  The position-`0` law of
`MahlerBurstDigit.lean` (`B ≡ −4 (mod g)`) is `G_0 = 2r − 4m ≡ 2(u − r)`.

**Law 2, proved here (`bgDigit_one_ne`).**  If `B ≡ −4 (mod g²)` then position
`1` misses `g − 1` for every `m < Q²`: with digits `(−4, 0, ℓ)`,
`G_0 = 2u − 2r − 2gu`, so `⌊G_0/g⌋ = −2u − [u < r]` and
`G_1 = 2r − 2u − [u < r] ∈ (−g, g)`; it is `−1` only if `2(r − u) ∈ {−1, 0}`
with the matching indicator, impossible by parity, and it is `g − 1 = 2Q` only
if `r − u ≥ Q`.  Together with `bgDigit_zero_ne` this is a two-position uniform
law; the remaining positions are the level-`2` problem
`2r·S + ℓ m − [u > r]` (`PENDING_WORK.md`).
-/

namespace NormalNumbers.Mahler

/-- Carry normalization of the integer expansion `Σ F_j g^j`. -/
def carryG (g : ℕ) (F : ℕ → ℤ) : ℕ → ℤ
  | 0 => F 0
  | i + 1 => F (i + 1) + carryG g F i / (g : ℤ)

theorem carryG_zero (g : ℕ) (F : ℕ → ℤ) : carryG g F 0 = F 0 := rfl

theorem carryG_succ (g : ℕ) (F : ℕ → ℤ) (i : ℕ) :
    carryG g F (i + 1) = F (i + 1) + carryG g F i / (g : ℤ) := rfl

/-- The partial expansion splits into normalized low digits plus the top carry. -/
theorem carryG_split (g : ℕ) (F : ℕ → ℤ) :
    ∀ i, ∑ j ∈ Finset.range (i + 1), F j * (g : ℤ) ^ j
      = (∑ j ∈ Finset.range i, (carryG g F j % g) * (g : ℤ) ^ j)
        + carryG g F i * (g : ℤ) ^ i := by
  intro i
  induction i with
  | zero => simp [carryG]
  | succ i ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, carryG_succ]
    have h := Int.emod_def (carryG g F i) (g : ℤ)
    rw [pow_succ]
    linear_combination (-(g : ℤ) ^ i) * h

theorem carry_low_nonneg (g : ℕ) (hg : 0 < g) (F : ℕ → ℤ) (i : ℕ) :
    0 ≤ ∑ j ∈ Finset.range i, (carryG g F j % g) * (g : ℤ) ^ j :=
  Finset.sum_nonneg fun j _ =>
    mul_nonneg (Int.emod_nonneg _ (by exact_mod_cast hg.ne')) (by positivity)

theorem carry_low_lt (g : ℕ) (hg : 0 < g) (F : ℕ → ℤ) :
    ∀ i, ∑ j ∈ Finset.range i, (carryG g F j % g) * (g : ℤ) ^ j < (g : ℤ) ^ i := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hgZ : (0 : ℤ) < g := by exact_mod_cast hg
    have h1 : carryG g F i % g < g := Int.emod_lt_of_pos _ hgZ
    have h2 : (0 : ℤ) < (g : ℤ) ^ i := by positivity
    nlinarith

/-- **Digits by carry normalization.**  If `N = Σ_{j<D} F_j g^j` then the base-`g`
digit of `N` at any position `i < D` is `G_i mod g`. -/
theorem digit_of_carry (g : ℕ) (hg : 0 < g) (F : ℕ → ℤ) (D i : ℕ) (hi : i < D) (N : ℕ)
    (hN : (N : ℤ) = ∑ j ∈ Finset.range D, F j * (g : ℤ) ^ j) :
    ((N / g ^ i % g : ℕ) : ℤ) = carryG g F i % g := by
  obtain ⟨t, rfl⟩ : ∃ t, D = (i + 1) + t := ⟨D - (i + 1), by omega⟩
  rw [Finset.sum_range_add, carryG_split] at hN
  have hT : ∑ j ∈ Finset.range t, F (i + 1 + j) * (g : ℤ) ^ (i + 1 + j)
      = (g : ℤ) ^ (i + 1) * ∑ j ∈ Finset.range t, F (i + 1 + j) * (g : ℤ) ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_add]; ring
  rw [hT] at hN
  set L := ∑ j ∈ Finset.range i, (carryG g F j % g) * (g : ℤ) ^ j with hL
  set T := ∑ j ∈ Finset.range t, F (i + 1 + j) * (g : ℤ) ^ j with hT'
  set G := carryG g F i with hG
  have hL0 : 0 ≤ L := carry_low_nonneg g hg F i
  have hL1 : L < (g : ℤ) ^ i := carry_low_lt g hg F i
  have hN' : (N : ℤ) = L + (g : ℤ) ^ i * (G + g * T) := by rw [hN, pow_succ]; ring
  have hgi : ((g : ℤ) ^ i) ≠ 0 := by positivity
  have hdiv : (N : ℤ) / (g : ℤ) ^ i = G + g * T := by
    rw [hN', Int.add_mul_ediv_left _ _ hgi, Int.ediv_eq_zero_of_lt hL0 hL1]; ring
  push_cast
  rw [hdiv, Int.add_mul_emod_self_left]

/-! ### The adder digit as a plain base-`g` digit -/

theorem repunit_add (g a b : ℕ) : repunit g (a + b) = repunit g a + g ^ a * repunit g b := by
  simp only [repunit, Finset.sum_range_add, Finset.mul_sum, pow_add]

/-- `bgDigit` is the digit at position `i` of `b·S_{i+1} + N`. -/
theorem bgDigit_eq_div_mod (g b N i : ℕ) (hg : 2 ≤ g) :
    bgDigit g b N i = (b * repunit g (i + 1) + N) / g ^ i % g := by
  have hsplit := bg_add_split g b N hg (i + 1)
  have hlt := bg_sum_lt g b N hg (i + 1)
  have h1 : (b * repunit g (i + 1) + N) % g ^ (i + 1)
      = (b * repunit g (i + 1) + N % g ^ (i + 1)) % g ^ (i + 1) := by
    conv_lhs => rw [Nat.add_mod]
    conv_rhs => rw [Nat.add_mod]
    simp
  have hmod : (b * repunit g (i + 1) + N) % g ^ (i + 1)
      = ∑ j ∈ Finset.range (i + 1), bgDigit g b N j * g ^ j := by
    rw [h1, hsplit, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
  have hg0 : 0 < g ^ i := by positivity
  have key : ∀ Y, Y / g ^ i % g = Y % g ^ (i + 1) / g ^ i := by
    intro Y
    rw [mod_pow_succ_split g Y i hg, Nat.add_mul_div_right _ _ hg0,
      Nat.div_eq_of_lt (Nat.mod_lt _ hg0)]
    simp
  rw [key, hmod, Finset.sum_range_succ, Nat.add_mul_div_right _ _ hg0,
    Nat.div_eq_of_lt (bg_sum_lt g b N hg i)]
  simp

/-- `bgDigit` is the digit at position `i` of `b·S_D + N` for any `D > i`. -/
theorem bgDigit_eq_div_mod' (g b N i D : ℕ) (hg : 2 ≤ g) (hi : i < D) :
    bgDigit g b N i = (b * repunit g D + N) / g ^ i % g := by
  obtain ⟨t, rfl⟩ : ∃ t, D = (i + 1) + t := ⟨D - (i + 1), by omega⟩
  rw [bgDigit_eq_div_mod g b N i hg, repunit_add g (i + 1) t, pow_succ g i]
  have hg0 : 0 < g ^ i := by positivity
  have : b * (repunit g (i + 1) + g ^ i * g * repunit g t) + N
       = (b * repunit g (i + 1) + N) + (g * (b * repunit g t)) * g ^ i := by ring
  rw [this, Nat.add_mul_div_right _ _ hg0, Nat.add_mul_mod_self_left]

/-! ### The `a = 2` family: every position is an affine congruence plus a carry -/

/-- **Positions of the `a = 2` family as carry normalization.**  For odd `g ≥ 3`,
`Q = (g−1)/2`, `r = m mod Q`, and a burst written with any integer digits
`B = Σ_{j<D} e_j g^j`, the digit emitted at position `i < D` is `G_i mod g`
where `G` is the carry normalization of `F_j = 2r + e_j m`. -/
theorem bgDigit_family (g : ℕ) (hg : 3 ≤ g) (hodd : g % 2 = 1) (B : ℕ) (e : ℕ → ℤ) (D : ℕ)
    (hB : (B : ℤ) = ∑ j ∈ Finset.range D, e j * (g : ℤ) ^ j) (m : ℕ) (i : ℕ) (hi : i < D) :
    (bgDigit g (m * 2 % (g - 1)) (m * B) i : ℤ)
      = carryG g (fun j => 2 * ((m % ((g - 1) / 2) : ℕ) : ℤ) + e j * m) i % g := by
  set Q := (g - 1) / 2 with hQ
  have hb : m * 2 % (g - 1) = 2 * (m % Q) := by
    rw [show g - 1 = 2 * Q by omega, show m * 2 = 2 * m by ring, Nat.mul_mod_mul_left]
  rw [hb, bgDigit_eq_div_mod' g _ _ i D (by omega) hi]
  apply digit_of_carry g (by omega) _ D i hi
  simp only [repunit]
  push_cast
  rw [Finset.mul_sum, hB, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Floor division of a small integer by `g`: `−g ≤ x < g` gives `⌊x/g⌋ ∈ {−1, 0}`
according to the sign of `x`. -/
theorem ediv_small (g x : ℤ) (hg : 0 < g) (hlo : -g ≤ x) (hhi : x < g) :
    x / g = if x < 0 then -1 else 0 := by
  split_ifs with h
  · have : x = (x + g) + g * (-1) := by ring
    rw [this, Int.add_mul_ediv_left _ _ hg.ne', Int.ediv_eq_zero_of_lt (by omega) (by omega)]
    ring
  · exact Int.ediv_eq_zero_of_lt (by omega) hhi

/-- A residue mod `g` equal to `g − 1`, for an integer in `(−g, g)`, pins the integer
to `−1` or `g − 1`. -/
theorem eq_of_emod_eq_sub_one (g x : ℤ) (_hg : 0 < g) (hlo : -g < x) (hhi : x < g)
    (h : x % g = g - 1) : x = -1 ∨ x = g - 1 := by
  rcases lt_or_ge x 0 with hx | hx
  · have : x % g = (x + g) % g := (Int.add_emod_right x g).symm
    rw [this, Int.emod_eq_of_lt (by omega) (by omega)] at h
    left; omega
  · rw [Int.emod_eq_of_lt hx hhi] at h
    right; omega

/-- **Law 2: `B ≡ −4 (mod g²)` clears position `1` up to `Q²`.**  For odd `g ≥ 5`
and `Q = (g−1)/2`, the adder digit at position `1` is never `g − 1` for any
`m < Q²`.  (Position `0` is `bgDigit_zero_ne`, which needs only `B ≡ −4 (mod g)`.) -/
theorem bgDigit_one_ne (g B m : ℕ) (hg : 5 ≤ g) (hodd : g % 2 = 1)
    (hB : B % (g * g) = g * g - 4) (hlt : m < ((g - 1) / 2) * ((g - 1) / 2)) :
    bgDigit g (m * 2 % (g - 1)) (m * B) 1 ≠ g - 1 := by
  set Q := (g - 1) / 2 with hQdef
  have hgQ : g = 2 * Q + 1 := by omega
  have hQ2 : 2 ≤ Q := by omega
  set u := m / Q with hu
  set r := m % Q with hr
  have hmqr : m = Q * u + r := (Nat.div_add_mod m Q).symm
  have hrQ : r < Q := Nat.mod_lt _ (by omega)
  have huQ : u < Q := by rw [hu, Nat.div_lt_iff_lt_mul (by omega)]; omega
  clear_value Q u r
  -- the burst with integer digits `(−4, 0, ℓ)`
  set k := B / (g * g) with hk
  set ℓ : ℤ := (k : ℤ) + 1 with hℓ
  let e : ℕ → ℤ := fun j => if j = 0 then -4 else if j = 1 then 0 else ℓ
  have hBZ : (B : ℤ) = ∑ j ∈ Finset.range 3, e j * (g : ℤ) ^ j := by
    have h1 := Nat.div_add_mod B (g * g)
    rw [hB, ← hk] at h1
    have h4 : 4 ≤ g * g := by nlinarith
    have h2 : ((B : ℕ) : ℤ) = (g : ℤ) * g * (k : ℤ) + ((g : ℤ) * g - 4) := by
      have := congrArg (fun n : ℕ => (n : ℤ)) h1
      push_cast [Nat.cast_sub h4] at this
      linarith
    simp only [e, Finset.sum_range_succ, Finset.sum_range_zero]
    simp
    rw [h2, hℓ]; ring
  intro hbad
  have hdig := bgDigit_family g (by omega) hodd B e 3 hBZ m 1 (by norm_num)
  rw [hbad] at hdig
  rw [← hQdef, ← hr] at hdig
  -- compute the carries
  have hgZ : (g : ℤ) = 2 * Q + 1 := by exact_mod_cast hgQ
  have hmZ : (m : ℤ) = Q * u + r := by exact_mod_cast hmqr
  have hrZ : (r : ℤ) < Q := by exact_mod_cast hrQ
  have huZ : (u : ℤ) < Q := by exact_mod_cast huQ
  have hg0 : (0 : ℤ) < g := by omega
  have hG0 : carryG g (fun j => 2 * (r : ℤ) + e j * m) 0 = (2 * u - 2 * r) + (g : ℤ) * (-2 * u) := by
    simp only [carryG, e, if_true]; rw [hmZ, hgZ]; ring
  have hfloor : ((2 * (u : ℤ) - 2 * r)) / (g : ℤ) = if (2 * (u : ℤ) - 2 * r) < 0 then -1 else 0 :=
    ediv_small _ _ hg0 (by omega) (by omega)
  have hG1 : carryG g (fun j => 2 * (r : ℤ) + e j * m) 1
      = 2 * r - 2 * u + (if (2 * (u : ℤ) - 2 * r) < 0 then -1 else 0) := by
    rw [carryG_succ, hG0, Int.add_mul_ediv_left _ _ hg0.ne', hfloor]
    simp only [e]; simp
    ring
  rw [hG1] at hdig
  have hcast : ((g - 1 : ℕ) : ℤ) = (g : ℤ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ g by omega)]; rfl
  rw [hcast] at hdig
  by_cases hc : (2 * (u : ℤ) - 2 * r) < 0
  · rw [if_pos hc] at hdig
    have h := eq_of_emod_eq_sub_one (g : ℤ) (2 * r - 2 * u + -1) hg0 (by omega) (by omega) hdig.symm
    omega
  · rw [if_neg hc] at hdig
    have h := eq_of_emod_eq_sub_one (g : ℤ) (2 * r - 2 * u + 0) hg0 (by omega) (by omega) hdig.symm
    omega

end NormalNumbers.Mahler
