/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderEscapeCert

/-!
# Family I: a uniform quadratic lower bound `M(p,1) > ⌊p/2⌋² − 2` 🧮

For odd `p = 2n + 1 ≥ 17` put `D = n + 2 = (p+3)/2`, so `p ≡ −3 (mod D)`.
The digit dynamics of `c/D` in base `p` is `c ↦ p·c ≡ −3c (mod D)`.  When
`p^k ≡ −1 (mod D)` for some `k` (i.e. `−1 ∈ ⟨−3⟩ ⊂ (ℤ/D)^×`), the orbit of
`1` passes through `D − 1`, and ONE junction closes a cycle:

* far states `F_c`, `c < D`: tail interval `[c/D, c/D + 4/(p³D)]`, digit
  `⌊cp/D⌋`, edge `F_c → F_{cp mod D}`;
* near state `N₋₁`: tail `c₋₁/D + 2/(p²D)` with `c₋₁ = p^(2k−1) mod D`,
  reached from `F_{c₋₂}` (`c₋₂ = p^(2k−2) mod D`);
* near state `N₀`: tail `T₀ = 1/D + 2/(pD)`, digit `1`, landing exactly on
  `F_{D−1}` (`p·T₀ − 1 = (D−1)/D`).

Every tail interval has the same slack `4/(p³D)`, so no edge is `hi`-extremal
and mixing is automatic.  The block `[p−1]` is avoided in every channel
`m ≤ n² − 2`: far edges need only `D < p`; the junction edge needs
`2m < p²`; `N₀` needs `m ≠ Dn`; and `N₋₁` fails exactly when `m ≡ 3 (mod D)`
and `⌊m/D⌋ = n − 2`, i.e. at `m = n² − 1` — which is why the bound is
`n² − 2` and not `n² − 1` (`experiments/mahler_family_I_check.py`).

All tail intervals share the denominator `E = p³D`; a state is described by
its numerator `num s` (so `lo = num/E`, `hi = (num+4)/E`) and every edge
`s → s'` satisfies `dig s · E + num s' = p · num s + δ` with `δ ∈ {0, 2p}`.
The whole certificate then reduces to four residue inequalities
(`key_far`, `key_junction`, `key_nm1`, `key_n0`).

`mahler_lower_bound_family_I` is the first **uniform-in-`p`** quadratic
lower bound on the prime side: `M(p,1) ≥ ⌊p/2⌋² − 1` for every odd `p ≥ 17`
(prime or not) with `−1 ∈ ⟨p⟩ (mod (p+3)/2)`.
-/

namespace NormalNumbers.Adder.FamilyI

open NormalNumbers NormalNumbers.Mahler

/-! ### The parameters -/

/-- `D = (p+3)/2` (for odd `p`). -/
def D (p : ℕ) : ℕ := (p - 1) / 2 + 2
/-- The common denominator of all tail intervals, `p³D`. -/
def E (p : ℕ) : ℕ := p ^ 3 * D p
/-- `c₋₁ = p^(2k−1) mod D`, the residue one step before the junction. -/
def cm1 (p k : ℕ) : ℕ := p ^ (2 * k - 1) % D p
/-- `c₋₂ = p^(2k−2) mod D`, the residue two steps before the junction. -/
def cm2 (p k : ℕ) : ℕ := p ^ (2 * k - 2) % D p

theorem D_pos (p : ℕ) : 0 < D p := by unfold D; omega

/-- The standing hypotheses: `p` odd, `p ≥ 17`, `p^k ≡ −1 (mod D)`. -/
structure Hyp (p k : ℕ) : Prop where
  odd : p % 2 = 1
  ge : 17 ≤ p
  pow : p ^ k % D p = D p - 1

namespace Hyp

variable {p k : ℕ} (h : Hyp p k)
include h

/-- The parameterization `p = 2n + 1`, `D = n + 2`, `n ≥ 8`. -/
theorem params : ∃ n, 8 ≤ n ∧ p = 2 * n + 1 ∧ D p = n + 2 := by
  refine ⟨(p - 1) / 2, ?_, ?_, rfl⟩ <;> · have := h.odd; have := h.ge; omega

theorem p_pos : 0 < p := by have := h.ge; omega
theorem two_le : 2 ≤ p := by have := h.ge; omega
theorem D_lt_p : D p < p := by obtain ⟨n, hn, rfl, hD⟩ := h.params; omega
theorem E_pos : 0 < E p := by unfold E; have := h.p_pos; have := D_pos p; positivity

theorem k_pos : 0 < k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · exfalso
    have hpow := h.pow
    obtain ⟨n, hn, rfl, hD⟩ := h.params
    rw [hk, pow_zero, hD, Nat.mod_eq_of_lt (by omega)] at hpow
    omega
  · exact hk

/-- `p^(2k) ≡ 1 (mod D)`. -/
theorem pow_two_k : p ^ (2 * k) % D p = 1 := by
  have hpow := h.pow
  obtain ⟨n, hn, rfl, hD⟩ := h.params
  rw [hD] at hpow ⊢
  rw [pow_mul', Nat.pow_mod, hpow, show n + 2 - 1 = n + 1 by omega,
    show (n + 1) ^ 2 = (n + 2) * n + 1 by ring, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

/-- `c₋₁ · p ≡ 1 (mod D)`. -/
theorem cm1_mul : cm1 p k * p % D p = 1 := by
  have hk := h.k_pos
  unfold cm1
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← pow_succ, show 2 * k - 1 + 1 = 2 * k by omega]
  exact h.pow_two_k

/-- `c₋₂ · p ≡ c₋₁ (mod D)`. -/
theorem cm2_mul : cm2 p k * p % D p = cm1 p k := by
  have hk := h.k_pos
  unfold cm1 cm2
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← pow_succ, show 2 * k - 2 + 1 = 2 * k - 1 by omega]

theorem cm1_lt : cm1 p k < D p := Nat.mod_lt _ (D_pos p)
theorem cm2_lt : cm2 p k < D p := Nat.mod_lt _ (D_pos p)

/-- Powers of `p` mod `D` are periodic with period `2k`. -/
theorem pow_add_two_k (j : ℕ) : p ^ (j + 2 * k) % D p = p ^ j % D p := by
  rw [pow_add, Nat.mul_mod, h.pow_two_k, mul_one, Nat.mod_mod]

theorem pow_add_mul_two_k (j t : ℕ) : p ^ (j + t * (2 * k)) % D p = p ^ j % D p := by
  induction t with
  | zero => simp
  | succ t ih => rw [Nat.succ_mul, ← add_assoc, h.pow_add_two_k, ih]

end Hyp

/-! ### The four digit conditions, as statements about `(m · num) mod p³D` -/

/-- `⌊m/D⌋ ≤ n − 2` when `m ≤ n² − 2`. -/
theorem quot_le (n m : ℕ) (hn : 8 ≤ n) (hm : m ≤ n ^ 2 - 2) : m / (n + 2) ≤ n - 2 := by
  have hmqr := Nat.div_add_mod m (n + 2)
  by_contra hcon
  push Not at hcon
  have : (n + 2) * (n - 1) ≤ (n + 2) * (m / (n + 2)) := Nat.mul_le_mul_left _ (by omega)
  have h3 : (n + 2) * (n - 1) + 2 = n ^ 2 + n := by
    obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  have h4 : n ^ 2 ≥ 4 := by nlinarith
  omega

section keys

variable {p k : ℕ} (h : Hyp p k)
include h

/-- **Far states.**  `(m·c·p³) mod p³D = p³·((mc) mod D) ≤ p³(D−1)`, and
`p(D−1) < (p−1)D` because `D < p`.  Valid for every `m`. -/
theorem key_far (c m : ℕ) (hc : c < D p) :
    p * (m * (c * p ^ 3) % E p) < (p - 1) * E p := by
  unfold E
  rw [show m * (c * p ^ 3) = p ^ 3 * (m * c) by ring, Nat.mul_mod_mul_left]
  have hr : m * c % D p ≤ D p - 1 := Nat.le_sub_one_of_lt (Nat.mod_lt _ (D_pos p))
  obtain ⟨n, hn, rfl, hD⟩ := h.params
  rw [hD] at hr ⊢
  have hp3 : 0 < (2 * n + 1) ^ 3 := by positivity
  calc (2 * n + 1) * ((2 * n + 1) ^ 3 * (m * c % (n + 2)))
      = (2 * n + 1) ^ 3 * ((2 * n + 1) * (m * c % (n + 2))) := by ring
    _ ≤ (2 * n + 1) ^ 3 * ((2 * n + 1) * (n + 1)) := by gcongr; omega
    _ < (2 * n + 1) ^ 3 * (2 * n * (n + 2)) :=
        Nat.mul_lt_mul_of_pos_left (by nlinarith) hp3
    _ = (2 * n + 1 - 1) * ((2 * n + 1) ^ 3 * (n + 2)) := by
        rw [show 2 * n + 1 - 1 = 2 * n by omega]; ring

/-- **The junction edge** `F_{c₋₂} → N₋₁` carries the extra `2pm`; needs
`2m < p²`. -/
theorem key_junction (m : ℕ) (hm : 2 * m < p ^ 2) :
    p * (m * (cm2 p k * p ^ 3) % E p) + m * (2 * p) < (p - 1) * E p := by
  unfold E
  rw [show m * (cm2 p k * p ^ 3) = p ^ 3 * (m * cm2 p k) by ring, Nat.mul_mod_mul_left]
  have hr : m * cm2 p k % D p ≤ D p - 1 := Nat.le_sub_one_of_lt (Nat.mod_lt _ (D_pos p))
  obtain ⟨n, hn, rfl, hD⟩ := h.params
  rw [hD] at hr ⊢
  rw [show 2 * n + 1 - 1 = 2 * n by omega]
  have hp3 : 0 < (2 * n + 1) ^ 3 := by positivity
  calc (2 * n + 1) * ((2 * n + 1) ^ 3 * (m * cm2 (2 * n + 1) k % (n + 2))) + m * (2 * (2 * n + 1))
      ≤ (2 * n + 1) * ((2 * n + 1) ^ 3 * (n + 1)) + m * (2 * (2 * n + 1)) := by gcongr; omega
    _ < 2 * n * ((2 * n + 1) ^ 3 * (n + 2)) := by nlinarith

/-- **The state `N₀`** (tail `(p+2)/(pD)`).  Safe for `m < Dn`; the
`n² − 2` cap gives `⌊m/D⌋ ≤ n − 2`. -/
theorem key_n0 (m : ℕ) (hm : m ≤ ((p - 1) / 2) ^ 2 - 2) :
    p * (m * ((p + 2) * p ^ 2) % E p) < (p - 1) * E p := by
  unfold E
  obtain ⟨n, hn, rfl, hD⟩ := h.params
  rw [hD, show (2 * n + 1 - 1) / 2 = n by omega] at *
  rw [show m * ((2 * n + 1 + 2) * (2 * n + 1) ^ 2) = (2 * n + 1) ^ 2 * (m * (2 * n + 3)) by ring,
      show (2 * n + 1) ^ 3 * (n + 2) = (2 * n + 1) ^ 2 * ((2 * n + 1) * (n + 2)) by ring,
      Nat.mul_mod_mul_left, show 2 * n + 1 - 1 = 2 * n by omega]
  suffices hs : m * (2 * n + 3) % ((2 * n + 1) * (n + 2)) < 2 * n * (n + 2) by
    calc (2 * n + 1) * ((2 * n + 1) ^ 2 * (m * (2 * n + 3) % ((2 * n + 1) * (n + 2))))
        = (2 * n + 1) ^ 2 * ((2 * n + 1) * (m * (2 * n + 3) % ((2 * n + 1) * (n + 2)))) := by ring
      _ < (2 * n + 1) ^ 2 * ((2 * n + 1) * (2 * n * (n + 2))) := by gcongr
      _ = 2 * n * ((2 * n + 1) ^ 2 * ((2 * n + 1) * (n + 2))) := by ring
  -- write `m = (n+2)u + r`
  set u := m / (n + 2) with hu
  set r := m % (n + 2) with hr
  have hmur : m = (n + 2) * u + r := (Nat.div_add_mod m (n + 2)).symm
  have hrD : r < n + 2 := Nat.mod_lt _ (by omega)
  have huQ : u ≤ n - 2 := quot_le n m hn hm
  -- pass to `ℤ`
  have hmZ : (m : ℤ) = (n + 2) * u + r := by exact_mod_cast hmur
  have hrZ : (r : ℤ) < n + 2 := by exact_mod_cast hrD
  have huZ : (u : ℤ) + 2 ≤ n := by exact_mod_cast (by omega : u + 2 ≤ n)
  have hr0 : (0 : ℤ) ≤ r := by positivity
  have hu0 : (0 : ℤ) ≤ u := by positivity
  have hnZ : (8 : ℤ) ≤ n := by exact_mod_cast hn
  have hgoal : (((m * (2 * n + 3) % ((2 * n + 1) * (n + 2)) : ℕ)) : ℤ) < 2 * n * (n + 2) := by
    rw [Int.natCast_mod]
    push_cast
    rcases le_or_gt (2 * u + 2 * r) (2 * n) with hcase | hcase
    · -- `W = pD·u + X`, `X = D(2u + 2r) − r`
      have hW : (m : ℤ) * (2 * n + 3) = ((n + 2) * (2 * u + 2 * r) - r) + ((2 * n + 1) * (n + 2)) * u := by
        rw [hmZ]; ring
      rw [hW, Int.add_mul_emod_self_left, Int.emod_eq_of_lt]
      · rcases lt_or_eq_of_le hcase with hlt | heq
        · nlinarith
        · -- `u + r = n`, so `r ≥ 2`
          have hr2 : (2 : ℤ) ≤ r := by linarith
          nlinarith
      · nlinarith
      · nlinarith
    · -- `W = pD·(u+1) + X'`, `X' = D(2u + 2r − 2n − 1) − r`
      have hcase' : 2 * n + 2 ≤ 2 * u + 2 * r := by omega
      have hcZ : (2 : ℤ) * n + 2 ≤ 2 * u + 2 * r := by exact_mod_cast hcase'
      have hW : (m : ℤ) * (2 * n + 3) = ((n + 2) * (2 * u + 2 * r - 2 * n - 1) - r) + ((2 * n + 1) * (n + 2)) * (u + 1) := by
        rw [hmZ]; ring
      rw [hW, Int.add_mul_emod_self_left, Int.emod_eq_of_lt]
      · nlinarith
      · nlinarith
      · nlinarith
  exact_mod_cast hgoal

/-- **The state `N₋₁`** (tail `c₋₁/D + 2/(p²D)`).  The only failing channels
below `Dn` are `m ≡ 3 (mod D)` with `⌊m/D⌋ = n − 2`, i.e. `m = n² − 1`;
`m ≤ n² − 2` excludes them. -/
theorem key_nm1 (m : ℕ) (hm : m ≤ ((p - 1) / 2) ^ 2 - 2) :
    p * (m * ((cm1 p k * p ^ 2 + 2) * p) % E p) < (p - 1) * E p := by
  have hc1 := h.cm1_mul
  have hclt := h.cm1_lt
  unfold E
  obtain ⟨n, hn, rfl, hD⟩ := h.params
  set c := cm1 (2 * n + 1) k with hc
  clear_value c
  rw [hD, show (2 * n + 1 - 1) / 2 = n by omega] at *
  rw [show 2 * n + 1 - 1 = 2 * n by omega]
  set p := 2 * n + 1 with hp
  -- `m·c = D u₁ + r₁`
  set u₁ := m * c / (n + 2) with hu₁
  set r₁ := m * c % (n + 2) with hr₁
  have hsplit : m * c = (n + 2) * u₁ + r₁ := (Nat.div_add_mod _ _).symm
  have hr₁D : r₁ < n + 2 := Nat.mod_lt _ (by omega)
  have hm2 : 2 * m < p ^ 2 := by
    have : m + 2 ≤ n ^ 2 := by
      have : 4 ≤ n ^ 2 := by nlinarith
      omega
    rw [hp]; nlinarith
  -- the residue: `m·num = p³D·u₁ + p(p²r₁ + 2m)`
  have hnum : m * ((c * p ^ 2 + 2) * p) = p * (p ^ 2 * r₁ + 2 * m) + (p ^ 3 * (n + 2)) * u₁ := by
    have : m * ((c * p ^ 2 + 2) * p) = p ^ 3 * (m * c) + 2 * m * p := by ring
    rw [this, hsplit]; ring
  have hlt : p * (p ^ 2 * r₁ + 2 * m) < p ^ 3 * (n + 2) := by
    have : p ^ 2 * r₁ + 2 * m < p ^ 2 * (n + 2) := by
      have : p ^ 2 * (r₁ + 1) ≤ p ^ 2 * (n + 2) := Nat.mul_le_mul_left _ (by omega)
      nlinarith
    calc p * (p ^ 2 * r₁ + 2 * m) < p * (p ^ 2 * (n + 2)) := Nat.mul_lt_mul_of_pos_left this (by omega)
      _ = p ^ 3 * (n + 2) := by ring
  rw [hnum, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  -- target: `p²r₁ + 2m < (p−1)pD = 2n·p·(n+2)`
  suffices hs : p ^ 2 * r₁ + 2 * m < 2 * n * (p * (n + 2)) by
    calc p * (p * (p ^ 2 * r₁ + 2 * m)) = p * (p * (p ^ 2 * r₁ + 2 * m)) := rfl
      _ < p * (p * (2 * n * (p * (n + 2)))) := by
          apply Nat.mul_lt_mul_of_pos_left _ (by omega); exact Nat.mul_lt_mul_of_pos_left hs (by omega)
      _ = 2 * n * (p ^ 3 * (n + 2)) := by ring
  rcases Nat.lt_or_ge r₁ (n + 1) with hcase | hcase
  · -- `r₁ ≤ n`: `p²n + 2m < 2np(n+2)`
    have : p ^ 2 * r₁ ≤ p ^ 2 * n := Nat.mul_le_mul_left _ (by omega)
    rw [hp] at this ⊢; nlinarith
  · -- `r₁ = n + 1 = D − 1`: then `m ≡ 3 (mod D)`
    have hr₁e : r₁ = n + 1 := by omega
    have hmod : m % (n + 2) = 3 := by
      have h1 : c * p ≡ 1 [MOD n + 2] := by
        unfold Nat.ModEq; rw [hc1, Nat.mod_eq_of_lt (by omega)]
      have h2 : m * c ≡ n + 1 [MOD n + 2] := by
        unfold Nat.ModEq; rw [← hr₁, hr₁e, Nat.mod_eq_of_lt (by omega)]
      have h3 : m * (c * p) ≡ m * 1 [MOD n + 2] := h1.mul_left m
      have h4 : p * (m * c) ≡ p * (n + 1) [MOD n + 2] := h2.mul_left p
      have h5 : p * (n + 1) ≡ 3 [MOD n + 2] := by
        unfold Nat.ModEq
        rw [hp, show (2 * n + 1) * (n + 1) = 3 + (n + 2) * (2 * n - 1) by
          obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
          rw [show 2 * (t + 1) - 1 = 2 * t + 1 by omega]; ring]
        rw [Nat.add_mul_mod_self_left]
      have h6 : m ≡ 3 [MOD n + 2] := by
        calc m = m * 1 := (mul_one m).symm
          _ ≡ m * (c * p) [MOD n + 2] := h3.symm
          _ = p * (m * c) := by ring
          _ ≡ p * (n + 1) [MOD n + 2] := h4
          _ ≡ 3 [MOD n + 2] := h5
      unfold Nat.ModEq at h6
      rw [h6, Nat.mod_eq_of_lt (by omega)]
    have hmdiv := Nat.div_add_mod m (n + 2)
    rw [hmod] at hmdiv
    have hq : m / (n + 2) ≤ n - 2 := quot_le n m hn hm
    have hq' : m / (n + 2) ≠ n - 2 := by
      intro heq
      rw [heq] at hmdiv
      have : (n + 2) * (n - 2) + 4 = n ^ 2 := by
        obtain ⟨t, rfl⟩ : ∃ t, n = t + 2 := ⟨n - 2, by omega⟩
        simp only [Nat.add_sub_cancel]; ring
      omega
    have hq3 : m / (n + 2) + 3 ≤ n := by omega
    have hmle : m + 3 * (n + 2) ≤ (n + 2) * n + 3 := by
      have := Nat.mul_le_mul_left (n + 2) hq3
      nlinarith
    rw [hr₁e, hp] at *
    nlinarith

end keys

/-! ### The certificate -/

section cert

variable (p k : ℕ)

/-- The far state `F_{c mod D}`. -/
def far (c : ℕ) : Fin (D p + 2) := ⟨c % D p, by have := Nat.mod_lt c (D_pos p); omega⟩
/-- The near state `N₋₁`. -/
def nm1 : Fin (D p + 2) := ⟨D p, by omega⟩
/-- The near state `N₀`. -/
def n0 : Fin (D p + 2) := ⟨D p + 1, by omega⟩

/-- Tail numerators over the common denominator `E = p³D`. -/
def num (s : Fin (D p + 2)) : ℕ :=
  if s.1 < D p then s.1 * p ^ 3
  else if s.1 = D p then (cm1 p k * p ^ 2 + 2) * p
  else (p + 2) * p ^ 2

/-- The emitted digits. -/
def dig (s : Fin (D p + 2)) : ℕ :=
  if s.1 < D p then s.1 * p / D p
  else if s.1 = D p then cm1 p k * p / D p
  else 1

/-- Successors: the far cycle, the junction `F_{c₋₂} → N₋₁ → N₀ → F_{D−1}`. -/
def nxt (s : Fin (D p + 2)) : List (Fin (D p + 2)) :=
  if s.1 < D p then
    (if s.1 = cm2 p k then [far p (s.1 * p), nm1 p] else [far p (s.1 * p)])
  else if s.1 = D p then [n0 p] else [far p (D p - 1)]

/-- The family-I escape certificate. -/
def cert : EscapeCert p where
  n := D p + 2
  a := dig p k
  next := nxt p k
  lo := fun s => (num p k s : ℚ) / E p
  hi := fun s => ((num p k s : ℚ) + 4) / E p
  c := fun s m => m * num p k s / E p

theorem far_mod (c : ℕ) : far p (c % D p) = far p c := by
  unfold far; exact Fin.ext (Nat.mod_mod _ _)

theorem far_val (c : ℕ) : (far p c).1 = c % D p := rfl

theorem num_far (c : ℕ) : num p k (far p c) = (c % D p) * p ^ 3 := by
  simp [num, far_val, Nat.mod_lt _ (D_pos p)]

theorem dig_far (c : ℕ) : dig p k (far p c) = (c % D p) * p / D p := by
  simp [dig, far_val, Nat.mod_lt _ (D_pos p)]

theorem num_nm1 : num p k (nm1 p) = (cm1 p k * p ^ 2 + 2) * p := by
  unfold num nm1; simp

theorem dig_nm1 : dig p k (nm1 p) = cm1 p k * p / D p := by
  unfold dig nm1; simp

theorem num_n0 : num p k (n0 p) = (p + 2) * p ^ 2 := by
  unfold num n0; simp

theorem dig_n0 : dig p k (n0 p) = 1 := by
  unfold dig n0; simp

theorem nxt_far (c : ℕ) :
    nxt p k (far p c) = if c % D p = cm2 p k then [far p (c % D p * p), nm1 p]
      else [far p (c % D p * p)] := by
  simp [nxt, far_val, Nat.mod_lt _ (D_pos p)]
  split_ifs <;> simp_all

theorem nxt_nm1 : nxt p k (nm1 p) = [n0 p] := by unfold nxt nm1; simp
theorem nxt_n0 : nxt p k (n0 p) = [far p (D p - 1)] := by unfold nxt n0; simp

/-- The far cycle edge is always present. -/
theorem far_mul_mem (c : ℕ) : far p (c * p) ∈ nxt p k (far p c) := by
  rw [nxt_far]
  have : far p (c % D p * p) = far p (c * p) := by
    unfold far; apply Fin.ext; simp [Nat.mul_mod]
  split_ifs <;> simp [this]

/-- Every state is a far state, `N₋₁`, or `N₀`. -/
theorem state_cases (s : Fin (D p + 2)) :
    (∃ c, c < D p ∧ s = far p c) ∨ s = nm1 p ∨ s = n0 p := by
  rcases Nat.lt_or_ge s.1 (D p) with hlt | hge
  · left; exact ⟨s.1, hlt, Fin.ext (by rw [far_val, Nat.mod_eq_of_lt hlt])⟩
  · right
    have := s.2
    rcases Nat.lt_or_ge s.1 (D p + 1) with h1 | h1
    · left; exact Fin.ext (by unfold nm1; simp; omega)
    · right; exact Fin.ext (by unfold n0; simp; omega)

/-- The four edge types. -/
theorem mem_nxt {s s' : Fin (D p + 2)} (hs' : s' ∈ nxt p k s) :
    (∃ c, c < D p ∧ s = far p c ∧ s' = far p (c * p)) ∨
    (s = far p (cm2 p k) ∧ s' = nm1 p) ∨
    (s = nm1 p ∧ s' = n0 p) ∨ (s = n0 p ∧ s' = far p (D p - 1)) := by
  rcases state_cases p s with ⟨c, hc, rfl⟩ | rfl | rfl
  · rw [nxt_far, Nat.mod_eq_of_lt hc] at hs'
    split_ifs at hs' with hj
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs'
      rcases hs' with rfl | rfl
      · left; exact ⟨c, hc, rfl, rfl⟩
      · right; left; exact ⟨by rw [hj], rfl⟩
    · simp only [List.mem_singleton] at hs'
      left; exact ⟨c, hc, rfl, hs'⟩
  · rw [nxt_nm1, List.mem_singleton] at hs'
    right; right; left; exact ⟨rfl, hs'⟩
  · rw [nxt_n0, List.mem_singleton] at hs'
    right; right; right; exact ⟨rfl, hs'⟩

end cert

/-! ### Edge data and the per-state bounds -/

section edges

variable {p k : ℕ} (h : Hyp p k)
include h

theorem dig_lt (s : Fin (D p + 2)) : dig p k s < p := by
  have hD := D_pos p
  have hp := h.two_le
  rcases state_cases p s with ⟨c, hc, rfl⟩ | rfl | rfl
  · rw [dig_far, Nat.mod_eq_of_lt hc, Nat.div_lt_iff_lt_mul hD, mul_comm p]
    exact Nat.mul_lt_mul_of_pos_right hc (by omega)
  · rw [dig_nm1, Nat.div_lt_iff_lt_mul hD, mul_comm p]
    exact Nat.mul_lt_mul_of_pos_right h.cm1_lt (by omega)
  · rw [dig_n0]; omega

/-- `⌊(D−1)p/D⌋ = p − 2` and `⌊(D−3)p/D⌋ = p − 6`. -/
theorem dig_top : dig p k (far p (D p - 1)) = p - 2 := by
  rw [dig_far]
  obtain ⟨n, hn, rfl, hD⟩ := h.params
  rw [hD, show n + 2 - 1 = n + 1 by omega, Nat.mod_eq_of_lt (by omega),
    show 2 * n + 1 - 2 = 2 * n - 1 by omega]
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
  rw [show 2 * (t + 1) - 1 = 2 * t + 1 by omega]
  apply Nat.div_eq_of_lt_le <;> nlinarith

theorem dig_p : dig p k (far p p) = p - 6 := by
  rw [dig_far]
  obtain ⟨n, hn, rfl, hD⟩ := h.params
  have hmod : (2 * n + 1) % (n + 2) = n - 1 := by
    rw [show 2 * n + 1 = (n - 1) + (n + 2) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  rw [hD, hmod]
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 8 := ⟨n - 8, by omega⟩
  rw [show t + 8 - 1 = t + 7 by omega, show 2 * (t + 8) + 1 - 6 = 2 * t + 11 by omega]
  apply Nat.div_eq_of_lt_le <;> nlinarith

theorem dig_le (s : Fin (D p + 2)) : dig p k s ≤ p - 2 := by
  have hD := D_pos p
  have hp := h.two_le
  have hDp := h.D_lt_p
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
  rcases state_cases p s with ⟨c, hc, rfl⟩ | rfl | rfl
  · rw [dig_far, Nat.mod_eq_of_lt hc]; exact key c hc
  · rw [dig_nm1]; exact key _ h.cm1_lt
  · rw [dig_n0]; have := h.ge; omega

theorem num_add_four_le (s : Fin (D p + 2)) : num p k s + 4 ≤ E p := by
  have hD := D_pos p
  have hc := h.cm1_lt
  unfold E
  rcases state_cases p s with ⟨c, hc, rfl⟩ | rfl | rfl
  · rw [num_far, Nat.mod_eq_of_lt hc]
    obtain ⟨n, hn, rfl, hD⟩ := h.params
    rw [hD] at hc ⊢
    have : (c + 1) * (2 * n + 1) ^ 3 ≤ (n + 2) * (2 * n + 1) ^ 3 := Nat.mul_le_mul_right _ hc
    have hP : 2 ^ 3 ≤ (2 * n + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    nlinarith
  · rw [num_nm1]
    obtain ⟨n, hn, rfl, hD⟩ := h.params
    rw [hD] at hc ⊢
    have : (cm1 (2 * n + 1) k + 1) * (2 * n + 1) ^ 3 ≤ (n + 2) * (2 * n + 1) ^ 3 :=
      Nat.mul_le_mul_right _ hc
    have hP : 2 * (2 * n + 1) + 4 ≤ (2 * n + 1) ^ 3 := by
      have h17 : 289 ≤ (2 * n + 1) ^ 2 := by nlinarith
      calc 2 * (2 * n + 1) + 4 ≤ 289 * (2 * n + 1) := by omega
        _ ≤ (2 * n + 1) ^ 2 * (2 * n + 1) := Nat.mul_le_mul_right _ h17
        _ = (2 * n + 1) ^ 3 := by ring
    nlinarith
  · rw [num_n0]
    obtain ⟨n, hn, rfl, hD⟩ := h.params
    rw [hD]; nlinarith

/-- Every edge satisfies `dig s · E + num s' = p · num s + δ` with `δ ≤ 2p`,
and the digit condition `p·((m·num s) mod E) + mδ < (p−1)E` for `m ≤ n² − 2`. -/
theorem edge_data {s s' : Fin (D p + 2)} (hs' : s' ∈ nxt p k s) :
    ∃ δ, δ ≤ 2 * p ∧ dig p k s * E p + num p k s' = p * num p k s + δ ∧
      ∀ m, m ≤ ((p - 1) / 2) ^ 2 - 2 →
        p * (m * num p k s % E p) + m * δ < (p - 1) * E p := by
  have hD := D_pos p
  rcases mem_nxt p k hs' with ⟨c, hc, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
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
  · -- junction `F_{c₋₂} → N₋₁`
    have hc2 := h.cm2_lt
    have hmul := h.cm2_mul
    refine ⟨2 * p, le_rfl, ?_, ?_⟩
    · rw [dig_far, num_far, num_nm1, Nat.mod_eq_of_lt hc2]
      unfold E
      have hdm := Nat.div_add_mod (cm2 p k * p) (D p)
      rw [hmul] at hdm
      calc cm2 p k * p / D p * (p ^ 3 * D p) + (cm1 p k * p ^ 2 + 2) * p
          = p ^ 3 * (D p * (cm2 p k * p / D p) + cm1 p k) + 2 * p := by ring
        _ = p ^ 3 * (cm2 p k * p) + 2 * p := by rw [hdm]
        _ = p * (cm2 p k * p ^ 3) + 2 * p := by ring
    · intro m hm
      rw [num_far, Nat.mod_eq_of_lt hc2]
      apply key_junction h
      obtain ⟨n, hn, rfl, hD⟩ := h.params
      rw [show (2 * n + 1 - 1) / 2 = n by omega] at hm
      have h4 : 4 ≤ n ^ 2 := by nlinarith
      have h2 : m + 2 ≤ n ^ 2 := by omega
      nlinarith
  · -- `N₋₁ → N₀`
    have hmul := h.cm1_mul
    refine ⟨0, by omega, ?_, ?_⟩
    · rw [dig_nm1, num_nm1, num_n0]
      unfold E
      have hdm := Nat.div_add_mod (cm1 p k * p) (D p)
      rw [hmul] at hdm
      calc cm1 p k * p / D p * (p ^ 3 * D p) + (p + 2) * p ^ 2
          = p ^ 3 * (D p * (cm1 p k * p / D p) + 1) + 2 * p ^ 2 := by ring
        _ = p ^ 3 * (cm1 p k * p) + 2 * p ^ 2 := by rw [hdm]
        _ = p * ((cm1 p k * p ^ 2 + 2) * p) + 0 := by ring
    · intro m hm
      rw [num_nm1, mul_zero, add_zero]
      exact key_nm1 h m hm
  · -- `N₀ → F_{D−1}`
    refine ⟨0, by omega, ?_, ?_⟩
    · rw [dig_n0, num_n0, num_far, Nat.mod_eq_of_lt (by omega)]
      unfold E
      obtain ⟨n, hn, rfl, hD⟩ := h.params
      rw [hD, show n + 2 - 1 = n + 1 by omega]; ring
    · intro m hm
      rw [num_n0, mul_zero, add_zero]
      exact key_n0 h m hm

/-- The per-state bound with `δ = 0` (every state has an outgoing edge). -/
theorem key_state (s : Fin (D p + 2)) (m : ℕ) (hm : m ≤ ((p - 1) / 2) ^ 2 - 2) :
    p * (m * num p k s % E p) < (p - 1) * E p := by
  have hD := D_pos p
  rcases state_cases p s with ⟨c, hc, rfl⟩ | rfl | rfl
  · rw [num_far, Nat.mod_eq_of_lt hc]; exact key_far h c m hc
  · rw [num_nm1]; exact key_nm1 h m hm
  · rw [num_n0]; exact key_n0 h m hm

/-- `4m ≤ p²D` for `m ≤ n² − 2`. -/
theorem four_m_le (m : ℕ) (hm : m ≤ ((p - 1) / 2) ^ 2 - 2) : 4 * m < p ^ 2 * D p := by
  obtain ⟨n, hn, rfl, hD⟩ := h.params
  rw [show (2 * n + 1 - 1) / 2 = n by omega] at hm
  rw [hD]
  have h4 : 4 ≤ n ^ 2 := by nlinarith
  have h2 : m + 2 ≤ n ^ 2 := by omega
  nlinarith [h2, Nat.zero_le (n ^ 3), Nat.zero_le (n ^ 2)]

/-- The residue plus `4m` stays below `E`: carry pinning with slack. -/
theorem res_add_lt (s : Fin (D p + 2)) (m : ℕ) (hm : m ≤ ((p - 1) / 2) ^ 2 - 2) :
    m * num p k s % E p + 4 * m < E p := by
  have hk := key_state h s m hm
  have h4 := four_m_le h m hm
  have hp := h.p_pos
  have hE : E p = p * (p ^ 2 * D p) := by unfold E; ring
  -- `p·r + 4pm < (p−1)E + pE/p·... `: multiply through by `p`
  by_contra hcon
  push Not at hcon
  have : p * E p ≤ p * (m * num p k s % E p + 4 * m) := Nat.mul_le_mul_left _ hcon
  have h5 : p * (4 * m) < E p := by rw [hE]; nlinarith
  have h6 : (p - 1) * E p + E p = p * E p := by
    rcases Nat.exists_eq_add_of_le hp with ⟨t, ht⟩; rw [ht]; simp; ring
  nlinarith

end edges

/-! ### Validity -/

section valid

variable {p k : ℕ} (h : Hyp p k)
include h

theorem valid_digits : ∀ s, (cert p k).a s < p := fun s => dig_lt h s

theorem valid_intervals : ∀ s, 0 ≤ (cert p k).lo s ∧ (cert p k).lo s ≤ (cert p k).hi s ∧
    (cert p k).hi s ≤ 1 := by
  intro s
  have hE : (0 : ℚ) < E p := by exact_mod_cast h.E_pos
  simp only [cert]
  refine ⟨by positivity, ?_, ?_⟩
  · gcongr; linarith
  · rw [div_le_one hE]
    have := num_add_four_le h s
    exact_mod_cast this

theorem valid_edges : ∀ s, ∀ s' ∈ (cert p k).next s,
    (cert p k).lo s ≤ ((cert p k).a s + (cert p k).lo s') / p ∧
    ((cert p k).a s + (cert p k).hi s') / p ≤ (cert p k).hi s := by
  intro s s' hs'
  obtain ⟨δ, hδ, hV, _⟩ := edge_data h hs'
  have hE : (0 : ℚ) < E p := by exact_mod_cast h.E_pos
  have hp : (0 : ℚ) < p := by exact_mod_cast h.p_pos
  have hp2 : (2 : ℚ) ≤ p := by exact_mod_cast h.two_le
  have hVQ : (dig p k s : ℚ) * E p + num p k s' = p * num p k s + δ := by exact_mod_cast hV
  have hδQ : (δ : ℚ) ≤ 2 * p := by exact_mod_cast hδ
  simp only [cert]
  have h1 : (dig p k s : ℚ) + (num p k s' : ℚ) / E p = ((p : ℚ) * num p k s + δ) / E p := by
    rw [← hVQ]; field_simp
  have h2 : (dig p k s : ℚ) + ((num p k s' : ℚ) + 4) / E p = ((p : ℚ) * num p k s + δ + 4) / E p := by
    rw [← hVQ]; field_simp; ring
  constructor
  · rw [le_div_iff₀ hp, h1, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hE]
    have : (0 : ℚ) ≤ δ := by positivity
    nlinarith
  · rw [div_le_iff₀ hp, h2, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hE]
    nlinarith

/-- No edge is `hi`-extremal: the slack `4/E` is never exhausted (`δ ≤ 2p < 4p − 4`). -/
theorem not_hiMax_of_edge {s s' : Fin (D p + 2)} (hs' : s' ∈ nxt p k s) :
    ¬ (cert p k).HiMax s s' := by
  intro hmax
  obtain ⟨δ, hδ, hV, _⟩ := edge_data h hs'
  have hE : (0 : ℚ) < E p := by exact_mod_cast h.E_pos
  have hp : (0 : ℚ) < p := by exact_mod_cast h.p_pos
  have hp17 : (17 : ℚ) ≤ p := by exact_mod_cast h.ge
  have hVQ : (dig p k s : ℚ) * E p + num p k s' = p * num p k s + δ := by exact_mod_cast hV
  have hδQ : (δ : ℚ) ≤ 2 * p := by exact_mod_cast hδ
  have h2 : (dig p k s : ℚ) + ((num p k s' : ℚ) + 4) / E p = ((p : ℚ) * num p k s + δ + 4) / E p := by
    rw [← hVQ]; field_simp; ring
  unfold EscapeCert.HiMax at hmax
  simp only [cert] at hmax
  rw [h2, div_div, div_eq_div_iff (by positivity) (by positivity)] at hmax
  nlinarith [mul_pos hE (by linarith : (0 : ℚ) < p - 2)]

theorem valid_carry : ∀ m, m ≤ ((p - 1) / 2) ^ 2 - 2 → ∀ s,
    ((cert p k).c s m : ℚ) ≤ m * (cert p k).lo s ∧
    m * (cert p k).hi s ≤ (cert p k).c s m + 1 := by
  intro m hm s
  have hE : (0 : ℚ) < E p := by exact_mod_cast h.E_pos
  have hEn := h.E_pos
  have hres := res_add_lt h s m hm
  have hdm := Nat.div_add_mod (m * num p k s) (E p)
  simp only [cert]
  constructor
  · calc ((m * num p k s / E p : ℕ) : ℚ) ≤ ((m * num p k s : ℕ) : ℚ) / (E p : ℚ) := Nat.cast_div_le
      _ = m * ((num p k s : ℚ) / E p) := by push_cast; ring
  · have hN : m * (num p k s + 4) ≤ (m * num p k s / E p + 1) * E p := by nlinarith
    rw [mul_div_assoc', div_le_iff₀ hE]
    exact_mod_cast hN

/-- The channel digit on an edge, as a single quotient. -/
theorem chDigit_eq {s s' : Fin (D p + 2)} (hs' : s' ∈ nxt p k s) (m : ℕ)
    (hm : m ≤ ((p - 1) / 2) ^ 2 - 2) :
    ∃ x, x < p - 1 ∧
      m * dig p k s + m * num p k s' / E p = x + p * (m * num p k s / E p) ∧
      (cert p k).chDigit m s s' = x := by
  obtain ⟨δ, hδ, hV, hkey⟩ := edge_data h hs'
  have hEn := h.E_pos
  have hp := h.p_pos
  have hdm := Nat.div_add_mod (m * num p k s) (E p)
  have hk := hkey m hm
  set c := m * num p k s / E p with hc
  set r := m * num p k s % E p with hr
  have hsplit : m * (dig p k s * E p + num p k s') = (p * r + m * δ) + (p * c) * E p := by
    rw [hV]
    calc m * (p * num p k s + δ) = p * (m * num p k s) + m * δ := by ring
      _ = p * (E p * c + r) + m * δ := by rw [hdm]
      _ = (p * r + m * δ) + (p * c) * E p := by ring
  have hX : m * dig p k s + m * num p k s' / E p = (p * r + m * δ) / E p + p * c := by
    rw [← Nat.mul_add_div hEn, show E p * (m * dig p k s) + m * num p k s'
      = m * (dig p k s * E p + num p k s') by ring, hsplit, Nat.add_mul_div_right _ _ hEn]
  have hx : (p * r + m * δ) / E p < p - 1 := by
    rw [Nat.div_lt_iff_lt_mul hEn]; exact hk
  refine ⟨(p * r + m * δ) / E p, hx, hX, ?_⟩
  unfold EscapeCert.chDigit
  simp only [cert]
  rw [hX, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem valid_recursion : ∀ m, m ≤ ((p - 1) / 2) ^ 2 - 2 → ∀ s, ∀ s' ∈ (cert p k).next s,
    (cert p k).c s m = (m * (cert p k).a s + (cert p k).c s' m) / p := by
  intro m hm s s' hs'
  obtain ⟨x, hx, hX, _⟩ := chDigit_eq h hs' m hm
  have hp := h.p_pos
  simp only [cert]
  rw [hX, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt (show x < p by omega), zero_add]

theorem valid_block : ∀ m, 1 ≤ m → m ≤ ((p - 1) / 2) ^ 2 - 2 →
    ∀ σ : Fin ([p - 1].length + 1) → Fin (cert p k).n,
    (∀ i : Fin [p - 1].length, σ i.succ ∈ (cert p k).next (σ i.castSucc)) →
    List.ofFn (fun i : Fin [p - 1].length =>
      (cert p k).chDigit m (σ i.castSucc) (σ i.succ)) ≠ [p - 1] := by
  intro m _ hm σ hσ
  have hedge : σ 1 ∈ nxt p k (σ 0) := hσ 0
  obtain ⟨x, hx, _, hch⟩ := chDigit_eq h hedge m hm
  simp only [List.length_singleton, List.ofFn_succ, List.ofFn_zero, ne_eq, List.cons.injEq,
    and_true]
  show ¬ (cert p k).chDigit m (σ 0) (σ 1) = p - 1
  rw [hch]; omega

/-- **Validity of the family-I certificate** for `M = n² − 2`. -/
theorem valid : (cert p k).Valid (((p - 1) / 2) ^ 2 - 2) [p - 1] :=
  ⟨valid_digits h, valid_intervals h, valid_edges h, valid_carry h, valid_recursion h,
    valid_block h⟩

end valid

/-! ### The two closed walks and the witness pair -/

/-- The junction walk: `F_{c₋₂} → N₋₁ → N₀ → F_{p^k} → F_{p^(k+1)} → ⋯`, closing after
`3k + 1` steps. -/
def walkA (p k : ℕ) (i : ℕ) : Fin (D p + 2) :=
  if i = 0 then far p (cm2 p k) else if i = 1 then nm1 p else if i = 2 then n0 p
  else far p (p ^ (k + (i - 3)))

/-- The pure far cycle from `F_{c₋₂}`, period `2k`. -/
def walkB (p k : ℕ) (i : ℕ) : Fin (D p + 2) := far p (p ^ (2 * k - 2 + i))

section walks

variable {p k : ℕ} (h : Hyp p k)

/-- Periodic extension of a closed sequence is a closed walk. -/
theorem isClosedWalk_periodic {g : ℕ} {C : EscapeCert g} (A : ℕ → Fin C.n) (ℓ : ℕ)
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

theorem walkA_zero : walkA p k 0 = far p (cm2 p k) := by simp [walkA]
theorem walkA_one : walkA p k 1 = nm1 p := by simp [walkA]
theorem walkA_two : walkA p k 2 = n0 p := by simp [walkA]
theorem walkA_ge {p k : ℕ} (i : ℕ) (hi : 3 ≤ i) : walkA p k i = far p (p ^ (k + (i - 3))) := by
  unfold walkA; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem far_pow_succ (j : ℕ) : far p (p ^ (j + 1)) = far p (p ^ j * p) := by rw [pow_succ]

include h

theorem far_pow_k : far p (p ^ k) = far p (D p - 1) := by
  have := D_pos p
  apply Fin.ext; rw [far_val, far_val, h.pow, Nat.mod_eq_of_lt (by omega)]

theorem far_cm2 : far p (cm2 p k) = far p (p ^ (2 * k - 2)) := by
  unfold cm2; exact far_mod p _

theorem walkA_closed :
    walkA p k 0 = far p (cm2 p k) ∧
    (∀ i, i + 1 < 3 * k + 1 → walkA p k (i + 1) ∈ nxt p k (walkA p k i)) ∧
    far p (cm2 p k) ∈ nxt p k (walkA p k (3 * k + 1 - 1)) := by
  have hk := h.k_pos
  have hc2 := h.cm2_lt
  refine ⟨walkA_zero, ?_, ?_⟩
  · intro i hi
    rcases i with _ | _ | _ | i
    · rw [walkA_zero, walkA_one, nxt_far, Nat.mod_eq_of_lt hc2, if_pos rfl]; simp
    · rw [walkA_one, walkA_two, nxt_nm1]; simp
    · rw [walkA_two, walkA_ge 3 le_rfl, nxt_n0]
      have e : far p (p ^ (k + (3 - 3))) = far p (D p - 1) := far_pow_k h
      rw [e]; simp
    · rw [walkA_ge (i + 3) (by omega), walkA_ge (i + 3 + 1) (by omega),
        show i + 3 + 1 - 3 = (i + 3 - 3) + 1 by omega, ← add_assoc, far_pow_succ]
      exact far_mul_mem p k _
  · rw [show 3 * k + 1 - 1 = 3 * k by omega, walkA_ge (3 * k) (by omega)]
    have : far p (cm2 p k) = far p (p ^ (k + (3 * k - 3)) * p) := by
      rw [far_cm2 h, ← pow_succ]
      apply Fin.ext
      rw [far_val, far_val, show k + (3 * k - 3) + 1 = (2 * k - 2) + 2 * k by omega,
        h.pow_add_two_k]
    rw [this]; exact far_mul_mem p k _

theorem walkB_closed (L : ℕ) (hL : L = (3 * k + 1) * (2 * k)) :
    walkB p k 0 = far p (cm2 p k) ∧
    (∀ i, walkB p k (i + 1) ∈ nxt p k (walkB p k i)) ∧
    far p (cm2 p k) ∈ nxt p k (walkB p k (L - 1)) := by
  have hk := h.k_pos
  refine ⟨?_, ?_, ?_⟩
  · unfold walkB; rw [add_zero, far_cm2 h]
  · intro i; unfold walkB; rw [← add_assoc, far_pow_succ]; exact far_mul_mem p k _
  · unfold walkB
    have hL1 : 1 ≤ L := by rw [hL]; nlinarith
    have : far p (cm2 p k) = far p (p ^ (2 * k - 2 + (L - 1)) * p) := by
      rw [far_cm2 h, ← pow_succ]
      apply Fin.ext
      rw [far_val, far_val, show 2 * k - 2 + (L - 1) + 1 = (2 * k - 2) + (3 * k + 1) * (2 * k) by omega,
        h.pow_add_mul_two_k]
    rw [this]; exact far_mul_mem p k _

/-- The witness pair: `u` = the junction walk repeated `2k` times, `v` = the far cycle. -/
theorem witness (L : ℕ) (hL : L = (3 * k + 1) * (2 * k)) (hL0 : 0 < L) :
    (cert p k).WitnessPair L (fun i : Fin L => walkA p k (i.1 % (3 * k + 1)))
      (fun i : Fin L => walkB p k i.1) hL0 (far p (cm2 p k)) := by
  have hk := h.k_pos
  have hp := h.ge
  have hL8 : 8 ≤ L := by rw [hL]; nlinarith
  obtain ⟨hA0, hAstep, hAclose⟩ := walkA_closed h
  obtain ⟨hB0, hBstep, hBclose⟩ := walkB_closed h L hL
  refine ⟨?_, ⟨hB0, fun j _ => hBstep j.1, hBclose⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact isClosedWalk_periodic (C := cert p k) (walkA p k) (3 * k + 1) (by omega) _ hA0 hAstep
      hAclose L (2 * k) (by rw [hL, mul_comm]) (by omega) hL0
  · refine ⟨⟨0, by omega⟩, ?_⟩
    show dig p k (walkA p k (0 % (3 * k + 1))) ≠ p - 1
    have := dig_le h (walkA p k (0 % (3 * k + 1))); omega
  · refine ⟨⟨0, by omega⟩, ?_⟩
    show dig p k (walkB p k 0) ≠ p - 1
    have := dig_le h (walkB p k 0); omega
  · refine ⟨⟨2, by omega⟩, show 2 + 1 < L by omega, ?_⟩
    simp only [Nat.mod_eq_of_lt (show 2 < 3 * k + 1 by omega),
      Nat.mod_eq_of_lt (show 2 + 1 < 3 * k + 1 by omega)]
    exact not_hiMax_of_edge h (hAstep 2 (by omega))
  · refine ⟨⟨0, by omega⟩, show 0 + 1 < L by omega, ?_⟩
    exact not_hiMax_of_edge h (hBstep 0)
  · refine ⟨⟨3, by omega⟩, ?_⟩
    simp only [cert, Nat.mod_eq_of_lt (show 3 < 3 * k + 1 by omega)]
    rw [walkA_ge 3 le_rfl]
    have e : far p (p ^ (k + (3 - 3))) = far p (D p - 1) := far_pow_k h
    rw [e, dig_top h]
    have hv : walkB p k 3 = far p p := by
      unfold walkB; apply Fin.ext
      rw [far_val, far_val, show 2 * k - 2 + 3 = 1 + 2 * k by omega, h.pow_add_two_k, pow_one]
    rw [hv, dig_p h]; omega

end walks

/-! ### The theorem -/

/-- **Family I: `M(p,1) > ⌊p/2⌋² − 2` uniformly.**  For every odd `p ≥ 17` (prime
or not) and every `k` with `p^k ≡ −1 (mod (p+3)/2)`, there is an irrational
`α` such that no multiplier `1 ≤ m ≤ ⌊p/2⌋² − 2` ever shows the digit `p − 1`
in `m·α`.  The certificate is the one-junction cycle over the background
`1/D`, `D = (p+3)/2`; the value `⌊p/2⌋² − 2` matches the exact census to
within `2` at every such prime (`docs/mahler-exact-values-2026-09-07.md`). -/
theorem mahler_lower_bound_family_I (p k : ℕ) (h : Hyp p k) :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ ((p - 1) / 2) ^ 2 - 2 →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt p ((m : ℝ) * α) [p - 1] n := by
  have hk := h.k_pos
  have hL0 : 0 < (3 * k + 1) * (2 * k) := by positivity
  exact (cert p k).escape_mahler_lower_bound h.two_le _ [p - 1] (valid h) _ _ _ hL0 _
    (witness h _ rfl hL0)

/-- The prime-facing form: for a prime `p ≥ 17` with `−1 ∈ ⟨p⟩ (mod (p+3)/2)`,
`M(p,1) ≥ ⌊p/2⌋² − 1`. -/
theorem mahler_lower_bound_prime_family_I (p : ℕ) (hp : p.Prime) (h17 : 17 ≤ p)
    (hk : ∃ k, p ^ k % ((p + 3) / 2) = (p + 3) / 2 - 1) :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ ((p - 1) / 2) ^ 2 - 2 →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt p ((m : ℝ) * α) [p - 1] n := by
  obtain ⟨k, hk⟩ := hk
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h2 | h2
    · omega
    · exact h2
  have hD : D p = (p + 3) / 2 := by unfold D; omega
  exact mahler_lower_bound_family_I p k ⟨hodd, h17, by rw [hD]; exact hk⟩

/-- **`M(41,1) ≥ 399`**: `41⁵ ≡ −1 (mod 22)`, a new point on the prime lower side
from the uniform theorem (`⌊41/2⌋² = 400`). -/
theorem mahler_lower_bound_base41 :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ 398 →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt 41 ((m : ℝ) * α) [40] n :=
  mahler_lower_bound_family_I 41 5 ⟨by norm_num, by norm_num, by decide⟩

/-- **`M(199,1) ≥ 9799`**: `199⁵⁰ ≡ −1 (mod 101)`; `⌊199/2⌋² = 9801`. -/
theorem mahler_lower_bound_base199 :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ 9799 →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt 199 ((m : ℝ) * α) [198] n :=
  mahler_lower_bound_family_I 199 50 ⟨by norm_num, by norm_num, by decide⟩

end NormalNumbers.Adder.FamilyI
