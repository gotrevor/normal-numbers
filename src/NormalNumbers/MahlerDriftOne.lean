/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.MahlerBackgroundCert

/-!
# Drift one: the two keys of the background certificate, proved from the arithmetic 🧮

`MahlerBackgroundCert.lean` reduces the one-junction certificate over `1/D` to two
per-channel keys.  This file proves both keys **for every channel** `m < D(p−1)/2`
from a single congruence, so that no per-prime `decide` is needed:

* `p` odd, `D` odd, `3 ≤ D`, `2D < p`;
* the junction source satisfies `c₂·(p+1) ≡ −2 (mod D)` — the review lap's
  *drift one* condition `w₀ = −b·c₂⁻¹ = p + 1` for `b = 2`;
* `−1 ∈ ⟨p⟩ (mod D)`: some `p^t ≡ −1 (mod D)`, which closes the walk.

**KeyB.**  Writing `2m = pv + w`, the residue of `N₀` is `w + p·((mc₂ + v) mod D)`,
so `keyB` fails only when `mc₂ + v ≡ −1 (mod D)` and `w ≥ p − D`.  Multiplying the
congruence by `p + 1` and using `c₂(p+1) ≡ −2` turns it into `w ≡ v + p + 1 (mod D)`.
With `0 ≤ v < D` and `p − D ≤ w < p` this leaves `w = v + p + 1 − D`, giving
`2m = (p+1)(v+1) − D` — **odd**, impossible — or `w = v + p + 1 − 2D`, forcing
`v = D − 1`, `w = p − D`, `2m = D(p−1)`, the first channel outside the range.

**KeyA.**  Automatic for `2D < p`: even at the worst residue `D − 1`,
`p²(D−1) + D(p−1) < (p−1)pD`.

The result is `M(p,1) ≥ D(p−1)/2 − 1` for every such `(p, D)`, hence `≈ p²/4` when
`D ≈ p/2`.  The remaining obligation for a uniform constant near `1/4` is purely
arithmetic: *every prime `p` has an odd `D ∈ (p/3, p/2)` coprime to `p+1` with
`−1 ∈ ⟨p⟩ (mod D)`* (`exists_drift_one_background`, disclosed `sorry`).  Checked
for every prime below `3000`, `experiments/mahler_drift_one_probe.py`.
-/

namespace NormalNumbers.Adder.Background

open NormalNumbers NormalNumbers.Mahler

/-- The drift-one hypotheses on `(p, D, c₀, t)`. -/
structure DriftOne (p D c₀ t : ℕ) : Prop where
  hp : 3 ≤ p
  hpodd : p % 2 = 1
  hD3 : 3 ≤ D
  hDodd : D % 2 = 1
  hDp : 2 * D < p
  hc₂ : (c₂ p D c₀ * (p + 1) + 2) % D = 0
  ht : 0 < t
  hpt : p ^ t % D = D - 1

/-- The channel bound reached: `D(p−1)/2 − 1`. -/
def driftBound (p D : ℕ) : ℕ := D * (p - 1) / 2 - 1

namespace DriftOne

variable {p D c₀ t : ℕ} (h : DriftOne p D c₀ t)
include h

theorem toHyp : Hyp p D 2 where
  hp := h.hp
  hD := by have := h.hD3; omega
  hb := by norm_num
  hbD := by have := h.hD3; have := h.hDp; omega

theorem D_pos : 0 < D := by have := h.hD3; omega

theorem c₂_lt : c₂ p D c₀ < D := Nat.mod_lt _ h.D_pos

/-- `2m ≤ D(p−1) − 2` for every channel in range, in the form `2m + D + 2 ≤ pD`. -/
theorem two_mul_le (m : ℕ) (hm : m ≤ driftBound p D) : 2 * m + D + 2 ≤ p * D := by
  unfold driftBound at hm
  have e : D * (p - 1) = p * D - D := by rw [Nat.mul_sub_one, mul_comm]
  have hp := h.hp
  have hD := h.hD3
  have hpD : D * 3 ≤ p * D := by
    have := Nat.mul_le_mul_left D hp; linarith [mul_comm D p]
  omega

/-! ### KeyA -/

theorem keyA (m : ℕ) (hm : m ≤ driftBound p D) :
    p ^ 2 * (m * c₁ p D c₀ % D) + m * 2 < (p - 1) * (p * D) := by
  have hm2 := h.two_mul_le m hm
  have hR : m * c₁ p D c₀ % D + 1 ≤ D := Nat.mod_lt _ h.D_pos
  have h1 : p ^ 2 * (m * c₁ p D c₀ % D) + p ^ 2 ≤ p ^ 2 * D := by
    have := Nat.mul_le_mul_left (p ^ 2) hR; linarith
  have h2 : 2 * (p * D) + p ≤ p ^ 2 := by
    have := Nat.mul_le_mul_left p h.hDp; nlinarith
  have e : (p - 1) * (p * D) = p ^ 2 * D - p * D := by
    rw [Nat.sub_one_mul]; ring_nf
  rw [e]
  omega

/-! ### KeyB -/

/-- The residue of `N₀` at channel `m`, split as `w + p·r` with `2m = pv + w` and
`r = (mc₂ + v) mod D`. -/
theorem n0_res (m : ℕ) :
    m * (c₂ p D c₀ * p + 2) % (p * D)
      = p * ((m * c₂ p D c₀ + 2 * m / p) % D) + 2 * m % p := by
  have hp : 0 < p := by have := h.hp; omega
  set v := 2 * m / p with hv
  set w := 2 * m % p with hw
  have hvw : 2 * m = p * v + w := (Nat.div_add_mod (2 * m) p).symm
  have hwp : w < p := Nat.mod_lt _ hp
  set A := m * c₂ p D c₀ + v with hA
  set r := A % D with hr
  set q := A / D with hq
  have hAqr : A = D * q + r := (Nat.div_add_mod A D).symm
  have hrD : r + 1 ≤ D := Nat.mod_lt _ h.D_pos
  have hpr : p * r + p ≤ p * D := by
    have := Nat.mul_le_mul_left p hrD; linarith
  have hnum : m * (c₂ p D c₀ * p + 2) = (p * r + w) + (p * D) * q := by
    have e1 : m * (c₂ p D c₀ * p + 2) = p * (m * c₂ p D c₀) + 2 * m := by ring
    rw [e1, hvw, show p * (m * c₂ p D c₀) + (p * v + w) = p * A + w by rw [hA]; ring,
      hAqr]
    ring
  rw [hnum, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem keyB (m : ℕ) (hm : m ≤ driftBound p D) :
    m * (c₂ p D c₀ * p + 2) % (p * D) < (p - 1) * D := by
  have hp := h.hp
  have hD3 := h.hD3
  have hDp := h.hDp
  have hm2 := h.two_mul_le m hm
  rw [h.n0_res m]
  set v := 2 * m / p with hv
  set w := 2 * m % p with hw
  have hvw : 2 * m = p * v + w := (Nat.div_add_mod (2 * m) p).symm
  have hwp : w < p := Nat.mod_lt _ (by omega)
  set c := c₂ p D c₀ with hc
  set r := (m * c + v) % D with hr
  have hrD : r + 1 ≤ D := Nat.mod_lt _ h.D_pos
  have e : (p - 1) * D = p * D - D := by rw [Nat.sub_one_mul]
  rw [e]
  by_contra hcon
  push Not at hcon
  -- `r = D − 1` and `w ≥ p − D`
  have hr' : r = D - 1 := by
    by_contra hne
    have hr2 : r + 2 ≤ D := by omega
    have := Nat.mul_le_mul_left p hr2
    have e2 : p * (r + 2) = p * r + 2 * p := by ring
    omega
  have hpr : p * r = p * D - p := by rw [hr', Nat.mul_sub_one]
  have hwD : p ≤ w + D := by omega
  -- `v < D`
  have hvD : v < D := by
    have h1 : p * v ≤ 2 * m := by omega
    have h2 : p * v < p * D := by omega
    exact Nat.lt_of_mul_lt_mul_left h2
  -- the congruence `m c + v ≡ −1 (mod D)`, multiplied by `p + 1`
  have hdiv : D ∣ m * c + v + 1 := by
    have : (m * c + v) % D + 1 = D := by omega
    have h1 := Nat.div_add_mod (m * c + v) D
    refine ⟨(m * c + v) / D + 1, ?_⟩
    rw [Nat.mul_succ]; omega
  have hc2 : D ∣ c * (p + 1) + 2 := Nat.dvd_of_mod_eq_zero h.hc₂
  obtain ⟨ℓ, hℓ⟩ := hdiv
  obtain ⟨k, hk⟩ := hc2
  -- `(v + p + 1 − w) = D·(ℓ(p+1) − m k)` in `ℤ`
  have hZ : ((v : ℤ) + p + 1 - w) = D * (ℓ * (p + 1) - m * k) := by
    have hℓZ : ((m : ℤ) * c + v + 1) = D * ℓ := by exact_mod_cast hℓ
    have hkZ : ((c : ℤ) * (p + 1) + 2) = D * k := by exact_mod_cast hk
    have hvwZ : (2 : ℤ) * m = p * v + w := by exact_mod_cast hvw
    linear_combination (p + 1 : ℤ) * hℓZ - (m : ℤ) * hkZ + hvwZ
  set g : ℤ := ℓ * (p + 1) - m * k with hg
  have hDZ : (0 : ℤ) < D := by exact_mod_cast h.D_pos
  have hlo : (2 : ℤ) ≤ D * g := by
    rw [← hZ]
    have : (w : ℤ) < p := by exact_mod_cast hwp
    linarith
  have hhi : (D : ℤ) * g ≤ 2 * D := by
    rw [← hZ]
    have h1 : (v : ℤ) + 1 ≤ D := by exact_mod_cast hvD
    have h2 : (p : ℤ) ≤ w + D := by exact_mod_cast hwD
    linarith
  have hg1 : 1 ≤ g := by
    by_contra hng; push Not at hng
    have : D * g ≤ 0 := by nlinarith
    linarith
  have hg2 : g ≤ 2 := by
    by_contra hng; push Not at hng
    have : 3 * D ≤ D * g := by nlinarith
    linarith
  -- the two cases
  have hpodd := h.hpodd
  have hDodd := h.hDodd
  rcases (show g = 1 ∨ g = 2 by omega) with hg' | hg'
  · -- `w = v + p + 1 − D`, so `2m = (p+1)(v+1) − D` is odd
    rw [hg', mul_one] at hZ
    have hwN : w + D = v + p + 1 := by
      have : ((w : ℤ) + D) = v + p + 1 := by linarith
      exact_mod_cast this
    -- parity: `p = 2s+1`, `D = 2d+1`
    obtain ⟨s, hs⟩ : ∃ s, p = 2 * s + 1 := ⟨p / 2, by omega⟩
    have hpv : p * v = 2 * (s * v) + v := by rw [hs]; ring
    omega
  · -- `w = v + p + 1 − 2D` forces `v = D − 1`, `w = p − D`, `2m = D(p−1)`
    rw [hg'] at hZ
    have hwN : w + 2 * D = v + p + 1 := by
      have : ((w : ℤ) + 2 * D) = v + p + 1 := by linarith
      exact_mod_cast this
    have hv' : v = D - 1 := by omega
    have hpv : p * v = p * D - p := by rw [hv', Nat.mul_sub_one]
    omega

/-! ### The remaining keys and the closure -/

theorem toKeys : Keys p D c₀ 2 (driftBound p D) where
  posM := by
    unfold driftBound
    have hp := h.hp; have hD := h.hD3; have := h.hDp
    have : D * 3 ≤ D * (p - 1) := Nat.mul_le_mul_left D (by omega)
    omega
  keyA := h.keyA
  keyB := h.keyB
  keyJ := by
    have hm2 := h.two_mul_le (driftBound p D) le_rfl
    have hp := h.hp; have hDp := h.hDp
    have h1 : 2 * (p ^ 2 * D) < p ^ 3 := by
      have := Nat.mul_le_mul_left (p ^ 2) hDp; nlinarith
    have h2 : p * D ≤ p ^ 2 * D := by nlinarith
    omega
  keyR := by
    have hm2 := h.two_mul_le (driftBound p D) le_rfl
    have hp := h.hp
    have : 2 * (p * D) ≤ p ^ 2 * D := by nlinarith
    omega

omit h in
/-- In `ZMod D`: `c₂ = c₀p²`. -/
theorem c₂_cast : ((c₂ p D c₀ : ℕ) : ZMod D) = (c₀ : ZMod D) * (p : ZMod D) ^ 2 := by
  have : ((c₂ p D c₀ : ℕ) : ZMod D) = ((c₀ * p ^ 2 : ℕ) : ZMod D) := by
    rw [ZMod.natCast_eq_natCast_iff']; unfold c₂; simp
  rw [this]; push_cast; ring

/-- In `ZMod D`: `p^t = −1`. -/
theorem pow_t_cast : ((p : ZMod D)) ^ t = -1 := by
  have h1 : ((p ^ t : ℕ) : ZMod D) = ((D - 1 : ℕ) : ZMod D) := by
    rw [ZMod.natCast_eq_natCast_iff', h.hpt, Nat.mod_eq_of_lt (by have := h.hD3; omega)]
  have h2 : ((D - 1 : ℕ) : ZMod D) = -1 := by
    rw [Nat.cast_sub (by have := h.hD3; omega), ZMod.natCast_self]; simp
  rw [← h2, ← h1]; push_cast; rfl

/-- In `ZMod D`: `c₂(p+1) = −2`. -/
theorem c₂_rel : ((c₂ p D c₀ : ℕ) : ZMod D) * ((p : ZMod D) + 1) = -2 := by
  have h1 : (((c₂ p D c₀ * (p + 1) + 2 : ℕ)) : ZMod D) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]; exact Nat.dvd_of_mod_eq_zero h.hc₂
  push_cast at h1
  linear_combination h1

theorem toClosure : Closure p D c₀ 2 (4 * t) (t + 2) where
  hD2 := by have := h.hD3; omega
  he := by have := h.ht; omega
  hj := by have := h.ht; omega
  hpow := by
    have h1 : ((p ^ (4 * t) : ℕ) : ZMod D) = ((1 : ℕ) : ZMod D) := by
      push_cast
      rw [show (p : ZMod D) ^ (4 * t) = ((p : ZMod D) ^ t) ^ 4 by ring, h.pow_t_cast]; norm_num
    rw [ZMod.natCast_eq_natCast_iff'] at h1
    rw [h1, Nat.mod_eq_of_lt (by have := h.hD3; omega)]
  hland := by
    have h1 : (((c₂ p D c₀ * p + 2 : ℕ)) : ZMod D) = ((c₀ * p ^ (t + 2) : ℕ) : ZMod D) := by
      push_cast
      rw [pow_add, h.pow_t_cast]
      linear_combination h.c₂_rel - (c₂_cast (p := p) (D := D) (c₀ := c₀))
    rwa [ZMod.natCast_eq_natCast_iff'] at h1
  hne := by
    intro heq
    have h1 : ((c₀ * p ^ (t + 2) : ℕ) : ZMod D) = ((c₀ * p ^ 3 : ℕ) : ZMod D) := by
      rwa [ZMod.natCast_eq_natCast_iff']
    push_cast at h1
    rw [pow_add, h.pow_t_cast] at h1
    have h2 : ((2 : ℕ) : ZMod D) = 0 := by
      push_cast
      linear_combination h.c₂_rel - ((p : ZMod D) + 1) * (c₂_cast (p := p) (D := D) (c₀ := c₀)) + h1
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := Nat.le_of_dvd (by norm_num) h2
    have := h.hD3
    omega

end DriftOne

/-- **The drift-one lower bound.**  For odd `p`, odd `D ≥ 3` with `2D < p`, a
junction source with `c₂(p+1) ≡ −2 (mod D)` and `p^t ≡ −1 (mod D)`:
`M(p,1) ≥ D(p−1)/2 − 1`. -/
theorem mahler_lower_bound_drift_one (p D c₀ t : ℕ) (h : DriftOne p D c₀ t) :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ driftBound p D →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt p ((m : ℝ) * α) [p - 1] n :=
  mahler_lower_bound_background p D c₀ 2 (driftBound p D) (4 * t) (t + 2)
    h.toHyp h.toKeys h.toClosure

/-- A junction source exists as soon as `D` is coprime to `p(p+1)`:
`c₀ = (D−2)·(p²(p+1))⁻¹`. -/
theorem exists_c₀ (p D : ℕ) (hD : 1 < D) (hcop : Nat.Coprime D (p * (p + 1))) :
    ∃ c₀, (c₂ p D c₀ * (p + 1) + 2) % D = 0 := by
  have hcop' : Nat.Coprime (p ^ 2 * (p + 1)) D := by
    have h1 : Nat.Coprime (p * (p + 1)) D := hcop.symm
    have hp : Nat.Coprime p D := Nat.Coprime.coprime_mul_right h1
    have hp1 : Nat.Coprime (p + 1) D := Nat.Coprime.coprime_mul_left h1
    exact Nat.Coprime.mul_left (hp.pow_left 2) hp1
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop' hD
  refine ⟨(D - 2) * u, ?_⟩
  have hu' : ((p ^ 2 * (p + 1) * u : ℕ) : ZMod D) = 1 := by
    rw [show (1 : ZMod D) = ((1 : ℕ) : ZMod D) by simp, ZMod.natCast_eq_natCast_iff', hu,
      Nat.mod_eq_of_lt hD]
  have hDZ : ((D - 2 : ℕ) : ZMod D) = -2 := by
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]; simp
  have hc : ((c₂ p D ((D - 2) * u) : ℕ) : ZMod D) = (((D - 2) * u * p ^ 2 : ℕ) : ZMod D) := by
    rw [ZMod.natCast_eq_natCast_iff']; unfold c₂; simp
  have goal : ((c₂ p D ((D - 2) * u) * (p + 1) + 2 : ℕ) : ZMod D) = 0 := by
    push_cast
    rw [hc]
    push_cast
    rw [hDZ]
    push_cast at hu'
    linear_combination (-2 : ZMod D) * hu'
  rw [ZMod.natCast_eq_zero_iff] at goal
  exact Nat.mod_eq_zero_of_dvd goal

/-! ### Instances: every parameter is forced by the arithmetic, nothing is scanned -/

/-- **`M(127,1) ≥ 3843`** (`0.968·⌊127/2⌋²`): background `1/61`, `127^15 ≡ −1 (mod 61)`,
`c₀ = 13`.  The only `decide`s are the two residues. -/
theorem mahler_lower_bound_base127_drift_one :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ 3842 →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt 127 ((m : ℝ) * α) [126] n :=
  mahler_lower_bound_drift_one 127 61 13 15
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by decide,
      by norm_num, by decide⟩

/-- **`M(101,1) ≥ 2450`** (`0.980·⌊101/2⌋²`): background `1/49`, `101^21 ≡ −1 (mod 49)`,
`c₀ = 19`. -/
theorem mahler_lower_bound_base101_drift_one :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ 2449 →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt 101 ((m : ℝ) * α) [100] n :=
  mahler_lower_bound_drift_one 101 49 19 21
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by decide,
      by norm_num, by decide⟩

/-! ### The arithmetic crux -/

/-! ### The classical form of the crux -/

/-- Euler's criterion, in the form the certificate needs: a non-square `a` modulo an
odd prime `q` has `a^(q/2) ≡ −1 (mod q)`. -/
theorem pow_half_mod_of_not_isSquare (q a : ℕ) (hq : q.Prime) (hq2 : 2 < q)
    (ha : ¬ IsSquare (a : ZMod q)) : a ^ (q / 2) % q = q - 1 := by
  have := Fact.mk hq
  have ha0 : (a : ZMod q) ≠ 0 := by
    intro h; exact ha ⟨0, by rw [h]; ring⟩
  rcases ZMod.pow_div_two_eq_neg_one_or_one q ha0 with h1 | h1
  · exact absurd ((ZMod.euler_criterion q ha0).2 h1) ha
  · have h2 : ((a ^ (q / 2) : ℕ) : ZMod q) = ((q - 1 : ℕ) : ZMod q) := by
      rw [Nat.cast_pow, h1, Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_one, zero_sub]
    rw [ZMod.natCast_eq_natCast_iff'] at h2
    rw [h2, Nat.mod_eq_of_lt (by omega)]

/-- A prime background `q` with `p` a quadratic non-residue is a drift-one background
(`t = q/2`). -/
theorem background_of_nonresidue (p q : ℕ) (hq : q.Prime) (hq2 : 2 < q)
    (h3 : p < 3 * q) (h2 : 2 * q < p) (hdvd : ¬ q ∣ p + 1) (hsq : ¬ IsSquare (p : ZMod q)) :
    q % 2 = 1 ∧ p < 3 * q ∧ 2 * q < p ∧ Nat.Coprime q (p + 1) ∧
      ∃ t, 0 < t ∧ p ^ t % q = q - 1 := by
  refine ⟨?_, h3, h2, (Nat.Prime.coprime_iff_not_dvd hq).2 hdvd, q / 2, by omega,
    pow_half_mod_of_not_isSquare q p hq hq2 hsq⟩
  rcases hq.eq_two_or_odd with h | h <;> omega

/-- **The arithmetic crux, classical form.**  Every prime `p ≥ 73` has a prime
`q ∈ (p/3, p/2)`, `q ∤ p + 1`, with `p` a quadratic non-residue modulo `q`.
Measured true for every prime `73 ≤ p < 6000` (`experiments/mahler_drift_one_probe.py
--qnr`); it FAILS at `p = 71` (whose drift-one background `29` has `71` a residue
with `ord_29(71) = 14`), which is why `71` is handled by hand below.  By quadratic
reciprocity this is a prime in a short interval with a prescribed Legendre symbol —
unconditionally a Linnik-strength statement; not in mathlib.  Disclosed `sorry`. -/
theorem exists_prime_nonresidue (p : ℕ) (hp : p.Prime) (h73 : 73 ≤ p) :
    ∃ q, q.Prime ∧ p < 3 * q ∧ 2 * q < p ∧ ¬ q ∣ p + 1 ∧ ¬ IsSquare (p : ZMod q) := by
  sorry

/-- **The arithmetic crux behind a uniform constant above `1/12`.**  Every prime
`p ≥ 61` has an odd background `D ∈ (p/3, p/2)`, coprime to `p + 1`, with
`−1 ∈ ⟨p⟩ (mod D)`.  Measured true for every prime `61 ≤ p < 4000`
(`experiments/mahler_drift_one_probe.py`); it FAILS at `p = 23` (best `D = 5`) and
`p = 59` (best `D = 19`), which is why the threshold is `61`.  Reduced to the classical
`exists_prime_nonresidue` (the only `sorry`), plus explicit witnesses at `61, 67, 71`. -/
theorem exists_drift_one_background (p : ℕ) (hp : p.Prime) (h61 : 61 ≤ p) :
    ∃ D, D % 2 = 1 ∧ p < 3 * D ∧ 2 * D < p ∧ Nat.Coprime D (p + 1) ∧
      ∃ t, 0 < t ∧ p ^ t % D = D - 1 := by
  rcases Nat.lt_or_ge p 73 with h | h
  · have hcases : p = 61 ∨ p = 67 ∨ p = 71 := by
      interval_cases p <;> first | (norm_num at hp; done) | simp
    rcases hcases with rfl | rfl | rfl
    · exact ⟨23, background_of_nonresidue 61 23 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)⟩
    · exact ⟨23, background_of_nonresidue 67 23 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)⟩
    · exact ⟨29, by norm_num, by norm_num, by norm_num, by norm_num, 7, by norm_num, by decide⟩
  · obtain ⟨q, hq, h3, h2, hdvd, hsq⟩ := exists_prime_nonresidue p hp h
    exact ⟨q, background_of_nonresidue p q hq (by omega) h3 h2 hdvd hsq⟩

/-- Any background as in `exists_drift_one_background` yields a `DriftOne` instance. -/
theorem driftOne_of_background (p D t : ℕ) (hp : p.Prime) (hodd : p % 2 = 1)
    (hDodd : D % 2 = 1) (h3 : p < 3 * D) (hDp : 2 * D < p) (hcop : Nat.Coprime D (p + 1))
    (ht : 0 < t) (hpt : p ^ t % D = D - 1) : ∃ c₀, DriftOne p D c₀ t := by
  have hD3 : 3 ≤ D := by
    rcases Nat.lt_or_ge D 3 with h | h
    · interval_cases D <;> omega
    · exact h
  have hcopP : Nat.Coprime D p := by
    have hpos : 0 < D := by omega
    exact ((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt hpos (by omega))).symm
  obtain ⟨c₀, hc⟩ := exists_c₀ p D (by omega) (Nat.Coprime.mul_right hcopP hcop)
  exact ⟨c₀, ⟨by omega, hodd, hD3, hDodd, hDp, hc, ht, hpt⟩⟩

/-- `driftBound` is monotone in `D`. -/
theorem driftBound_mono (p : ℕ) {D D' : ℕ} (h : D ≤ D') : driftBound p D ≤ driftBound p D' := by
  unfold driftBound
  have := Nat.mul_le_mul_right (p - 1) h
  omega

/-- **The conditional uniform bound.**  Granting `exists_drift_one_background`, every
prime `p ≥ 61` has `M(p,1) > (⌊p/3⌋ + 1)(p − 1)/2 − 1 ≥ p²/6 − O(p)` — the factor
`3` of `mahler_lower_bound_prime_family_II` halved, and `p²/4 − O(p)` whenever the
background can be taken near `p/2`. -/
theorem mahler_lower_bound_prime_drift_one (p : ℕ) (hp : p.Prime) (h61 : 61 ≤ p) :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ (p / 3 + 1) * (p - 1) / 2 - 1 →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt p ((m : ℝ) * α) [p - 1] n := by
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h2 | h2
    · omega
    · exact h2
  obtain ⟨D, hDodd, h3, hDp, hcop, t, ht, hpt⟩ := exists_drift_one_background p hp h61
  obtain ⟨c₀, h⟩ := driftOne_of_background p D t hp hodd hDodd h3 hDp hcop ht hpt
  obtain ⟨α, hα, hM⟩ := mahler_lower_bound_drift_one p D c₀ t h
  refine ⟨α, hα, fun m hm1 hm => hM m hm1 (le_trans hm ?_)⟩
  have : p / 3 + 1 ≤ D := by omega
  exact driftBound_mono p this

/-! ### General offset `b`: the keys from the two channel bounds -/

/-- Drift-one hypotheses for a junction of offset `b`: `b ∣ p + 1`, `gcd(b, D) = 1`,
`c₂(p+1) ≡ −b (mod D)`. -/
structure DriftOneB (p D c₀ b : ℕ) : Prop where
  hp : 3 ≤ p
  hD3 : 3 ≤ D
  hb : 2 ≤ b
  hbD : b + D < p
  hbp : b ∣ p + 1
  hcop : Nat.Coprime b D
  hc₂ : (c₂ p D c₀ * (p + 1) + b) % D = 0

namespace DriftOneB

variable {p D c₀ b : ℕ} (h : DriftOneB p D c₀ b)
include h

theorem toHyp : Hyp p D b where
  hp := h.hp
  hD := by have := h.hD3; omega
  hb := by have := h.hb; omega
  hbD := h.hbD

theorem D_pos : 0 < D := by have := h.hD3; omega

/-- **KeyA** from `bm < p(p − D)`. -/
theorem keyA (m : ℕ) (hm : b * m < p * (p - D)) :
    p ^ 2 * (m * c₁ p D c₀ % D) + m * b < (p - 1) * (p * D) := by
  have hR : m * c₁ p D c₀ % D + 1 ≤ D := Nat.mod_lt _ h.D_pos
  have h1 : p ^ 2 * (m * c₁ p D c₀ % D) + p ^ 2 ≤ p ^ 2 * D := by
    have := Nat.mul_le_mul_left (p ^ 2) hR; linarith
  have hDp : D < p := by have := h.hbD; have := h.hb; omega
  have hp := h.hp
  have e3 : p * D ≤ p * p := Nat.mul_le_mul_left p hDp.le
  have e : (p - 1) * (p * D) + p * D = p ^ 2 * D := by
    rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ (by omega))]; ring
  have e2 : p * (p - D) + p * D = p ^ 2 := by
    rw [Nat.mul_sub, Nat.sub_add_cancel e3]; ring
  have e4 : m * b = b * m := by ring
  omega

/-- The residue of `N₀` at channel `m`, split as `w + p·r` with `bm = pv + w`. -/
theorem n0_res (m : ℕ) :
    m * (c₂ p D c₀ * p + b) % (p * D)
      = p * ((m * c₂ p D c₀ + b * m / p) % D) + b * m % p := by
  have hp : 0 < p := by have := h.hp; omega
  set v := b * m / p with hv
  set w := b * m % p with hw
  have hvw : b * m = p * v + w := (Nat.div_add_mod (b * m) p).symm
  have hwp : w < p := Nat.mod_lt _ hp
  set A := m * c₂ p D c₀ + v with hA
  set r := A % D with hr
  set q := A / D with hq
  have hAqr : A = D * q + r := (Nat.div_add_mod A D).symm
  have hrD : r + 1 ≤ D := Nat.mod_lt _ h.D_pos
  have hpr : p * r + p ≤ p * D := by
    have := Nat.mul_le_mul_left p hrD; linarith
  have hnum : m * (c₂ p D c₀ * p + b) = (p * r + w) + (p * D) * q := by
    have e1 : m * (c₂ p D c₀ * p + b) = p * (m * c₂ p D c₀) + b * m := by ring
    rw [e1, hvw, show p * (m * c₂ p D c₀) + (p * v + w) = p * A + w by rw [hA]; ring,
      hAqr]
    ring
  rw [hnum, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- **KeyB** from `bm + D < (b−1)pD`.  The only channels violating keyB satisfy
`bm = (p+1)(v+1) − Dg` with `b ∣ g`, hence `g ≥ b` and `bm ≥ (b−1)pD − D`. -/
theorem keyB (m : ℕ) (hm : b * m + D < (b - 1) * p * D) :
    m * (c₂ p D c₀ * p + b) % (p * D) < (p - 1) * D := by
  have hp := h.hp
  have hD3 := h.hD3
  have hb := h.hb
  have hDp : D < p := by have := h.hbD; omega
  rw [h.n0_res m]
  set v := b * m / p with hv
  set w := b * m % p with hw
  have hvw : b * m = p * v + w := (Nat.div_add_mod (b * m) p).symm
  have hwp : w < p := Nat.mod_lt _ (by omega)
  set c := c₂ p D c₀ with hc
  set r := (m * c + v) % D with hr
  have hrD : r + 1 ≤ D := Nat.mod_lt _ h.D_pos
  have e : (p - 1) * D + D = p * D := by
    rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ (by omega))]
  by_contra hcon
  push Not at hcon
  have hr' : r = D - 1 := by
    by_contra hne
    have hr2 : r + 2 ≤ D := by omega
    have := Nat.mul_le_mul_left p hr2
    have e2 : p * (r + 2) = p * r + 2 * p := by ring
    omega
  have hpr : p * r + p = p * D := by
    have e1 : p * (r + 1) = p * D := by rw [show r + 1 = D by omega]
    linarith
  have hwD : p ≤ w + D := by omega
  have hdiv : D ∣ m * c + v + 1 := by
    have : (m * c + v) % D + 1 = D := by omega
    have h1 := Nat.div_add_mod (m * c + v) D
    refine ⟨(m * c + v) / D + 1, ?_⟩
    rw [Nat.mul_succ]; omega
  have hc2 : D ∣ c * (p + 1) + b := Nat.dvd_of_mod_eq_zero h.hc₂
  obtain ⟨ℓ, hℓ⟩ := hdiv
  obtain ⟨k, hk⟩ := hc2
  -- `v + p + 1 − w = D·g` in `ℤ`
  have hZ : ((v : ℤ) + p + 1 - w) = D * (ℓ * (p + 1) - m * k) := by
    have hℓZ : ((m : ℤ) * c + v + 1) = D * ℓ := by exact_mod_cast hℓ
    have hkZ : ((c : ℤ) * (p + 1) + b) = D * k := by exact_mod_cast hk
    have hvwZ : (b : ℤ) * m = p * v + w := by exact_mod_cast hvw
    linear_combination (p + 1 : ℤ) * hℓZ - (m : ℤ) * hkZ + hvwZ
  set g : ℤ := ℓ * (p + 1) - m * k with hg
  have hDZ : (0 : ℤ) < D := by exact_mod_cast h.D_pos
  have hwZ : (w : ℤ) < p := by exact_mod_cast hwp
  have hwDZ : (p : ℤ) ≤ w + D := by exact_mod_cast hwD
  have hlo : (2 : ℤ) ≤ D * g := by rw [← hZ]; linarith
  have hg0 : 0 ≤ g := by
    by_contra hng; push Not at hng
    have : D * g < 0 := by nlinarith
    linarith
  obtain ⟨gN, hgN⟩ := Int.eq_ofNat_of_zero_le hg0
  -- `b·m + D·gN = (p+1)(v+1)` in `ℕ`, hence `b ∣ D·gN`, hence `b ∣ gN`
  have hbm : b * m + D * gN = (p + 1) * (v + 1) := by
    have : ((b : ℤ) * m + D * gN) = (p + 1) * (v + 1) := by
      rw [← hgN]
      have hvwZ : (b : ℤ) * m = p * v + w := by exact_mod_cast hvw
      linear_combination hvwZ - hZ
    exact_mod_cast this
  have hbdvd : b ∣ D * gN := by
    have h1 : b ∣ (p + 1) * (v + 1) := Dvd.dvd.mul_right h.hbp _
    rw [← hbm] at h1
    exact (Nat.dvd_add_right (dvd_mul_right b m)).mp h1
  have hbg : b ∣ gN := Nat.Coprime.dvd_of_dvd_mul_left h.hcop hbdvd
  have hgpos : 0 < gN := by
    by_contra h0; push Not at h0
    have : gN = 0 := by omega
    rw [this] at hgN; rw [hgN] at hlo; simp at hlo
  have hgb : b ≤ gN := Nat.le_of_dvd hgpos hbg
  have hv1 : D * gN ≤ v + 1 + D := by
    have : (D : ℤ) * gN ≤ v + 1 + D := by rw [← hgN, ← hZ]; linarith
    exact_mod_cast this
  have h1 : p * (D * gN) ≤ p * (v + 1 + D) := Nat.mul_le_mul_left p hv1
  have h2 : p * D * b ≤ p * D * gN := Nat.mul_le_mul_left _ hgb
  have e3 : (b - 1) * p * D + p * D = p * D * b := by
    rw [show (b - 1) * p * D = (b - 1) * (p * D) by ring, Nat.sub_one_mul,
      Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ (by omega))]
    ring
  -- assemble: `bm = (p+1)(v+1) − D gN ≥ pD(gN − 1) − D ≥ pD(b−1) − D`
  nlinarith

theorem keys (M : ℕ) (hM0 : 0 < M) (hMA : b * M < p * (p - D))
    (hMB : b * M + D < (b - 1) * p * D) : Keys p D c₀ b M where
  posM := hM0
  keyA := fun m hm => h.keyA m (lt_of_le_of_lt (Nat.mul_le_mul_left b hm) hMA)
  keyB := fun m hm => h.keyB m (by have := Nat.mul_le_mul_left b hm; omega)
  keyJ := by
    have hp := h.hp
    have hDp : D < p := by have := h.hbD; have := h.hb; omega
    have e3 : p * D ≤ p * p := Nat.mul_le_mul_left p hDp.le
    have e2 : p * (p - D) + p * D = p ^ 2 := by
      rw [Nat.mul_sub, Nat.sub_add_cancel e3]; ring
    have e4 : p ^ 2 + p ^ 2 * D ≤ p ^ 3 + p * D := by nlinarith
    omega
  keyR := by
    have hp := h.hp
    have hD := h.hD3
    have hDp : D < p := by have := h.hbD; have := h.hb; omega
    have e3 : p * D ≤ p * p := Nat.mul_le_mul_left p hDp.le
    have e2 : p * (p - D) + p * D = p ^ 2 := by
      rw [Nat.mul_sub, Nat.sub_add_cancel e3]; ring
    have e5 : 2 * p ^ 2 ≤ p ^ 2 * D := by nlinarith
    have e6 : 2 * b * M = 2 * (b * M) := by ring
    omega

end DriftOneB

end NormalNumbers.Adder.Background
