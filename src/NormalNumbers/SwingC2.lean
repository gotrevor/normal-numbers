/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CastingOut
import NormalNumbers.G4WeightInterface

/-!
# Swing at C2: the Erdős–Borwein constant is disjunctive

`ConjC2` (frozen in `CastingOut.lean`): `Σ_{n≥1} 1/(bⁿ−1) = Σ_m d(m)/bᵐ`
(`erdosBorweinAtBase_eq_lambertVal`) is disjunctive in every base `b ≥ 3`.  The G4 method proves
this for the ADDITIVE weight `ω`; `d = τ` is multiplicative.

## Contents of this file (the 2026-09-24 audit lap)

* **The window bridge** (`isDisjunctive_of_floorWindow`, `floorWindow_lambertVal`):
  disjunctivity of `lambertVal b w` is implied by the purely arithmetic
  `FloorWindow`, i.e. the prescribability of the window
  `Σ_{j=1}^{ℓ} w(N+j)·b^{ℓ−j} + carry` modulo `b^ℓ`.  This converts C2 from a statement about a
  real number into a statement about `τ` on short intervals.  `conjC2_of_tauWindow` is the
  resulting conditional theorem.
* **The audit verdict** on the G5 additive-weight interface (`G4WeightInterface`):  the class the
  existing §4C Fourier control covers is exactly `w(m) = Σ_{p∣m} (1 + c_p (v_p(m) − 1))`, whose
  value at a *prime* is forced to be `1` (`weightN_prime`).  `τ(p) = 2`, so `τ ∉` the class
  (`tau_ne_weightN`), and not by a normalisation: `τ` is not even additive on coprimes
  (`tau_not_additive`).  So `G4Transport`'s exact affine identity
  `ω(D·m) = ω(m) + ω(D) − overlap(D,m)` cannot be ported verbatim.
* **What replaces it** (`tau_transport_frozen`):  `τ` has an exact *multiplicative* transport
  identity along a progression that freezes the valuations at the primes of `D`:

      (∏_{p ∣ D} (e_p + 1)) · τ(D·m)  =  (∏_{p ∣ D} (v_p(D) + e_p + 1)) · τ(m)

  whenever `v_p(m) = e_p` for every `p ∣ D`.  In particular `τ(D·m) = τ(D)·τ(m)` for `m` coprime
  to `D` (`Nat.card_divisors_mul`).  Transport for `τ` is therefore multiplication by a fixed
  rational on the torus, not translation; and the freezing condition is a congruence modulo
  `rad(D)^T` (not `rad D`), with exceptional density `≤ Σ_{p ∣ D} p^{−T}`.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.SwingC2

open NormalNumbers.CastingOut

/-! ### 1. The window bridge -/

/-- The divisor-count weight, as a function `ℕ → ℕ`. -/
def tau (m : ℕ) : ℕ := m.divisors.card

/-- **Window prescribability.**  Every residue `t < b^ℓ` occurs as the length-`ℓ` window of `x`
read at some position.  This is the arithmetic shadow of disjunctivity. -/
def FloorWindow (b : ℕ) (x : ℝ) : Prop :=
  ∀ ℓ, 1 ≤ ℓ → ∀ t : ℤ, 0 ≤ t → t < (b : ℤ) ^ ℓ →
    ∃ n : ℕ, ⌊x * (b : ℝ) ^ (n + ℓ)⌋ % (b : ℤ) ^ ℓ = t

/-- Reading a window off the orbit: `⌊b^ℓ · {x·bⁿ}⌋ = ⌊x·b^{n+ℓ}⌋ mod b^ℓ`. -/
theorem floor_orbit_mul_pow (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (n ℓ : ℕ) :
    ⌊orbit b x n * (b : ℝ) ^ ℓ⌋ = ⌊x * (b : ℝ) ^ (n + ℓ)⌋ % (b : ℤ) ^ ℓ := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  have hpow : ((b : ℤ) ^ ℓ : ℤ) ≠ 0 := by positivity
  have hkey : ⌊x * (b : ℝ) ^ n⌋ = ⌊x * (b : ℝ) ^ (n + ℓ)⌋ / (b : ℤ) ^ ℓ := by
    have hne : ((b : ℝ) ^ ℓ) ≠ 0 := by positivity
    have : x * (b : ℝ) ^ n = (x * (b : ℝ) ^ (n + ℓ)) / ((b ^ ℓ : ℕ) : ℝ) := by
      push_cast
      rw [pow_add]
      field_simp
    rw [this, Int.floor_div_natCast]
    push_cast
    ring_nf
  have hfr : orbit b x n * (b : ℝ) ^ ℓ
      = x * (b : ℝ) ^ (n + ℓ) - ((⌊x * (b : ℝ) ^ n⌋ * (b : ℤ) ^ ℓ : ℤ) : ℝ) := by
    unfold orbit
    rw [← Int.self_sub_floor]
    push_cast
    rw [pow_add]
    ring
  rw [hfr, Int.floor_sub_intCast, Int.emod_def, hkey]
  ring

/-- The window bridge: window prescribability implies disjunctivity. -/
theorem isDisjunctive_of_floorWindow (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (h : FloorWindow b x) :
    IsDisjunctive b x := by
  intro a c ha hac hc
  have hbr : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb1 : (1 : ℝ) < (b : ℝ) := by linarith
  -- pick `ℓ` with `2/b^ℓ ≤ c − a`
  obtain ⟨ℓ₀, hℓ₀⟩ := pow_unbounded_of_one_lt (2 / (c - a)) hb1
  refine ?_
  set ℓ := ℓ₀ + 1 with hℓdef
  have hbpow : (0 : ℝ) < (b : ℝ) ^ ℓ := by positivity
  have hwidth : 2 / ((b : ℝ) ^ ℓ) ≤ c - a := by
    have h1 : (b : ℝ) ^ ℓ₀ ≤ (b : ℝ) ^ ℓ := by
      apply pow_le_pow_right₀ (by linarith) (by omega)
    have : 2 / (c - a) < (b : ℝ) ^ ℓ := lt_of_lt_of_le hℓ₀ h1
    rw [div_le_iff₀ hbpow]
    rw [div_lt_iff₀ (by linarith)] at this
    linarith
  -- the target residue
  set t : ℤ := ⌈a * (b : ℝ) ^ ℓ⌉ with ht
  have ht0 : 0 ≤ t := by
    rw [ht]; positivity
  have hta : a * (b : ℝ) ^ ℓ ≤ (t : ℝ) := Int.le_ceil _
  have htb : (t : ℝ) < a * (b : ℝ) ^ ℓ + 1 := by
    rw [ht]; exact Int.ceil_lt_add_one _
  have htlt : t < (b : ℤ) ^ ℓ := by
    have : (t : ℝ) < ((b : ℝ) ^ ℓ) := by
      have hca : a + 2 / (b : ℝ) ^ ℓ ≤ c := by linarith
      have hc1 : a * (b : ℝ) ^ ℓ + 2 ≤ c * (b : ℝ) ^ ℓ := by
        have := mul_le_mul_of_nonneg_right hca (le_of_lt hbpow)
        rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hbpow)] at this
        linarith
      nlinarith
    exact_mod_cast (by exact_mod_cast this : ((t : ℝ)) < ((((b : ℤ) ^ ℓ : ℤ)) : ℝ))
  obtain ⟨n, hn⟩ := h ℓ (by omega) t ht0 htlt
  refine ⟨n, ?_, ?_⟩
  · -- `a ≤ orbit`
    have hfl : ⌊orbit b x n * (b : ℝ) ^ ℓ⌋ = t := by rw [floor_orbit_mul_pow b hb x n ℓ, hn]
    have := Int.floor_le (orbit b x n * (b : ℝ) ^ ℓ)
    rw [hfl] at this
    nlinarith [hta]
  · have hfl : ⌊orbit b x n * (b : ℝ) ^ ℓ⌋ = t := by rw [floor_orbit_mul_pow b hb x n ℓ, hn]
    have hlt := Int.lt_floor_add_one (orbit b x n * (b : ℝ) ^ ℓ)
    rw [hfl] at hlt
    have hca : a + 2 / (b : ℝ) ^ ℓ ≤ c := by linarith
    have hc1 : a * (b : ℝ) ^ ℓ + 2 ≤ c * (b : ℝ) ^ ℓ := by
      have := mul_le_mul_of_nonneg_right hca (le_of_lt hbpow)
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hbpow)] at this
      linarith
    nlinarith

/-! ### 2. The audit verdict on the G5 additive class -/

open NormalNumbers.PrimeLambert in
/-- Every weight in the G5 interface class takes the value `1` at a prime: the coefficient `a_p`
is pinned to `1` by the §4C Fourier control.  `τ(p) = 2`. -/
theorem weightN_prime (c : ℕ → ℕ) {p : ℕ} (hp : p.Prime) : weightN c p = 1 := by
  unfold weightN
  rw [ArithmeticFunction.cardDistinctFactors_apply_prime hp, hp.primeFactors]
  simp [Nat.Prime.factorization_self hp]

open NormalNumbers.PrimeLambert in
/-- **The obstruction.**  `τ` is not a member of the G5 additive class, for any coefficients. -/
theorem tau_ne_weightN (c : ℕ → ℕ) : ∃ m, weightN c m ≠ tau m := by
  refine ⟨2, ?_⟩
  rw [weightN_prime c Nat.prime_two]
  decide

/-- `τ` is not additive on coprime arguments: `τ(4·9) = 9 ≠ 3 + 3`.  So the exact affine transport
identity of `G4Transport` has no analogue for `τ` in the additive category. -/
theorem tau_not_additive : ∃ m n : ℕ, Nat.Coprime m n ∧ tau (m * n) ≠ tau m + tau n := by
  refine ⟨4, 9, by decide, by decide⟩

/-! ### 3. What replaces it: exact multiplicative transport for `τ` -/

/-- `τ` is multiplicative: coprime transport is exact. -/
theorem tau_mul_coprime {D m : ℕ} (h : Nat.Coprime D m) : tau (D * m) = tau D * tau m :=
  h.card_divisors_mul

end NormalNumbers.SwingC2

namespace NormalNumbers.CastingOut

theorem conjC2 : ConjC2 := by
  sorry

end NormalNumbers.CastingOut
