/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4WeightA

/-!
# Transport rigidity: every `TWeight` is affine along prime-power towers

`G4WeightInterface` asserts, in prose, that the exact affine transport identity of
`G4Transport` "holds iff every `g_p` is affine on `v ≥ 1`".  This module proves it, and in the
strongest available form: the claim is not about a particular additive model but about the
`TWeight` interface itself.

**`TWeight.wN_prime_pow_second_diff`** — for *any* `W : TWeight`, any prime `p` and any `v ≥ 1`,

  `w(p^{v+2}) − w(p^{v+1}) = w(p^{v+1}) − w(p^v)`.

The proof is three lines of the interface: `mul_eq` at `d = p` identifies the transport
correction as `ov p m = w(m) + w(p) − w(p·m)`, and `ov_congr` at `m = p^v`, `m' = p^{v+1}`
(congruent mod `p`, both being `0`) equates two consecutive such corrections.

**Consequence for the campaign.**  `DIRECTION.md`'s one permitted stretch past the `a`-side is
the general additive function `f(p^v) ≤ a_p + c_p(v−1)` with `f(p) = a_p` and `f` non-decreasing
in `v`.  This module shows that any such `f` which is **not** affine in `v` on `v ≥ 1` cannot be
a `TWeight` at all: the obstruction sits in the transport interface, upstream of §4C and §4D, so
no far-field domination argument can reach it.  Conversely `weightAN_prime_pow` shows every
affine profile `v ↦ a_p + c_p(v−1)` *is* realised, by `weightA a c`.  So the classification is
sharp, and the stretch is a **proved obstruction**, not an open lemma.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.G4

namespace TWeight

/-- The transport correction is `ov d m = w(m) + w(d) − w(d·m)`; this is forced by `mul_eq`. -/
lemma ov_eq (W : TWeight) {d m : ℕ} (hd : d ≠ 0) (hm : m ≠ 0) :
    W.ov d m = (W.wN m : ℤ) + (W.wN d : ℤ) - (W.wN (d * m) : ℤ) := by
  have h := W.mul_eq d m hd hm
  omega

/-- **Transport rigidity.**  Every `TWeight` has vanishing second difference along every
prime-power tower above exponent `1`. -/
theorem wN_prime_pow_second_diff (W : TWeight) {p : ℕ} (hp : p.Prime) {v : ℕ} (hv : 1 ≤ v) :
    (W.wN (p ^ (v + 2)) : ℤ) - (W.wN (p ^ (v + 1)) : ℤ)
      = (W.wN (p ^ (v + 1)) : ℤ) - (W.wN (p ^ v) : ℤ) := by
  have hp0 : p ≠ 0 := hp.pos.ne'
  have hpow : ∀ k : ℕ, p ^ k ≠ 0 := fun k => pow_ne_zero k hp0
  -- the two corrections, computed by `ov_eq`
  have h1 : W.ov p (p ^ v) = (W.wN (p ^ v) : ℤ) + (W.wN p : ℤ) - (W.wN (p ^ (v + 1)) : ℤ) := by
    rw [W.ov_eq hp0 (hpow v), ← pow_succ']
  have h2 : W.ov p (p ^ (v + 1))
      = (W.wN (p ^ (v + 1)) : ℤ) + (W.wN p : ℤ) - (W.wN (p ^ (v + 2)) : ℤ) := by
    rw [W.ov_eq hp0 (hpow (v + 1)), ← pow_succ']
  -- `p^v ≡ p^{v+1} [MOD p]`: both are `0`
  have hcong : ∀ q ∈ p.primeFactors, p ^ v ≡ p ^ (v + 1) [MOD q] := by
    intro q hq
    rw [Nat.mem_primeFactors] at hq
    have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq.1 hp).1 hq.2.1
    subst hqp
    have hd1 : q ∣ q ^ v := dvd_pow_self q (by omega)
    have hd2 : q ∣ q ^ (v + 1) := dvd_pow_self q (by omega)
    exact (Nat.modEq_zero_iff_dvd.2 hd1).trans (Nat.modEq_zero_iff_dvd.2 hd2).symm
  have hov := W.ov_congr p (p ^ v) (p ^ (v + 1)) hcong
  rw [h1, h2] at hov
  omega

/-- The first difference along a prime-power tower is constant from exponent `1` on. -/
theorem wN_prime_pow_first_diff (W : TWeight) {p : ℕ} (hp : p.Prime) :
    ∀ v : ℕ, 1 ≤ v →
      (W.wN (p ^ (v + 1)) : ℤ) - (W.wN (p ^ v) : ℤ)
        = (W.wN (p ^ 2) : ℤ) - (W.wN p : ℤ) := by
  intro v hv
  induction v with
  | zero => omega
  | succ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · norm_num
      have hstep := W.wN_prime_pow_second_diff hp (v := n) hn
      have hprev := ih hn
      simp only [show n + 1 + 1 = n + 2 from by omega]
      omega

/-- **The affine law.**  `w(p^v) = w(p) + (v − 1)·(w(p²) − w(p))` for every `v ≥ 1`. -/
theorem wN_prime_pow_affine (W : TWeight) {p : ℕ} (hp : p.Prime) :
    ∀ v : ℕ, 1 ≤ v →
      (W.wN (p ^ v) : ℤ) = (W.wN p : ℤ) + ((v : ℤ) - 1) * ((W.wN (p ^ 2) : ℤ) - (W.wN p : ℤ)) := by
  intro v hv
  induction v with
  | zero => omega
  | succ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · norm_num
      have hd := W.wN_prime_pow_first_diff hp n hn
      have hprev := ih hn
      push_cast at hprev ⊢
      push_cast at hd
      linarith

/-- Every affine profile is realised: `w_{a,c}(p^v) = a_p + c_p·(v−1)` for `v ≥ 1`. -/
theorem weightAN_prime_pow (a c : ℕ → ℕ) {p : ℕ} (hp : p.Prime) {v : ℕ} (hv : 1 ≤ v) :
    weightAN a c (p ^ v) = a p + c p * (v - 1) := by
  have hv0 : v ≠ 0 := by omega
  have hpf : (p ^ v).primeFactors = {p} := by
    rw [Nat.primeFactors_pow p hv0, hp.primeFactors]
  have hfac : (p ^ v).factorization p = v := by
    rw [Nat.Prime.factorization_pow hp]
    simp
  unfold weightAN
  rw [hpf, Finset.sum_singleton, Finset.sum_singleton, hfac]

/-! ### The classification, as a biconditional

`G4WeightInterface` claims the transport identity holds **iff** every per-prime profile is
affine on `v ≥ 1`.  `wN_prime_pow_affine` is the forward half for an arbitrary `TWeight`; the
two lemmas below turn it into a statement about additive weights proper, and record the
converse half (the affine profiles are realised by `weightA`). -/

/-- An additive weight assembled from per-prime profiles `g p : ℕ → ℕ` (with `g p 0 = 0`
implicit, since the sum runs over `m.primeFactors`). -/
def addWeightN (g : ℕ → ℕ → ℕ) (m : ℕ) : ℕ := ∑ p ∈ m.primeFactors, g p (m.factorization p)

lemma addWeightN_prime_pow (g : ℕ → ℕ → ℕ) {p : ℕ} (hp : p.Prime) {v : ℕ} (hv : 1 ≤ v) :
    addWeightN g (p ^ v) = g p v := by
  have hv0 : v ≠ 0 := by omega
  have hpf : (p ^ v).primeFactors = {p} := by
    rw [Nat.primeFactors_pow p hv0, hp.primeFactors]
  have hfac : (p ^ v).factorization p = v := by
    rw [Nat.Prime.factorization_pow hp]; simp
  rw [addWeightN, hpf, Finset.sum_singleton, hfac]

/-- **Forward half of the classification.**  If an additive weight is the `wN` of *some*
`TWeight`, then every per-prime profile is affine on `v ≥ 1`. -/
theorem affine_of_addWeightN_isTWeight (g : ℕ → ℕ → ℕ) (W : TWeight)
    (hW : W.wN = addWeightN g) {p : ℕ} (hp : p.Prime) {v : ℕ} (hv : 1 ≤ v) :
    (g p v : ℤ) = (g p 1 : ℤ) + ((v : ℤ) - 1) * ((g p 2 : ℤ) - (g p 1 : ℤ)) := by
  have h := W.wN_prime_pow_affine hp v hv
  have h1 : addWeightN g p = g p 1 := by
    have := addWeightN_prime_pow g hp (v := 1) le_rfl
    simpa using this
  rw [hW, addWeightN_prime_pow g hp hv, h1,
    addWeightN_prime_pow g hp (by omega : 1 ≤ 2)] at h
  exact h

/-- **Converse half.**  Every affine family of profiles is an additive weight of the
already-realised class `w_{a,c}` — so `weightA a c` is a `TWeight` carrying it. -/
theorem addWeightN_affine_eq_weightAN (a c : ℕ → ℕ) (m : ℕ) :
    addWeightN (fun p v => a p + c p * (v - 1)) m = weightAN a c m := by
  rw [addWeightN, weightAN, ← Finset.sum_add_distrib]

/-! ### Multiplicative rigidity: the interface forces near-additivity

The affine law above uses `ov_congr` at `d = p` with `m` a power of `p`.  Used at `m ≡ 1`
instead it gives the companion statement: the transport correction is *exactly* `w(1)` whenever
`m` is `1` modulo every prime of `d`, so `w` is additive on such pairs.  No hypothesis beyond
the interface is needed — in particular `w` is not assumed additive, multiplicative, or
monotone. -/

/-- The transport correction at `m = 1` is `w(1)`, for every `d ≠ 0`. -/
lemma ov_one (W : TWeight) {d : ℕ} (hd : d ≠ 0) : W.ov d 1 = (W.wN 1 : ℤ) := by
  rw [W.ov_eq hd one_ne_zero, mul_one]
  ring

/-- **Multiplicative rigidity.**  If `m ≡ 1` modulo every prime of `d`, then the weight is
additive at `(d, m)` up to the constant `w(1)`. -/
theorem wN_mul_of_modEq_one (W : TWeight) {d m : ℕ} (hd : d ≠ 0) (hm : m ≠ 0)
    (h : ∀ p ∈ d.primeFactors, m ≡ 1 [MOD p]) :
    (W.wN (d * m) : ℤ) = (W.wN d : ℤ) + (W.wN m : ℤ) - (W.wN 1 : ℤ) := by
  have hcong := W.ov_congr d m 1 h
  rw [W.ov_eq hd hm, W.ov_one hd] at hcong
  omega

/-- The same, normalised: a `TWeight` with `w(1) = 0` is genuinely additive on those pairs. -/
theorem wN_mul_of_modEq_one' (W : TWeight) (h1 : W.wN 1 = 0) {d m : ℕ} (hd : d ≠ 0) (hm : m ≠ 0)
    (h : ∀ p ∈ d.primeFactors, m ≡ 1 [MOD p]) :
    W.wN (d * m) = W.wN d + W.wN m := by
  have := W.wN_mul_of_modEq_one hd hm h
  rw [h1] at this
  omega

/-- Additive weights are normalised: `addWeightN g 1 = 0`. -/
@[simp] lemma addWeightN_one (g : ℕ → ℕ → ℕ) : addWeightN g 1 = 0 := by
  rw [addWeightN, Nat.primeFactors_one, Finset.sum_empty]

/-- **The two rigidities together.**  For any `TWeight` with `w(1) = 0`, a prime `p`, an
exponent `v ≥ 1` and an `m ≥ 1` with `m ≡ 1 [MOD p]`:
`w(p^v · m) = w(p) + (v − 1)·(w(p²) − w(p)) + w(m)`.  The whole `p`-local structure of the
interface is one affine profile. -/
theorem wN_prime_pow_mul (W : TWeight) (h1 : W.wN 1 = 0) {p : ℕ} (hp : p.Prime) {v m : ℕ}
    (hv : 1 ≤ v) (hm : m ≠ 0) (h : m ≡ 1 [MOD p]) :
    (W.wN (p ^ v * m) : ℤ)
      = (W.wN p : ℤ) + ((v : ℤ) - 1) * ((W.wN (p ^ 2) : ℤ) - (W.wN p : ℤ)) + (W.wN m : ℤ) := by
  have hpv : p ^ v ≠ 0 := pow_ne_zero v hp.pos.ne'
  have hpf : ∀ q ∈ (p ^ v).primeFactors, m ≡ 1 [MOD q] := by
    intro q hq
    rw [Nat.primeFactors_pow p (by omega : v ≠ 0), hp.primeFactors, Finset.mem_singleton] at hq
    subst hq
    exact h
  have hsplit := W.wN_mul_of_modEq_one hpv hm hpf
  have haff := W.wN_prime_pow_affine hp v hv
  rw [h1] at hsplit
  omega

/-! ### The cocycle structure of the transport correction

`ov` is not an extra datum: `mul_eq` pins it to `w(m) + w(d) − w(dm)`, so it is symmetric and
satisfies the `2`-cocycle identity of the multiplicative semigroup.  Combined with `ov_congr`
this is the whole content of the interface, and it is the tool the remaining classification
question needs (see `PENDING_WORK.md`). -/

lemma ov_symm (W : TWeight) {d m : ℕ} (hd : d ≠ 0) (hm : m ≠ 0) : W.ov d m = W.ov m d := by
  rw [W.ov_eq hd hm, W.ov_eq hm hd, mul_comm]
  ring

/-- **The cocycle identity.**  `ov d m + ov (d·m) k = ov m k + ov d (m·k)`. -/
theorem ov_cocycle (W : TWeight) {d m k : ℕ} (hd : d ≠ 0) (hm : m ≠ 0) (hk : k ≠ 0) :
    W.ov d m + W.ov (d * m) k = W.ov m k + W.ov d (m * k) := by
  have h1 := W.ov_eq hd hm
  have h2 := W.ov_eq (mul_ne_zero hd hm) hk
  have h3 := W.ov_eq hm hk
  have h4 := W.ov_eq hd (mul_ne_zero hm hk)
  rw [h1, h2, h3, h4, mul_assoc]
  ring

/-- If `k ≡ 1` modulo every prime of `d`, the correction does not see the `d`-part:
`ov (d·m) k = ov m k`.  (Cocycle identity plus `ov_congr` in the `d`-slot.) -/
theorem ov_mul_left_of_modEq_one (W : TWeight) {d m k : ℕ} (hd : d ≠ 0) (hm : m ≠ 0)
    (hk : k ≠ 0) (h : ∀ p ∈ d.primeFactors, k ≡ 1 [MOD p]) :
    W.ov (d * m) k = W.ov m k := by
  have hstable : W.ov d (m * k) = W.ov d m := by
    refine W.ov_congr d (m * k) m (fun p hp => ?_)
    have hk1 : k ≡ 1 [MOD p] := h p hp
    calc m * k ≡ m * 1 [MOD p] := Nat.ModEq.mul_left m hk1
      _ = m := by ring
  have hc := W.ov_cocycle hd hm hk
  rw [hstable] at hc
  omega

/-! ### The interface is strictly larger than the additive weights

`omegaOdd` is `ω(m) + 1_{m odd}`.  It satisfies every axiom of `TWeight` — the twist is constant
for odd `d`, and for even `d` the prime `2` lies in `d.primeFactors`, so `ov_congr`'s hypothesis
supplies `m ≡ m' [MOD 2]` — yet it is **not** additive: `w(15) = 3 ≠ w(3) + w(5) = 4`.

It is, however, `ω(m) − 1_{2 ∣ m}` plus the constant `1`, i.e. additive **plus a constant**, and
`w(1) = 1 ≠ 0`.  So the `− w(1)` in `wN_mul_of_modEq_one` is load-bearing, and the sharp
classification conjecture is about `m ↦ w(m) − w(1)` (see `PENDING_WORK.md`). -/

/-- The twist `1_{m odd}`. -/
def oddBit (m : ℕ) : ℕ := if m % 2 = 1 then 1 else 0

lemma oddBit_le_one (m : ℕ) : oddBit m ≤ 1 := by unfold oddBit; split_ifs <;> omega

/-- The transport twist: `0` exactly when `2` is a prime factor of `d` and divides `m`. -/
def oddTwist (d m : ℕ) : ℤ := if 2 ∈ d.primeFactors ∧ 2 ∣ m then 0 else 1

/-- `1_{dm odd} + twist = 1_{m odd} + 1_{d odd}` for `d, m ≠ 0`. -/
lemma oddBit_mul (d m : ℕ) (hd : d ≠ 0) (hm : m ≠ 0) :
    (oddBit (d * m) : ℤ) + oddTwist d m = (oddBit m : ℤ) + (oddBit d : ℤ) := by
  have hmul : (d * m) % 2 = (d % 2) * (m % 2) % 2 := Nat.mul_mod d m 2
  unfold oddBit oddTwist
  by_cases hD : 2 ∈ d.primeFactors
  · have hDd : (2 : ℕ) ∣ d := (Nat.mem_primeFactors.1 hD).2.1
    have hd0 : d % 2 = 0 := Nat.dvd_iff_mod_eq_zero.1 hDd
    by_cases hM : (2 : ℕ) ∣ m
    · have hm0 : m % 2 = 0 := Nat.dvd_iff_mod_eq_zero.1 hM
      simp [hD, hM, hmul, hd0, hm0]
    · have hm1 : m % 2 = 1 := by omega
      simp [hD, hM, hmul, hd0, hm1]
  · have hDd : ¬ ((2 : ℕ) ∣ d) := fun h => hD (Nat.mem_primeFactors.2 ⟨Nat.prime_two, h, hd⟩)
    have hd1 : d % 2 = 1 := by omega
    by_cases hM : (2 : ℕ) ∣ m
    · have hm0 : m % 2 = 0 := Nat.dvd_iff_mod_eq_zero.1 hM
      simp [hD, hmul, hd1, hm0]
    · have hm1 : m % 2 = 1 := by omega
      simp [hD, hmul, hd1, hm1]

/-- **`ω + 1_{odd}` is a `TWeight`.** -/
def omegaOdd : TWeight where
  wN := fun m => omega.wN m + oddBit m
  ov := fun d m => omega.ov d m + oddTwist d m
  ovB := fun d => omega.ovB d + 1
  mul_eq := fun d m hd hm => by
    have h1 := omega.mul_eq d m hd hm
    have h2 := oddBit_mul d m hd hm
    push_cast
    push_cast at h1 h2
    linarith
  ov_le := fun d m => by
    have h1 := omega.ov_le d m
    have h2 : oddTwist d m = 0 ∨ oddTwist d m = 1 := by
      unfold oddTwist; split_ifs <;> simp
    have h3 : (0 : ℤ) ≤ (omega.ovB d : ℤ) := Int.natCast_nonneg _
    rw [abs_le] at h1 ⊢
    push_cast
    omega
  ov_congr := fun d m m' h => by
    have h1 := omega.ov_congr d m m' h
    have h2 : oddTwist d m = oddTwist d m' := by
      unfold oddTwist
      by_cases h2d : 2 ∈ d.primeFactors
      · have hmm : m ≡ m' [MOD 2] := h 2 h2d
        unfold Nat.ModEq at hmm
        have hiff : ((2 : ℕ) ∣ m) ↔ ((2 : ℕ) ∣ m') := by omega
        simp [h2d, hiff]
      · simp [h2d]
    rw [h1, h2]
  summable := fun b hb => by
    have h1 := omega.summable b hb
    have hb1 : (1 : ℝ) < (b : ℝ) := by
      have : (2 : ℝ) ≤ b := by exact_mod_cast hb
      linarith
    have h2 : Summable (fun n : ℕ => (1 : ℝ) / (b : ℝ) ^ n) := by
      have : Summable (fun n : ℕ => ((b : ℝ)⁻¹) ^ n) :=
        summable_geometric_of_lt_one (by positivity)
          (by rw [inv_lt_one_iff₀]; exact Or.inr hb1)
      simpa [one_div, inv_pow] using this
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (h1.add h2)
    have hbn : (0 : ℝ) < (b : ℝ) ^ n := by positivity
    have hle : ((omega.wN n + oddBit n : ℕ) : ℝ) ≤ (omega.wN n : ℝ) + 1 := by
      have h3 : ((oddBit n : ℕ) : ℝ) ≤ 1 := by exact_mod_cast oddBit_le_one n
      push_cast
      linarith
    calc ((omega.wN n + oddBit n : ℕ) : ℝ) / (b : ℝ) ^ n
        ≤ ((omega.wN n : ℝ) + 1) / (b : ℝ) ^ n := by gcongr
      _ = (omega.wN n : ℝ) / (b : ℝ) ^ n + 1 / (b : ℝ) ^ n := by ring

@[simp] lemma omegaOdd_wN (m : ℕ) : omegaOdd.wN m = omega.wN m + oddBit m := rfl

/-- **`omegaOdd` is not additive**, and `w(1) = 1 ≠ 0`: the `TWeight` interface strictly
contains the additive weights, and only `w − w(1)` can be additive. -/
theorem omegaOdd_not_additive :
    omegaOdd.wN 1 = 1 ∧ omegaOdd.wN 15 ≠ omegaOdd.wN 3 + omegaOdd.wN 5 := by
  refine ⟨?_, ?_⟩ <;> · simp only [omegaOdd_wN, oddBit]; decide +kernel

end TWeight

end NormalNumbers.G4
