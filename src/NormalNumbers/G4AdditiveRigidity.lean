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

end TWeight

end NormalNumbers.G4
