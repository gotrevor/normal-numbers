/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtMultiShift

/-!
# The joint modulus of `K` shifted congruences

Lap 36's `K`-fold expansion produces, for each tuple `(d_0,…,d_{K-1})` of powerful moduli, the
joint progression `{n : ∀ i, d_i ∣ n+i+1}`.  At `K = 2` the moduli of two *consecutive* integers
are automatically coprime, so the progression is one class mod `d_0 d_1` and the tuple mass
carries the full gain `1/(d_0 d_1)` (`pair_mass_le`).  **At `K ≥ 3` that fails**: `n+1` and `n+3`
can share the factor `2`, so the joint modulus is `lcm(d_i)`, which may be much smaller than
`∏ d_i`, and the `1/∏ d_i` gain — the thing that makes the tuple sum absolutely convergent — is
in danger.

This file settles it.  The point is that a *nonempty* joint progression forces
`gcd(d_i, d_j) ∣ j − i`, so every pairwise gcd is at most `K`, and therefore

    ∏_{i<K} d_i  ≤  lcm(d_i) · K^{K²} .

So the gain survives, at the price of a factor `K^{K²}`.  For the schedule
`K = D_N ≍ log log log N` this factor is `exp(O((log log log N)² log log log log N))`, which is
`(log log N)^{o(1)}` — utterly negligible against the `D = 1` rung's `(log N)^{-a}`.  **The
consequence for the named input**: `QuantDepthElliott`'s constant budget must be widened from
`b^{κD}` to a general `C(D)` subject to `C(D_N)·η(N) → 0`, which the `log log log` schedule
satisfies with enormous room.  That is a shape change to a Prop *we* state, not a new analytic
input.

Ingredients, all elementary:

* `gcd_lcm_dvd_mul_gcd` — `gcd c (lcm a b) ∣ gcd c a · gcd c b`, from `lcm a b ∣ a·b` and
  mathlib's `gcd_mul_dvd_mul_gcd`.
* `gcd_finsetLcm_dvd` — the `Finset` version, by induction.
* `prod_dvd_lcm_mul_gcdProd` — `∏_{i<K} d_i ∣ lcm(d_i) · ∏_{i<K} ∏_{j<i} gcd(d_i,d_j)`, by
  induction on `K` using `gcd_mul_lcm`.  (Exact, no primes, no valuations.)
* `gcd_dvd_sub_of_dvd_shift` — a nonempty joint progression forces `gcd(d_i,d_j) ∣ j − i`.
* `prod_le_lcm_mul_pow` — the conclusion.
-/

open Finset

namespace NormalNumbers

namespace CastingOut

/-- `gcd c (lcm a b) ∣ gcd c a * gcd c b`.  The gcd/lcm distributivity we need, in the only
direction we need it. -/
theorem gcd_lcm_dvd_mul_gcd (a b c : ℕ) : gcd c (lcm a b) ∣ gcd c a * gcd c b := by
  have h1 : lcm a b ∣ a * b := lcm_dvd (dvd_mul_right a b) (dvd_mul_left b a)
  have h2 : gcd c (lcm a b) ∣ gcd c (a * b) :=
    dvd_gcd (gcd_dvd_left _ _) ((gcd_dvd_right _ _).trans h1)
  exact h2.trans (gcd_mul_dvd_mul_gcd c a b)

/-- `gcd c (lcm_{j ∈ s} d j) ∣ ∏_{j ∈ s} gcd c (d j)`. -/
theorem gcd_finsetLcm_dvd (c : ℕ) (d : ℕ → ℕ) (s : Finset ℕ) :
    gcd c (s.lcm d) ∣ ∏ j ∈ s, gcd c (d j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.lcm_insert, Finset.prod_insert ha]
      exact (gcd_lcm_dvd_mul_gcd _ _ _).trans (mul_dvd_mul_left _ ih)

/-- **The exact defect.**  `∏_{i<K} d_i` divides `lcm(d_i)` times the product of all pairwise
gcds.  Elementary induction on `K` via `gcd_mul_lcm`; no prime factorisations. -/
theorem prod_dvd_lcm_mul_gcdProd (d : ℕ → ℕ) (K : ℕ) :
    (∏ i ∈ range K, d i) ∣
      (range K).lcm d * ∏ i ∈ range K, ∏ j ∈ range i, gcd (d i) (d j) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.range_add_one,
        Finset.lcm_insert]
      have hg : gcd (d K) ((range K).lcm d) ∣ ∏ j ∈ range K, gcd (d K) (d j) :=
        gcd_finsetLcm_dvd (d K) d (range K)
      have hML : (range K).lcm d * d K
          = gcd (d K) ((range K).lcm d) * lcm (d K) ((range K).lcm d) := by
        rw [gcd_eq_nat_gcd, lcm_eq_nat_lcm, Nat.gcd_mul_lcm]
        ring
      calc (∏ i ∈ range K, d i) * d K
          ∣ ((range K).lcm d * ∏ i ∈ range K, ∏ j ∈ range i, gcd (d i) (d j)) * d K :=
            mul_dvd_mul_right ih (d K)
        _ = ((range K).lcm d * d K) * ∏ i ∈ range K, ∏ j ∈ range i, gcd (d i) (d j) := by
            ring
        _ = (gcd (d K) ((range K).lcm d) * lcm (d K) ((range K).lcm d))
              * ∏ i ∈ range K, ∏ j ∈ range i, gcd (d i) (d j) := by rw [hML]
        _ ∣ ((∏ j ∈ range K, gcd (d K) (d j)) * lcm (d K) ((range K).lcm d))
              * ∏ i ∈ range K, ∏ j ∈ range i, gcd (d i) (d j) :=
            mul_dvd_mul_right (mul_dvd_mul_right hg _) _
        _ = lcm (d K) ((range K).lcm d)
              * ((∏ i ∈ range K, ∏ j ∈ range i, gcd (d i) (d j))
                * ∏ j ∈ range K, gcd (d K) (d j)) := by ring

/-- **A nonempty joint progression bounds every pairwise gcd.**  If `d_i ∣ n+i+1` and
`d_j ∣ n+j+1` with `j ≤ i`, then `gcd(d_i, d_j) ∣ i − j`. -/
theorem gcd_dvd_sub_of_dvd_shift {di dj n i j : ℕ} (hi : di ∣ n + i + 1)
    (hj : dj ∣ n + j + 1) (hji : j ≤ i) : gcd di dj ∣ i - j := by
  have h1 : gcd di dj ∣ n + i + 1 := (gcd_dvd_left _ _).trans hi
  have h2 : gcd di dj ∣ n + j + 1 := (gcd_dvd_right _ _).trans hj
  have h3 := Nat.dvd_sub h1 h2
  rwa [show n + i + 1 - (n + j + 1) = i - j by omega] at h3

/-- **The gain survives at every `K`.**  If the joint progression `∀ i < K, d_i ∣ n+i+1` is
nonempty (witnessed by `n`) and every `d_i` is positive, then

    ∏_{i<K} d_i ≤ lcm(d_i) · K^{K²} ,

so the `1/∏ d_i` weight that makes the tuple sum absolutely convergent is recovered from the
joint modulus `lcm(d_i)` at the cost of a factor depending only on `K`. -/
theorem prod_le_lcm_mul_pow {K : ℕ} (d : ℕ → ℕ) (hd : ∀ i, i < K → 0 < d i) {n : ℕ}
    (hn : ∀ i, i < K → d i ∣ n + i + 1) :
    (∏ i ∈ range K, d i) ≤ (range K).lcm d * K ^ (K * K) := by
  classical
  -- every pairwise gcd is at most `K`
  have hgcd : ∀ i ∈ range K, ∀ j ∈ range i, gcd (d i) (d j) ≤ K := by
    intro i hi j hj
    rw [Finset.mem_range] at hi
    rw [Finset.mem_range] at hj
    have hdvd := gcd_dvd_sub_of_dvd_shift (hn i hi) (hn j (by omega)) (le_of_lt hj)
    have hpos : 0 < i - j := by omega
    have := Nat.le_of_dvd hpos hdvd
    omega
  -- so the gcd product is at most `K^{K²}`
  have hG : (∏ i ∈ range K, ∏ j ∈ range i, gcd (d i) (d j)) ≤ K ^ (K * K) := by
    have hrow : ∀ i ∈ range K, (∏ j ∈ range i, gcd (d i) (d j)) ≤ K ^ K := by
      intro i hi
      rw [Finset.mem_range] at hi
      calc (∏ j ∈ range i, gcd (d i) (d j)) ≤ ∏ j ∈ range i, K :=
            Finset.prod_le_prod' (fun j hj => hgcd i (Finset.mem_range.2 hi) j hj)
        _ = K ^ i := by rw [Finset.prod_const, Finset.card_range]
        _ ≤ K ^ K := Nat.pow_le_pow_right (by omega) (le_of_lt hi)
    calc (∏ i ∈ range K, ∏ j ∈ range i, gcd (d i) (d j)) ≤ ∏ _i ∈ range K, K ^ K :=
          Finset.prod_le_prod' hrow
      _ = (K ^ K) ^ K := by rw [Finset.prod_const, Finset.card_range]
      _ = K ^ (K * K) := by rw [← pow_mul]
  -- and the divisibility turns into the inequality
  have hdvd := prod_dvd_lcm_mul_gcdProd d K
  have hLpos : 0 < (range K).lcm d := by
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · simp
    · refine Nat.pos_of_ne_zero fun h0 => ?_
      rw [Finset.lcm_eq_zero_iff] at h0
      obtain ⟨i, hi, hzero⟩ := h0
      have hiK : i < K := by simpa using hi
      exact absurd hzero (hd i hiK).ne'
  have hGpos : 0 < ∏ i ∈ range K, ∏ j ∈ range i, gcd (d i) (d j) := by
    refine Finset.prod_pos fun i hi => Finset.prod_pos fun j hj => ?_
    rw [Finset.mem_range] at hi hj
    exact Nat.gcd_pos_of_pos_left _ (hd i hi)
  have h1 : (∏ i ∈ range K, d i)
      ≤ (range K).lcm d * ∏ i ∈ range K, ∏ j ∈ range i, gcd (d i) (d j) :=
    Nat.le_of_dvd (by positivity) hdvd
  exact le_trans h1 (Nat.mul_le_mul_left _ hG)

end CastingOut

end NormalNumbers

-- axiom audit
#print axioms NormalNumbers.CastingOut.gcd_lcm_dvd_mul_gcd
#print axioms NormalNumbers.CastingOut.gcd_finsetLcm_dvd
#print axioms NormalNumbers.CastingOut.prod_dvd_lcm_mul_gcdProd
#print axioms NormalNumbers.CastingOut.gcd_dvd_sub_of_dvd_shift
#print axioms NormalNumbers.CastingOut.prod_le_lcm_mul_pow
