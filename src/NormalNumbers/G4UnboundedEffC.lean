/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4UnboundedAvg
import NormalNumbers.G4SchedOmega

/-!
# Campaign B, step B2e: the effective constant in closed form

`effC c P₀ A = max (A + frozenHarm c P₀) (cMax c P₀)` is what the tame §4D pays instead of
`max C 1`.  Both branches are controlled by the single quantity `cMax c P₀ = max_{p∣P₀} c_p`:
the harmonic branch is `cMax` times `∑_{p∣P₀} 1/(p−1) ≤ 1 + log ω(P₀)`
(`G4SchedOmega.sum_inv_sub_one_primeFactors_le_log`).  So the schedule only ever has to beat

    `A + (max_{p∣P₀} c_p) · (1 + log ω(P₀))`,

a quantity that for `c_p = O(polylog p)` is polynomial in `k₄` — see
`DESIGN-2026-09-16-prime-subset.md`.
-/

open Finset
open scoped BigOperators ArithmeticFunction.Omega

namespace NormalNumbers.G4

/-! ### B2e: `effC` in closed form — largest coefficient times `log log` -/

/-- `cMax` from a pointwise bound on the primes dividing `P₀`. -/
lemma cMax_le {c : ℕ → ℕ} {P₀ V : ℕ} (h : ∀ p ∈ P₀.primeFactors, c p ≤ V) :
    cMax c P₀ ≤ (V : ℝ) := by
  unfold cMax
  exact_mod_cast Finset.sup_le h

/-- **The harmonic branch of `effC` is `cMax` times a `log log`.**  `∑_{p∣P₀} c_p/(p−1)
≤ (max_{p∣P₀} c_p) · ∑_{p∣P₀} 1/(p−1) ≤ cMax · (1 + log ω(P₀))`. -/
lemma frozenHarm_le_cMax_mul (c : ℕ → ℕ) (P₀ : ℕ) :
    frozenHarm c P₀ ≤ cMax c P₀ * (1 + Real.log (P₀.primeFactors.card)) := by
  have hstep : frozenHarm c P₀ ≤ cMax c P₀ * ∑ p ∈ P₀.primeFactors, 1 / ((p : ℝ) - 1) := by
    rw [Finset.mul_sum]
    unfold frozenHarm
    refine Finset.sum_le_sum fun p hp => ?_
    have h2 := (Nat.prime_of_mem_primeFactors hp).two_le
    have h2' : (2 : ℝ) ≤ p := by exact_mod_cast h2
    have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hle : (c p : ℝ) ≤ cMax c P₀ := by
      unfold cMax
      exact_mod_cast Finset.le_sup (f := c) hp
    rw [mul_one_div]
    gcongr
  refine hstep.trans (mul_le_mul_of_nonneg_left ?_ (cMax_nonneg c P₀))
  exact sum_inv_sub_one_primeFactors_le_log P₀

/-- **`effC` in closed form.**  Everything the schedule has to beat is `A` plus the largest
coefficient on a prime dividing `P₀`, times a `log log`. -/
lemma effC_le_closed {c : ℕ → ℕ} {A : ℝ} (hA : 1 ≤ A) (P₀ : ℕ) :
    effC c P₀ A ≤ A + cMax c P₀ * (1 + Real.log (P₀.primeFactors.card)) := by
  have hh := frozenHarm_le_cMax_mul c P₀
  have hc0 := cMax_nonneg c P₀
  have hlog : (0 : ℝ) ≤ Real.log (P₀.primeFactors.card) := Real.log_natCast_nonneg _
  refine max_le (by linarith) ?_
  nlinarith


/-! ### The primes dividing the progression modulus

`P₀ = (∏_α d_α²) · freezeQ` and `freezeQ = (∏_{q ≤ 2T} q)·∏_{i≠i'} |ρ_i − ρ_{i'}|`, so every
prime factor of `P₀` is bounded by `max(Dm, 2T, ρmax)` — a *schedule* quantity, exponentially
smaller than `P₀` itself.  This is what turns `cMax c P₀` into something the budget can pay. -/

theorem prime_le_of_dvd_P₀ (G : GridParams) {p : ℕ} (hp : p.Prime) (hdvd : p ∣ G.P₀)
    {Dm ρmax : ℕ} (hDm : ∀ α, G.d α ≤ Dm) (hρ : ∀ i : G.Idx, G.ρ i ≤ ρmax) :
    p ≤ max (max Dm (2 * Fintype.card G.Idx)) ρmax := by
  classical
  have hP : G.P₀ = G.Mprod * G.freezeQ := rfl
  rw [hP] at hdvd
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with hM | hF
  · obtain ⟨α, -, hα⟩ := hp.prime.exists_mem_finset_dvd (by
      simpa [GridParams.Mprod] using hM)
    have hd : p ∣ G.d α := hp.dvd_of_dvd_pow hα
    have : p ≤ G.d α := Nat.le_of_dvd (G.d_pos α) hd
    exact le_trans (le_trans this (hDm α)) (le_trans (le_max_left _ _) (le_max_left _ _))
  · rw [GridParams.freezeQ] at hF
    rcases (Nat.Prime.dvd_mul hp).1 hF with hA | hB
    · obtain ⟨q, hq, hqd⟩ := hp.prime.exists_mem_finset_dvd hA
      have hq' := Nat.mem_primesBelow.1 hq
      have : p = q := ((Nat.prime_dvd_prime_iff_eq hp hq'.2).1 hqd)
      subst this
      exact le_trans (by omega : p ≤ 2 * Fintype.card G.Idx)
        (le_trans (le_max_right _ _) (le_max_left _ _))
    · obtain ⟨i, -, hi⟩ := hp.prime.exists_mem_finset_dvd hB
      obtain ⟨i', -, hii⟩ := hp.prime.exists_mem_finset_dvd hi
      by_cases h : i = i'
      · rw [if_pos h] at hii
        exact absurd (Nat.le_of_dvd Nat.one_pos hii) (by have := hp.two_le; omega)
      · rw [if_neg h] at hii
        have hpos : 0 < Nat.dist (G.ρ i) (G.ρ i') :=
          Nat.dist_pos_of_ne (fun h' => h (G.ρ_injective h'))
        have hle : p ≤ Nat.dist (G.ρ i) (G.ρ i') := Nat.le_of_dvd hpos hii
        have hd : Nat.dist (G.ρ i) (G.ρ i') ≤ max (G.ρ i) (G.ρ i') := by
          unfold Nat.dist; omega
        have : max (G.ρ i) (G.ρ i') ≤ ρmax := max_le (hρ i) (hρ i')
        exact le_trans (le_trans hle (le_trans hd this)) (le_max_right _ _)

/-- **`cMax` at the schedule's modulus**, for a coefficient vector monotone in `p`. -/
theorem cMax_le_of_mono (G : GridParams) {c : ℕ → ℕ} (hmono : Monotone c)
    {Dm ρmax : ℕ} (hDm : ∀ α, G.d α ≤ Dm) (hρ : ∀ i : G.Idx, G.ρ i ≤ ρmax) :
    cMax c G.P₀ ≤ (c (max (max Dm (2 * Fintype.card G.Idx)) ρmax) : ℝ) := by
  refine cMax_le (fun p hp => hmono ?_)
  exact prime_le_of_dvd_P₀ G (Nat.prime_of_mem_primeFactors hp)
    (Nat.dvd_of_mem_primeFactors hp) hDm hρ

/-- `ω(P₀)` is at most the prime bound: all prime factors sit in `[2, M]`. -/
theorem card_primeFactors_P₀_le (G : GridParams) {Dm ρmax : ℕ} (hDm : ∀ α, G.d α ≤ Dm)
    (hρ : ∀ i : G.Idx, G.ρ i ≤ ρmax) :
    G.P₀.primeFactors.card ≤ max (max Dm (2 * Fintype.card G.Idx)) ρmax + 1 := by
  classical
  set M := max (max Dm (2 * Fintype.card G.Idx)) ρmax with hM
  have hsub : G.P₀.primeFactors ⊆ Finset.range (M + 1) := by
    intro p hp
    exact Finset.mem_range.2 (Nat.lt_succ_of_le (prime_le_of_dvd_P₀ G
      (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp) hDm hρ))
  calc G.P₀.primeFactors.card ≤ (Finset.range (M + 1)).card := Finset.card_le_card hsub
    _ = M + 1 := Finset.card_range _

/-- **`effC` at the schedule's modulus, in schedule quantities only.** -/
theorem effC_le_sched (G : GridParams) {c : ℕ → ℕ} (hmono : Monotone c) {A : ℝ} (hA : 1 ≤ A)
    {Dm ρmax : ℕ} (hDm : ∀ α, G.d α ≤ Dm) (hρ : ∀ i : G.Idx, G.ρ i ≤ ρmax) :
    effC c G.P₀ A
      ≤ A + (c (max (max Dm (2 * Fintype.card G.Idx)) ρmax) : ℝ)
          * (1 + Real.log ((max (max Dm (2 * Fintype.card G.Idx)) ρmax : ℕ) + 1)) := by
  set M := max (max Dm (2 * Fintype.card G.Idx)) ρmax with hM
  refine (effC_le_closed (c := c) hA G.P₀).trans ?_
  have h1 := cMax_le_of_mono G hmono hDm hρ
  have h2 : Real.log (G.P₀.primeFactors.card) ≤ Real.log ((M : ℝ) + 1) := by
    have hcard := card_primeFactors_P₀_le G hDm hρ
    have : ((G.P₀.primeFactors.card : ℕ) : ℝ) ≤ (M : ℝ) + 1 := by exact_mod_cast hcard
    rcases Nat.eq_zero_or_pos G.P₀.primeFactors.card with h0 | hpos
    · rw [h0]
      simp only [Nat.cast_zero, Real.log_zero]
      have : (0:ℝ) ≤ (M:ℝ) := Nat.cast_nonneg _
      exact Real.log_nonneg (by linarith)
    · exact Real.log_le_log (by exact_mod_cast hpos) this
  have hlog0 : (0 : ℝ) ≤ Real.log (G.P₀.primeFactors.card) := Real.log_natCast_nonneg _
  have hc0 := cMax_nonneg c G.P₀
  have hcM : (0 : ℝ) ≤ (c M : ℝ) := Nat.cast_nonneg _
  push_cast
  nlinarith [Real.log_natCast_nonneg (M + 1)]

/-! ### The doubly-logarithmic class: `cMax` is polynomial in `K`

`DESIGN-2026-09-16-prime-subset.md` records why this is the class the schedule can pay for:
every prime dividing `P₀` is at most `max(Dm, 2T, ρmax)`, and that is of the size of
`gridDm ≤ 2^{2·2^{21K²}}` (`Sched.gridDm_le_two_pow`).  A coefficient vector bounded by
`⌊log₂ log₂ p⌋` therefore has `cMax ≤ V` whenever the prime bound is at most `2^{2^V}` — i.e.
`V ≈ 21K²`, polynomial, while the junk budget allows `2^{Θ(K)}`. -/

/-- **`cMax` for a doubly-logarithmic coefficient vector.** -/
theorem cMax_le_of_logLog (G : GridParams) {c : ℕ → ℕ}
    (hc : ∀ x, c x ≤ Nat.log 2 (Nat.log 2 x)) {Dm ρmax V : ℕ}
    (hDm : ∀ α, G.d α ≤ Dm) (hρ : ∀ i : G.Idx, G.ρ i ≤ ρmax)
    (hM : max (max Dm (2 * Fintype.card G.Idx)) ρmax ≤ 2 ^ 2 ^ V) :
    cMax c G.P₀ ≤ (V : ℝ) := by
  refine cMax_le (fun p hp => ?_)
  have hple : p ≤ 2 ^ 2 ^ V :=
    le_trans (prime_le_of_dvd_P₀ G (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp) hDm hρ) hM
  calc c p ≤ Nat.log 2 (Nat.log 2 p) := hc p
    _ ≤ Nat.log 2 (Nat.log 2 (2 ^ 2 ^ V)) :=
        Nat.log_mono_right (Nat.log_mono_right hple)
    _ = V := by rw [Nat.log_pow (by norm_num), Nat.log_pow (by norm_num)]

/-- **`effC` for a doubly-logarithmic `c`**, in the two quantities the schedule already
bounds: the prime-size exponent `V` and `log ω(P₀)`. -/
theorem effC_le_of_logLog (G : GridParams) {c : ℕ → ℕ}
    (hc : ∀ x, c x ≤ Nat.log 2 (Nat.log 2 x)) {A : ℝ} (hA : 1 ≤ A) {Dm ρmax V : ℕ}
    (hDm : ∀ α, G.d α ≤ Dm) (hρ : ∀ i : G.Idx, G.ρ i ≤ ρmax)
    (hM : max (max Dm (2 * Fintype.card G.Idx)) ρmax ≤ 2 ^ 2 ^ V) {L : ℝ}
    (hL : Real.log (G.P₀.primeFactors.card) ≤ L) (hL0 : 0 ≤ L) :
    effC c G.P₀ A ≤ A + (V : ℝ) * (1 + L) := by
  refine (effC_le_closed (c := c) hA G.P₀).trans ?_
  have h1 := cMax_le_of_logLog G hc hDm hρ hM
  have hc0 := cMax_nonneg c G.P₀
  have hlog0 : (0 : ℝ) ≤ Real.log (G.P₀.primeFactors.card) := Real.log_natCast_nonneg _
  nlinarith

end NormalNumbers.G4
