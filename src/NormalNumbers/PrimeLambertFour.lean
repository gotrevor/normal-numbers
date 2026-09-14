/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PrimeLambertDefs
import NormalNumbers.Disjunctive

/-!
# The base-four prime Lambert number `G₄`: frozen endpoint

The G4 disjunctivity campaign (`KICKOFF-2026-09-14-g4-disjunctivity.md`) targets the candidate
theorem that

  `G₄ = ∑_{p prime} 1/(4^p − 1) = ∑_{n ≥ 1} ω(n)/4^n`

is disjunctive in base `4`, hence in base `2`.  This module pins the endpoint:

* `primeLambertAtBase b = ∑' n, ω(n)/bⁿ` and `primeLambertFour = primeLambertAtBase 4`.
  ⚠️ `PrimeLambert.primeLambert` is the **base-two** number and is left untouched
  (`primeLambertAtBase_two` records the agreement).
* summability at every base `b ≥ 2` (`summable_omegaR_div_pow`);
* the prime-sum form `primeSumAtBase b = ∑'_{p prime} 1/(bᵖ − 1)` and the identity
  `primeSumAtBase b = primeLambertAtBase b` (`primeSumAtBase_eq_primeLambertAtBase`);
* the headline Props `G4DisjunctiveFour` / `G4DisjunctiveTwo`, and the *proved* reduction
  `isDisjunctive_two_of_four` through the existing `isDisjunctive_pow_iff` (`b = 2`, `k = 2`).

The disjunctivity statements themselves are **not** proved here; `G4Wiring.lean` reduces them to
the named analytic inputs A–E of the candidate proof.
-/

open Filter Topology
open scoped BigOperators

namespace NormalNumbers.PrimeLambert

/-- The prime Lambert number at integer base `b`: `∑_{n ≥ 0} ω(n) / bⁿ` (the `n = 0` term is `0`). -/
noncomputable def primeLambertAtBase (b : ℕ) : ℝ := ∑' n : ℕ, omegaR n / (b : ℝ) ^ n

/-- **`G₄`**, the base-four prime Lambert number `∑ ω(n)/4ⁿ`. -/
noncomputable def primeLambertFour : ℝ := primeLambertAtBase 4

/-- `primeLambertAtBase 2` is the existing base-two constant. -/
theorem primeLambertAtBase_two : primeLambertAtBase 2 = primeLambert := by
  simp [primeLambertAtBase, primeLambert]

/-- Summability of `ω(n)/bⁿ` for every base `b ≥ 2`. -/
lemma summable_omegaR_div_pow {b : ℕ} (hb : 2 ≤ b) :
    Summable (fun n : ℕ => omegaR n / (b : ℝ) ^ n) := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := (1 / (b : ℝ))) (by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [div_lt_one (by linarith)]; linarith)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) h
  · have := omegaR_nonneg n; positivity
  · rw [div_eq_mul_inv, ← inv_pow, pow_one, one_div]
    gcongr
    exact omegaR_le n

/-- The prime-sum form `∑_{p prime} 1/(bᵖ − 1)`. -/
noncomputable def primeSumAtBase (b : ℕ) : ℝ := ∑' p : Nat.Primes, 1 / ((b : ℝ) ^ (p : ℕ) - 1)

/-! ### The series identity `∑_{p prime} 1/(bᵖ − 1) = ∑_n ω(n)/bⁿ`

Both sides are the sum of `b^{-pm}` over pairs `(p, m)`, `p` prime, `m ≥ 1`: summing over `m`
first gives the geometric series `1/(bᵖ−1)`, summing over the fibre `pm = n` counts the distinct
prime divisors of `n`. -/

/-- The double-series term `b^{-p(m+1)}` for `p` prime (and `0` otherwise), indexed by `(p, m)`. -/
noncomputable def primePowTerm (b : ℕ) (x : ℕ × ℕ) : ℝ :=
  if x.1.Prime then 1 / (b : ℝ) ^ (x.1 * (x.2 + 1)) else 0

lemma primePowTerm_nonneg (b : ℕ) (x : ℕ × ℕ) : 0 ≤ primePowTerm b x := by
  unfold primePowTerm; split_ifs <;> positivity

lemma summable_primePowTerm {b : ℕ} (hb : 2 ≤ b) : Summable (primePowTerm b) := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hr0 : (0 : ℝ) ≤ 1 / b := by positivity
  have hr1 : (1 : ℝ) / b < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hg := summable_geometric_of_lt_one hr0 hr1
  refine Summable.of_nonneg_of_le (primePowTerm_nonneg b) (fun x => ?_) (hg.mul_of_nonneg hg
    (fun _ => pow_nonneg hr0 _) (fun _ => pow_nonneg hr0 _))
  unfold primePowTerm
  split_ifs with hp
  · rw [← pow_add, one_div_pow]
    refine one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by linarith) ?_)
    have := hp.two_le
    nlinarith
  · exact mul_nonneg (pow_nonneg hr0 _) (pow_nonneg hr0 _)

/-- Summing over `m` first: the inner geometric series. -/
lemma tsum_primePowTerm_snd {b : ℕ} (hb : 2 ≤ b) (p : ℕ) :
    ∑' m : ℕ, primePowTerm b (p, m) = if p.Prime then 1 / ((b : ℝ) ^ p - 1) else 0 := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  unfold primePowTerm
  simp only
  split_ifs with hp
  · have hbp : (1 : ℝ) < (b : ℝ) ^ p := one_lt_pow₀ (by linarith) hp.ne_zero
    set r : ℝ := 1 / (b : ℝ) ^ p with hr
    have hr0 : 0 ≤ r := by positivity
    have hr1 : r < 1 := by rw [hr, div_lt_one (by linarith)]; exact hbp
    have : (fun m : ℕ => 1 / (b : ℝ) ^ (p * (m + 1))) = fun m => r * r ^ m := by
      funext m
      rw [hr, pow_mul, pow_succ', ← one_div_mul_one_div, one_div_pow]
    rw [this, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, hr]
    have hne : (b : ℝ) ^ p - 1 ≠ 0 := by linarith
    field_simp
  · simp

/-- The map `(p, m) ↦ p (m + 1)`. -/
def primePowIndex (x : ℕ × ℕ) : ℕ := x.1 * (x.2 + 1)

/-- Summing over the fibre `p(m+1) = n` counts the distinct prime divisors of `n`. -/
lemma tsum_primePowTerm_fiber {b : ℕ} (hb : 2 ≤ b) (n : ℕ) :
    ∑' x : (primePowIndex ⁻¹' {n} : Set (ℕ × ℕ)), primePowTerm b x = omegaR n / (b : ℝ) ^ n := by
  classical
  rw [tsum_subtype]
  set s : Finset (ℕ × ℕ) := Finset.range (n + 1) ×ˢ Finset.range (n + 1) with hs
  have hsupp : ∀ x ∉ s, (primePowIndex ⁻¹' {n}).indicator (primePowTerm b) x = 0 := by
    intro x hx
    rw [Set.indicator_apply_eq_zero]
    intro hxn
    simp only [Set.mem_preimage, Set.mem_singleton_iff, primePowIndex] at hxn
    unfold primePowTerm
    rw [if_neg]
    intro hp
    apply hx
    rw [hs, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    have h2 := hp.two_le
    constructor <;> nlinarith
  rw [tsum_eq_sum hsupp]
  have hfilter : ∀ x ∈ s, (primePowIndex ⁻¹' {n}).indicator (primePowTerm b) x
      = if (primePowIndex x = n ∧ x.1.Prime) then 1 / (b : ℝ) ^ n else 0 := by
    intro x _
    rw [Set.indicator_apply]
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    unfold primePowTerm
    by_cases hxn : primePowIndex x = n
    · rw [if_pos hxn]
      by_cases hp : x.1.Prime
      · rw [if_pos hp, if_pos ⟨hxn, hp⟩]
        unfold primePowIndex at hxn
        rw [hxn]
      · rw [if_neg hp, if_neg (fun h => hp h.2)]
    · rw [if_neg hxn, if_neg (fun h => hxn h.1)]
  rw [Finset.sum_congr rfl hfilter, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    omegaR_eq, div_eq_mul_one_div (n.primeFactors.card : ℝ)]
  congr 1
  norm_cast
  -- the fibre is in bijection with the prime factors of `n`
  refine Finset.card_bij' (fun x _ => x.1) (fun p _ => (p, n / p - 1)) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter] at hx
    obtain ⟨_, hxn, hp⟩ := hx
    rw [Nat.mem_primeFactors]
    refine ⟨hp, ⟨x.2 + 1, hxn.symm⟩, ?_⟩
    rw [← hxn]
    exact Nat.mul_ne_zero hp.ne_zero (Nat.succ_ne_zero _)
  · intro p hp
    rw [Nat.mem_primeFactors] at hp
    obtain ⟨hp, hpn, hn0⟩ := hp
    obtain ⟨k, rfl⟩ := hpn
    have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hn0)
    have hdiv : p * k / p = k := Nat.mul_div_cancel_left k hp.pos
    simp only [Finset.mem_filter, hs, Finset.mem_product, Finset.mem_range, primePowIndex, hdiv]
    have h2 := hp.two_le
    have hk' : k ≤ p * k := Nat.le_mul_of_pos_left k hp.pos
    refine ⟨⟨by nlinarith, by omega⟩, ?_, hp⟩
    rw [Nat.sub_add_cancel hk]
  · intro x hx
    simp only [Finset.mem_filter] at hx
    obtain ⟨_, hxn, hp⟩ := hx
    unfold primePowIndex at hxn
    rw [← hxn, Nat.mul_div_cancel_left _ hp.pos]
    simp
  · intro p _
    rfl

/-- **The series identity** `∑_{p prime} 1/(bᵖ − 1) = ∑_n ω(n)/bⁿ`, for every base `b ≥ 2`. -/
theorem primeSumAtBase_eq_primeLambertAtBase {b : ℕ} (hb : 2 ≤ b) :
    primeSumAtBase b = primeLambertAtBase b := by
  classical
  have hsum := summable_primePowTerm hb
  -- prime side
  have h1 : primeSumAtBase b = ∑' x : ℕ × ℕ, primePowTerm b x := by
    rw [hsum.tsum_prod' (fun p => hsum.prod_factor p)]
    simp_rw [tsum_primePowTerm_snd hb]
    unfold primeSumAtBase
    rw [← tsum_subtype_eq_of_support_subset (s := {p : ℕ | p.Prime})]
    · have hst : ∑' p : {p : ℕ | p.Prime}, (if (p : ℕ).Prime then 1 / ((b : ℝ) ^ (p : ℕ) - 1) else 0)
          = ∑' p : Nat.Primes, 1 / ((b : ℝ) ^ (p : ℕ) - 1) :=
        tsum_congr fun p => if_pos p.2
      exact hst.symm
    · intro p hp
      simp only [Function.mem_support] at hp
      by_contra h
      exact hp (if_neg h)
  -- omega side
  have h2 : ∑' x : ℕ × ℕ, primePowTerm b x = primeLambertAtBase b := by
    have := (hsum.hasSum.tsum_fiberwise primePowIndex).tsum_eq
    rw [← this]
    unfold primeLambertAtBase
    exact tsum_congr (tsum_primePowTerm_fiber hb)
  rw [h1, h2]

/-- `G₄` in its prime-sum form: `∑_{p prime} 1/(4ᵖ − 1) = ∑ ω(n)/4ⁿ`. -/
theorem primeSumAtBase_four : primeSumAtBase 4 = primeLambertFour :=
  primeSumAtBase_eq_primeLambertAtBase (by norm_num)

/-- The headline Prop of the campaign: `G₄` is disjunctive in base four. -/
def G4DisjunctiveFour : Prop := IsDisjunctive 4 primeLambertFour

/-- The binary corollary: `G₄` is disjunctive in base two. -/
def G4DisjunctiveTwo : Prop := IsDisjunctive 2 primeLambertFour

/-- Base four to base two, through the existing base-power dictionary (`k = 2`). -/
theorem isDisjunctive_two_of_four (h : IsDisjunctive 4 primeLambertFour) :
    IsDisjunctive 2 primeLambertFour := by
  have := isDisjunctive_pow_iff 2 2 (by norm_num) (by norm_num) primeLambertFour
  norm_num at this
  exact this.2 h

theorem G4DisjunctiveTwo_of_four (h : G4DisjunctiveFour) : G4DisjunctiveTwo :=
  isDisjunctive_two_of_four h

end NormalNumbers.PrimeLambert
