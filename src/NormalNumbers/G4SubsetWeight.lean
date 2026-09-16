/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PrimeLambertFour

/-!
# Campaign A, step A4: the subset weight `ω_S` and its exact transport identity

For a set `S` of primes, `ω_S(m) = #{p ∈ S : p ∣ m}` and

    `c_S(b) = ∑_n ω_S(n)/bⁿ = ∑_{p ∈ S} 1/(b^p − 1)`.

Everything the disjunctivity proof needs of `ω` at the *arithmetic* level is the exact transport
identity `ω(dm) + overlap(d,m) = ω(d) + ω(m)` together with the periodicity of `overlap` modulo
`rad d`.  Both hold verbatim for `ω_S` — this file proves them — because restricting to `S`
commutes with the union of prime supports (`Finset.filter_union`).  `S = univ` recovers `ω`
(`omegaSN_univ`), the sanity instance the campaign requires.

The analytic side (local contraction restricted to `S`) is where the Mertens rate enters, and is
handled in `G4SubsetSchedule` / `G4MertensAP`.
-/

open Finset

namespace NormalNumbers.PrimeLambert

variable (S : ℕ → Prop) [DecidablePred S]

/-- `ω_S(m) = #{p ∈ S : p ∣ m}`, as a natural number (so the digits are integers). -/
def omegaSN (m : ℕ) : ℕ := (m.primeFactors.filter S).card

/-- `ω_S` as a real. -/
noncomputable def omegaS (m : ℕ) : ℝ := (omegaSN S m : ℝ)

/-- `#{p ∈ S : p ∣ d and p ∣ m}`, the `S`-restricted overlap. -/
def overlapS (d m : ℕ) : ℕ := ((d.primeFactors.filter S).filter (fun p => p ∣ m)).card

/-- The prime-subset Lambert series `c_S(b) = ∑_n ω_S(n)/bⁿ`. -/
noncomputable def subsetLambert (b : ℕ) : ℝ := ∑' n : ℕ, omegaS S n / (b : ℝ) ^ n

variable {S}

lemma omegaS_nonneg (m : ℕ) : 0 ≤ omegaS S m := by
  rw [omegaS]; positivity

/-- `ω_S ≤ ω` pointwise. -/
lemma omegaS_le_omegaR (m : ℕ) : omegaS S m ≤ omegaR m := by
  rw [omegaS, omegaR, cardDistinctFactors_eq_card_primeFactors]
  exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

lemma summable_omegaS_div_pow {b : ℕ} (hb : 2 ≤ b) :
    Summable (fun n : ℕ => omegaS S n / (b : ℝ) ^ n) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (summable_omegaR_div_pow hb)
  · have hb0 : (0 : ℝ) < b := by
      have : (2 : ℝ) ≤ b := by exact_mod_cast hb
      linarith
    have := omegaS_nonneg (S := S) n
    positivity
  · have hb0 : (0 : ℝ) < (b : ℝ) ^ n := by
      have : (2 : ℝ) ≤ b := by exact_mod_cast hb
      positivity
    exact div_le_div_of_nonneg_right (omegaS_le_omegaR n) hb0.le

/-! ### The exact transport identity -/

/-- The `S`-restricted version of `primeFactors_inter`. -/
lemma primeFactorsS_inter (d m : ℕ) (hm : m ≠ 0) :
    (d.primeFactors.filter S) ∩ (m.primeFactors.filter S)
      = (d.primeFactors.filter S).filter (fun p => p ∣ m) := by
  ext p
  simp only [Finset.mem_inter, Finset.mem_filter, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨h1, hs⟩, h2, -⟩
    exact ⟨⟨h1, hs⟩, h2.2.1⟩
  · rintro ⟨⟨h1, hs⟩, hdvd⟩
    exact ⟨⟨h1, hs⟩, ⟨h1.1, hdvd, hm⟩, hs⟩

/-- **The exact `ω_S`-transport identity**: `ω_S(d·m) + overlap_S(d,m) = ω_S(m) + ω_S(d)`. -/
theorem omegaSN_mul_eq (d m : ℕ) (hd : d ≠ 0) (hm : m ≠ 0) :
    omegaSN S (d * m) + overlapS S d m = omegaSN S m + omegaSN S d := by
  unfold omegaSN overlapS
  rw [Nat.primeFactors_mul hd hm, Finset.filter_union, ← primeFactorsS_inter d m hm,
    Finset.card_union_add_card_inter, add_comm]

/-- The real form, matching `omegaR_mul_eq`. -/
theorem omegaS_mul_eq (d m : ℕ) (hd : d ≠ 0) (hm : m ≠ 0) :
    omegaS S (d * m) = omegaS S m + omegaS S d - overlapS S d m := by
  have h := omegaSN_mul_eq (S := S) d m hd hm
  have h' : ((omegaSN S (d * m) + overlapS S d m : ℕ) : ℝ)
      = ((omegaSN S m + omegaSN S d : ℕ) : ℝ) := by rw [h]
  simp only [omegaS]
  push_cast at h'
  linarith

/-- The `S`-overlap depends only on `m` modulo the primes dividing `d`. -/
theorem overlapS_congr (d m m' : ℕ) (h : ∀ p ∈ d.primeFactors, m ≡ m' [MOD p]) :
    overlapS S d m = overlapS S d m' := by
  unfold overlapS
  congr 1
  refine Finset.filter_congr (fun p hp => ?_)
  have hp' : p ∈ d.primeFactors := (Finset.mem_filter.1 hp).1
  have := h p hp'
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, this]

lemma overlapS_le (d m : ℕ) : overlapS S d m ≤ overlap d m :=
  Finset.card_le_card (by
    intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1.1, hp.2⟩)

/-! ### The closed form `c_S(b) = ∑_{p ∈ S} 1/(b^p − 1)` -/

/-- The double family `[p prime ∈ S, p ∣ n, n ≠ 0]·b^{−n}` whose two iterated sums are the two
descriptions of `c_S(b)`. -/
private noncomputable def cell (S : ℕ → Prop) [DecidablePred S] (b : ℕ) (x : ℕ × ℕ) : ℝ :=
  if x.2.Prime ∧ S x.2 ∧ x.2 ∣ x.1 ∧ x.1 ≠ 0 then ((b : ℝ) ^ x.1)⁻¹ else 0

/-- **The closed form.**  `∑_n ω_S(n)/bⁿ = ∑_{p ∈ S} 1/(b^p − 1)`, the description of `c_S` in
the campaign statement. -/
theorem subsetLambert_eq_tsum_inv {b : ℕ} (hb : 2 ≤ b) :
    subsetLambert S b
      = ∑' p : ℕ, (if p.Prime ∧ S p then 1 / ((b : ℝ) ^ p - 1) else 0) := by
  classical
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  set f : ℕ → ℕ → ℝ := fun n p =>
    if p.Prime ∧ S p ∧ p ∣ n ∧ n ≠ 0 then ((b : ℝ) ^ n)⁻¹ else 0 with hf
  have hf0 : ∀ n p, 0 ≤ f n p := by
    intro n p
    rw [hf]
    simp only
    split_ifs
    · positivity
    · exact le_rfl
  -- rows: fixed `n`
  have hrowsupp : ∀ n : ℕ, ∀ p ∉ n.primeFactors.filter S, f n p = 0 := by
    intro n p hp
    have hc : ¬ (p.Prime ∧ S p ∧ p ∣ n ∧ n ≠ 0) := by
      intro hc
      exact hp (Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hc.1, hc.2.2.1, hc.2.2.2⟩, hc.2.1⟩)
    simp only [hf]
    exact if_neg hc
  have hrowS : ∀ n, Summable (f n) := fun n => summable_of_ne_finset_zero (hrowsupp n)
  have hrow : ∀ n, ∑' p, f n p = omegaS S n / (b : ℝ) ^ n := by
    intro n
    rw [tsum_eq_sum (hrowsupp n)]
    have hval : ∀ p ∈ n.primeFactors.filter S, f n p = ((b : ℝ) ^ n)⁻¹ := by
      intro p hp
      simp only [Finset.mem_filter, Nat.mem_primeFactors] at hp
      simp only [hf]
      exact if_pos ⟨hp.1.1, hp.2, hp.1.2.1, hp.1.2.2⟩
    rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
    rw [omegaS, omegaSN, div_eq_mul_inv]
  -- columns: fixed `p`
  have hcolS : ∀ p, Summable (fun n => f n p) := by
    intro p
    refine Summable.of_nonneg_of_le (fun n => hf0 n p) (fun n => ?_)
      (summable_geometric_of_lt_one (r := (b : ℝ)⁻¹) (by positivity) (by
        rw [inv_lt_one_iff₀]; right; linarith))
    simp only [hf]
    split_ifs
    · rw [← inv_pow]
    · positivity
  have hcol : ∀ p : ℕ, ∑' n, f n p = if p.Prime ∧ S p then 1 / ((b : ℝ) ^ p - 1) else 0 := by
    intro p
    by_cases hp : p.Prime ∧ S p
    · rw [if_pos hp]
      have hp2 : 2 ≤ p := hp.1.two_le
      have hbp : (1 : ℝ) < (b : ℝ) ^ p := one_lt_pow₀ (by linarith) (by omega)
      set r : ℝ := ((b : ℝ) ^ p)⁻¹ with hrdef
      have hr0 : 0 < r := by rw [hrdef]; positivity
      have hr1 : r < 1 := by
        rw [hrdef, inv_lt_one_iff₀]
        right; exact hbp
      have hgeo0 : HasSum (fun k : ℕ => r ^ k) (1 - r)⁻¹ :=
        hasSum_geometric_of_lt_one hr0.le hr1
      have hval : r * (1 - r)⁻¹ = 1 / ((b : ℝ) ^ p - 1) := by
        have hne : ((b : ℝ) ^ p - 1) ≠ 0 := by intro hc; rw [sub_eq_zero] at hc; linarith
        rw [hrdef]
        field_simp
      have hgeo : HasSum (fun k : ℕ => r ^ (k + 1)) (1 / ((b : ℝ) ^ p - 1)) := by
        rw [← hval]
        exact (hgeo0.mul_left r).congr_fun (fun k => by rw [pow_succ]; ring)
      have hinj : Function.Injective (fun k : ℕ => p * (k + 1)) := by
        intro k1 k2 hk
        simp only at hk
        have : k1 + 1 = k2 + 1 := Nat.eq_of_mul_eq_mul_left (by omega) hk
        omega
      have hzero : ∀ n ∉ Set.range (fun k : ℕ => p * (k + 1)), f n p = 0 := by
        intro n hn
        have hc : ¬ (p.Prime ∧ S p ∧ p ∣ n ∧ n ≠ 0) := by
          rintro ⟨-, -, hdvd, hn0⟩
          obtain ⟨m, rfl⟩ := hdvd
          have hm : m ≠ 0 := by rintro rfl; exact hn0 (by ring)
          exact hn ⟨m - 1, by simp only; congr 1; omega⟩
        simp only [hf]
        exact if_neg hc
      have hcomp : ∀ k : ℕ, f (p * (k + 1)) p = r ^ (k + 1) := by
        intro k
        have hne : p * (k + 1) ≠ 0 := Nat.mul_ne_zero (by omega) (Nat.succ_ne_zero k)
        simp only [hf]
        rw [if_pos ⟨hp.1, hp.2, Dvd.intro _ rfl, hne⟩, hrdef, inv_pow, ← pow_mul]
      have hHS : HasSum (fun n => f n p) (1 / ((b : ℝ) ^ p - 1)) :=
        (Function.Injective.hasSum_iff (f := fun n => f n p) hinj hzero).1
          (hgeo.congr_fun (fun k => hcomp k))
      exact hHS.tsum_eq
    · rw [if_neg hp]
      have hz : ∀ n, f n p = 0 := by
        intro n
        have hc : ¬ (p.Prime ∧ S p ∧ p ∣ n ∧ n ≠ 0) := by
          rintro ⟨h1, h2, -, -⟩
          exact hp ⟨h1, h2⟩
        simp only [hf]
        exact if_neg hc
      simp [hz]
  -- the swap
  have huncurry : Summable (Function.uncurry f) := by
    have huc : Function.uncurry f = fun x : ℕ × ℕ => f x.1 x.2 := rfl
    rw [huc, summable_prod_of_nonneg (fun x => hf0 x.1 x.2)]
    refine ⟨fun n => hrowS n, ?_⟩
    refine Summable.congr (summable_omegaS_div_pow (S := S) hb) (fun n => (hrow n).symm)
  calc subsetLambert S b = ∑' n, ∑' p, f n p := by
        rw [subsetLambert]
        exact tsum_congr fun n => (hrow n).symm
    _ = ∑' p, ∑' n, f n p := (huncurry.tsum_comm' hrowS hcolS).symm
    _ = ∑' p : ℕ, (if p.Prime ∧ S p then 1 / ((b : ℝ) ^ p - 1) else 0) := tsum_congr hcol

/-! ### The sanity instance `S = univ` -/

/-- With `S` everything, `ω_S` is `ω` on the nose. -/
@[simp] theorem omegaSN_univ (m : ℕ) :
    omegaSN (fun _ => True) m = ArithmeticFunction.cardDistinctFactors m := by
  have hfil : m.primeFactors.filter (fun _ => True) = m.primeFactors := by
    apply Finset.filter_true_of_mem
    intro _ _
    trivial
  rw [omegaSN, hfil, cardDistinctFactors_eq_card_primeFactors]

@[simp] theorem omegaS_univ (m : ℕ) : omegaS (fun _ => True) m = omegaR m := by
  rw [omegaS, omegaSN_univ, omegaR]

@[simp] theorem subsetLambert_univ (b : ℕ) :
    subsetLambert (fun _ => True) b = primeLambertAtBase b := by
  rw [subsetLambert, primeLambertAtBase]
  exact tsum_congr fun n => by rw [omegaS_univ]

end NormalNumbers.PrimeLambert
