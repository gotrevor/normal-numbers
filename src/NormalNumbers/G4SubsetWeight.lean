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
