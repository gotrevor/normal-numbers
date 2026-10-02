/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.JointLambertRescaledTail

/-!
# Joint Lambert disjunctivity, unconditionally

The frozen headlines `JointLambertDisjunctivity` and `JointWords {2,4}`, with **no**
hypotheses.  The statements are the ones frozen in `JointLambertStatement.lean`; only the
route to them is new.

`JointLambertDisjunctivity.jointWords_of_inputs` stays exactly as it was, conditional on
`AGP` and `PrimeIntervalSupply`; this module re-runs the identical assembly against the
unconditional tail theorem `exists_joint_small_tail_all_bases_rescaled`.  The only change
anywhere in the argument is the prime-search schedule: `X = 2^(4k¹²)` in place of
`X = 2^(4k⁴)`, which moves the CRT modulus `B ≤ 2^(k⁴)` from the AGP range `X^{1/4}` into the
Siegel–Walfisz range `exp(c√log X)`, where `exists_pointwise_exponential_distribution` — a
proved, `#print axioms`-clean theorem of the installed dependency — already applies.

`AGP` remains open, and this module does not close it.  What it shows is that `AGP` was never
what the qualitative consumer needed.
-/

namespace NormalNumbers.JointLambert

open Finset

theorem jointWords_unconditional (S : Finset ℕ)
    (hb2 : ∀ b ∈ S, 2 ≤ b) : JointWords S := by
  intro lengths values hwin N
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨N, le_refl _, by simp⟩
  -- a common multiple of the bases
  set c : ℕ := ∏ b ∈ S, b with hcdef
  have hbc : ∀ b ∈ S, b ∣ c := fun b hb => Finset.dvd_prod_of_mem _ hb
  have hc2 : 2 ≤ c := by
    obtain ⟨b₀, hb₀⟩ := hne
    have h1 : b₀ ≤ c :=
      Finset.single_le_prod' (f := fun i => i) (fun i hi => by have := hb2 i hi; omega) hb₀
    have := hb2 b₀ hb₀
    omega
  -- one positive margin over the finite set
  set P : ℕ := ∏ b ∈ S, b ^ lengths b with hPdef
  have hPbig : ∀ b ∈ S, b ^ lengths b ≤ P :=
    fun b hb => Finset.single_le_prod' (f := fun i => i ^ lengths i)
      (fun i hi => Nat.one_le_pow _ _ (by have := hb2 i hi; omega)) hb
  have hPpos : 0 < P := Finset.prod_pos fun b hb => Nat.pow_pos (by have := hb2 b hb; omega)
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hPpos
  set ε : ℝ := 1 / (P : ℝ) with hεdef
  have hε : 0 < ε := by rw [hεdef]; positivity
  -- interior cylinders for the prescribed words
  obtain ⟨s, a, hs2, ha2, hbox⟩ := evenEncoding S hb2
      (fun b => (values b : ℝ) / (b : ℝ) ^ lengths b)
      (fun b => ((values b : ℝ) + 1 / 2) / (b : ℝ) ^ lengths b) (by
        intro b hb
        have hb2' := hb2 b hb
        have hb0 : (0 : ℝ) < b := by
          have : (2 : ℝ) ≤ b := by exact_mod_cast hb2'
          linarith
        have hbl0 : (0 : ℝ) < (b : ℝ) ^ lengths b := by positivity
        obtain ⟨hlen, hval⟩ := hwin b hb
        have hvR : (values b : ℝ) + 1 ≤ (b : ℝ) ^ lengths b := by
          have h1 : (values b : ℕ) + 1 ≤ b ^ lengths b := by omega
          have h2 : ((values b : ℕ) + 1 : ℝ) ≤ ((b ^ lengths b : ℕ) : ℝ) := by
            exact_mod_cast h1
          simpa using h2
        refine ⟨by positivity, ?_, ?_⟩
        · rw [div_lt_div_iff₀ hbl0 hbl0]
          nlinarith [hbl0]
        · rw [div_le_one hbl0]; linarith)
  obtain ⟨r, rfl⟩ : ∃ r, s = r + 1 := ⟨s - 1, by omega⟩
  have hr1 : 1 ≤ r := by omega
  obtain ⟨k, n, -, hkr, hn1, hnN, hkill, hsurv, -, hall⟩ :=
    exists_joint_small_tail_all_bases_rescaled hc2 ha2 hr1 hε 0 (N + 1)
  obtain ⟨M, rfl⟩ : ∃ M, n = M + 1 := ⟨n - 1, by omega⟩
  refine ⟨M, by omega, fun b hbS => ?_⟩
  have hb2' := hb2 b hbS
  have hb0 : (0 : ℝ) < b := by
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb2'
    linarith
  have hbl0 : (0 : ℝ) < (b : ℝ) ^ lengths b := by positivity
  obtain ⟨hlen, hval⟩ := hwin b hbS
  obtain ⟨hlo, hhi⟩ := hbox b hbS
  obtain ⟨hT0, hTε⟩ := hall b hb2'
  -- the chosen margin dominates `ε/2` in this coordinate
  have hmargin : ε / 2 ≤ (1 / 2) / (b : ℝ) ^ lengths b := by
    have h1 : ((b ^ lengths b : ℕ) : ℝ) ≤ (P : ℝ) := by exact_mod_cast hPbig b hbS
    have h2 : (b : ℝ) ^ lengths b ≤ (P : ℝ) := by simpa using h1
    rw [hεdef, div_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [h2, hbl0]
  exact floor_digit_of_common_offset b (lengths b) (values b) c a r k M hb2' (hbc b hbS)
    hval hkr hkill hsurv hlo hhi hT0 (lt_of_lt_of_le hTε hmargin)

/-- **The frozen headline, with no hypotheses at all.** -/
theorem jointLambertDisjunctivity_unconditional : JointLambertDisjunctivity :=
  fun S hb2 => jointWords_unconditional S hb2

/-- The required dependent-base control: bases `2` and `4`, with no coprimality or
multiplicative-independence hypothesis anywhere. -/
theorem jointWords_two_four_unconditional : JointWords ({2, 4} : Finset ℕ) :=
  jointWords_unconditional {2, 4} (by decide)


/-! ### Exact-type audit surface

Compiler-enforced: each `example` states the frozen type and supplies the new theorem, so a
drift in either breaks the build. -/

section Audit

example : JointLambertDisjunctivity := jointLambertDisjunctivity_unconditional
example : JointWords ({2, 4} : Finset ℕ) := jointWords_two_four_unconditional
example : ∀ S : Finset ℕ, (∀ b ∈ S, 2 ≤ b) → JointWords S := jointWords_unconditional

/-- The three excised-conductor cases of `exists_rescaled_prime_supply` all really occur in
the allocation: `P = 1` (no exclusion), `P` prime and outside the pool `(2^k, 2^(k+1))` (zero
pool primes lost), `P` prime and inside it (one pool prime lost).  The last is the binding
case, and `exists_prime_allocation_nonvacuous` exercises exactly it. -/
example :
    ∃ (q : ℕ) (p : ℕ → ℕ → ℕ),
      q ∈ ({3, 5, 7, 11} : Finset ℕ) ∧
      (∀ j t, j ∈ killedIdx 2 1 → t < j + 1 → p j t ∈ ({3, 5, 7, 11} : Finset ℕ)) ∧
      (∀ j t, j ∈ killedIdx 2 1 → t < j + 1 → p j t ≠ q) ∧
      ¬ (6 ∣ jointB 2 2 1 q p) := exists_prime_allocation_nonvacuous

/-- `P = 1` costs nothing: coprimality to `1` is free, so the `Dset = ∅` branch really does
impose no constraint on the allocated modulus. -/
example (B : ℕ) : Nat.Coprime B 1 := Nat.coprime_one_right B

end Audit

end NormalNumbers.JointLambert
