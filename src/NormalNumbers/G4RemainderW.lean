/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4Remainder
import NormalNumbers.G4FrameW

/-!
# §4D for the prime-subset weight: the three-range split of `ω_S`

`G4Remainder` splits `ω(m)` into the frozen primes (`p ∣ P₀`), the small primes
(`p ≤ R`, `p ∤ P₀`, counted by the vector `S`) and the large primes (`omegaBig`).  For campaign A
the same split is needed for `ω_S`, and the point of this module is that it costs **no new
machinery**: the local layer of `ω_S` is `omegaOn` of the *filtered* finset of small primes, so
the small-prime vector `Sval bb ((smallPrimes R P₀).filter S)` is the `S`-restricted vector, and
every §4C/§4D estimate that is stated for an arbitrary finset of primes applies verbatim.

* `omegaSN_split` — `ω_S(m) = omegaOn (P₀.primeFactors.filter S) m
  + omegaOn ((smallPrimes R P₀).filter S) m + omegaBigS R P₀ S m`;
* `omegaBigS_le_omegaBig` — the `S`-junk is dominated by the `ω`-junk, so every remainder bound
  of `G4Remainder` transfers by monotonicity;
* `blockSum_omegaS_split` — the exact decomposition of the retained block.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.G4

open PrimeLambert

variable (S : ℕ → Prop) [DecidablePred S]

/-- The `S`-restricted large-prime count. -/
def omegaBigS (R P₀ : ℕ) (m : ℕ) : ℕ :=
  (m.primeFactors.filter (fun p => S p ∧ ¬ p ∣ P₀ ∧ R < p)).card

lemma omegaBigS_le_omegaBig (R P₀ m : ℕ) : omegaBigS S R P₀ m ≤ omegaBig R P₀ m := by
  classical
  refine Finset.card_le_card (fun p hp => ?_)
  simp only [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.2.1, hp.2.2.2⟩

lemma omegaOn_filter_primeFactors_eq {P₀ m : ℕ} (hP₀ : P₀ ≠ 0) (hm : m ≠ 0) :
    omegaOn (P₀.primeFactors.filter S) m
      = ((m.primeFactors.filter S).filter (fun p => p ∣ P₀)).card := by
  classical
  unfold omegaOn
  congr 1
  ext p
  simp only [Finset.mem_filter, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨⟨h1, h2, -⟩, hS⟩, h3⟩; exact ⟨⟨⟨h1, h3, hm⟩, hS⟩, h2⟩
  · rintro ⟨⟨⟨h1, h2, -⟩, hS⟩, h3⟩; exact ⟨⟨⟨h1, h3, hP₀⟩, hS⟩, h2⟩

lemma omegaOn_filter_smallPrimes_eq {R P₀ m : ℕ} (hm : m ≠ 0) :
    omegaOn ((smallPrimes R P₀).filter S) m
      = ((m.primeFactors.filter S).filter (fun p => ¬ p ∣ P₀ ∧ p ≤ R)).card := by
  classical
  unfold omegaOn
  congr 1
  ext p
  simp only [Finset.mem_filter, Nat.mem_primeFactors, mem_smallPrimes]
  constructor
  · rintro ⟨⟨⟨h1, h2, h3⟩, hS⟩, h4⟩; exact ⟨⟨⟨h1, h4, hm⟩, hS⟩, h3, h2⟩
  · rintro ⟨⟨⟨h1, h2, -⟩, hS⟩, h3, h4⟩; exact ⟨⟨⟨h1, h4, h3⟩, hS⟩, h2⟩

/-- **The frozen / small / large partition of `ω_S`.** -/
theorem omegaSN_split (R : ℕ) {P₀ m : ℕ} (hP₀ : P₀ ≠ 0) (hm : m ≠ 0) :
    omegaSN S m = omegaOn (P₀.primeFactors.filter S) m
      + omegaOn ((smallPrimes R P₀).filter S) m + omegaBigS S R P₀ m := by
  classical
  rw [omegaOn_filter_primeFactors_eq S hP₀ hm, omegaOn_filter_smallPrimes_eq S hm]
  unfold omegaSN omegaBigS
  rw [← Finset.card_filter_add_card_filter_not (s := m.primeFactors.filter S)
      (p := fun p => p ∣ P₀), add_assoc]
  congr 1
  rw [← Finset.card_filter_add_card_filter_not
    (s := (m.primeFactors.filter S).filter (fun p => ¬ p ∣ P₀)) (p := fun p => p ≤ R)]
  congr 1
  · congr 1
    ext p
    simp only [Finset.mem_filter]
    tauto
  · congr 1
    ext p
    simp only [Finset.mem_filter, not_le]
    tauto

/-- The real form of the split, on a nonzero argument. -/
lemma omegaS_split (R : ℕ) {P₀ m : ℕ} (hP₀ : P₀ ≠ 0) (hm : m ≠ 0) :
    omegaS S m = (omegaOn (P₀.primeFactors.filter S) m : ℝ)
      + (omegaOn ((smallPrimes R P₀).filter S) m : ℝ) + (omegaBigS S R P₀ m : ℝ) := by
  unfold omegaS
  rw [omegaSN_split S R hP₀ hm]
  push_cast
  ring

/-- **The exact remainder decomposition for `ω_S`.**  The `S`-local layer is the ordinary
small-prime vector of the *filtered* finset `(smallPrimes R P₀).filter S`. -/
theorem blockSum_omegaS_split (bb : ℕ) (G : GridParams) (R : ℕ) (n : ℕ)
    (a : Fin G.K → Fin G.s) :
    blockSum bb G (omegaS S) n a
      = blockSum bb G (fun m => (omegaOn (G.P₀.primeFactors.filter S) m : ℝ)) n a
        + Sval bb ((smallPrimes R G.P₀).filter S) (shiftAL G.B G.Q G.D₀ (N := G.N)) n a
        + blockSum bb G (fun m => (omegaBigS S R G.P₀ m : ℝ)) n a := by
  rw [Sval_eq_blockSum, ← blockSum_add, ← blockSum_add]
  refine blockSum_congr bb G a fun α jj => ?_
  exact omegaS_split S R G.P₀_pos.ne' (by have := shiftAL_pos G (α, jj); omega)

end NormalNumbers.G4
