/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Erdos257AllPrimes
import NormalNumbers.Erdos257Divergent
import NormalNumbers.LiteratureTTDyadicReferee

/-!
# Erdős #257 for prime sets, on the literal citations

The headlines of `Erdos257AllPrimes` / `Erdos257Divergent` take the counted dyadic form
`CastingOut.TTEquidistributedDyadic`; `CastingOut.ttEquidistributedDyadic_of_real` derives it from
`CastingOut.TTEquidistributedReal`, the literal transcription of Tao–Teräväinen arXiv:2512.01739
Theorem 3.1(i).  These restate the headlines on the literal form.
-/

namespace NormalNumbers.Erdos257

/-- **Erdős #257 for every infinite set of primes**, from Erdős 1968 and Tao–Teräväinen
Theorem 3.1(i) as published. -/
theorem erdos257_allPrimes_of_literature (h68 : Literature.Erdos1968CoprimeSummable)
    (htt : CastingOut.TTEquidistributedReal) :
    ∀ S : Set ℕ, (∀ p ∈ S, p.Prime) → S.Infinite →
      Irrational (∑' n : S, (1 : ℝ) / (2 ^ n.1 - 1)) :=
  erdos257_allPrimes_of_cases h68 (CastingOut.ttEquidistributedDyadic_of_real htt)

/-- **Base-2 disjunctivity for every divergent prime set**, from Tao–Teräväinen Theorem 3.1(i) as
published. -/
theorem isDisjunctive_subsetLambert_two_of_divergent_literature
    (htt : CastingOut.TTEquidistributedReal) {S : Set ℕ} [DecidablePred (· ∈ S)]
    (hS : ∀ p ∈ S, p.Prime) (hdiv : ¬ Summable (fun p : S => (1 : ℝ) / p.1)) :
    IsDisjunctive 2 (PrimeLambert.subsetLambert (· ∈ S) 2) :=
  isDisjunctive_subsetLambert_two_of_divergent (CastingOut.ttEquidistributedDyadic_of_real htt) hS hdiv

end NormalNumbers.Erdos257
