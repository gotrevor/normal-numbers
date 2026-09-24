import NormalNumbers.PairDecoupleSplit

/-!
# PairDecouple — the PROOF direction

The only open input of `conjC1_of_delange_katai_decouple` (C1 swing).  Exactly the hypothesis
`hDc` there.  A sibling worktree (`wip/pd-refute`) attacks the negation.

`PairDecoupleSplit.lean` reduces it, with the cut `P` eliminated, to either of two named leaves:
`TopMassVanishing` (mass form, heuristically false) or `LargeDecay` (decay form, heuristically
true).  `LargeDecay` is the successor crux.
-/

namespace NormalNumbers.CastingOut

/-- **THE SUCCESSOR CRUX.**  The large-prime remainder of the pair difference `θ_{pn} − θ_{qn}`
equidistributes along every progression to the small-prime modulus `Q = Π_{r ≤ P} r`.

This is what the CRT/Mertens heuristic predicts: over primes `r > P` the local factors satisfy
`‖pairLocalFactor b t r p q‖ ≤ 1 − c/r` (`SwingC1Pair.lean`, unconditional) and `Σ_{r > P} 1/r`
diverges, so the model mean is `0`.  What is open is converting the model into a genuine density
statement for a single residue class — the same natural-density-versus-full-period gap, but now
with the small primes *removed* from the integrand, so no periodic factor is left to interfere.

Progress so far (`PairDecoupleSplit.lean`): the primes `> P` split at a second cut `y`, the
middle range `(P, y]` is handled unconditionally by exact CRT with defect `O(Π_{P<r≤y} r / R)`,
and the whole remaining content is the range `> y`. -/
theorem topDefect_all : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
    ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → ∀ P c : ℕ, ∀ ε > 0, ∀ Y : ℕ, ∃ y ≥ Y,
      ∀ᶠ S in Filter.atTop, topDefect b P y p q (((m : ℤ) : ℝ) / b) c S < ε := by
  sorry

theorem largeDecay_all : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
    ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → LargeDecay b p q (((m : ℤ) : ℝ) / b) := by
  intro b hb m hm hdvd p q hp hq hpq
  have hbpos : (0 : ℝ) < (b : ℝ) := by
    have : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  have hmR : ((m : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
  exact largeDecay_of_topDefect b p q _ (by omega) (div_ne_zero hmR (ne_of_gt hbpos)) hp hq hpq
    (topDefect_all b hb m hm hdvd p q hp hq hpq)

theorem pairDecouple_all : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
    ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → PairDecouple b p q (((m : ℤ) : ℝ) / b) := by
  intro b hb m hm hdvd p q hp hq hpq
  exact pairDecouple_of_largeDecay b p q _ (largeDecay_all b hb m hm hdvd p q hp hq hpq)

end NormalNumbers.CastingOut

namespace NormalNumbers.CastingOut

end NormalNumbers.CastingOut
