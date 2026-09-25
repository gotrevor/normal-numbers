# HANDOFF c3-mrt 2026-09-25 — lap 19

**Branch** `wip/c3-mrt` · **HEAD** `27a4f8e` · working tree **clean** · `lake build` green
(9257 jobs) at every commit.  All new results sorry-free and
`[propext, Classical.choice, Quot.sound]`.  Pure addition: one new module,
`src/NormalNumbers/C3MrtArchimedean.lean`; no existing statement touched.

Read first: `DIRECTION.md` → **CURRENT DIRECTIVE** (set lap 18; it outranks this file).
Prior batons: `HANDOFF-c3mrt-2026-09-25-lap18.md` (the review lap, and the mathematical
setting), `-lap8.md` (laps 7–17), `-session-wrap.md` (laps 1–6).  Overview: `STATUS.md`.

## The crux is untouched

`weylLambertTwist_holds` (`SwingC3Leaf.lean`) unchanged; `conjC3_via_weylLambert` carries
`sorryAx` through it alone.  Everything else in the C3/MRT chain is trust-triple.

## Where lap 19 got to

**Range 1 of the archimedean non-pretentiousness certificate is a proved inequality.**
`range_one_mass_bound`: if every prime `p ≤ X` satisfies `|t|·log p ≤ T`, then

    (1 − cos ε) · ( mass of {p ≤ X : p ≡ 1 mod q}  −  (2·windowCount T z + 1)·windowMassBound )
      ≤  pretentiousDistSqToTwist (ζ^Ω) χ t X ,        ε = resEps z = |arg z|/2 > 0 .

Both subtracted quantities are independent of `X` **and of `t`**; the class mass grows like
`(1/φ(q))·log log X`.  Supporting chain, all new this lap:

| name | content |
|---|---|
| `windowIndex`, `windowIndex_spec` | the resonance window a prime falls into, by choice |
| `abs_windowIndex_le` | `|t| log p ≤ T ⟹ |m| ≤ ⌈(T+ε+π)/2π⌉` — only `O(T)` windows meet `[2,X]` |
| `resonant_mass_le` | fiberwise summation over those indices; each fiber is lap 18's `window_mass_le`.  `t = 0` folds in (no prime is resonant: `|arg z| = 2ε > ε`) |
| `pretentiousTerm_class_eq` | on `p ≡ 1 (mod q)` the term is exactly `(1 − Re(z p^{−it}))/p` |
| `pretentiousTerm_nonneg_prime`, `pretentiousDistSq_ge_sum_good` | discarding the other primes is free; each good prime pays `1 − cos ε` |

## NEXT — resume here

1. **Insert Mertens in the class.**  `G4.MertensAP.mertensRate_residueClass (ha : IsUnit a)`
   (`G4MertensAP.lean:816`, `{q} [NeZero q] {a : ZMod q}`) gives `∃ c C, 0 < c ∧ ∀ N ≥ 2,
   c·log log N − C ≤ sumInvPrimesIn (· ≡ a) N`.  Take `a = 1` (`isUnit_one`).  *Watch the index
   set*: `sumInvPrimesIn` sums over `N.primesBelow` (primes `< N`) while `classPrimes q X` uses
   `primesUpTo X` (primes `≤ X`), so `sumInvPrimesIn … X ≤ ∑ p ∈ classPrimes q X, p⁻¹` by
   `Finset.sum_le_sum_of_subset_of_nonneg` — the inequality is in the useful direction.
   Conclusion to state:

       theorem range_one_certificate (hz) (hz1) (A T : ℝ) (q ≠ 0) :
         ∃ X₀, ∀ X ≥ X₀, ∀ χ : DirichletCharacter ℂ q, ∀ t, (|t| * Real.log X ≤ T) →
           A ≤ pretentiousDistSqToTwist (restrictToNat (zOmInt z)) χ t X

   Uniformity in `χ` is free — `range_one_mass_bound` never looks at `χ` beyond `χ(p) = 1` on
   the class.  Uniformity over `q ≤ A` needs a `Finset.max` over the finitely many `q`.
   The hypothesis `hT` is discharged by `Real.log_le_log` (`p ≤ X`) plus `|t| ≤ T/log X`.
2. **Range 2: name it once.**  `def TwistedPrimeSumSaving (A : ℕ) (T : ℝ) : Prop :=
   ∃ X₀, ∀ X ≥ X₀, ∀ q ≤ A, ∀ χ, ∀ t, T/Real.log X ≤ |t| → |t| ≤ A*X →
   ‖twistPrimeSum χ t X‖ ≤ Erdos67b.PrimeEstimates.primeReciprocals X − A`.  Then
   `pretentiousDistSqToTwist_zOm_ge` closes Range 2 in two lines.  This Prop IS the
   Vinogradov–Korobov log-derivative bound; the dependency isolates the same input as
   `Erdos67b.PolynomialHeightPrimeCorrelationBound` (`TwistSeparation.lean:782`).  **Do not
   try to prove it** — lap 18 recorded why the elementary route cannot reach `|t| ≳ (log X)^K`.
3. **Assemble** `nonPretentious_zOm` (Range 1 ∪ Range 2, with `T = T(A)` chosen so the two
   ranges cover `ℝ`), feed `initial_segment_bound_of_elliott` (`C3MrtRungTwo.lean`), then the
   tuple sum over coprime powerful pairs `d, e ≤ Y` (laps 8–13 supply weight transfer,
   truncation and the window stack).

## Still refuted — DO NOT RETRY

Lap 18's two (resonance counting past `|t| ≳ (log X)^K` is short-interval-hard; crude
`|ζ(1+it)| ≪ log t` cancels exactly at `|t| ≍ X`), plus the four standing ones from the earlier
wraps (smooth/rough Kubilius split; self-similar recursion; growing `P`; direct use of
`unitCircleLogElliott`).

## Confidence

* leaf TRUE ≈ 95%; leaf PROVABLE in natural density with known techniques ≈ 15% (unchanged).
* **Range-1 certificate (step 1 above) closable next lap: ≈ 90%** — no new mathematics, and the
  one API mismatch (`primesBelow` vs `primesUpTo`) is noted above.
* `D = 2` rung conditional on exactly two literature-proved inputs: ≈ 75%.
