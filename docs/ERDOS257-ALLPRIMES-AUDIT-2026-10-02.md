# Erdős #257 for every infinite set of primes: audit and direction (2026-10-02)

*Direction only.  The record is `src/NormalNumbers/Erdos257AllPrimes.lean`; every claim below cites its declaration.*

## Verdict

**The gap is real** (90%), and smaller than "everything without a Mertens rate".  Write `F_S(e) = Σ_{p∈S, p<2^{2^e}} 1/p`.

* **(ii) convergent** `Σ_{p∈S} 1/p < ∞`: Erdős 1968 (Math. Student 36, p. 222, read from the scan): pairwise coprime `nᵢ` **and** `Σ 1/nᵢ < ∞` give irrationality at every integer base `t ≥ 2`.  Primes are pairwise coprime, so this covers every convergent prime set.  `Literature.Erdos1968CoprimeSummable` (t = 2, exponents ≥ 2: weaker), `erdos257_convergent` **proved** from it.
* **(i) regular**: the proved `erdos257_primeSubset` needs `MertensRate` (`F_S(e) ≥ c·e − C`, linear in `e`).  The rate is consumed once, against a demand `M(K) = exp(O(K log K))` inside a moment cap `e ≲ 2^{8K²}`, so `F_S(e) ≥ e^ε − C` for any `ε > 0` should suffice: `WeakMertensRate`, `isDisjunctive_subsetLambert_two_of_weakRate` (sorry, 50%).  `weakMertensRate_of_mertensRate` **proved**; `squareBlockPrimes` (`F ≈ log 2·√e`) has the weak rate and no Mertens rate, so the stretch is strict.
* **(iii) gap** `GapSet`: divergent, and `F_S(e) = e^{o(1)}` infinitely often.  Example `towerGapPrimes`, primes with `⌊log₂⌊log₂ p⌋⌋` a power of 2, `F ≈ log 2·log₂ e` (`towerGapPrimes_gapSet`, sorry, 85%).

**Splitting is closed**: `weakMertensRate_mono` / `gapSet_subset_noWeakRate` (proved) show a gap set has no regular subset, so `S = S_reg ∪ S_sparse` adds nothing (and the two constants would be irrational + irrational, which settles nothing anyway).

Wiring `erdos257_allPrimes_of_cases` (Erdős 1968 + TT 3.1(i) + the two open lemmas ⟹ target) is **proved**.  `erdos257_allPrimes` itself: sorry, **30%**.

## The hardest step: decoupling the cutoff exponent from `K`

`isDisjunctive_subsetLambert_two_of_gapSet` (30%).  The cap's factor `e` comes from the *upper* harmonic sum over all primes below `R` (`term_b`/`term_c` in `G4SchedBE`, `Σ_{p<R} 1/p ≤ 3e + 5`).  For `ω_S` it can be the `S`-sum `≤ F_S(e) + O(1)`.  If every `e`-dependence of the witness routes through `F_S(e)`, demand and cap are both conditions on `F_S(e)`, and since `F_S` grows by at most `log 2 + o(1)` per step, every divergent `S` hits the window.  Unchecked: `four_mul_le_two_pow_NE` (`e ≤ 2^{8K²}` vs `N K = 100K²`), the effective covariance supply `VeryLargeCovSupplyEff` at huge `e`, and the variance step when the `S`-mass sits on primes dividing the grid modulus.  No Erdős-style argument is known for divergent sets: his proof needs the uncontrolled tail `Σ 1/nᵢ` to be `< 1`.

## Freshness (2026-10-02)

erdosproblems.com/257 (edited 15 Apr 2026): known cases are ℕ, coprime summable (Er68), primes and prime powers (Tao–Teräväinen); nothing for prime subsets.  formal-conjectures: wcook04 #6529 (open, coprimality-free summable, Lean proof claimed), #6528 (weighted/mixed), neither divergent.  The audit `ERDOS257-BASE2-SUBSET-AUDIT` "side conjecture" (45%) is this lane.

## Recommended treadmill objective

Phase 1 (cheap, closes the strict stretch): prove `isDisjunctive_subsetLambert_two_of_weakRate` by generalising `MertensAP.exists_cutoff_subset` to `WeakMertensRate` and re-checking the cap in `G4Base2Sched`; then the three example lemmas.  Phase 2 (the crux): an `S`-restricted moment cap in `G4SchedBE` (`term_b`/`term_c` over `S`-primes), then `isDisjunctive_subsetLambert_two_of_gapSet`.  A refutation (a size fact that genuinely needs `e ≤ poly(K)`-scale) is an advance: record it as a theorem plus Maze row.

`--require-decls isDisjunctive_subsetLambert_two_of_weakRate,towerGapPrimes_gapSet,squareBlockPrimes_weakRate,squareBlockPrimes_not_mertensRate,isDisjunctive_subsetLambert_two_of_gapSet,erdos257_allPrimes_of_cases`
