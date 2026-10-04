/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.RealDefs
import NormalNumbers.ReciprocalNormal
import NormalNumbers.SwingC1Log

/-!
# New siblings for the barrier library

Standard counterexamples a normality argument must survive, stated here because the repo had no
Lean form of them.  Each is a known (or near-folklore) fact, frozen with a disclosed `sorry`, a
confidence, and an English construction.  `Barriers.lean` registers them as `frozen` barriers;
`#barrier_audit` demands promotion once a proof lands.

* `exists_rat_isNormalUpTo_not_isNormal`: correct statistics for every word of length `≤ k`,
  not normal.  Guards mechanisms that check finitely many orders.
* `exists_isLogNormal_not_isSimplyNormal`: normal under logarithmic averaging, not even simply
  normal under natural averaging.  Guards lane E2 (the log rung is distinct) and C1-log.
* `exists_normal_prefix_limit_not_normal`: normal numbers agreeing with a non-normal one on
  ever-longer prefixes.  Guards soft diagonal and limit arguments.
* `tsum_two_pow_div_fermat`: a rational Lambert-type series.  Guards irrationality mechanisms.
* `not_exists_prime_nonresidue_71`: the drift-one arithmetic crux is false at `p = 71`
  (proved).
-/

namespace NormalNumbers.Barriers.Siblings

open Filter Topology Finset

/-! ## Order-`k` statistics do not give normality -/

/-- **Normality up to order `k`**: the normality limit of `IsNormalSequence`, for words of length
at most `k` only. -/
def IsNormalUpTo (b k : ℕ) (s : ℕ → ℕ) : Prop :=
  ∀ w : List ℕ, w ≠ [] → w.length ≤ k → (∀ d ∈ w, d < b) →
    Tendsto (fun n => (countOccurrences w ((List.range n).map s) : ℝ) / n) atTop
      (𝓝 ((b : ℝ) ^ w.length)⁻¹)

/-- **Sibling (a).**  For every `k` some rational has the correct frequency for every binary word
of length `≤ k`, and no rational is normal.

Confidence 99%.  Construction: let `D_k` be a binary de Bruijn word of order `k` (length `2^k`,
every length-`k` word occurs exactly once cyclically) and `q = D_k / (2^{2^k} − 1)`, whose
expansion is `D_k` repeated.  A length-`k` word occurs once per period, so its frequency is
`2^{−k}`; a word of length `j < k` extends to `2^{k−j}` words of length `k`, so its frequency is
`2^{−j}`.  A purely periodic sequence of period `p` has at most `p` distinct words of each length,
so some word of length `m` with `2^m > p` never occurs and `q` is not normal.  (`D_k` contains
both digits for `k ≥ 1`, so the expansion has no `1^∞` tail; `k = 0` is vacuous.) -/
theorem exists_rat_isNormalUpTo_not_isNormal (k : ℕ) :
    ∃ q : ℚ, IsNormalUpTo 2 k (digitOf 2 (Int.fract (q : ℝ))) ∧ ¬ IsNormal 2 (q : ℝ) := by
  sorry

/-! ## Logarithmic averaging is a strictly weaker rung -/

open Classical in
/-- Logarithmic frequency of the word `w` among the first `n` start positions of `s`: occurrences
at `i` weigh `1/(i+1)`, normalised by the harmonic sum. -/
noncomputable def logOccFreq (w : List ℕ) (s : ℕ → ℕ) (n : ℕ) : ℝ :=
  (∑ i ∈ range n, if (∀ j (hj : j < w.length), s (i + j) = w[j]) then (1 : ℝ) / (i + 1) else 0) /
    ∑ i ∈ range n, (1 : ℝ) / (i + 1)

/-- **Logarithmic normality** of a real number in base `b`: every word's logarithmic frequency
in the digits of `Int.fract x` tends to `b^{−|w|}`. -/
def IsLogNormal (b : ℕ) (x : ℝ) : Prop :=
  ∀ w : List ℕ, w ≠ [] → (∀ d ∈ w, d < b) →
    Tendsto (logOccFreq w (digitOf b (Int.fract x))) atTop (𝓝 ((b : ℝ) ^ w.length)⁻¹)

/-- **Sibling (b).**  In every base some number is normal under logarithmic averaging, in
particular log-simply-normal in the `SwingC1Log` sense, without being simply normal.  So the log
rung of lane E2 is genuinely weaker, and a log-averaged mechanism must not conclude a
natural-average statement.

Confidence 95% (folklore; natural-density convergence implies logarithmic, not conversely).
Construction: start from a normal `z` and set to `0` its digits on the blocks `[N_j, 2N_j)` with
`N_j = 2^{2^j}`.  The blocks up to `N` carry harmonic weight `O(j) = O(log log N)` against
`log N`, so log frequencies are those of `z`, which are normal because Cesàro convergence implies
logarithmic convergence.  At `n = 2N_j` the digit `0` has natural frequency `≥ 1/2 + (1/2)/b`,
so `x` is not simply normal. -/
theorem exists_isLogNormal_not_isSimplyNormal (b : ℕ) (hb : 2 ≤ b) :
    ∃ x : ℝ, IsLogNormal b x ∧ CastingOut.SimplyNormalLog b x ∧
      ¬ ReciprocalNormal.IsSimplyNormal b x := by
  sorry

/-! ## Limits of normal numbers -/

/-- **Sibling (c).**  Normal numbers can agree with a non-normal number (here `0`) on prefixes of
unbounded length.  So a diagonal argument that only matches ever-longer prefixes of normal stages
proves nothing; it must control the Weyl means on the windows between stages.

Confidence 99%.  Construction: take a normal `z ∈ (0,1)` and zero its first `M_j = j` digits;
changing finitely many digits does not change any limiting frequency. -/
theorem exists_normal_prefix_limit_not_normal :
    ∃ x : ℕ → ℝ, (∀ j, IsNormal 2 (x j)) ∧
      (∀ j i, i < j → digitOf 2 (Int.fract (x j)) i = 0) ∧ ¬ IsNormal 2 0 := by
  sorry

/-! ## A rational Lambert-type series -/

/-- **Sibling (d).**  A Lambert-type series over the doubling set is rational:
`Σ_{k≥0} 2^k/(2^{2^k}+1) = 1`.  So an irrationality mechanism for Lambert sums
`Σ_{n∈A} a_n/(b^n ± 1)` must use something about `A` or the weights that fails here.

Confidence 100% (classical).  Proof: `1/(x−1) − 2^{k+1}/(x^{2^{k+1}}−1)` telescopes, since
`1/(y−1) − 2/(y²−1) = 1/(y+1)` with `y = x^{2^k}` gives
`2^k/(x^{2^k}−1) − 2^{k+1}/(x^{2^{k+1}}−1) = 2^k/(x^{2^k}+1)`; at `x = 2` the tail
`2^{k+1}/(2^{2^{k+1}}−1) → 0`. -/
theorem tsum_two_pow_div_fermat :
    ∑' k : ℕ, (2 : ℝ) ^ k / (2 ^ (2 ^ k) + 1) = 1 := by
  sorry

/-! ## The drift-one arithmetic crux fails at `71` -/

/-- **Sibling (proved).**  The statement of `DriftOne.exists_prime_nonresidue` is false at
`p = 71`: the primes in `(71/3, 71/2)` are `29` and `31`, and `71` is a square mod both
(`71 ≡ 10²` mod 29, `71 ≡ 3²` mod 31).  So any proof must use `p ≥ 73`. -/
theorem not_exists_prime_nonresidue_71 :
    ¬ ∃ q, q.Prime ∧ 71 < 3 * q ∧ 2 * q < 71 ∧ ¬ q ∣ 71 + 1 ∧
      ¬ IsSquare ((71 : ℕ) : ZMod q) := by
  rintro ⟨q, hq, h1, h2, -, hns⟩
  apply hns
  have hlo : 23 < q := by omega
  have hhi : q < 36 := by omega
  interval_cases q <;> norm_num at hq
  · exact ⟨10, by decide⟩
  · exact ⟨3, by decide⟩

end NormalNumbers.Barriers.Siblings
