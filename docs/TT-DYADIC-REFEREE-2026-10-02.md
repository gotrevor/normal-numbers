# Referee: `CastingOut.TTEquidistributedDyadic` vs Tao–Teräväinen Thm 3.1(i)

Source: arXiv:2512.01739v2 (25 Apr 2026), §3, Theorem 3.1, (3.1), (3.2), (3.4), and the §3.2 reductions.  Lean: `src/NormalNumbers/LiteratureTTEquidistributedDefect.lean:62`; referee file `src/NormalNumbers/LiteratureTTDyadicReferee.lean` (not in the root import).

## Verdict: (a), implied, but by our own derivation (confidence 85%)

TT does not state the Prop.  It follows from TT's literal statement by a short elementary perturbation-plus-counting argument, which the paper does not contain (exponent `c → c/2`; the docstring's `c/4` is looser but also fine).  Wherever the quantifiers differ, the Lean is the same as TT or weaker.  **(d) Not vacuous.**  The counted exceptional set cannot swallow every scale (`full_exceptional_set_not_admissible`).  The conclusion is asked at every natural `N` of a good block, and `δ N` there is pinned by the hypothesis.  The consumer's instance (`binInd` sieve indicators of large primes) discharges the hypotheses, and its conclusion is a real two-dimensional sieve-correlation statement.

## Quantifier table (Lean vs TT)

| Slot | TT 3.1(i) | Lean | Verdict |
|---|---|---|---|
| `g₁, g₂` | 1-bounded multiplicative `ℕ → ℂ`; `g₁` real | `IsCoprimeMultiplicativeNat` (`g 1 = 1`, coprime mult.), `‖g‖ ≤ 1`, `im g₁ = 0` | same |
| `X, L` | `X ≥ 2`, `1 ≤ L ≤ log X` | same | same |
| (3.1) | all real `N ∈ [X^0.4, X]`, all `a, q ∈ ℕ`, error `O(N/L)` | same range, all `q ≥ 1`, error `≤ N/L` (constant 1) | Lean hypothesis stronger, so the Prop is weaker: OK |
| (3.2) | `g₁(p) = 1` for `exp(log^{1/11}X) ≤ p ≤ exp(log^{1/10}X)` | same | same |
| `c`, constants | `c` sufficiently small absolute; `≪` absolute once (3.1)'s constant is fixed | `∃ c Cst`, uniform in everything | same (the constant is fixed at 1) |
| `E` | `E ⊂ [√X, X]`, `(1/log X)∫_E dt/t ≪ L^{-c}`, independent of `W, b, h` | `Finset` of `j ∈ dyadicScales X` (`√X ≤ 2^j`, `2^{j+1} ≤ X`), `#E ≤ Cst L^{-c} #scales`, independent of `W, b, h` | **derived** (below) |
| where (3.4) holds | every real `N ∈ [√X, X] \ E` | every natural `N ∈ [2^j, 2^{j+1})`, `j ∉ E` (all inside `[√X, X)`) | **derived** |
| `W, b` | `W ∈ [L^c]`, `b ∈ ℤ` | `0 < W ≤ L^c`, `b ∈ ℕ` (via `b % W`) | same / weaker |
| `h₁ ≠ h₂` | integers `O(L^c)` | naturals `≤ L^c` | weaker |
| `δ` in (3.4) | `δ_N` at the same real `N` | `δ (N : ℝ)` at the natural `N` | needs transfer (below) |

## The derivation (the one place we go beyond TT)

Take `η = L^{-c/2}`.  (1) **δ transfer.**  (3.1) at `q = 1` with constant 1 gives `|δ_N| ≤ 3` and `|δ_N − δ_{N'}| ≤ 2/L + O(η + 1/N)` when `|log N − log N'| ≤ η`.  The docstring omits this step; without it, evaluating `δ` at the natural `N` would be unjustified.  (2) **Perturbation.**  Moving from a real `N' ∉ E` to a natural `N` within relative distance `η` changes the normalized sum by `O(η + W/N + 1/L)`: `O(ηN/W + 1)` boundary terms of size `≤ 4`, the `W/N` prefactor, and the `δ` shift.  (3) **Counting.**  `N` fails only if `[Ne^{-η}, Ne^{η}] ∩ [√X, X]` (log-length `≥ η`) lies inside `E`.  Each `t` lies in at most 2 enlarged blocks, so there are `≤ 2∫_E dt/t / η ≪ L^{-c/2} log X ≪ L^{-c/2}·#scales` bad blocks.  Small `L` is absorbed into `Cst`.  Result: the Prop with `c/2`, and `W, h ≤ L^{c/2} ≤ L^c`.  I found no gap beyond (1).  The 15% residual covers TT itself being wrong and a constant-chasing slip in (2)–(3).

## Defect and repair

**Most dangerous mismatch:** the cited `Prop` is not a transcription.  The step from measure to count, and from real `N` to the natural `N` with `δ` re-evaluated, is our own unformalized argument, and a reader checking the citation against the PDF will not find it.  It is not a falsity.

**Repair (Lean record, `LiteratureTTDyadicReferee.lean`, elaborates; one intended `sorry`):**
* `TTEquidistributedReal`: the literal transcription, with (3.4) at every **real** `N ∈ [√X, X] \ E`.  This closes the null-set loophole of `TTEquidistributedCorrelation` without counting scales.
* `ttEquidistributedDyadic_of_real : TTEquidistributedReal → TTEquidistributedDyadic`, `sorry`, 85%, English proof in the docstring.  Proving it makes the headline conditional on TT verbatim.
* `TTEquidistributedDyadicPow2` + proved `ttEquidistributedDyadicPow2_of_dyadic`.  The consumer only ever uses `N = 2^j`: `binPair_cov_core`, `G4Base2PairCov.lean` ~l.395, `hEgood … (2 ^ k)`.  So downstream would accept this weaker Prop with no change to its logic.  It does not remove the derivation, though: real `N'` must still be moved to `2^j`.

Recommended: re-freeze the headline on `TTEquidistributedReal` once `ttEquidistributedDyadic_of_real` is proved.  Until then, the docstring of `TTEquidistributedDyadic` should state the δ-transfer step (1).
