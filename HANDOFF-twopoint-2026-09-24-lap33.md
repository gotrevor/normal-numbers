# HANDOFF twopoint — lap 33: the Levin–Fainleib identity for the Delange kernel

Branch `wip/twopoint-avg`.  New file `src/NormalNumbers/TwoPointDelangeLF.lean` (sorry-free,
trust-triple), import added to `src/NormalNumbers.lean`.

## Crux this lap
`DelangeKernelMean z : Σ_{n≤N} h_z(n)/n → 0` — the last dischargeable residue of the 🟡
`DelangeMean` axiom (the tail residue fell in lap 28).

## A refuted sub-approach, recorded
**Rankin's trick / any absolute-value comparison of the sum with its Euler product CANNOT work.**
For `u = ‖z−1‖ ∈ (0,1)` the absolute sum `Σ_{n≤N} μ²(n)u^{ω(n)}/n ≍ (log N)^u` **diverges**, while
`|Π_{p≤N}(1+(z−1)/p)| ≍ (log N)^{Re z−1} → 0`.  The smooth tail separating the truncated sum from
the product is therefore *larger in modulus than either side*, so there is no route from the
already-proved `prod_delangeLocal_tendsto_zero` to `DelangeKernelMean` by triangle inequality.
Do not retry.  (I priced the Rankin exponent explicitly: `σ = c/log N` gives
`e^{-c}(log N)^{u e^{c}}`, minimised at `≍ 1`, never `o(1)`.)

## The advance
The correct engine is Levin–Fainleib/Wirsing, which runs on the `log`-weighted sum.  Its exact
starting identity is now a theorem, with **no analytic input whatever**:

**`sum_delangeKernel_mul_log`** — for every `z` and every `N`,

    Σ_{n≤N} h(n)·log n / n  =  (z−1) · Σ_{p≤N} (log p / p) · Σ_{m ≤ N/p, p ∤ m} h(m)/m .

Supporting lemmas:
| lemma | content |
|---|---|
| `log_eq_sum_log_primeFactors` | `log n = Σ_{p ∣ n} log p` for squarefree `n ≠ 0` |
| `delangeKernel_prime_mul` | `h(pm) = (z−1)h(m)` if `p ∤ m`, else `0` — the kernel's prime step |

Proof shape: split `log n` over `n`'s prime factors (exact for squarefree, and `h` is supported
there), swap the sums, reindex the multiples of `p` by `n = p·m` (`sum_multiples_reindex`, reused
from the Kátai rearrangement), and apply the prime step.  Every step is an identity.

## Why this is the right brick
Levin–Fainleib bounds `|S(N)|·log N` against `Σ_{p≤N}(log p/p)|S(N/p)|` plus an error, and then
runs an integral/induction on `S`.  The identity above is the only arithmetic input; what remains
is (a) removing the `p ∤ m` restriction (one more prime step, `O(1/p)` loss), (b) Mertens
(`Σ_{p≤N} log p/p = log N + O(1)`, in the PNT port), (c) the Gronwall-type induction.  Those are
analytic but standard, and the arithmetic is now done.

## Run to date
* lap 28 `92ede26` — `DelangeKernelTail` unconditional for `‖z−1‖<1`.
* lap 29 `ab283df` — the peel weight drops at growing depth.
* lap 30 `2d4d2c3` — exact CRT counts for the `2K` forms.
* lap 31 `6775ae3` — the weight-free reduction is an EQUIVALENCE.
* lap 32 `f29262a` — depth invariance; weight ⟺ unbounded depth.
* lap 33 (this) — the Levin–Fainleib identity.

## Next
1. Remove the `p ∤ m` restriction from the inner sum (elementary, one prime step).
2. Port `Σ_{p ≤ N} log p / p = log N + O(1)` from `src/PNTPort/` (or prove the Mertens form
   needed).  Then the Levin–Fainleib induction.
3. Still open at the C1 crux: the prime-cut split of `MultiElliottGrowing`.

## Confidence
- `twoPointWeightedAvg_all` TRUE 90%; provable with known techniques 3%.
- `DelangeKernelMean` for `‖z−1‖<1` closable in 3–6 laps: **35%** (arithmetic done, analysis left).
