# Prime Lambert irrationality: the compressed-cancellation argument in Lean

Bounded campaign (brief 2026-09-14).  Target constant

    G = primeLambert = ∑_{n≥1} ω(n)/2^n  ( = ∑_p 1/(2^p − 1) ),

`ω = ArithmeticFunction.cardDistinctFactors`.  Irrationality is already known
(Tao–Teräväinen, arXiv:2512.01739v2, Thm 1.3); that theorem is **not** cited as an axiom.
This is a formalization of the candidate *elementary* compressed-cancellation argument.
No novelty claim.  Headline `irrational_primeLambert` is **sorry-gated**; see "Status".

The [complete paper proof draft](prime-lambert-proof-draft.md) preserves the geometry,
parameter choices, and analytic argument, not just the formal conditional statements.
The [single-coordinate mass obstruction](prime-lambert-isolator-obstruction.md) records
a separate internally audited paper theorem: isolating one radix tail after K exact
cancellations requires integer coefficient mass at least 2^K.  It is not yet formalized.

## Modules (owned footprint)

| module | content | status |
|---|---|---|
| `PrimeLambertDefs` | `primeLambert`, summability, `tailT k = 2^k G − tailInt k`, `rational_tail_int`; exact transport `ω(dm) + overlap d m = ω m + ω d`, `dilatedTail_eq`, exact periodicity `transportCorr_congr` | proved, axiom-clean |
| `PrimeLambertConfig` | transported configurations `TConfig = (ℕ×ℤ) →₀ ℤ`, `CancelsAt c j` (pushforward along `j·d − s` vanishes), `phaseSum c K n`, **Theorem A** `phaseSum_sub_int` | proved, axiom-clean |
| `PrimeLambertGeometry` | group ring `ℤ[ℤ×ℤ]`, `Cancels`, `edge`, `hexagon` (cancels at its triple; six-atom form `hexagon_eq_six`), `dilate`, `hexTensor r B` cancels at all `1..6r` (`hexTensor_cancels`), coprime transform `toConfig` preserving cancellation (`cancelsAt_toConfig`), positivity, pairwise coprimality (`transform_coprime`), assembly `exists_tconfig_cancelling` | proved, axiom-clean |
| `PrimeLambertAnalytic` | finite tail `truncPhase`, per-prime parts `primePart`, exact additive split `truncPhase_split` (bad/small/large), the four analytic Props `TailTruncation`, `LargePrimeNegligible`, `BadPrimeFrozen`, `SmallPrimeDecay`, proved wiring `phaseOscillation_of_chain`, `ChainExists → Irrational primeLambert` (`irrational_of_chainExists`) | wiring proved, axiom-clean; the four Props open |
| `PrimeLambertTail` | `badPrimeFrozen_of_residue` (exact freezing ⇒ `BadPrimeFrozen`), `phaseSum_sub_truncPhase` (`F − F_J = phaseSum c J n`), `ω(m) ≤ log₂ m`, `ω(dm) ≤ ω d + ω m`, exact tail bound `abs_truncation_error_le`: `\|F − F_J\| ≤ ∑_a \|c a\|(ω d_a + log₂(k_a+1) + J + 1)/2^J`, `tailTruncation_of_bound` | proved, axiom-clean |
| `PrimeLambertHexagonNegative` | `HexNonneg q`, `HexNonnegOfLargeMean q`; eighth-root witness on `ℤ/19ℤ` with `6859·H = 469 − 450√2 < 0`, `\|𝔼 f\| = (7+3√2)/19 > 1/2`; `not_hexNonneg_nineteen`, `not_hexNonnegOfLargeMean_nineteen`, `not_meanRetention_nineteen` | proved, axiom-clean (refutations) |
| `PrimeLambertMoments` | sharp Taylor bound `‖e^{it} − ∑_{k<M}(it)^k/k!‖ ≤ \|t\|^M/M!` (`norm_expRem_le'`), even-moment average bound `norm_avg_e_sub_taylor_le`; independent CRT model `indepAvg` (uniform residue mod `∏_{p small} p`), sample average `sampleAvg`; Props `IndepCharDecay`, `MomentComparison`, `IndepMomentSmall`; **proved transfer** `smallPrimeDecay_of_moments` (even `M_N`), `MomentChain → SmallPrimeDecay` | transfer proved, axiom-clean; the three Props open |
| `PrimeLambertLarge` | unconditional `\|X_p(n)\| ≤ ‖c‖₁ 2^{−K}`, exact weighted per-argument count bound `abs_classSum_le_argumentPrimes`, Prop `LargePrimeArgumentCountSmall`, `largePrimeNegligible_of_argumentCount`; the coarser union-count bound is retained separately | inequalities and conditional transfer proved; quantitative divisor and parameter bounds open |
| `PrimeLambertOscillation` | `e`, `ProgressionFamily`, `phaseAverage`, `PhaseOscillation` (draft eq. (5)), `norm_phaseAverage_eq_one`, `irrational_of_phaseOscillation` | proved, axiom-clean; `phaseOscillation` is the single disclosed `sorry` |

Build: `lake build NormalNumbers.PrimeLambertMoments NormalNumbers.PrimeLambertLarge
NormalNumbers.PrimeLambertHexagonNegative` (targeted; the root module is host-owned and does
not import these yet).

## The exact arithmetic (all proved)

1. `T(k) = ∑_{j≥1} ω(k+j)2^{-j} = 2^k G − ∑_{m≤k} 2^{k−m} ω(m)`.  So `qG ∈ ℤ ⇒ qT(k) ∈ ℤ`.
2. `ω(d(k+j)) = ω(k+j) + ω(d) − #{p | d : p | k+j}`; summing against `2^{-j}`:
   `∑_{j≥1} 2^{-j} ω(d(k+j)) = T(k) + ω(d) − E_d(k)`, and `E_d(k)` depends only on
   `k mod p` for the primes `p | d` (hypothesis form `∀ p ∈ d.primeFactors, k ≡ k' [MOD p]`,
   equivalent to freezing `k mod rad d`; the radical API was not needed).
3. For a configuration `c` cancelling at sites `1..K` and `n = d_a k_a + s_a` on every atom,
   the `j ≤ K` part of `F(n) = ∑_a c(a) ∑_{j>K} 2^{-j} ω(n + j d_a − s_a)` vanishes
   (`finite_part_eq_zero`), so `F(n) = ∑_a c(a)(T(k_a) + ω(d_a) − E_{d_a}(k_a))` (`phaseSum_eq`).
4. **Theorem A**: with `qG ∈ ℤ` and quotients frozen mod every prime of each `d_a`,
   `q(F(n) − F(n')) ∈ ℤ`.  Hence `e(qF)` is constant of modulus one on the progression and
   `‖phaseAverage‖ = 1` (`norm_phaseAverage_eq_one`).
5. Wiring: `PhaseOscillation → Irrational primeLambert`.

## Status of the analytic chain (open)

`ChainExists` (in `PrimeLambertAnalytic`) is the exact remaining obligation, split into four
named Props on a `Chain q` (configurations `c N` cancelling at `1..K N`, progression samples,
sieve data `J, bad, small, large` with primality/disjointness/cover fields):

| Prop | draft | content |
|---|---|---|
| `TailTruncation` | (20) | `sup_{n∈P_N} \|F − F_J\| ≤ ε_N → 0` |
| `LargePrimeNegligible` | (19) | `sup_{n∈P_N} \|∑_{p large} X_p\| ≤ ε_N → 0` |
| `BadPrimeFrozen` | §5.2 | `∑_{p bad} X_p` constant on `P_N` (exact, no bound) |
| `SmallPrimeDecay` | §5.3–5.4 | `‖𝔼_{P_N} e(q ∑_{p small} X_p)‖ → 0` |

Discharged reductions (`PrimeLambertTail`): `BadPrimeFrozen` holds whenever the sample is
frozen modulo every bad prime (`badPrimeFrozen_of_residue`); `TailTruncation` holds whenever
the exact bound `∑_a |c a|(ω d_a + log₂(k_a+1) + J + 1)/2^J` tends to zero on the sample
(`tailTruncation_of_bound`), for the hexagon parameters this is `O(H(log N + log d + J)/2^J)`,
draft (20).  `LargePrimeNegligible` holds whenever the number of large primes dividing some
finite-tail argument, times `‖c‖₁ 2^{−K}`, is uniformly `o(1)` on the sample
(`LargePrimeCountSmall`, `largePrimeNegligible_of_count`, `PrimeLambertLarge`); the pointwise
bound `|X_p(n)| ≤ ‖c‖₁ 2^{−K}` needs no distinct-root hypothesis.  This union-of-active-primes
criterion is a valid but overly strong sufficient condition, not the intended draft (19)
bound.  Substituting the union count `H(J−K) log(3N)/log R` loses an extra factor `H(J−K)`.
The required estimate (`abs_classSum_le_argumentPrimes`) counts primes separately for each argument, before summing its
coefficient weight: if every argument has at most B primes from the class, the bound is
`B ‖c‖₁ 2^{−K}`.  `LargePrimeArgumentCountSmall` states that per-argument bound together
with its weighted decay, and `largePrimeNegligible_of_argumentCount` proves the transfer.
In the draft, `B = log(3N)/log R = O(M)` gives the needed decay.  The divisor count and
its concrete asymptotic ledger still need to be supplied to this conditional theorem.

`phaseOscillation_of_chain` proves that these four imply `PhaseOscillation` (Lipschitz bound
`‖e(x)−1‖ ≤ 4π\|x\|`, unimodular constant factor for the frozen class).  `SmallPrimeDecay` is
the deep step.  `PrimeLambertMoments` decomposes it exactly (draft §5.3–5.4).  The independent
model is *defined* as `S_N` at a uniform residue `r mod ∏_{p small} p`
(`indepAvg C N g = (1/∏p) ∑_{r<∏p} g(S_N(r))`); CRT independence of the local variables is a
theorem about this model, not a modelling assumption.  With an even moment cutoff `M_N`:

| Prop | draft | content |
|---|---|---|
| `IndepCharDecay C` | (13),(15) | `‖indepAvg e(q·)‖ → 0` (draft: `≤ exp(−c_q V_N)`, `V_N ≍ H4^{−K}L → ∞`) |
| `MomentComparison C M` | (16) | `∀ k ≤ M_N, \|sampleAvg x^k − indepAvg x^k\| ≤ δ_N → 0` (draft: `N^{−9/10+o(1)}`) |
| `IndepMomentSmall C M` | (17) | `(2π\|q\|)^{M_N}/M_N! · indepAvg x^{M_N} → 0` (draft: `≤ 2exp(C_qV_N − M_N)`) |

**Proved** (`smallPrimeDecay_of_moments`): these three, for even `M_N`, imply
`SmallPrimeDecay C`.  Pointwise, with `T = (2π|q|)^M/M!`,

    ‖𝔼_P e(qS)‖ ≤ ‖𝔼' e(qS')‖ + 2e^{2π|q|} δ + 2T·𝔼' S'^M,

from the sharp Taylor remainder `‖e^{it} − ∑_{k<M}(it)^k/k!‖ ≤ |t|^M/M!` (proved by induction
via the integral form of the remainder, `norm_expRem_le'`) applied on both averages; evenness
turns the remainder majorant `|S|^M` into the moment `S^M`, which `MomentComparison` controls
and `IndepMomentSmall` kills.  The Taylor coefficients sum to at most `e^{2π|q|}`.  This is the
centred even-moment step of the draft, machine-checked; what remains open is exactly the sieve
input: `IndepCharDecay` (local characteristic-function product, variance growth),
`MomentComparison` (periodicity of `k`-fold products with period `≤ R^k`, AP error
`O(AR^k/N)`, CRT identification of the uniform average), and `IndepMomentSmall` (two-sided mgf
(14) plus `M_N ≫ V_N`).


`PhaseOscillation` asserts: for each `q ≠ 0` there exist `c N`, `K N`, frozen progression
samples `P N`, with `c N` cancelling at `1..K N`, and `‖𝔼_{n∈P N} e(q F_N(n))‖ → 0`.
This is exactly draft §5 eq. (5).  It is not a restatement of irrationality: it is a
quantitative equidistribution statement about a specific signed additive function on
progressions.  Nothing in it is proved yet.  The intended discharge (draft §5.1–5.5):

- geometry: hexagon tensor gives `c` with `H = 6^{K/3}` atoms, weights `±1`, cancelling
  `1..K`, distinct multipliers after the `d = 1 + Q(D+u)` transform;
- exact freezing of bad primes `p | W`;
- independent small-prime model, variance `V ≍ H 4^{-K} L → ∞`, char. function `≤ e^{-cV}`;
- CRT moment comparison for `k ≤ M` with error `N^{-9/10+o(1)}`;
- even-moment Taylor transfer;
- large-prime pointwise bound `O(M H 2^{-K}) → 0` and binary tail `O(H 2^{-J} log N) → 0`.

Geometry (a) is done: `exists_tconfig_cancelling r B Q` produces, for every `r`, scale `B`
and `Q ≥ 0`, a `TConfig` cancelling at all sites `1..6r` with positive multipliers.  Not yet
formalized from the geometry: distinctness of the `6^{2r}` first coordinates for `B ≥ 7`
(balanced-base uniqueness), the `ℓ¹`-mass `H = 6^{K/3}`, and the surviving squared mass at
site `K+1`.  The analytic sub-Props and their conditional wiring have been stated and
proved as recorded above.  Their quantitative number-theoretic hypotheses and the
complete parameterized construction are the remaining work.

## Refutations recorded

**Hexagon mean retention is false on `ℤ/7ℤ`** (`PrimeLambertHexagonCounterexample`,
attended addendum 2026-09-14).  `MeanRetention q` says every unimodular `f : ZMod q → ℂ` has
`|𝔼 f|^6 ≤ Re H(f)` for the cyclic hexagon correlation `H`.  `not_meanRetention_seven` is
proved on the bare trust triple: witness `f(x) = ζ^{e_x}`, `ζ = e^{2πi/7}`,
`e = (0,5,3,6,5,5,4)`; residue counts `(133,0,42,63,63,42,0)` and `(13,8,7,3,3,7,8)` by kernel
`decide`; `343 H = 112 − 63c − 21c²`, `|S|² = 2 + 5c + 4c²` with `c = 2cos(2π/7)` proved to
satisfy `c³ + c² − 2c − 1 = 0` and `c > 6/5`.  The full complex
inequality is formalized, not only its real-algebra certificate.  Scope: this is the cyclic
toy average; this witness has `H > 0`, so by itself it does not refute `H(f) ≥ 0`.

**Hexagon nonnegativity is false on `ℤ/19ℤ`, even with mean `> 1/2`**
(`PrimeLambertHexagonNegative`, addendum 00:39 UTC).  `HexNonneg q` says every unimodular
`f : ZMod q → ℂ` has `Re H(f) ≥ 0`; `HexNonnegOfLargeMean q` adds the hypothesis
`|𝔼 f| > 1/2`.  Witness `f(x) = η^{e_x}`, `η = e^{2πi/8} = (1+i)√2/2` (identified exactly via
`cos(π/4) = sin(π/4) = √2/2`), `e = (0,2,4,3,3,2,1,2,4,0,2,2,4,0,2,3,2,1,1)`.  Hexagon residue
counts mod 8 `(1561,450,753,900,1092,900,753,450)` (6859 triples, kernel `decide`, ~30 s) and
exponent multiplicities `(3,3,7,3,3)` give `6859·H(f) = 469 − 450√2 < 0` (certificate
`469² < 2·450²`) and `∑ f = i(7+3√2)`, so `|𝔼 f| = (7+3√2)/19 > 1/2`.  Proved:
`not_hexNonneg_nineteen`, `not_hexNonnegOfLargeMean_nineteen`, `not_meanRetention_nineteen`
(bare trust triple).  Consequence: no universally positive lower bound `H ≥ φ(|𝔼 f|)` can hold,
and taking `|H|` or `H²` does not repair it: the addendum's IVT corollary (recorded here, not
formalized) centres the phases at `π/2` and interpolates `f_t = e^{it(θ−π/2)}`, `0 ≤ t ≤ 1`;
the mean `(7 + 6cos(tπ/4) + 6cos(tπ/2))/19 ≥ (7+3√2)/19 > 1/2` throughout, while the real
continuous `H(f_t)` runs from `1` to a negative value, so some interpolant has `H = 0` with
mean `> 1/2`.

Separately, a paper countermodel (iid base-four bits, concentration; see
`normal-numbers-disjunctivity-frontier-2026-09-14.md`) shows the growing affine signed
oscillation alone does not imply disjunctivity.  That probabilistic theorem is **not**
formalized here; it is recorded only for scope.

The draft's own negative control (the eight-for-four `B₂` seed with
directions `a=(2,2), b=(1,7)` has two atoms with first coordinate `5` and different shifts,
so the coprime transform assigns incompatible congruences) is a candidate for an exact
`decide`-checked Prop in the geometry module.
