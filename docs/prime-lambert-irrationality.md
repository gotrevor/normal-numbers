# Prime Lambert irrationality: the compressed-cancellation argument in Lean

Bounded campaign (brief 2026-09-14).  Target constant

    G = primeLambert = ∑_{n≥1} ω(n)/2^n  ( = ∑_p 1/(2^p − 1) ),

`ω = ArithmeticFunction.cardDistinctFactors`.  Irrationality is already known
(Tao–Teräväinen, arXiv:2512.01739v2, Thm 1.3); that theorem is **not** cited as an axiom.
This is a formalization of the candidate *elementary* compressed-cancellation argument.
No novelty claim.  Headline `irrational_primeLambert` is **sorry-gated**; see "Status".

## Modules (owned footprint)

| module | content | status |
|---|---|---|
| `PrimeLambertDefs` | `primeLambert`, summability, `tailT k = 2^k G − tailInt k`, `rational_tail_int`; exact transport `ω(dm) + overlap d m = ω m + ω d`, `dilatedTail_eq`, exact periodicity `transportCorr_congr` | proved, axiom-clean |
| `PrimeLambertConfig` | transported configurations `TConfig = (ℕ×ℤ) →₀ ℤ`, `CancelsAt c j` (pushforward along `j·d − s` vanishes), `phaseSum c K n`, **Theorem A** `phaseSum_sub_int` | proved, axiom-clean |
| `PrimeLambertGeometry` | group ring `ℤ[ℤ×ℤ]`, `Cancels`, `edge`, `hexagon` (cancels at its triple; six-atom form `hexagon_eq_six`), `dilate`, `hexTensor r B` cancels at all `1..6r` (`hexTensor_cancels`), coprime transform `toConfig` preserving cancellation (`cancelsAt_toConfig`), positivity, pairwise coprimality (`transform_coprime`), assembly `exists_tconfig_cancelling` | proved, axiom-clean |
| `PrimeLambertAnalytic` | finite tail `truncPhase`, per-prime parts `primePart`, exact additive split `truncPhase_split` (bad/small/large), the four analytic Props `TailTruncation`, `LargePrimeNegligible`, `BadPrimeFrozen`, `SmallPrimeDecay`, proved wiring `phaseOscillation_of_chain`, `ChainExists → Irrational primeLambert` (`irrational_of_chainExists`) | wiring proved, axiom-clean; the four Props open |
| `PrimeLambertOscillation` | `e`, `ProgressionFamily`, `phaseAverage`, `PhaseOscillation` (draft eq. (5)), `norm_phaseAverage_eq_one`, `irrational_of_phaseOscillation` | proved, axiom-clean; `phaseOscillation` is the single disclosed `sorry` |

Build: `lake build NormalNumbers.PrimeLambertOscillation` (targeted; the root module is
host-owned and does not import these yet).

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

`phaseOscillation_of_chain` proves that these four imply `PhaseOscillation` (Lipschitz bound
`‖e(x)−1‖ ≤ 4π\|x\|`, unimodular constant factor for the frozen class).  `SmallPrimeDecay` is
the deep step; its intended proof (independent model, variance `V → ∞`, CRT moment comparison
to order `M`, even-moment Taylor transfer) is not yet decomposed into Lean Props.


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
site `K+1`.  Next: (b) state the analytic sub-Props as separate `def … : Prop` with explicit
quantifiers, and a wiring `→ PhaseOscillation`.

## Refutations recorded

**Hexagon mean retention is false on `ℤ/7ℤ`** (`PrimeLambertHexagonCounterexample`,
attended addendum 2026-09-14).  `MeanRetention q` says every unimodular `f : ZMod q → ℂ` has
`|𝔼 f|^6 ≤ Re H(f)` for the cyclic hexagon correlation `H`.  `not_meanRetention_seven` is
proved on the bare trust triple: witness `f(x) = ζ^{e_x}`, `ζ = e^{2πi/7}`,
`e = (0,5,3,6,5,5,4)`; residue counts `(133,0,42,63,63,42,0)` and `(13,8,7,3,3,7,8)` by kernel
`decide`; `343 H = 112 − 63c − 21c²`, `|S|² = 2 + 5c + 4c²` with `c = 2cos(2π/7)` proved to
satisfy `c³ + c² − 2c − 1 = 0` and `c > 6/5` (from `2π/7 < π/3`).  The full complex
inequality is formalized, not only its real-algebra certificate.  Scope: this is the cyclic
toy average; it does not refute `H(f) ≥ 0` (the witness has `H > 0`), and the `C₁₉` negative-`H`
witness of the audit is not formalized.

Separately, a paper countermodel (iid base-four bits, concentration; see
`normal-numbers-disjunctivity-frontier-2026-09-14.md`) shows the growing affine signed
oscillation alone does not imply disjunctivity.  That probabilistic theorem is **not**
formalized here; it is recorded only for scope.

The draft's own negative control (the eight-for-four `B₂` seed with
directions `a=(2,2), b=(1,7)` has two atoms with first coordinate `5` and different shifts,
so the coprime transform assigns incompatible congruences) is a candidate for an exact
`decide`-checked Prop in the geometry module.
