# AUDIT 2026-09-22 — the family theorem at every `β > 2` (`isNormal_subsetLambert_of_sparseIterPow`)

Reviewer: Ren / Fable 5.1, **G4-lane Fable acting as independent reviewer of the sparse-NN lane** (Trevor's
reassignment 2026-09-22 ~19:10Z).  Read-only audit of commit dc0247e (`wip/g5-prime-subset`), source and paper
(`papers/prime-model-assembly-2026-09-22.md` Parts IV–V).  Distinct from the Collatz Fable's end-to-end review:
this note covers the *family layer* (schedule, four limits, tail, hypotheses, statement fidelity) and takes the
Part I window bound as an input whose statement I checked and whose proof I did not re-derive.

**Verdict: no defect found.  The Lean statement matches the intended mathematics; the argument reconstructs
independently (§3); `β > 2` is the exact frontier of *this majorant*, not of the mathematics (§4).**
Axioms of the theorem and of `KMT_quant₂_primeModel` / `exists_sparse_normal_unconditional` re-checked on the
host: `[propext, Classical.choice, Quot.sound]`.

## 1. Statement fidelity (what the theorem says, checked definition by definition)

`isNormal_subsetLambert_of_sparseIterPow {β : ℝ} (hβ : 2 < β) (hS : SparseIterPow P β) (hP : DivergentRecip P) :
IsNormal 4 (subsetLambert P 4)`, for any `P : ℕ → Prop` with `DecidablePred P`.

| symbol | Lean | intended |
|---|---|---|
| `subsetLambert P 4` | `∑' n, ω_P(n)/4^n`, `ω_P(n) = #(n.primeFactors.filter P)` | `∑_{p ∈ P prime} 1/(4^p − 1)` (distinct primes in `P` dividing `n`; non-prime members of `P` are ignored everywhere) ✓ |
| `IsNormal 4 x` | every nonempty digit block `w` of `fract x` in base 4 has frequency `→ 4^{−|w|}` | normality in base 4 ✓ |
| `DivergentRecip P` | `¬ Summable (fun p => if p.Prime ∧ P p then 1/p else 0)` | `∑_{p∈P} 1/p = ∞` ✓ |
| `SparseIterPow P β` | `∀ᶠ x, π_P(x)·(L₃x)^β ≤ π(x)` with `π_P(x) = #{p < x : p prime, P p}`, `π(x) = #{p < x}`, `L₃ = log log log`, real `rpow` | `π_P(x) ≤ π(x)/(log log log x)^β` eventually ✓ (same `p < x` convention on both sides; `rpow` of a negative base at tiny `x` is irrelevant under `∀ᶠ`) |

No hypothesis on `P` beyond these two.  `P` need not be a set of primes, need not have any regularity, and the
divergence may be arbitrarily slow (§3.4).

## 2. Proof architecture (as in the source)

`isNormal_subsetLambert_of_KMT_along P (JI P) (tailOK_pow …) (kmt_along_pow …)`, where the frozen wiring
(`G4WiringSparse.lean`: Weyl criterion + orbit identification + L¹ tail) needs

- `TailOK P JI`: `(1/N) ∑_{n<N} |tailB(n) − truncTailS (JI N) n| → 0`;
- `KMT_along P JI`: `∀ h ≠ 0, windowMeanS P (JI N) h N → 0`.

Schedule (`PrimeModelFamilyIterMass.lean`): `J₁N = ⌊L₃N⌋₊`, `ε_N = J₁N^{−4}`, `y_N = ⌊N^{ε_N}⌋₊`,
`JI N = min(J₁N, ⌊S_P(y_N)/8⌋₊)` with `S_P(y) = recipSumLe P y = ∑_{p ≤ y, p∈P} 1/p`.  `P` enters the schedule only
through `S_P(y_N)`; `h` never enters it.

## 3. Independent reconstruction (hand-checked constants)

Write `u = L₃N`, `v = L₄N = log u`, `J = JI N ≤ J₁ ≤ u`, `R = recipSumIoc P y_N N` (fresh mass in `(y_N, N]`).

**3.1 Parameter facts** (`epsI_facts`, `yI_facts`; all eventual).  `2u⁴ ≤ L₂N` (since `2(log t)⁴ ≤ t`), so
`ε_N ≥ 2/L₂N > 1/L₂N`; `J₁ ≥ 20 ⇒ J₁³ ≥ 8000 > 7680 ⇒ ε_N ≤ 1/(7680 J₁) ≤ 1/(7680 J)`; `ε_N < 1/2`;
`log(1/ε_N) = 4 log J₁ ≤ 4v`.  `y_N`: `ε_N log N ≥ 2` gives `N^{ε_N} ≥ e² > 2`, so `y_N ≥ N^{ε_N}/2 ≥ 2` and
`log y_N ≥ ε_N log N/2`, hence `log N/log y_N ≤ 2J₁⁴` and `L₂ y_N ≥ L₂N − log(2J₁⁴) ≥ L₂N/2`.  These give
`Regime N J ε_N` (the hypothesis of the window bound) eventually, with no exceptional range left over: the paper's
regime R1 (`ε > 1/(7680k)`) never occurs on this schedule.

**3.2 Fresh mass** (`fresh_bound_pow`, `fresh_mass_pow`, `fresh_mass_two_pow`).  For `y_N < t ≤ M+1`:
`L₃t ≥ log(L₂N/2) = u − log 2 ≥ u/2`, so `π_P(t) ≤ π(t)/(L₃t)^β ≤ (2^β/u^β) π(t)` — the domination is stated on
`(y_N, M+1]`, the correct range for `π(t) = #{p < t}` (Astra's Part II correction is implemented).  Abel
(`recipSumIoc_le_of_dominated`) gives `R(y, M) ≤ δ(∑_{y<p≤M}1/p + 1)` and the Mertens-type upper bound
`primeRecipSum_le` gives `∑_{y<p≤M} 1/p ≤ 8 + 12 log(log M/log y)`; with `log(log N/log y_N) ≤ log 2 + 4 log J₁ ≤ 1 + 4v`
this is `R ≤ (2^β/u^β)(21 + 48v)`.  At `M = 2N` the ratio is `≤ 4J₁⁴`, giving `≤ (2^β/u^β)(33 + 48v) ≤ 81·2^β u^{1−β}`
(using `v ≤ u`), which is `≤ 1` eventually **for every `β > 1`**.

**3.3 The four limits** (`kmt_along_pow` consumes `window_bound_regime`, whose statement is
`‖W‖ ≤ 24k√(log(1/ε))√(2R) + e^{3k} e^{−S_P(y)} + (2k² + 2k e^{20} + 4 + 2·4^k) e^{−1/(8k²ε)}` under `Regime` and
`NontrivialWindow k h`):

- Transfer: `24J·√(4v)·√(2·2^β(21+48v)/u^β) ≤ 24u·√(8v·2^β·69v)/u^{β/2} = 24√(552·2^β)·v·u^{1−β/2}`
  (`21 + 48v ≤ 69v` for `v ≥ 1`; `8·69 = 552`).  `→ 0 ⟺ β > 2`.  At `β = 3` this is `1595 v/√u`, the paper's `1600`.
- Old mass: `8J ≤ S_P(y_N)` by construction, so `e^{3J − S} ≤ e^{−5S/8} → 0` because `S_P(y_N) → ∞` (divergence +
  `y_N → ∞`).  **No rate of divergence is used.**
- Sieve: `1/(8J²ε_N) = J₁⁴/(8J²) ≥ J₁²/8`; coefficient `≤ e^{22}·4^{J₁}` for `J₁ ≥ 40`; `e^{22 + J₁ log 4 − J₁²/8} ≤ e^{−J₁}`
  once `J₁²/8 ≥ J₁(1 + log 4) + 22`, true at `J₁ = 40` (`200 ≥ 117`).  `→ 0`.
- Nontrivial window: site `j = |h| + 1 ≤ J` eventually (`J → ∞`), and `0 < |h|/4^{|h|+1} < 1`, so `h/4^j ∉ ℤ`.  This is
  the only place `h` enters; the schedule is `h`-free, so `KMT_along` (`∀ h ≠ 0`, one limit each) is exactly what is
  delivered.  No uniformity in `h` is claimed or needed.

**3.4 Tail** (`tail_pow` via the frozen `tail_error_L1`: `≤ (S_P(2N) + 5J + 12)/4^J`).  Two branches of the `min`:
- `J = J₁`: `J ≥ u − 1 ⇒ 4^J ≥ (L₂N)^{log 4}/4`; numerator `≤ 12 L₂(2N) + 21 + 5u + 12 ≤ 30 L₂N` by the universal
  crude bound `S_P(2N) ≤ ∑_{p≤2N}1/p ≤ 12L₂(2N) + 21`; ratio `≤ 120 (L₂N)^{1 − log 4} → 0` since `log 4 > 1`.
  No density input at all in this branch.
- `J = ⌊S_P(y_N)/8⌋₊`: `S_P(y_N) < 8J + 8` and `S_P(2N) = S_P(y_N) + R(y_N, 2N) ≤ 8J + 9`; numerator `≤ 13J + 21`;
  ratio `→ 0` as `J → ∞`.  This branch is where **arbitrarily slow divergence** lives: the fresh mass through `2N`
  is `≤ 1`, so the accumulated mass can grow as slowly as it likes and `4^J` still wins.  `J → ∞` needs only
  `S_P(y_N) → ∞`.

**3.5 The `β` bookkeeping.**  `β > 1` is used twice (`fresh_mass_two_pow`, hence `tail_pow`, `tailOK_pow`);
`β > 2` once (`term_one_pow`); `β ≥ 0` for `rpow` monotonicity in `fresh_bound_pow`.  The theorem's single
hypothesis `2 < β` covers all three.  `SparseIterPow P 3 ↔ SparseIter3 P` is proved, so Part IV is a special case.

## 4. What the threshold means, and what it does not

- `β > 2` is exactly where the *coarse* transfer majorant `24k√(log 1/ε)√(2R)` vanishes on this schedule: the
  product `u · √v · √(v/u^β)` is `v·u^{1−β/2}`.  At `β = 2` it is `≍ L₄N → ∞`.  So Part V's "exact frontier of the
  schedule family" is correct **for that majorant**.
- It is **not** a frontier of the mathematics.  Astra's phase-weighted transfer (mailbox `20260922T190221Z-astra-…`,
  refereed correct by the sparse-NN Fable at `190445Z`) removes the factor `k` for fixed `h`:
  `‖W − W_y‖ ≤ (4π|h|/3)(2R + k/x)`, and with it every `β > 0`, and the little-o hypothesis `(π_P/π)·L₄ → 0`,
  follow with the same schedule (Part VI, in progress at the time of this audit).  The `β > 2` theorem stands as a
  correct, weaker corollary.

## 5. Inputs taken as given (statements checked, proofs not re-derived here)

`window_bound_regime` (Part I core: phase factorisation, residue/CRT factor, Brun lower/upper counts, model
transfer), `tail_error_L1`, `isNormal_subsetLambert_of_KMT_along` (Weyl + orbit), `recipSumIoc_le_of_dominated`
(Abel), `primeRecipSum_le` (Mertens upper, dyadic blocks), `recipSumLe_le_crude`.  All are sorry-free Lean theorems
on the branch; the axiom print covers them.  The Collatz Fable's end-to-end review is the place for Part I.

## 6. Minor observations (no action required)

- Real `β`: `SparseIterPow` is stated with `Real.rpow`; for `β ∈ ℕ` this agrees with `pow` (`sparseIterPow_three_iff`).
- `π_P` counts `p < x`, `recipSumLe` sums `p ≤ y`: consistent throughout because every comparison is routed through
  the `(y, M+1]` domination, never through an equality of the two conventions.
- The paper's Part IV "density `≤ 8/(L₃N)³`" is the `β = 3` instance of `2^β/u^β` ✓.
- Nothing in the proof depends on `2 ∈ P` or on `P` avoiding small primes; small primes sit in the residue factor of
  Part I (per Astra's Part I audit).

## Addendum A (same day, ~19:20Z): the superseding theorem at a86a0d8, `isNormal_subsetLambert_of_sparseL4o`

Audited with the same method (read-only; `PrimeModelKMTFixedH.lean`, `PrimeModelFamilyL4.lean`).  **No defect.**

**A.1 Phase-weighted transfer** (`windowMean_sub_windowMeanLe_le_h`).  Per site, `‖z_j^{a+c} − z_j^a‖ = ‖z_j^c − 1‖ ≤ c‖z_j − 1‖`
(`norm_pow_sub_one_le`, telescoping) and `‖z_j − 1‖ = ‖e(h/4^{j+1}) − e(0)‖ ≤ 4π|h|/4^{j+1}` (`norm_ePhase_sub`, Lipschitz `4π`);
the window product telescopes (`norm_prod_sub_prod_le`, unit-modulus factors) with `c = ω_{>y}(n+j+1)`; the per-shift count
`∑_{n<x} ω_{>y}(n+j+1) ≤ 2x·recipSumIoc S y x + k` (`sum_omegaGt_shift_le`: primes in `(y, x]` hit `≤ x/p + 1 ≤ 2x/p` values,
primes in `(x, x+k]` hit one each, at most `k` of them); `∑_{j<k} 4^{−(j+1)} ≤ 1/3`.  Result
`‖W − W_y‖ ≤ (4π|h|/3)(2R + k/x)`, **no factor `k` on the fresh mass**, `h` fixed.  Exactly Astra's lemma
(`20260922T190221Z`, `190418Z`).  `window_bound_regime_h` swaps only this term into `window_bound_regime`; the model,
sieve and old-mass terms are untouched.

**A.2 Hypothesis and domination.**  `SparseL4o P := (π_P(x)/π(x))·L₄x → 0` (real quotient; `π(x) ≥ 1` for `x ≥ 3`).
For `η > 0`: eventually `π_P(t) < η π(t)/L₄t` for `t ≥ x₀`; on `(y_N, M+1]`, `L₄t ≥ L₄N/2` (`L4_half_le`: `L₃t ≥ L₃N − 1`
and `log(u − 1) ≥ log u − 1` for `u ≥ 2.7`), so `π_P(t) ≤ (2η/L₄N) π(t)`, and Abel gives
`R(y_N, M) ≤ (2η/L₄N)(9 + 12 log(log M/log y_N))`.

**A.3 Limits** (`v = L₄N ≥ 1`).  `R(y_N, N) ≤ (2η/v)(21 + 48v) = 42η/v + 96η ≤ 138η`; with `η = ε/200` this is `< ε`
(`fresh_mass_L4o`).  `R(y_N, 2N) ≤ (2η/v)(33 + 48v) ≤ 162η`; with `η = 1/400` this is `≤ 0.405 < 1` (`fresh_mass_two_L4o`),
which is all the mass-limited tail branch needs.  Transfer `(4π|h|/3)(2R + J/N) → 0` since `J ≤ L₃N ≤ log N` and
`log N/N → 0`.  Old-mass, sieve, regime, nontrivial-window and the tail's cap branch are reused verbatim from Parts
IV–V (`term_two_iter3`, `term_three_iter3`, `regime_iter3`, `tail` with `fresh_mass_two_L4o`).  `h` enters only through
the coefficient `4π|h|/3` and `NontrivialWindow`, both fine for the fixed-`h` `KMT_along`.

**A.4 Subsumption.**  `sparseL4o_of_sparseIterPow (β > 0)`: `(π_P/π)·L₄ ≤ L₄/L₃^β = log u/u^β → 0` ✓.  So the `β > 2`
theorem of the main audit is a corollary, and so is every `π_P ≤ π/(L₄)^γ`, `γ > 1`, and `π/(L₄ log L₄)`.

**A.5 What remains the barrier of this route** (agreeing with Astra's `190915Z` construction, refereed by the sparse-NN
Fable at `191023Z`): density `≍ 1/L₄`.  On the schedule `ε = J₁^{−4}`, `log(1/ε) ≈ 4L₄N`, so `R ≍ (density)·L₄N` is bounded
below when `π_P/π ≍ 1/L₄`; the tail and sieve majorants pin `ε` to this window (`J ≥ c log t` from the tail, `J²ε → 0` from
the sieve), so no schedule move helps.  The abstract consumer `FreshMassZero P := recipSumIoc P (yI N) (2N) → 0`
(Astra `190707Z`, in progress as `PrimeModelFamilyConsumer.lean`) is the right statement of what the route proves.

## Addendum B (~19:30Z): axiom sweep over the headline declarations — verification gap closed

Trevor's instruction: close the verification gap with the existing audit mechanism, no further mathematical review.
Tool: `lean-axiom-gate --exact` (allows ONLY `propext`, `Classical.choice`, `Quot.sound`), imports
`PrimeModelKMTFixedH`, `PrimeModelFamilyL4`, `PrimeModelFamilyConsumer`, at HEAD `bbe447f` of `wip/g5-prime-subset`
(contains the a86a0d8 family and the ab71135 consumer).  Declaration list and verbatim output:
**`AUDIT-2026-09-22-axiom-sweep.txt`** (this repo, root).  Result: **14/14 ✓**, every target exactly
`[Classical.choice, Quot.sound, propext]`, exit 0.  Targets (all under `NormalNumbers.PrimeModel`):
`KMT.window_bound_regime`, `KMT.window_bound_regime_h`, `KMT.windowMean_sub_windowMeanLe_le_h`,
`KMT.KMT_quant₂_primeModel`, `KMT.exists_sparse_normal_unconditional`, `Family.isNormal_subsetLambert_of_sparse`,
`FamilySharp.isNormal_subsetLambert_of_sparseIter`, `FamilyIter.isNormal_subsetLambert_of_sparseIter3`,
`FamilyIter.sparseIterPow_three_iff`, `FamilyIter.isNormal_subsetLambert_of_sparseIterPow`,
`FamilyIter.sparseL4o_of_sparseIterPow`, `FamilyIter.isNormal_subsetLambert_of_sparseL4o`,
`FamilyIter.isNormal_subsetLambert_of_freshMassZero`, `FamilyIter.freshMassZero_of_sparseL4o`.
Operational note for the next sweep: the tool's default import set includes the second lib target `Comparator`, which is
not built, so every target reports "NO axiom info" unless modules are passed with `--import`; and in zsh a
space-separated target list must be expanded with `${=T}`.

Closing state.  Astra's `20260922T192103Z` answered the sole open hypothesis question (no hidden hypothesis on `P`;
`Regime` + `NontrivialWindow` suffice; `k ≤ y` from `k_le_yOf`).  The substantive outcome of the lane is the family
theorem and its independently checked proof; the `1/L₄` example limits these majorants, not normality.
