# HANDOFF c3-mrt 2026-09-25 lap60 — DEEP REFLECTION: ROUTE ESCALATION + the decisive probe lands

**Read first:** `DIRECTION.md` → CURRENT DIRECTIVE (it OUTRANKS this file) and
`ROUTE-ESCALATION-2026-09-25-c3mrt.md`.  Detail: `PENDING_WORK.md` → "Reflection — 2026-09-25".

## BUILD HYGIENE

    lake build                                 # 9257 jobs  (root)
    lake build NormalNumbers.C3MrtProgChase    # 8990 jobs  (old chain tip — still green)
    lake build NormalNumbers.C3MrtMultElliott  # 8914 jobs  ← NEW, the re-anchored route

`C3MrtMultElliott` branches off `C3MrtKPoint`; it is not yet in the `ProgChase` chain, so build
it explicitly until a consumer joins them.

## The crux

`weylLambertTwist_holds` (`SwingC3Leaf.lean`) unchanged — still the only campaign `sorry` in
`src/`.  Nothing renamed, weakened or deleted; this lap is pure addition plus documentation.

## ROUTE VERDICT: **ESCALATE** — re-anchor on merely-multiplicative Elliott / TT Thm 3.1

Three findings, each checked against a primary source rather than a handoff.

**R1 (compiler).**  `Erdos67b.IsMultiplicativeOnPositiveInt` (`Erdos67b/LogElliott.lean:329`) has
**no coprimality clause** — it is *complete* multiplicativity.  `ζ^ω` fails it, which is why lap 4
built the `z^ω = z^Ω ⋆ g` powerful-divisor bridge.  `prod_le_lcm_mul_pow`'s `K^{K²}`, the lap-40
budget repair and the headline decay class `exp(−C(log log log N)⁴)` are **all** downstream of
that one artificial hypothesis.  Elliott's conjecture, and Tao's Theorem 1.3 that the dependency
is formalising, ask only for *multiplicative*.

**R2 (source).**  Tao–Teräväinen arXiv 2512.01739 Thm 3.1
(`papers/tao-teravainen-2025-quantitative-correlations.txt:1566`) beats the current anchor on four
axes at once — merely multiplicative, **natural** (dyadic) averaging, `L^{-c}` saving with
`L ≤ log X`, and progressions `1_{n≡b (W)}` with `W ≤ L^c` built in — at the price of an
exceptional set of scales of log-density `≪ L^{-c}`.  Also confirmed:
`primeLambertAtBase b = ∑' n, ω(n)/bⁿ` is **verbatim** the constant of their Theorem 1.3
(Erdős #69).  And verbatim from the same paper (`:2997`): a triple-correlation version of Thm 3.1
"does not appear to be within current technology"; removing the exceptional set is out of reach
"for similar reasons".

**R3 (refuted — do not re-chase).**  A two-point-only proof of the leaf along TT §5's lines.
Their variance shrinkage `O(2^{-K}/p)` is bought with the *rationality* hypothesis (the dilation
identity `ω(n+ph) = ω(n/p+h) + 1 − 1_{p²|n+ph}` at `2^K` distinct primes `p_ε`).  Van der Corput
does not substitute — it makes `X_p` mean-zero but doubles the point count and leaves
`Var(X_p) ≍ c_h/p`.  A direct moment expansion of `e(h∑_{p>Y}w_p)` against the small-prime period
dies at the level-of-distribution barrier (`∑_{p>Y} p·E[w_p] ≍ N/log N`).

Trigger tell (b) had fired: finishability 28 % → 22 % → 22 % → 20 % across three session wraps
with no route change.  No 🚦 trigger had ever been registered for the C3 chapter; **C3-T1/T2/T3
are now registered** in `DIRECTION.md`.

## What landed in Lean — `src/NormalNumbers/C3MrtMultElliott.lean` (10 declarations, sorry-free)

* `IsCoprimeMultiplicativeInt` — Elliott's actual hypothesis class.
  `isCoprimeMultiplicativeInt_of_completely`: the dependency's predicate implies it, so
  **nothing is weakened** — `KPointLogElliottMult` is a *strengthening*.
* `zOmegaInt`, `omegaNat_mul_coprime`, `isCoprimeMultiplicativeInt_zOmegaInt`,
  `norm_zOmegaInt_le_one` — `ζ^ω` is an admissible input.
* `pretentiousDistSqToTwist_zOmegaInt_eq` — **the certificate transfers verbatim.**  The
  pretentious distance is a sum over *primes* and `ω(p) = Ω(p) = 1`, so `ζ^ω` and `ζ^Ω` are at
  literally the same distance from every twist.  Hence `nonPretentious_zOmega`: laps 18–21's
  archimedean certificate for `ζ^ω`, at **zero** extra analytic cost, on the same VK input.
* `KPointLogElliottMult K`, `kPointLogElliott_of_mult`.
* **`nondegenerateForms_class`** — the forms `M₀·n + (r+i+1)` are pairwise nondegenerate with
  determinant `M₀(j−i)`, for *any* `M₀ > 0`.
* **`kPointLogCorrelation_zOmega`** — the decisive identity: the class-restricted `K`-point sum in
  the progression variable **is** `kPointLogCorrelation` of `zOmegaInt` along those forms.
* **`class_window_bound_of_mult`** — the payoff, `[propext, Classical.choice, Quot.sound]`:
  on `KPointLogElliottMult K` the `ε·log W` window bound holds for
  `∑_{n∈window} harmonicWeight n · ∏_i z_i^{ω(M₀n + r+i+1)}` with **no divisor tuples, no
  truncation, no tuple mass, no lcm, and no `K^{K²}`** — bypassing
  `C3MrtOmegaBridge → MultiForms → MultiMass → MultiTupleMass → MultiTrunc → MultiInner →
  ProgForms → ProgTrunc → ProgInner` entirely.  Trigger C3-T2 is on course.

## NEXT — resume here

1. **`progression_log_rung_class_mult`** — transcribe `multi_correlation_of_uniform_rung_prog`'s
   ε-chase (`C3MrtProgChase.lean`) against `class_window_bound_of_mult`.  The old chase has to
   carry `d`-tuples, `progLcm`, `sqfWMass` and `K^{K²}` through `M`; the new one carries **none**
   of them, so `M = 1` and the `εr ↦ ε/2` bookkeeping collapses.  Output: lap 59's conclusion on
   the merely-multiplicative anchor, with no budget.
2. Then the weight bridge (`(m+1)⁻¹` vs `(n+1)⁻¹`, spelled out in `-lap59.md`) — still needed, and
   now it is the *only* bookkeeping between the anchor and `ProgressionLogRung`.
3. Then `TwoPointNaturalCorrelation` — TT Thm 3.1(ii) stated faithfully (natural dyadic averaging,
   `L^{-c}`, `W ≤ L^c`, exceptional set of scales) — and the `D = 2` **natural-density** rung from
   it, which discharges `LogToNaturalCorrelation` at `K = 2`.

## Still refuted — DO NOT RETRY

Everything in `-session-wrap-laps40-42.md`, `-laps43-51.md`, `-laps52-59.md`.  Added this lap:
finding **R3** above.  Also: do NOT spend laps on brick 4b as stated, on the quantitative
`η`-restatement, or on sharpening `prod_le_lcm_mul_pow` — all three perfect the *old* anchor.

## Confidence

* leaf TRUE ≈ 97 % (unchanged).
* leaf PROVABLE with known techniques ≈ **8 %** — sharply *down* from 20 %, and this is the
  honest number, not a mood.  TT say in print that three-point correlations are out of reach; the
  route provably needs *unbounded* order (truncating at depth `K` leaves residual s.d.
  `≍ b^{-K}√(log log N)`, re-derived independently this lap).  The previous 20–28 % was inflated
  by treating the `K^{K²}`/decay-class gap as "the distance to the literature" when it was an
  artefact of the anchor.
* **ledger QUALITY**, which is the ratified deliverable, is sharply *up*: the `D = 2` layer is now
  on a path to a **published** theorem in natural density, and the two generational items are
  named, quoted and isolated.
