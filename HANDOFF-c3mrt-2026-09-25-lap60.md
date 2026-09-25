# HANDOFF c3-mrt 2026-09-25 lap60 — DEEP REFLECTION: ROUTE ESCALATION + the decisive probe lands

**Read first:** `DIRECTION.md` → CURRENT DIRECTIVE (it OUTRANKS this file) and
`ROUTE-ESCALATION-2026-09-25-c3mrt.md`.  Detail: `PENDING_WORK.md` → "Reflection — 2026-09-25".

## BUILD HYGIENE

    lake build                                 # 9257 jobs  (root)
    lake build NormalNumbers.C3MrtProgChase    # 8990 jobs  (old chain tip — still green)
    lake build NormalNumbers.C3MrtMultElliott  # 8914 jobs  ← NEW, the re-anchored route
    lake build NormalNumbers.C3MrtMultRung     # 8927 jobs  ← NEW TIP of that route

`C3MrtMultElliott` branches off `C3MrtKPoint`; `C3MrtMultRung` imports it and `C3MrtMultiRung`.
Neither is in the `ProgChase` chain, so build the new tip explicitly until a consumer joins them.

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

**Exactly ONE brick stands between the new anchor and lap 59's conclusion.**
`progression_log_rung_class_mult`, from `rung_class_of_named_inputs_mult`:

1. **Reindex.**  `n ≡ r (mod M₀)`, `n < N` ↔ `n = M₀·j + r`, `j < (N − r + M₀ − 1)/M₀`; then
   `n + i + 1 = M₀·j + (r+i+1)`, which is *verbatim* the rung's argument.  `class_sum_reindex`
   (lap 53) already does this bookkeeping.
2. **The weight bridge** (old brick 4b, unchanged in shape, and now the ONLY bookkeeping item).
   The rung carries `Erdos67b.harmonicWeight j = 1/j`; the target carries
   `harmW n = (M₀ j + r + 1)⁻¹`.  The difference
   `(M₀ j + r + 1)⁻¹ − M₀⁻¹ j⁻¹ = (M₀ − r − 1)/(M₀ j (M₀ j + r + 1))` is absolutely
   `≤ (M₀ + r)/(M₀ j²)`, and `sum_inv_sq_le` (`C3MrtRungTwo:372`) is already in the repo.
   `ε ↦ ε·M₀` absorbs the factor `M₀⁻¹`.
3. **Choose `m`.**  `m = Nat.log A ((N − r)/M₀)`, exactly as in
   `multi_correlation_of_uniform_rung_prog`'s `hrung` step (`C3MrtProgChase.lean:88–125`), giving
   `m · log A ≤ log N`.  Note the old chase also has to carry `M = K^{K²}·∏ sqfWMass` through the
   `ε/2` split — here `M = 1`, so that whole half collapses.

Then, and only then:

4. **`TwoPointNaturalCorrelation`** — TT Thm 3.1(ii) stated faithfully (1-bounded multiplicative,
   natural dyadic averaging `∑_{N<n≤2N}`, `L^{-c}` saving with `1 ≤ L ≤ log X`, progression
   `1_{n≡b (W)}` with `W ≤ L^c`, exceptional set `E ⊂ [√X,X]` of log-density `≪ L^{-c}`), and the
   `D = 2` **natural-density** rung from it — which is what discharges `LogToNaturalCorrelation`
   at `K = 2` and converts that ledger row from 🔴 to 🟡.

## And the rung — `src/NormalNumbers/C3MrtMultRung.lean` (lap 60b, 2 declarations, sorry-free)

* `initial_segment_bound_of_kElliottMult` — lap 50's window decomposition transcribed onto
  `KPointLogElliottMult`.  The decomposition never looked at *which* multiplicativity the family
  had, so only the hypothesis changes; the proof is otherwise verbatim.
* **`rung_class_of_named_inputs_mult`** — `[propext, Classical.choice, Quot.sound]`.  On
  `KPointLogElliottMult K` + `TwistedPrimeSumSavingAllLevels` alone:

      ∃ A₀ ≥ 2, ∀ A ≥ A₀, ∃ i₀, ∀ m ≥ i₀,
        ‖∑_{j ∈ Ioc 0 (A^m)} (1/j) ∏_{i<K} z_i^{ω(M₀·j + r+i+1)}‖
          ≤ (1 + log(A^{i₀})) + m·(ε log A).

  This ONE statement replaces **both** `rung_multi_of_named_inputs` (lap 51) **and**
  `rung_multi_uniform_prog` (lap 59).  With no divisor tuples there is nothing to truncate and
  no `exists_common_threshold` to run (the old route runs it twice, over the finite set of
  admissible `(d, a)` pairs), so the single `A` and the single `i₀` come out directly.

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
