# HANDOFF elliott 2026-09-25 laps 92–94 — the crux's Archimedean input was FALSE; refuted, repaired, and the small-shift band PROVED

Branch `wip/elliott-port`, HEAD `482e109`, working tree **clean**.
**Green means BOTH targets** (see the trap below):
`lake build` → 9257 jobs · `lake build NormalNumbers.ElliottAxiomAudit` → 9675 jobs.
Never `lake exe cache get`.  Never edit `.lake/packages/lean-proofs-latest/`.
**`DIRECTION.md` CURRENT DIRECTIVE governs — read it first.  Do NOT edit it** (altitude laps own it;
lap 92 was one and set it).

## The three laps in one line

Laps 85–91 reduced the downstream consumer to two named classical `Prop`s; **one of them was
false**, so the reduction was vacuous.  Lap 92 refuted it in-kernel and re-decomposed, laps 93–94
*proved* the band the repair opened up.  The consumer now rests on two honest inputs.

## State of the Elliott campaign

* **Headline: DONE, untouched.**  `ElliottGeneral.nonasymptoticLogElliott` (lap 83) and the
  genuinely multiplicative `…nonasymptoticLogElliottMult` (lap 84) are both proved and print
  `[propext, Classical.choice, Quot.sound]`.
* **`src/` Elliott scope: zero `sorry`.**  Every open obligation is a named `Prop` taken as a
  hypothesis — which is why lap 92's discovery could be a *theorem* rather than a retraction.
* **Consumer (DIRECTION item 4): live, on exactly two inputs.**

```
'NormalNumbers.ElliottSmallShift.twoPointElliottLog_of_archimedean_and_primeDensity'
    : [propext, Classical.choice, Quot.sound]          ← the live headline of the consumer
'NormalNumbers.ElliottArchimedeanRefuted.not_archimedeanCorrelationBound' : trust triple
```

## What landed, laps 92–94 (3 new modules, all sorry-free, all trust triple)

| file | content |
|---|---|
| `ElliottArchimedeanRefuted.lean` | `not_archimedeanCorrelationBound {A} (0<A) {η} (0<η) : ¬ ArchimedeanCorrelationBound A η` |
| `ElliottTwistRepair.lean` | `AlmostRealTwist`, the repaired dichotomy, the re-proved consumer, `twistAlmostRealDichotomy_of_old` |
| `ElliottSmallShift.lean` | two-sided Mertens, `AlmostRealTwistProp`, `ReductionScale`, `exists_reductionScale`, the assembly, the two payoffs |

**The refutation (lap 92).**  Witness `v = 2/log X`: it satisfies the hypothesis `1 < |v| log X`
exactly (`= 2`), but then `|v| log p ≤ 2` for *every* `p ≤ X`, so with `cos θ ≥ 1 − θ²/2`,
`(log p)² ≤ (log X)(log p)` and Mertens I, `Re ∑_{p≤X}p^{-iv}/p ≥ M(X) − 2 − 2C`, beating
`(1−η)M(X)`.  The defect is the *frequency range* (`1/log X` instead of `(log X)^{-1+ε}`), not the
estimate.  ⛔ `ElliottCharRigidity.twoPointElliottLog_of_archimedean_and_density` is **vacuous** —
do not build on it, do not restate input (c).

**The repair (lap 92).**  The consumer never needed `C ≈ M(X)`, only `C` close to a real
`R ∈ [0,M(X)]`, because rotating by `ζ = e(u) ≠ 1` already costs `(1 − max(Re ζ,0))·M(X)`.  That is
the one-lemma core, `re_phase_mul_twistCorr_le`.

**The band, proved (laps 93–94).**  Two-sided Mertens
(`Erdos67b.PrimeEstimates.abs_primeReciprocals_sub_log_log_le`, found by the mandated survey) turns
the band into **scale reduction**: the Archimedean twist is not a bounded perturbation of `1` across
`[2,X]` but *is* across `[2,Y]` with `log Y = 1/|t|`, and `[2,Y]` still carries all but `ρ·M(X)` of
the prime mass.  Run the old proved argument at scale `Y`, transport to `X` at the cost of the
discarded mass; the conclusion weakens from `O(1)`-close to `ρ·M(X)`-close, which is all the
consumer needs.  `exists_reductionScale` then supplies the scale on the whole band.

## The two remaining inputs — and they are consistent

| input | statement | depth |
|---|---|---|
| **(c′)** `∀ A r, 0<r → ∃ η>0, ArchimedeanCorrelationBoundAbove A η (smallShiftThreshold r)` | `T X < \|v\| ≤ A²X → ‖archCorr v X‖ ≤ (1−η)M(X)` | 🟡 the only zero-free-region site |
| **(d1)** `ElliottCharRigidity.PrimeDensityAP A` | `c·M(X) − B ≤ ∑_{p≤X, p≡a(q)} 1/p` on unit classes | 🟡 Mertens in progressions; **no zero-free region** |

**EA-1 boundary check, done and passing**: `smallShiftThreshold ρ X ≈ (log X)^{-1+ρ/2}`, where the
true size of `archCorr` is `≈ (1−ρ/2)M(X)` — so (c′) holds at its own boundary with `η ≈ ρ/2`.
That is exactly what the refuted lap-91 pair failed, and it is why (c′) is stated with `η` allowed
to depend on the threshold scale `r`.

## What the next lap does

**(c′), the long pole.**  Do NOT expect to clear it; narrow it.  Before writing Lean, spend the
paper probe recorded in `PENDING_WORK.md`:

> if `∑_{p≤X}(1 − Re(γ̄ p^{-iv}))/p ≤ ηM` then `n ↦ n^{iv}` is pretentious to the constant `γ`,
> which should force `|∑_{n≤X} n^{iv}| ≫_η X`; but van der Corput on dyadic blocks gives
> `|∑_{n≤X} n^{iv}| ≪ X^{1/2} log X` for `1 ≪ |v| ≪ X²` (the second derivative of `v log u` is
> `v/u² ≍ X/N²` on `n ≍ N`).

If that closes, (c′) is **unconditional** on `1 ≪ |v| ≤ A²X` — the entire polynomial-height range,
replacing the zero-free region outright — and only `T X ≤ |v| ≲ 1` is left, which Mertens-with-error
handles.  **The uncertain half is the mean-value lower bound** ("pretentious to a constant ⟹ mean
`≫ X`", Halász/Wirsing territory): probe *that* first, since it is the route-decisive step.

(d1) `PrimeDensityAP` is the softer alternative target if (c′) stalls: Siegel–Walfisz and the
Dirichlet L-machinery are already in `BoundedGaps`, and `ArithmeticFunction.vonMangoldt.residueClass`
showed up in `PrimeMertens.lean` as a promising handle.

## Traps recorded these laps

* **The Elliott chain is NOT reachable from `src/NormalNumbers.lean`, and must not be wired in.**
  Adding `import NormalNumbers.ElliottAxiomAudit` there fails:
  `import PrimeNumberTheoremAnd.Sobolev failed, environment already contains 'CS.deriv' from
  PNTPort.Sobolev`.  So a bare `lake build` does **not** check the campaign — always run
  `lake build NormalNumbers.ElliottAxiomAudit` too.  (Tried and reverted, lap 92.)
* `Real.one_sub_sq_div_two_le_cos : 1 − x^2/2 ≤ cos x` exists (Trigonometric/Bounds).
* `Complex.exp_ofReal_mul_I_re : (exp (↑x * I)).re = cos x` — first rewrite `I * t * L` into
  `↑(t*L) * I` by `push_cast; ring`.
* `Complex.div_ofReal_re` needs the denominator as `((p : ℝ) : ℂ)`, not `(p : ℂ)`.
* `linarith` treats `η * M` and `M * η` as **different atoms**; after `div_le_iff₀` the product
  comes out in the other order.  Multiply the hypothesis by hand rather than rewriting with
  `div_add'`.
* A bare `field_simp` can close a goal outright, making a following `ring` error with "No goals".
* `Nat.sub_one_lt_floor (a : R) : a - 1 < ⌊a⌋₊` is the floor lower bound; `Nat.le_floor` lifts
  `(2:ℝ) ≤ z` to `2 ≤ ⌊z⌋₊`.
* When a new Elliott module needs a *sibling* module's names (`ElliottCharRigidity.…`), add the
  import — the namespace resolves only if the file is actually imported, and the error reads as a
  plain "Unknown identifier".

## Doc map

`DIRECTION.md` CURRENT DIRECTIVE (lap 92, binding) · `STATUS.md` (refreshed lap 92) ·
`PENDING_WORK.md` top section (the live attack paths, updated through lap 94) ·
`ROUTE-ESCALATION-2026-09-25-archimedean.md` (the refutation + repair in full) ·
`HANDOFF-elliott-2026-09-25-lap92.md` (with lap 93/94 addenda) · audit surface
`src/NormalNumbers/ElliottAxiomAudit.lean`.
