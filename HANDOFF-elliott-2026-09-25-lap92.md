# HANDOFF elliott 2026-09-25 lap 92 — input (c) REFUTED in-kernel, and the crux re-decomposed

Branch `wip/elliott-port`, working tree clean, **both** green targets pass:
`lake build` (9257 jobs) and `lake build NormalNumbers.ElliottAxiomAudit` (9674 jobs).
Never `lake exe cache get`.  Never edit `.lake/packages/lean-proofs-latest/`.
**`DIRECTION.md` CURRENT DIRECTIVE governs — read it first.  Do NOT edit it.**

## The lap in one line

The Archimedean input that laps 85–91 reduced the crux to is **false**; it is now a `¬` theorem in
`src/`, and the decomposition has been repaired into a strictly cleaner one that drops the whole
rigidity branch.

## What landed

Two new modules, both sorry-free, both `[propext, Classical.choice, Quot.sound]`:

| file | content |
|---|---|
| `ElliottArchimedeanRefuted.lean` | `not_archimedeanCorrelationBound {A} (0 < A) {η} (0 < η) : ¬ ArchimedeanCorrelationBound A η` |
| `ElliottTwistRepair.lean` | `AlmostRealTwist`, the repaired dichotomy, the re-proved consumer, inputs (c′) and (e), `twoPointElliottLog_of_repaired_inputs` |

**The refutation.**  Witness `v = 2/log X`: it satisfies the hypothesis `1 < |v| log X` exactly
(`= 2`), but then `|v| log p ≤ 2` for every `p ≤ X`, so with `cos θ ≥ 1 − θ²/2` and
`(log p)² ≤ (log X)(log p)` plus Mertens I,
`Re ∑_{p≤X}p^{-iv}/p ≥ M(X) − 2 − 2C`, which beats `(1−η)M(X)` once `M(X) > (2+2C)/η`.
Hence `ElliottCharRigidity.twoPointElliottLog_of_archimedean_and_density` is **vacuous**.

**The repair.**  The consumer never needed `C ≈ M(X)`; it needed `C` within `O(1)` of a real
`R ∈ [0, M(X)]` (`AlmostRealTwist`), because rotating by `ζ = e(u) ≠ 1` then already costs
`(1 − max(Re ζ,0))·M(X)` — that is the one-lemma core, `re_phase_mul_twistCorr_le`.  The inputs are
split at a threshold function `T` (honestly `T X = (log X)^{-1+ε}`, *not* `1/log X`):

* **(c′)** `ArchimedeanCorrelationBoundAbove A η T` — `T X < |v| ≤ A²X → ‖archCorr v X‖ ≤ (1−η)M(X)`
* **(e)** `SmallShiftAlmostReal A K T` — `|t| ≤ T X → AlmostRealTwist K χ t X`

and `twistAlmostRealDichotomy_of_inputs` needs only the bootstrap link `A√(2δ) < η`.
`twistAlmostRealDichotomy_of_old` proves the old dichotomy implies the new one, so **nothing from
laps 85–91 is lost** — only the false input is.  `CharacterClusterRigidity`, `PrimeDensityAP`,
`exists_charDefect_le` and the de-twisting branch are now OFF the critical path.

## What the next lap does

**Input (e), staged** — see `PENDING_WORK.md` top section for the four sub-targets.  Start with the
shared prerequisite survey: a **two-sided** Mertens `∑_{p≤u}1/p = log log u + B + O(1/log u)`.  Only
the lower half is in use (`PrimeEstimates.mertensBound`).  `Util.MertensThird.mertens_third_theorem`
in the dependency tree is the most promising source — its log is exactly the wanted two-sided form.
Then e-NP (non-principal `χ`, `R = 0`, from `L(1,χ) ≠ 0`), then e-P-Im (the bounded `Si`), then
e-P-Re.

(c′) stays the long pole.  Before grinding it, spend a paper probe on the van der Corput route
recorded in `PENDING_WORK.md` — it would give (c′) unconditionally on `1 ≪ |v| ≤ A²X`.

## Traps recorded this lap

* **The Elliott chain is NOT reachable from `src/NormalNumbers.lean`, and must not be wired in**:
  `import NormalNumbers.ElliottAxiomAudit` there fails with
  `import PrimeNumberTheoremAnd.Sobolev failed, environment already contains 'CS.deriv' from
  PNTPort.Sobolev`.  So a bare `lake build` does **not** check the campaign; always run
  `lake build NormalNumbers.ElliottAxiomAudit` too.  (Tried and reverted this lap.)
* `Real.one_sub_sq_div_two_le_cos : 1 - x^2/2 ≤ cos x` exists in mathlib (Trigonometric/Bounds).
* `Complex.exp_ofReal_mul_I_re : (exp (↑x * I)).re = cos x` — rewrite `I * t * L` into
  `↑(t*L) * I` by `push_cast; ring` first.
* `Complex.div_ofReal_re` needs the denominator as `((p : ℝ) : ℂ)`, not `(p : ℂ)`; convert with
  `push_cast; ring` inside a `show`.
* `div_le_div_of_nonneg_right` wants `0 ≤ c` (already in the corpus); `gcongr` is more robust here.
* `linarith` treats `η * M` and `M * η` as **different atoms** — after `div_le_iff₀` the product
  comes out in the other order.  Multiply the hypothesis by hand
  (`mul_le_mul_of_nonneg_left` + a `field_simp` equality) instead of rewriting with `div_add'`.
* A bare `field_simp` can close a goal outright; a following `ring` then errors with
  "No goals to be solved".

## Audit surface

`lake build NormalNumbers.ElliottAxiomAudit` now also prints the refutation and all five repair
theorems.  All trust triple.
