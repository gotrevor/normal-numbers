# HANDOFF c3-mrt 2026-09-25 — SESSION WRAP (laps 33–39)

**Branch** `wip/c3-mrt` · **HEAD** `e9db6dc` · working tree **clean** · both build targets green
at every commit.  Read `DIRECTION.md` → CURRENT DIRECTIVE first (it outranks this file).
Per-lap detail: `-lap33.md` … `-lap39.md`.  Earlier: `-session-wrap.md` (1–6), `-lap8.md`,
`-lap18/19/21.md`, `-lap32.md` (20–32).

## BUILD HYGIENE — read before claiming green

`src/NormalNumbers.lean` does **not** import the `C3Mrt*` chain (the directive forbids importing
a `lean-proofs-latest` consumer into the `NormalNumbers` root), so a bare `lake build` and the
pre-commit hook do **not** typecheck any `C3Mrt*` module.  Always run BOTH:

    lake build                                  # 9257 jobs
    lake build NormalNumbers.C3MrtMultiForms    # the C3Mrt chain tip (imports everything else)

Done at every commit in laps 33–39.

## The crux is untouched

`weylLambertTwist_holds` (`SwingC3Leaf.lean`) unchanged; it is the **only** `sorry` in `src/` for
this campaign (lap 33 closed the last disclosed sub-`sorry`).  `conjC3_via_weylLambert` carries
`sorryAx` through it alone.  No existing statement anywhere was weakened, renamed or edited; this
session is pure addition.

## Session result — the named-input ledger changed shape

**Before (lap 32):** `ConjC3`'s `D = 2` rung rested on two named inputs, and `D ≥ 3` was believed
to need a strictly new open conjecture (`KPointLogElliott k`).

**After (lap 39):**

| depth | named input | status |
|---|---|---|
| `D = 1` | — | **PROVED** outright (Delange, `depthAvg_one_tendsto`) |
| `D = 2` | `KPointLogElliott 2` (= `Erdos67b.NonasymptoticLogElliott`, proved equivalent lap 34) + VK | rung **PROVED** modulo those (lap 33) |
| `D ≥ 3` | `ProductLogElliott D` (= **Tao–Teräväinen's structure theorem, a published theorem**) + the same VK | 5 of 7 assembly steps proved |

The remaining distance to `ConjC3` is no longer "a `k`-point Elliott conjecture".  It is exactly
**(a)** log density → natural density, and **(b)** uniformity of the rate in `D` up to
`D ≍ log log log N`, i.e. `QuantDepthElliott`.

## What landed, lap by lap

* **33** — `rung_two_correlation` **PROVED** (the last disclosed sub-`sorry`): `rung_two_uniform`
  collapses the per-pair `A₀`/`i₀` to one base `A` and exponent `I`; then the ε-chase
  `ε → ε_r → Y → A → I → N₀`.
* **34** — `C3MrtKPoint.lean`: `KPointLogElliott K`; `kPointLogElliott_two_iff` (**equivalent** to
  the dependency's bet at `K = 2` — faithfulness, an `iff`); `kPointLogElliott_of_succ` (the
  hierarchy is monotone downward, by padding with the constant `1`).
* **35** — `C3MrtProductPhase.lean`, **the session's biggest result**: Tao–Teräväinen kill the
  log-averaged `k`-point correlation whenever the *product* is non-pretentious; their odd-order
  Chowla restriction is an artefact of `λ^k ≡ 1` for even `k`.  Our product **never** degenerates:
  `∏_{i<D} ζ_i = e(h·G_D/b^D)` with `gcd(b^D, G_D) = 1`, so `≠ 1` exactly when `b^D ∤ h`, hence at
  every `D > log_b|h|`.  `nonPretentious_prod_depthRoot` discharges TT's hypothesis from the
  existing archimedean certificate.
* **36** — `C3MrtMultiShift.lean`: `sum_pow_omega_multi_eq`, the `K`-fold bridge expansion
  (induction peeling the last shift; `F` **must** be quantified inside the induction).
* **37** — `C3MrtJointModulus.lean`: `prod_le_lcm_mul_pow`, `∏ d_i ≤ lcm(d_i)·K^{K²}`, resolving
  the `K ≥ 3` non-coprimality obstruction lap 36 found.  `prod_dvd_lcm_mul_gcdProd` is exact and
  factorisation-free.
* **38** — `C3MrtTupleMass.lean`: `tuple_mass_le` (the `K`-fold `pair_mass_le`; the tuple sum
  factors completely via `Finset.sum_prod_piFinset`) and `prod_div_lcm_le`.
* **39** — `C3MrtMultiForms.lean`: `multi_forms_det` — the `K` forms' determinant is
  `L(j−i)/(d_i d_j)`, so nondegeneracy is automatic at every `K` (the `K = 2` determinant of `1`
  was not luck); and `joint_class_multi`, the `K`-fold CRT, needing no coprimality.

All new declarations are axiom-clean `[propext, Classical.choice, Quot.sound]`.

## NEXT — resume here

1. `inner_sum_linear_forms` analogue: reindex `n = L·k + a` (from `joint_class_multi`), so
   `(n+i+1)/d_i = (L/d_i)k + (a+i+1)/d_i`; then `filter_linear_lt_eq_range` applies verbatim with
   `L` for `d·e`.
2. `multi_truncation_bound`: iterate `offset_truncation_bound_of_mass` `K` times; error
   telescopes to `≤ ∑_{i<K}(∏_{j<i} sqfWMass z_j)(1 + log(N+K))·bridgeTail z_i Y`.
3. **Pay lap 38's indexing debt**: standardise on `Fin K` + `Finset.univ.lcm` (the convention
   `joint_class_multi` and `nondegenerateForms_multi` already use) and restate
   `prod_le_lcm_mul_pow` / `prod_div_lcm_le` over `Finset.univ` by applying the `range` versions
   to the `ℕ → ℕ` extension of the tuple.
4. Per-tuple rung bound + ε-chase, mirroring laps 29–33.
5. Then the **one shape change lap 37 forces**: `QuantDepthElliott`'s constant budget must widen
   from `b^{κD}` to a general `C(D)` with `C(D_N)·η(N) → 0` (the `K^{K²}` of lap 37, which at
   `D_N ≍ log log log N` is `(log log N)^{o(1)}`).  That is a Prop **we** state
   (`C3MrtSchedule.lean`); do it only when the assembly needs it, and never weaken
   `weylLambertTwist_holds` or `conjC3`.

## Still refuted — DO NOT RETRY

Smooth/rough Kubilius split; self-similar recursion; growing `P`; direct `unitCircleLogElliott`;
resonance counting past `|t| ≳ (log X)^K`; crude `|ζ(1+it)| ≪ log t`; naive iteration without the
`1/(de)` gain.  **Do not attack `TwistedPrimeSumSaving`** — it is the named VK input.  Newly
added: restricting the schedule to odd depths (lap 35 — never needed); quantifying `F` outside the
`K`-induction (lap 36); the prime-valuation route to `prod_le_lcm_mul_pow` (lap 37 is exact);
worrying the `K` forms might be degenerate (lap 39 — they never are); looking for a coprimality
hypothesis in the `K`-fold CRT (there is none).

## Confidence

* `D = 2` rung on two named inputs: **done, in-kernel**.
* `K ≥ 3` assembly completable: ≈ 82% (5 of 7 steps; both flagged structural risks discharged).
* leaf TRUE ≈ 97% (up from 95%: a published theorem now covers the qualitative shape at every
  fixed depth).
* leaf PROVABLE with known techniques ≈ 28% (up from 15% at session start; the wall is now
  uniformity in `D` plus log→natural, not a new Elliott conjecture).
