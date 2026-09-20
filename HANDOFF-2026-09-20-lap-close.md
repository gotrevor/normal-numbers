# HANDOFF 2026-09-20 — lap close (budget)

Branch `wip/g5-prime-subset`, HEAD `e38b949`.  Build 🟢 **9103 jobs**.  Working tree clean;
nothing uncommitted.  `src/` = the two pre-expedition forbidden-drift `sorry`s
(`phaseOscillation`, `exists_prime_nonresidue`); **zero `axiom`s**.

Two threads ran this lap.  Full detail:
`HANDOFF-2026-09-20-rough-independence.md` (thread 1) and
`HANDOFF-2026-09-20-campaignB-close.md` (thread 2).

## Thread 1 — the attended `RoughIndependence` override (COMPLETE)

`src/NormalNumbers/G4WiringRough.lean`, new and **sorry-free**, axiom-clean.  All six kickoff
leaves closed; `isNormal_G4_of_rough` proved.  `CRTConstant` — frozen, uniform in `J`, measured
*false* in the Chowla sector — is replaced as the SD-sector input by three weaker nodes plus a
machine-checked small-prime half (`omegaLe`/`omegaAbove` split, primorial-periodicity,
`periodic_mean_close`, `smoothWindowCRT`).

Two forced deviations, both documented in-file:
1. the kickoff's `omegaLe_add_primorial` is **false** at `m = 0`; it carries `m ≠ 0`;
2. leaf 5's `J·P/N` error cannot be absorbed into `C/log N · ∏‖full_j‖` (that product → 0).
   Repair: keep it relative via `‖R_W‖ ≤ (B_R+|C_R|)∏‖R_j‖` and hD.2 + hS; needs the new
   `windowJ_log_div_tendsto_zero`.

Then the crux was **narrowed**: `RoughIndependenceAt h y` (single `y`, error `C/log N`, no `1/y`
gain) is all the wiring consumes.  The live open obligation is exactly **`RoughIndependenceAt h 2`**.

## Thread 2 — campaign B (the standing CURRENT DIRECTIVE) reaches its FINISH LINE

* **Terminal objective**: `audit_isDisjunctive_weightA_logLog` added to `G4WeightStatement.lean`
  (step 4 of the mandated order; steps 1–3 had landed in earlier laps).  Trust-triple clean.
* **The one permitted stretch** (general additive `f`): **refuted in the kernel**, then turned
  into a classification programme, in the new `src/NormalNumbers/G4AdditiveRigidity.lean`
  (sorry-free, trust-triple clean).  All of these are theorems about the bare `TWeight`
  interface — nothing is assumed additive, multiplicative or monotone:

  | result | status |
  |---|---|
  | `ov_eq`, `ov_symm`, `ov_cocycle`, `ov_mul_left_of_modEq_one` | `ov` is a symmetric 2-cocycle, forced by `mul_eq` |
  | `wN_prime_pow_second_diff`, `_first_diff`, `wN_prime_pow_affine` | **affine along every prime-power tower** |
  | `wN_mul_of_modEq_one`, `wN_prime_pow_mul` | **additive when `m ≡ 1 mod rad d`** |
  | `addWeightN`, `affine_of_addWeightN_isTWeight`, `addWeightN_affine_eq_weightAN` | `G4WeightInterface`'s prose "iff" is now a machine-checked biconditional |
  | `omegaOdd`, `omegaOdd_not_additive` | **"every `TWeight` is additive" is FALSE** |

  So a non-affine `f` is not a `TWeight` at all: the obstruction is in the transport interface,
  upstream of §4C and §4D, and no far-field domination can reach it.

## Next steps

1. **The one open interface question, precisely stated** (`PENDING_WORK.md`): for every
   `TWeight`, is `m ↦ w(m) − w(1)` additive?  Affine + `m ≡ 1 mod rad d` are proved; plain
   additivity is refuted by `omegaOdd` (which is additive **plus a constant**), so the `− w(1)`
   is load-bearing.  Tools in place: `ov_symm`, `ov_cocycle`, `ov_mul_left_of_modEq_one`.  The
   gap: for coprime `d, m` one wants `ov d m = w(1)`, and the cocycle only relates corrections
   at residues already `≡ 1` somewhere.  Next probe: a Dirichlet prime `q ≡ m [MOD rad d]`
   together with `ord_q(p)`.  Attempted this lap, **not** settled.
2. **Probe `SmoothRoughDecoupling`** — the only unprobed node in the new `G₄` chain.  If it
   fails, the N1 split needs redesign before any effort goes into `RoughIndependenceAt h 2`.
3. **A new directive is what the repo needs.**  Campaign B's pre-registered FINISH LINE is met
   on both conditions, and its closing instruction is "do not open a successor campaign".  Both
   remaining `src/` `sorry`s are on its ⛔ forbidden-drift list.  Candidate directions (not acted
   on) are in `HANDOFF-2026-09-20-campaignB-close.md` §4 — the most promising is **widening the
   transport interface** (`ov_congr` mod `(rad d)^k`), which the rigidity theorems now make a
   precise question rather than a vague one.
