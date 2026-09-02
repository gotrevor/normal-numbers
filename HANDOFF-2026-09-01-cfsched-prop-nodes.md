# HANDOFF: CFScheduleA sorries → Prop nodes; refutation; tower deductions 🪷

Branch `wip/cfschedulea-prop-nodes` (worktree `~/src/normal-numbers-cfsched`, branched from
`wip/adder-tower-c9` @ `40ff0a2`).  Attended-agent session, 2026-09-01.  Full `lake build`
green at every commit (pre-commit hook builds).

## What advanced

1. **`src/` is sorry-free — honestly.**  The two disclosed `sorry`s of the abandoned
   interleaved-schedule route are conjecture-graph NODES now (`def … : Prop`, statements
   verbatim), and every dependent takes the node as an explicit hypothesis
   (`theorem foo (h : Node) …`).  Nothing deleted.
   - `VarianceBlockCountPsiPushed` — RED.  Dependents `psi_pushed_chebyshev_brick` →
     `gaussMeasure_aggregate_psi_pushed_le` → `exists_scale_cfCylinder_psi_avoid_zbad_poly`
     are marked VACUOUS in their docstrings.
   - `SchedABlockLinear` — OPEN, and the docstring now says *why it will stay open*: `schedA`
     is a `Classical.choose` recursion whose spec (`StepSpecA`) carries no block upper bound,
     so the Prop is neither provable nor refutable from the spec (choice-opaque); the
     2026-08-24 measure-budget obstruction argues the mathematics behind it is false.
     Dependents `schedA_block_geom` → `schedA_hfreq_x`/`_z` → `exists_interleaved_affine_witness`.
2. **The refuted node has a kernel-checked negation** —
   `varianceBlockCountPsiPushed_false` (`CFScheduleARefuted.lean`, trust triple), and it
   SHARPENS the obstruction note: the affine map is irrelevant.  Already for `ψ = id`,
   `v = [1]`, `wx' = [2,…,2]` the cylinder-restricted second moment about the GLOBAL mean is
   `Θ(n²)·γ(wx')`.  The route died because a restricted Chebyshev must centre at the
   conditional mean, which the schedule never controlled.
3. **Tower deductions** (`AdderTowerDeductions.lean`, from the novelty audit's "short
   deductions"): the single-multiplier floor (`exists_irrational_mul_omits_digit`) ⇒ **C2 is
   cardinality-optimal**, **B–B `M(3,1) = 2` LOWER half** (`Literature.berendBoshernitzan_M31_lower_holds`,
   declared in the ledger namespace from this file; `Literature.lean` untouched), `M(g,1) ≥ 2`
   for all `g ≥ 3`; and **C5 sharpened** (`c5_sharp`, no `X + 4Y` channel, two lines from C1).

4. **N3 — `e` enters the kick machine** (`EFactorialKick.lean`, new node family from
   `docs/new-conjectures-2026-08-29.md` §N3, listed under ROADMAP "D-next"): factorial split
   `eSplit b n = min{m : bⁿ < (m+1)!}`, rational surrogate `fract (bⁿ·A(M)/M!)` with the rigid
   numerator `eNum` (A000522 recurrence proved), tail bracket from mathlib's `exp_bound'`,
   moving-sliver cores (`window_of_fract_small/_large`, generalising `KickedOrbit`'s to
   `hi < 2`), the ALL-BASE run dichotomy `eSurrogate_window_of_zeroRun`/`_of_maxRun`
   (unconditional), and the CITED node `EIrrationalityExponentTwo` (`μ(e) = 2`) with the
   `(1+ε)n` run-cap edge `eRun_le_of_exponentTwo`.  Probe already green
   (`experiments/e_binary_runs.py`).  ⚠️ The Davis 1978 reference in the node docstring is
   tier S (from memory, PDF not held) — verify before outward use.

5. **N2 — the Stoneham Rosetta stone** (`StonehamBase6.lean`): `stoneham_base6_readout`,
   the base-6 orbit of `α₂,₃` reads out `3^a mod 2^c` with an exponentially small error
   (statement exactly the N2 note's; `readout 10 = 2187` anchored by `decide`).  The node
   `PowersOfThreeReadoutDense` is deliberately NOT frozen: its window margin must be pinned
   and the degeneracy probe run first (docstring says what is needed).
6. **N3 rigidity** `eNum_zmod`/`eNum_mod`: `A(M) ≡ A(M mod p) (mod p)`.

7. **Hygiene**: `CFScheduleA.lean` now builds with zero linter warnings (42 cleared:
   `push_neg`→`push Not`, `Set.mem_setOf_eq`→`Set.mem_ofPred_eq`, unused binders `_h…`,
   unused simp args / no-op `push_cast`).  Proof-internal only.

## Commits (branch `wip/cfschedulea-prop-nodes`, on top of `40ff0a2`)

`ed814d8` Prop nodes · `7eb13b5` refutation · `50b7827` tower deductions · `b053496` docs ·
`3f549b8` EFactorialKick · `033a3cf` numerator rigidity · `bd0b915` StonehamBase6 ·
`97de3a8` hygiene · (+ this handoff).  Every commit's pre-commit hook ran the full
`lake build` green (8846 jobs at the end).

## Verification (the quantum, run once)

- `lean-sorry src` = 0.
- `collectAxioms` census over every user-facing NormalNumbers constant (1726 before →
  1796 at the final commit), diffed against the pre-edit baseline: the ONLY changes are
  (a) the nine former-`sorryAx` constants, now trust triple, and (b) additions — the two
  Props and the new modules' declarations.  No pre-existing constant's axiom set moved;
  no constant depends on `sorryAx`.  Script: `AxiomCensus.lean` (session scratch, ~25
  lines, `collectAxioms` per constant), outputs `axioms-before.txt` / `axioms-final.txt`.
- `lean-axiom-gate --exact -i NormalNumbers` ✓ on: `exists_absolutely_normal_cf_normal`,
  `…_khinchin`, `exists_cfNormal_and_affine_cfNormal`, `exists_cfNormal_and_affine_family_cfNormal'`
  (census; the gate's shell quoting chokes on the prime), `isNormal_iff_equidistributed_orbit`,
  `isNormal_log_two_of_equidistributed`, `isNormal_two_stoneham23`, `Adder.adder_sixfold_disjunction`,
  `Adder.adder_c9_disjunction_universal`, `piSqBBP_proved`, `ae_khinchinTypical`,
  `isAbsolutelyNormal_of_uniformDigitTV`, `lnTwoRun_le_unconditional_sharp`,
  `exists_interleaved_affine_witness` (now conditional, trust triple),
  `varianceBlockCountPsiPushed_false`, and the six new deduction headlines.

## Files touched (for integration)

- `src/NormalNumbers/CFScheduleA.lean` (Prop nodes + docstrings), `src/NormalNumbers/CFScheduleARefuted.lean`
  (new), `src/NormalNumbers/AdderTowerDeductions.lean` (new), `src/NormalNumbers/EFactorialKick.lean`
  (new), `src/NormalNumbers/StonehamBase6.lean` (new), `src/NormalNumbers.lean` (four mid-file
  import lines: after `CFScheduleA`, after `AdderTowerC2`, after `PiBBP`, after `Stoneham` —
  the box appends at the end, so this merges clean), `formalization.yaml`, `README.md`, `STATUS.md`, `ROADMAP.md`,
  `KHINCHIN.md` (§B6 status line), this handoff.
- NOT touched: `PENDING_WORK.md`, `BRIEF-adder-tower.md`, `Literature.lean`, `DIRECTION.md`,
  `docs/` (box territory / operator-owned).  Stale name in a docstring left alone to avoid a
  CF-chain rebuild: `CFDigitLaw.lean:794` still says `schedA_block_linear`.

## Box footprint during this run (base checkout `~/src/normal-numbers`, branch `wip/adder-tower-c9`)

`a629043` C10 (AdderTowerC10.lean, emitter, certs, BRIEF-adder-tower.md, PENDING_WORK.md,
NormalNumbers.lean +1), `8afbd05` Mahler Theorem M (MahlerMultiplier.lean, LiteratureMahler.lean,
Literature.lean docstrings, BRIEF-literature-statements.md, PENDING_WORK.md, NormalNumbers.lean +2),
`e64ac29` handoff.  No file overlap with this branch except `src/NormalNumbers.lean` (disjoint hunks).

## For Trevor's decision

- `BRIEF-adder-tower.md` (box-owned) has no "floors" addendum for the deductions; add one at
  integration if wanted (C2 optimal cardinality, C5 sharp).  `docs/tower-novelty-audit-2026-08-29.md`
  (operator-owned) could cite `c5_sharp` under "C5 is a C1 corollary".
- `Literature.lean` could absorb `berendBoshernitzan_M31_lower` (+ `_holds`) from
  `AdderTowerDeductions.lean` when the box is off that file.
