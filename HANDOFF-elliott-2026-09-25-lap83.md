# HANDOFF elliott 2026-09-25 lap 83 — **THE HEADLINE IS PROVED AND AXIOM-CLEAN**

Branch `wip/elliott-port`, HEAD `81f791e` (this commit), working tree clean, `lake build` green (9257 jobs).
Never `lake exe cache get`.  Never edit `.lake/packages/lean-proofs-latest/`.
**`DIRECTION.md` CURRENT DIRECTIVE governs — read it first.  Do NOT edit it.**

## The result

```
'NormalNumbers.ElliottGeneral.nonasymptoticLogElliott' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

`Erdos67b.NonasymptoticLogElliott` — Tao 2016, *The logarithmically averaged Chowla and Elliott
conjectures for two-point correlations*, Forum Math. Pi 4, Theorem 1.3, in plby's finitary
formulation — is a **theorem** of this repo, on top of the dependency's proved
`Erdos67b.unitCircleLogElliott`.  **Zero `sorry` in the Elliott scope.**

The last open obligation, `ElliottLeafTwo.exists_caseB_threshold`, was discharged this lap in the
new `src/NormalNumbers/ElliottCaseB.lean`.  See `PENDING_WORK.md` → "Lap 83" for the one real idea
(the ε-budget's circularity is broken by choosing `D₁` and `D₂` **in order**), the scale
bookkeeping, and seven recorded traps.

## `src/` sorry inventory (Elliott scope)

Empty.

## What the next lap does

`DIRECTION.md` CURRENT DIRECTIVE, in full.  In one line: the proved headline is Tao Thm 1.3
restricted to **completely** multiplicative `g₁, g₂` (the dependency's
`IsMultiplicativeOnPositiveInt` has no coprimality hypothesis), so state and prove a `src/`-owned
`NonasymptoticLogElliottMult` for merely multiplicative `gᵢ`.  Expected shape: weaken hypotheses in
place along the leaf-2 chain — nothing there appears to consume complete multiplicativity of `gᵢ`
(every downstream use of `IsCompletelyMultiplicativeOnPositive` is on the cover's `cmExt u`).
Trigger **EM-1** fires if that expectation is wrong.

## Audit surface

`lake build NormalNumbers.ElliottAxiomAudit` prints the `#print axioms` base of every load-bearing
theorem of the campaign (now including the whole Case-B chain).  All trust triple.
