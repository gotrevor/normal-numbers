# KICKOFF 2026-09-24 — Tao's general two-point log-Elliott (known result, formalization lane)

Worktree `~/src/nn-elliott`, branch `wip/elliott-port`.  Opus/low.  Target
`src/NormalNumbers/ElliottGeneral.lean`: `nonasymptoticLogElliott`.  This is KNOWN mathematics
(Tao 2016, Thm 1.3); the job is to get the proof down.  Deprecations, `native_decide`, heartbeat
boosts are all fine.

## What you start from
Boris Alexeev's `plby/lean-proofs` is a Lake DEPENDENCY (`lean-proofs-latest`, via the fork
`gotrevor/lean-proofs` branch `mathlib-v4.33.1`, source under `.lake/packages/lean-proofs-latest/src/latest/`).
Never copy its files into this repo (Trevor: no vendoring).  If it needs a change, say so in the
handoff: it goes on the fork, not here.  Key pieces:
- `Erdos67b.NonasymptoticLogElliott` (`LogElliott.lean`): the statement to prove.
- `Erdos67b.unitCircleLogElliott` (`ElliottComplete.lean`): the PROVED special case (f completely
  multiplicative, `|f| = 1`, correlation `f(n)·conj f(n+h)`).  Its proof: graph/Fourier criterion
  (`exists_logPairCorrelation_small_of_fourier_first_moments`) + MRT
  (`mrtModulatedShortIntervalUnrestricted`) + entropy decrement.  THIS is your template.
- `NonasymptoticLogElliott.unitCircle`: the general ⇒ special reduction (other direction).

## The three generalisations, in the order to attack
1. **Completely multiplicative → multiplicative, `|g| ≤ 1`.**  Tao handles this; MRT for bounded
   multiplicative (not unit, not completely) is in MRT's original paper.  Check which MRT variant
   the dependency proves, and extend it in `src/` (new theorems, not edits to its files).
2. **Shift `n, n+h` → affine forms `a₁n+b₁, a₂n+b₂`.**  Tao's reduction: dilate by `a₁a₂`, restrict to
   residue classes; the entropy-decrement step is unchanged.
3. **`g₁ ≠ g₂`, pretentiousness on `g₁` only.**
Freeze each as a named intermediate `Prop` + theorem in `src/NormalNumbers/Elliott*.lean` so a lap can
end with a strictly smaller open leaf.  Read Tao's paper section structure (arXiv:1509.05422) if you
know it; the plby files' docstrings cite section numbers.

## Why we want it (the downstream use, a later lap, not required)
C1's two-point leaf (`PairDecoupleTwoPoint.lean`, `TwoPointElliott`) is the correlation of
`ζ^{ω(pn+1)}` and `ζ^{ω(qn+1)}`: multiplicative, not completely; dilated affine forms; unit modulus.
The log-density version of it follows from the general theorem plus non-pretentiousness of `ζ^ω`
(`D(ζ^ω, χ·n^{it}; X)² → ∞` uniformly: compare `DelangeSlot*.lean`, `TwoPointDelange*.lean` on
`wip/twopoint-avg`).  If the headline lands, stating `TwoPointElliottLog` and deriving it is the
natural next step.

## Rules
- Ratified: never delete, rename or weaken `nonasymptoticLogElliott`.  Never copy dependency files into the repo; never edit
  `Maze.lean`, other files' statements, `papers/`, other KICKOFFs.
- Build `lake build NormalNumbers.ElliottGeneral` (warm tree; never `lake exe cache get`).  Files importing
  the dependency are deliberately NOT imported by the `NormalNumbers` root (PNT+ declaration names
  would collide with `src/PNTPort`).  Commit each green step.
- HANDOFF `HANDOFF-elliott-<date>-lapN.md`: the crux, this lap's advance, confidence it lands.
