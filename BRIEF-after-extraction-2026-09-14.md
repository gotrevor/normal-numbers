*Repo copy of the attended brief `~/personal/claude/knowledge/core/projects/normal-numbers-after-extraction-2026-09-14.md` (Ren/Astra, 2026-09-14 22:58 EDT), staged by Ren (Claude) for the Fable run authorized by Trevor 2026-09-14 night: "OK to burn our Fable usage tonight.  It's a worthwhile endeavor.  Dig in!"  The DIRECTION override names the objectives; this file is the mathematics.*

# After the extracted normal number: return to the original digit stream

## Decision

Bank the completed extraction theorem and write its mathematical account.  Do not make the converse power-base theorem, further bases of the extracted number, or a lengthy novelty search the next frontier campaign.  Those are separate, optional tasks.  The research priority is to obtain information about G4's ordinary digits that the existing sparse-sample mask can change.  Confidence in this prioritization: 85%, not an estimate of the probability of solving normality.

Checked at 22:58 EDT on 2026-09-14: the treadmill is stopped; inspected repository HEAD `5bceae7`, with a clean worktree.  `isNormal_fullRealW` and `digitOf_fullRealW` state normality and the exact binary-digit identity for the extracted real.  The head estimate and capped-flank repair are implemented.  Fable's attended review records its independent host check.  This visit read source and handoffs; it did not repeat that check or launch another run.

## A scope correction before choosing the next attack

The old B probe proves confinement for

`kIdxOf G b n α = (n - b % d_α²) / d_α`.

That is not the fixed physical orbit index `(n-t_α)/d_α` when the multiplier residue varies.  For `0 ≤ t < d`, `0 ≤ c < d`, and `n = t + d*c + d²*q`, the physical index is `c+d*q`, while the re-centred index is `d*q`.  Example: `d=5`, `t=1`, `c=2`, `q=3`, `n=86` gives indices 17 and 15.  The latter is divisible by 5 because the definition subtracted the residue carrying the missing two positions.

Thus `not_dense_of_any_residue` is a valid statement about its defined sampler, not a universal impossibility theorem for every way of varying CRT phases.  `Frame.propA_of_progression` already accepts an arbitrary multiplier-residue vector c while retaining `n=t_α+d_α*k_α`.  Re-basing t also changes the arithmetic shifts; uniformity of that altered frame is a separate obligation, not merely a constant output translation.

**This does not rescue phase averaging.**  A second, genuine constraint survives even when the physical index is kept fixed.

## First elementary lemma: residual CRT confinement

Fix pairwise coprime positive multipliers `d_α`, offsets `0 ≤ t_α < d_α`, and let `D = ∏_α d_α`.  Allow every multiplier residue and auxiliary frozen-prime class, but retain the simultaneous exact identities `n=t_α+d_α*k_α` for every atom.

CRT still confines n to one class `a mod D`.  For `n=a+D*q`,

`k_α = (a-t_α)/d_α + (D/d_α)*q`.

Consequently the union of length-m binary windows read at `2*k_α` has upper density at most

`Σ_α m / (2*(D/d_α)) = m * (Σ_α d_α) / (2D)`.

This is a fixed-grid coverage bound, not a claim about all possible grids or their union across scales.  Its proof is an arithmetic-progression residue count followed by a union bound.  It remains valid without the extra `d_α | k_α` restriction used by B.  Record the actual schedule specialization before calling the bound small there.

The cheap Fable task is to formalize this correctly indexed statement and the scalar re-centring identity.  Keep the old theorem; correct prose that overgeneralizes it.  Do not spend a campaign trying to fill the original digit stream by releasing only the extra squared-modulus constraints.

## Second elementary lemma: what exact cancellation allows us to vary

In the current tensor grid, cancellation of term j is obtained because `j*d_α-t_α` is independent of coordinate j.  At **fixed multipliers**, suppose new offsets `t'_α` preserve those same pointwise coordinate-cancellation identities for every coordinate.  Then `t'_α-t_α` is independent of each coordinate, hence constant on the product grid.  A common offset change only translates sample time; it does not create new physical orbit indices when the corresponding sample is translated too, apart from finite cutoff effects.

This is a short proof over integers, not yet formalized in this review.  It applies to this specific coordinatewise mechanism, not to all cancellations of the weighted sum or all carry methods.  Formalize that scope explicitly.

Together, these lemmas identify the next research requirement: **vary the multipliers, replace exact coordinatewise cancellation, or tolerate and control its error**.  Merely changing the class label or shifting every offset together does not do it.

## Bounded frontier brief, prepared but not launched

After banking those obstructions, investigate one explicitly specified deformation of the carry/tensor construction.  Before substantial Lean assembly, require:

1. Actual orbit indices of the unchanged G4, with all divisibility hypotheses visible.
2. A finite-prefix coverage and weighting calculation demonstrating access to positions unavailable to the fixed-grid construction.  Coverage alone is not equidistribution.
3. The exact replacement transport identity, including any new error term.  Quantify its cost against the existing entropy/volume saving at digit resolution; do not assume it is small or independent.
4. A proof or an explicit obstruction for that stated deformation.  A random-prime model can diagnose the mechanism, but cannot replace the arithmetic estimate.

A successful preliminary outcome is a genuinely better sampling mechanism with an isolated arithmetic estimate.  A successful negative outcome is a proved limitation of the tested mechanism.  Neither should be reported as normality of G4.  Another sparse extraction would return to the completed task and require a fresh decision.

The final mathematical write-up of the extracted constant is useful low-cost work alongside this.  No new worker or treadmill was launched by this planning turn.

Sources: `G4EntropyWStatement.lean`, `G4EntropyWSqueeze.lean`, `G4EntropyWHead.lean`, `G4EntropyWCap.lean`, `G4EntropyResidueProbe.lean:48`, `G4Transport.lean:234`, `G4Progression.lean`; [[normal-numbers-entropy-review-2026-09-14]], [[normal-numbers-fable-prefix-closeout-2026-09-14]].
