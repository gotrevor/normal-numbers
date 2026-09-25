# HANDOFF elliott 2026-09-25 (laps 8–14) — the crux's analytic content is PROVED

Branch `wip/elliott-port`, HEAD `85c0ba1`.  Working tree clean.
`lake build` green (9257 jobs).  Never `lake exe cache get`.

## Headline target

`NormalNumbers.ElliottGeneral.nonasymptoticLogElliott : Erdos67b.NonasymptoticLogElliott`
(Tao 2016, Thm 1.3), on top of the dependency's proved `Erdos67b.unitCircleLogElliott`.
Never edit dependency files; never vendor them.

## What changed this session (laps 8–14)

Seven green commits, all axiom-clean (`[propext, Classical.choice, Quot.sound]`), all pure
additions in `src/`.  **The entire analytic content of the crux is now proved.**

New files, in dependency order (all zero-sorry):

| file | contents |
|---|---|
| `ElliottTwistedGraphCRT.lean` | CRT/Hoeffding layer: `pairTwistedCoordinate/Observable/Sum/MeanCRT`, `pairTwisted_tail_card_mul_exp_le`, `exists_pairTwisted_exponential_tail`, bridge `pairTwistedMeanCRT_eq_pairTwistedPrimeGraphMean` |
| `ElliottTwistedGraphDecoupling.lean` | `pairTwistedDiscrepancy`, `exists_logProb_pairTwisted_small_tail`, `exists_logProb_pairTwisted_decoupling` |
| `ElliottTwistedGraphBounded.lean` | perturbation estimates + `exists_logProb_bounded_pairTwisted_decoupling` (finite alphabet removed) |
| `ElliottTwistedGraphCorrelation.lean` | `norm_logProb_pairTwistedGraph_sub_correlation_le`, `exists_logProb_pairTwistedMean_correlation{,_close}`, **`exists_logProb_dyadic_pairTwistedMean_lower`** |
| `ElliottTwistedGraphCriterion.lean` | **`exists_pairLogCorrelation_small_of_fourier_first_moments`** — the complete two-function finite graph criterion |
| `ElliottShiftRung.lean` | `shiftedPairLogCorrelation`, `norm_shiftedPairLogCorrelation_le_trimmed`, **`shiftCMLogElliott`**, anchor `unitCircle_of_shiftCM` |
| `ElliottTwistedGraphMirror.lean` | the `_snd` mirrors, `mrtNonpretentious_conj`, **`shiftCMLogElliottMirror`** |

### The five findings that made it work

1. **The concentration engine is already generic.**
   `Erdos67b.crt_complex_tail_card_mul_exp_le` takes an arbitrary observable family with a
   per-index norm radius.  Both generalisations (second block, per-prime unimodular twist)
   move the observable but not the radius, so the Hoeffding tail carries the **dependency's
   own** constant ρ²/(64R²).  Same phenomenon as on the Fourier side (lap 4).
2. **Two functions in a one-sequence entropy argument.**  Run the entropy selection on a
   single `F : ℕ → α` in a finite alphabet with **two** decode maps `d₁, d₂`, reading both
   blocks off the same block of `F`.  One scale serves both functions; no second entropy
   budget.  The pair alphabet for the discretization rung is the product `net × net` of the
   dependency's own unit-disk net.
3. **The twist may be chosen after the scale.**  `logProb_block_rare_event_le` takes an
   arbitrary rare-event family and the entropy selection's outputs never mention it, so `w`
   is quantified under `∀ h s`.  That is what lets the assembly pick
   `w p = conj (f₁ p · f₂ p)` from the functions themselves.
4. **The correlation coefficient is unchanged.**  Because the twist restores the dilation
   identity *exactly*, the pair-twisted graph's coefficient is **literally** the dependency's
   real `primeGraphCorrelationWeight H h s`.  Hence
   `exists_dyadic_primeGraphCorrelationWeight_lower` (function-free) and
   `exists_uniform_primeGraph_window_error` (function-free) apply verbatim and the final
   constant is the dependency's 16 vs 32.
5. **MRT needs no two-function version.**  It is applied to `f₁` only, and everything
   downstream (`logProb_fourier_firstMoment_of_MRT`, window bookkeeping) mentions one
   function.  So Tao's asymmetry (hypothesis on `g₁` alone) is uniform across **both**
   analytic inputs, not a peculiarity of the graph step.  The Lean statement of the criterion
   now *witnesses* that asymmetry: `f₂` enters only via `‖blockFourier T (conj∘c) t‖ ≤ H`
   plus Parseval.

### The blocker found and discharged at lap 14

`shiftCMLogElliott` assumes non-pretentiousness of the **unshifted** function.  The crux's
forms `a·n+c₁`, `a·n+c₂` assume only `c₁ ≠ c₂`, so for `c₂ < c₁` the hypothesised function
sits at the **larger** shift.  Checked and refuted as free relabellings: pair swap
(`elliottLogCorrelation_swap`) needs non-pretentious `f₂`; global conjugation gives
`∑ w (conj f₂)(m) (conj f₁)(m+h)`, first function again from `f₂`; reindex `m ↦ m−h` just
moves the shift.  **Resolution:** in
`norm_pairTwistedPrimeGraphMean_le_largeFrequencies` the two blocks enter the pairing
symmetrically and Parseval hits both, so the choice of which factor stays in the
large-frequency sum is free.  `ElliottTwistedGraphMirror.lean` makes the other choice and
propagates it up four rungs.  **Both orientations are now available.**

## Ladder state

`src/NormalNumbers/ElliottLadder.lean` still has its **two** original sorries:
`dilatedCMLogElliott` (l. ~290) and `nonasymptotic_of_affineCM` (l. ~326).
Proved there already: `affineCM_of_dilatedCM` (Tao's affine generality is free on the CM
unimodular rung), `unitCircle_of_dilatedCM`, the `pairObservable` layer.

## NEXT (lap 15), in order

1. **The `a = 1` case of the crux.**  Forms `(n+c₁, n+c₂)`, `c₁ ≠ c₂`, hypothesis on `f₁`.
   Split on the sign of `d := c₂ − c₁`: `d > 0` → `shiftCMLogElliott`; `d < 0` →
   `shiftCMLogElliottMirror` applied to the pair `(f₂, f₁)` at shift `|d|`.
   The plumbing is: substitute `m = n + c₁` (an integer translation of
   `elliottLogWindow X W = Ioc (X/W) X`), and absorb
   (a) `O(|c₁|)` boundary terms, each of harmonic weight `≤ 1/(X/W) ≤ 1`, and
   (b) the weight discrepancy `∑ |1/(m−c₁) − 1/m| = |c₁| ∑ 1/(m(m−c₁)) = O(1)`.
   Both constants depend only on `c₁, c₂`, so they are absorbed by choosing `A₀` large
   (`ε log W → ∞`), exactly as `L₀` is in `elliottExists_finalThreshold`.
   Useful: `elliottLogCorrelation_positiveIntExtension_pair` (proved) is the bridge from
   `elliottLogCorrelation … 1 1 c₁ c₂` to `shiftedPairLogCorrelation`.
2. **The AP-mod-`a` restriction — expected to be a genuine third generalisation.**
   For general `a`, substituting `m = a·n` gives
   `∑_{n} (1/n) f₁(an+c₁) f₂(an+c₂) = a ∑_{m ≡ 0 (a)} (1/m) f₁(m+c₁) f₂(m+c₂)`,
   i.e. the pure-shift correlation **restricted to an AP of modulus `a`**.  The graph step
   `N ↦ pN` sends the class `N ≡ r (a)` to `pN ≡ pr (a)`, so the residue class is *not*
   preserved and the restriction must be carried through the graph argument.  Note the
   additive-character expansion `1_{a|m} = (1/a) ∑_j e(jm/a)` is **not** a way out: the
   twist `m ↦ e(jm/a)` is not multiplicative, so the resulting correlations are outside the
   rung.  Record the verdict either way; if the AP genuinely must be threaded, the cheapest
   route is probably to make the *block* carry the residue (the entropy layer already
   accepts an arbitrary finite alphabet, so `α × ZMod a` is admissible).
   Leaf 2 (`nonasymptotic_of_affineCM`) will itself produce divisibility constraints
   `d ∣ aᵢn+bᵢ`, so a single AP-capable rung discharges both needs.
3. **Leaf 2** (`1`-bounded multiplicative → CM unimodular) is untouched and is the larger of
   the two remaining risks.  Full route is in its docstring in `ElliottLadder.lean`.

## Confidence

The crux's analytic core is done, with the dependency's constants throughout and both shift
orientations available; nothing left on the `DilatedCMLogElliott` path has feasibility in
doubt except item 2's AP threading, whose difficulty is now precisely stated.  Leaf 2 remains
standard but unstarted multiplicative-function technology.

`DIRECTION.md`'s CURRENT DIRECTIVE (2026-09-23) predates the Elliott kickoff (2026-09-24) and
this run's explicit operator scope, and does not mention Elliott; its forbidden-drift list
does not cover these files.  Left unedited — altitude laps own it.
