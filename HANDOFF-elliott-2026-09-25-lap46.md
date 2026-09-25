# HANDOFF elliott 2026-09-25 lap 46 — the dilated crux is CLOSED

Branch `wip/elliott-port`.  `lake build NormalNumbers.ElliottGeneral` green (9565 jobs).
Never `lake exe cache get`.  Never edit `.lake/packages/lean-proofs-latest/`.

## What landed (all zero sorry, `#print axioms` = trust triple)

**`NormalNumbers.ElliottDilatedRung.dilatedCMLogElliott` is now a real theorem.**  Leaf 2 (the
mirror) is proved, so the whole dilated crux rung is axiom-clean.

Route taken: the handoff's option (a), but made cheap.  The asymmetry of the dilated stack is only
apparent — in `norm_dilatedPairTwistedMean_le_largeFrequencies` the two blocks enter the pairing
`‖F_b(t+uD)‖·‖F_{conj c}(t)‖` symmetrically and Parseval is applied to both, so which factor
survives the large-frequency sum is free.  (Option (b), relabelling via
`elliottLogCorrelation_swap`, is genuinely impossible: swapping exchanges functions *and* shifts, so
it maps "non-pretentious at the smaller shift" to itself.  Same obstruction as recorded in
`ElliottTwistedGraphMirror`'s header.)

1. **`src/NormalNumbers/ElliottDilatedUpperMirror.lean`** (new).
   * `norm_dilatedPairTwistedMean_le_largeFrequencies_snd` — the other threshold choice; the second
     block survives at the **plain** frequency `t` (the alias shift `u*D` lives on the discarded
     first block), so the moment hypothesis is simpler than the un-mirrored one.
   * `affineBlock_conj`.
   * `norm_logProb_dilatedPairTwistedMean_le_of_fourier_first_moment_snd`.
   * `exists_dilatedPairTwistedMean_small_of_fourier_first_moment_snd` — same choreography
     (`cutoff = η/64`, `N = C/cutoff⁴`, `ζ = η/(1024(N+1))`), untouched.
2. **`src/NormalNumbers/ElliottDilatedSelectMirror.lean`** (new).
   `exists_affineLogCorrelation_small_of_fourier_first_moments_snd`.  The lower bound
   (`exists_logProb_dyadic_dilatedMean_lower`) is symmetric in the two functions and needed no
   mirror; only the upper half of the collision changes.
3. **`ElliottDilatedRung.dilatedNatShiftCMLogElliottMirror`** — the forward proof verbatim with MRT
   applied to `conj ∘ f₂`, legitimate by `ElliottTwistedGraph.mrtNonpretentious_conj` (already in
   `src/` from the pure-shift mirror lap).

## Open `sorry`s in scope (1)

| # | obligation | file:line |
|---|---|---|
| 1 | `nonasymptotic_of_affineCM` (leaf 2/3, Hall) | `ElliottLadder.lean:297` |

## NEXT (lap 47)

`nonasymptotic_of_affineCM` is now the *only* thing between here and
`Erdos67b.NonasymptoticLogElliott`.  Hall's inequality; decomposition in `PENDING_WORK.md`
Finding 2.  Case A's thin-window sub-regime is the only hard part; Shiu is NOT needed.
