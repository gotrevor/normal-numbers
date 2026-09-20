# HANDOFF 2026-09-20 — N1a proved, N1a′ reduced: the G₄ window law now rests on **two** nodes

Branch `wip/g5-prime-subset`.  Continues `HANDOFF-2026-09-20-rough-independence.md`, whose
"next attack" was: *probe `SmoothRoughDecoupling` (the only unprobed node in the new chain)*.
Done, and the probe cracked it open further than expected.  File
`src/NormalNumbers/G4WiringRough.lean` is **sorry-free** throughout; every theorem below is
`[propext, Classical.choice, Quot.sound]`.

## Where the chain stood, and where it stands

Start of lap (after the split lap), on the non-Chowla sector:

    CRTConstantSched h  ⟸  RoughIndependence h  ∧  SmoothRoughDecoupling h  ∧  SmoothNonvanishing h
                               (frozen)               (frozen, unprobed)         (frozen)

End of lap:

    CRTConstantSched h  ⟸  RoughIndependenceAt h 2  ∧  ParityDiscrepancy h
                               (the crux)                (new, strictly weaker than N1a′)

`isNormal_G4_of_parity` is the headline wiring with exactly those two hypotheses.

## 1. N1a is now a **theorem** (`smoothNonvanishingAt_two`)

For `h ≠ 0` with `v₂(h)` even, `∏_{j≤windowJ N} ‖smoothSiteMean N h j 2‖ ≥ δ > 0` eventually.
The period-2 average is `(1 + e(h 4^{-j}))/2`, of modulus `|cos(π h 4^{-j})|`; it vanishes iff
`v₂(h) = 2j − 1` — *exactly* the Chowla sector, which is why `ChowlaSector` was defined as
`Odd (padicValInt 2 h)`.  Head: a finite product of nonzero factors.  Tail:
`1 − 2π|h| 4^{-j}`, Weierstrass bound plus a geometric tail.  Transfer to the site means by
`periodic_mean_close` (`4/N` per site) and `norm_prod_sub_prod_le`.

Supporting: `omegaLe_two_eq`, `halfAvg`, `smoothSiteMean_two_close`,
`ePhase_ne_neg_one_of_not_chowla`, `one_sub_sum_le_prod`, `sum_quarter_pow_Ico_le`.

The frozen `SmoothNonvanishing` statement was **not** edited: a single-`y` form
`SmoothNonvanishingAt` was added (the frozen Prop is definitionally `∀ y ≥ 2, …At h y`), and
`smoothWindowCRT` / `crtConstantSched_of_rough` keep their types as corollaries.

## 2. N1a′ is **reduced**, via two exact covariance identities

Probe (`PROBE-2026-09-20-smooth-rough-decoupling.md`, `probes/rough_decoupling.py`): the node
holds, `rel·log N` flat, local exponents 0.70–1.32 bracketing 1.  But the probe's real payoff was
structural.  At `y = 2` the smooth phase is **two-valued** — at a site because `ω_{≤2}(m) = [2∣m]`,
at the *window* because `[2 ∣ n+j+1]` alternates in `j`, so `smoothTail 2 J n` depends on `n` only
through its parity (`smoothTail_two_eq`, values `tailEven J` / `tailOdd J`).  For any two-valued
factor the covariance is computable outright:

    twoValued_covariance :  𝔼[s·r] − 𝔼[s]𝔼[r] = (a − b)(c_¬p Σ_p r − c_p Σ_¬p r)/N²

with no hypothesis on `r`.  Both halves of `SmoothRoughDecoupling` at `y = 2` are instances
(`fullSiteMean_covariance_identity`, `fullWindowMean_covariance_identity`), so the node collapses
to one quantity, `parityDisc`.  Hence the new node

    ParityDiscrepancy h : ∃ C, ∀ᶠ N, (∀ j ≥ 1, ‖parityDisc N j (roughPhase h j)‖
                                        ≤ C/log N · N²‖fullSiteMean N h j‖) ∧ (window analogue)

and `smoothRoughDecouplingAt_two_of_parity : ParityDiscrepancy h → SmoothRoughDecouplingAt h 2`.
The reduction needed **relative** telescoping (`norm_prod_sub_prod_rel`, `prod_one_add_le`): the
target bound is relative to `∏‖fullSiteMean‖`, which decays, so the uniform-ε bound is useless.
The `J`-uniformity comes free from `‖e(h4^{-j}) − 1‖ ≤ 4π|h|4^{-j}`, whose sum over `j` converges.

## 3. What `ParityDiscrepancy` *means* (`parityDisc_eq_scale`)

`ω_{>2}(2m) = ω_{>2}(m)`, so summing the rough phase over the *even* arguments of a window is
summing it over a window at **half the scale** (`sum_even_eq_half`, `omegaAbove_two_double`,
`sum_shift`).  Exactly:

    parityDisc N j (roughPhase h j) = N · roughSum h j ⌈(N+j)/2⌉ ⌈(2N+j)/2⌉ − cₑ · roughSum h j (N+j) (2N+j)

No oscillating sum: the node says the rough mean **changes by `O(1/log N)` when the scale is
halved**.  For a Selberg–Delange mean `≍ c(log N)^{z−1}` that is the derivative bound
`(1 + log 2/log N)^{z−1} = 1 + O(1/log N)` — strictly more classical than the Halász input that
`RoughIndependence` needs.

Probed directly (`probes/parity_discrepancy.py`): `‖parityDisc_j‖/(N²‖full_j‖)·log N` is flat in
`N` at `≈ 0.75, 0.47, 0.17, 0.04, 0.01` for `j = 1..5` — `C ≈ 1.5` covers `h = 1,3,5`, and the
`4^{-j}` decay in `j` is visible.

## Next attack (in order)

1. **`RoughIndependenceAt h 2` is now the sole crux** — the window mean of the rough phase
   factorises into its site means, relative error `O(1/log N)`.  This is the Halász /
   Selberg–Delange node; nothing in the lap touched it.  Attack: the same two-valued trick does
   **not** apply (the rough phase is not finitely-valued), but the window/site comparison is again
   a covariance, so the first honest step is to write `roughWindowMean − ∏ roughSiteMean` as a
   telescoping sum of *two-site* covariances and probe whether the two-site correlation carries
   the `1/log N`.
2. **`ParityDiscrepancy` via scale-smoothness.**  `parityDisc_eq_scale` already reduces it; what
   is missing to make it a *theorem* is a lower bound on `‖fullSiteMean N h j‖` (the statement is
   relative), for which the `cₑ` vs `N/2` slack (`|cₑ − N/2| ≤ 1/2`, harmless morally) is the only
   obstruction.  Consider a variant node stated with `roughSiteMean` on the right instead.
3. `SmoothRoughDecoupling` for general `y` (not needed by the wiring) would want the CRT product
   `∏_{p≤y}(1 + (z−1)/p)`; not worth it — the wiring fixes `y = 2`.
