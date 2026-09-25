# HANDOFF 2026-09-25 (session 2) — TT interface repaired; the faithful archimedean supply, narrowed

**Branch** `wip/c3-mrt`   **HEAD** `563a4bd`   **Build** green, `lake build` 9442 jobs, clean tree.
All new results carry only `[propext, Classical.choice, Quot.sound]`.

## What this session did (laps 102–107)

1. **Lap 102 — the defects, machine-checked** (`src/NormalNumbers/C3MrtTTDefect.lean`).
   `ttNonPretentious_trivial` (old `TTNonPretentious` free for every 1-bounded `g`),
   `not_kPointNoExcWith_const_one`, `not_kPointNaturalCorrelationNoExc`,
   `not_twoPointNaturalCorrelationNoExc` (the `D = 2` "named open problem" was FALSE, not open),
   `twoPointNaturalCorrelation_trivially_true`.  Faithful restatements + guards:
   `ttPretentiousSumChar` (Dirichlet characters, `conj χ`, verified against paper lines 557-576),
   `TTNonPretentiousAt A` / `TTNonPretentiousUnif`, `TwoPointDyadicCorrelation`,
   `KPointNoExcAtWith A`; guards `not_ttNonPretentiousUnif_one`, `not_ttNonPretentiousAt_one`,
   `full_exceptional_set_not_admissible` + `exists_L_cost_lt_one`.  4 `Maze.lean` kernel rows.
   SURVIVORS table: `HANDOFF-2026-09-25-tt-interface-restated.md`.
2. **Lap 103 — headline repaired.**  `C3MrtUnifK.KPointNoExcFor Pnp` + `C3MrtSlowSched.ArchSupply
   Pnp` make the window/schedule/threshold chain parametric in the archimedean hypothesis
   *in place*; `C3MrtFaithfulInput.conjC3_of_geom_input_at` is `ConjC3` from two faithful,
   non-vacuous inputs.
3. **Lap 104 — the new crux decomposed** (`C3MrtArchFaithful.lean`).  `ttPretentiousSumChar_eq`:
   the faithful sum is `∑_{p≤X²}1/p − Re(z·twistedPrimeSum)`.  Chain
   `NarrowTwistSmall`+`WideTwistSmall` → `FaithfulArchLower` → `ArchSupply` → `ConjC3`.
   Two sub-routes refuted: the norm-only narrow bound (false at `t=0, χ=1`), and the resonance
   certificate in the wide range (its `log(2+|t|)` loss is `≍ log X` there).
4. **Lap 105 — narrow range at `q = 1` proved.**  `ttPretentiousSum_lower_of_uniformResonantMass`
   (content extracted from the vacuous corollary) → `narrowTwistSmallTriv_of_uniformResonantMass`.
5. **Lap 106 — principal characters reduced to `q = 1`.**  `sum_inv_primes_dvd_le`,
   `norm_twistedPrimeSum_principal_sub`, `twistedPrimeSum_zero_modulus`,
   `narrowTwist_principal_of_triv`, `narrowTwistSmall_of_triv_of_nonPrincipal`.
6. **Lap 107 — uniformity in `h'`, exponent side.**  `resEps_depthRoot_ge`
   (`|arg(depthRoot b h' 0)| ≥ 2π/b`), `kappaDepth b := (1/10)·min(π/b,1/256)²`,
   `ttExponent_depthRoot_ge`.

## Where the headline stands

    conjC3_of_geom_input_at :
      (∀ b ≥ 3, ∀ K, KPointNoExcAtWith A (cKgeom c₀ θ b) (CstKdeg m) K) →
      (∀ b ≥ 3, ArchSupply (TTNonPretentiousAt A) b) → ConjC3        (0 < θ < 1)

and `conjC3_of_geom_input_lower` replaces the second input by `FaithfulArchLower b C`.
Open obligations, all named in `src/`:
* `NonPrincipalTwistSmall` — narrow range, `χ ≠ χ₀`; expected EASY (`L(1+it,χ)` non-vanishing
  gives `O(log log(q(2+|t|))) = O(log log log X)` in TT's range).
* `WideTwistSmall` — `|t| > (log X)^{1/125}`; needs a zero-free region for `L(s,χ)`.
* the constant side of the `h'`-uniformity: a `Finset.max` over the `b−1` values of `h' mod b`.
* `KPointNoExcAtWith` — the correlation input itself (the original crux, one Weyl sum).

## Next steps, in order

1. Finite-max step for `C₁` (index by `k : Fin b`; `depthRoot b h' 0` depends only on `h' mod b`),
   then assemble `FaithfulArchLower b C(b)` end-to-end.
2. `NonPrincipalTwistSmall`: look for a mathlib/PNTPort route to `∑_{p≤Y}χ(p)p^{-it}/p` bounds.
3. Rethread `C3MrtRootsInput` / `C3MrtDepthInput` / `C3MrtEvtInput` / `C3MrtDyadicInput` onto
   `KPointNoExcFor` (mechanical; they are copies of the `_with` chain — all currently VACUOUS).

No uncommitted edits.
