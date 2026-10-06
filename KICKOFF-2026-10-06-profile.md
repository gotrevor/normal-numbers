# KICKOFF 2026-10-06: the exponent sets the normal profile (prepped, not launched)

Branch `proof/cantorexp-profile`, file `src/NormalNumbers/CantorExactExponentProfile.lean`.

Headline (frozen): `exists_computable_mem_cantorSet_irrExponent_normalProfile`.  The stretch
point is normal to `b = 3ˢt` iff `t > 3^{s(μ₀−1)}` (`ProfileOK`), for every rational `μ₀ > 2`.

Order of work:
1. `not_isNormal_of_not_profileOK` (elementary, 90%).  Generalize
   `CantorExactExponent.not_isNormal_of_three_dvd_of_small` from digit frequency to the block
   `0^ℓ`, and use `j ≥ a/s` (not `j ≥ a`) as the integrality start.
2. `ae_isNormal_of_profileOK` (the crux, 70%).  Port `CantorLiouvilleAll.secondMoment_le_b`
   to `b = 3ˢt`.  The pair frequency `h bᵐ(bᵈ−1)` has ternary digits `h(bᵈ−1)tᵐ` shifted by `sm`.
   The orbit counting uses `t`.  The free count comes from the window lemma: below the threshold
   no run covers `[sm, (s+log₃t)m]`.  State the window lemma first, as its own declaration.
3. Wiring: extend the derandomizer test family with the `3 ∣ b` bases.

The mechanism must fail on the sibling `t = 1` (powers of 3); check that the port's
hypotheses exclude it.  A refutation is an advance: if step 2 dies, freeze the reason as a Maze
row.  Done-when: the headline is sorry-free and the root audits are green.
