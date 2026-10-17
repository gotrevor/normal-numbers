# Prime class lap 9 reflection (2026-10-17): dependent half proved

## Concrete advance

- Reflection corrected the recurring scheduling description in laps 6--8.  The kick-depth pattern
  is not additively periodic in `n`; it is covariant under multiplicative dilation.  With
  `A = ∑ i, u i * p^(s i)` and `L = ∏ i, s i`, every cell
  `[A*p^(L*t), (A+1)*p^(L*t))` has
  `K_i(n) = K_i(A) + (∏_{j≠i} s_j)*t`.  Thus all weighted gaps
  `T - s_i*K_i(n)` are fixed on the whole cell.
- The new sorry-free `StonehamPrimeClassSchedule.lean` proves that exact depth formula and the
  fixed-gap theorem.  It then combines lap 8's literal numerator divisibility with the rational
  state bridge to show that the reduced mixed-`s` state is exactly an integer throughout every
  dilated cell.  Concrete singleton and empty-family anchors check the definitions.
- The new sorry-free `StonehamPrimeClassNonNormal.lean` isolates the analytic obstruction.  If a
  multiply-by-`b` orbit is `O(1/n)` from integers throughout those fixed-proportion geometric
  cells, its fractional parts put too much mass in two arbitrarily thin edge intervals, contrary
  to equidistribution.
- `not_isRationallyJointNormal_of_not_linearIndependent` is now proved.  It takes the integral
  cyclotomic witness from lap 6, reduces the exponents by the inverse Mahler identity, applies the
  fixed-gap state integrality theorem, and contradicts normality with the edge-visit obstruction.
  The scoped file now has exactly one direct `sorry`, the independent/normal half.
- The proved headline's `BarrierAudit` waiver is removed.  The Maze row `joint normality is
  pairwise` remains correctly `.parked/.frozen`: its explicit pairwise proof still transitively
  uses the remaining normal-half `sorry` through T-B', so the kickoff's instruction to promote
  that row applies only after the normal half is axiom-clean.

## Verification

- `lake env lean src/NormalNumbers/StonehamPrimeClassSchedule.lean` — success, no warnings.
- `lake build NormalNumbers.StonehamPrimeClassSchedule` — success, 8,781 jobs.
- `lake build NormalNumbers.StonehamPrimeClassNonNormal` — success, 8,782 jobs.
- `lake env lean src/NormalNumbers/StonehamPrimeClass.lean` — success; the only warning is the
  remaining normal-half `sorry`.
- `lake build NormalNumbers.BarrierAudit` — success, 10,394 jobs; 26 proved, 6 cited, 2 frozen.
- `~/personal/bin/lean-green ~/src/nn-prime-class --target NormalNumbers.StonehamPrimeClass
  --import NormalNumbers.StonehamPrimeClass` with axiom checks for
  `primeClassSchedule_fixedGap`, `stonehamState_eq_int_of_fixedGaps`,
  `primeClassSchedule_state_eq_int`, `not_equidistributed_of_geometric_edge_visits`,
  `not_isNormal_of_geometric_integer_approx`, and
  `not_isRationallyJointNormal_of_not_linearIndependent` — 8,963 jobs; every declaration is
  exactly `[Classical.choice, Quot.sound, propext]`; final verdict `FORMALIZE-TIER GREEN`.
- A separate diagnostic axiom run on `stonehamThreeSevenPairwiseNormal_holds` and
  `stonehamThreeSeven_pairwise_not_joint_unconditional` ended `RED` with `sorryAx` on both, as
  expected: it confirms that the Maze promotion must wait for the normal half.
- `git diff --check` — clean.

## Current blocker

Only `isRationallyJointNormal_of_linearIndependent` remains directly sorried.  For an arbitrary
nonzero rational coefficient vector, first restrict to its nonzero support (linear independence
is inherited), clear denominators, and apply inverse Mahler normalization.  At time `n`, let
`K_i = stonehamK (p^(s_i)) u_i n` and choose the largest weighted depth `T = max_i s_i*K_i`.
The threshold inequalities for `stonehamK` imply a uniform bound on every gap
`δ_i = T - s_i*K_i`; this is the next elementary scheduling lemma.

For each of the finitely many bounded gap patterns, the leading cleared-state coefficient is a
nonzero rational combination of the independent powers `ζ^(u_i)`.  Clear it to an integral
polynomial, prove its cyclotomic resultant is nonzero, and use the finite Teichmüller congruence
to bound its `p`-adic valuation by a pattern-dependent constant.  Maximizing over the finite
patterns gives
`den(stonehamState n) ≥ p^(T-B)`.  Since `T` grows logarithmically with `n`, this yields a
`StonehamStateDenPowerLower`, after which
`stonehamCombination_mean_tendsto_of_powerLower` and Weyl finish the normal half.

## Next highest-value attack

Create `StonehamPrimeClassPowerLower.lean`.  Start with the uniform weighted-depth-gap bound and a
finite encoding of all gap patterns, including a concrete small-family anchor.  Then prove the
per-pattern nonzero resultant from `LinearIndependent` and package the uniform p-adic loss before
wiring the analytic theorem.  Do not return to additive-periodic cells: multiplicative dilation
was the dependent-half mechanism, while bounded max-depth gaps are the normal-half mechanism.
