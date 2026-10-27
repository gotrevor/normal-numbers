# Route 2 false-starts and structural reductions

**Disposition, 2026-10-26: abandoned as intractable with current methods.**
Registered as `Pi route 2: prime reservoir and residual coupling` in `Maze.lean`,
with checked evidence and open-premise links in `MazeAudit.lean`.
This includes the cutoff and approximate-coupling variants already investigated.
Reopening requires a concrete mechanism forcing visits of the sum, explaining
which comparison hypotheses it escapes.  A new cutoff or transverse estimate
alone does not qualify.  This is not a refutation of every possible reservoir argument.
Policy and complete follow-up inventory: [MAZE.md](../../MAZE.md).

- idea: joint-uniformity probe vs composite control / promising: primes are the uncancellable source /
  fails: composite-denominator control is equally uniform (N=1500), so the statistic cannot credit
  primality / witness: `scripts/pi_route2_joint.py` output in HANDOFF lap 1.
- idea: primes leaving the window inject an O(1) "random" transfer R→S / promising: residues of 16^k
  mod distinct primes look uncorrelated / fails: only p = 4n+1 leaves, and Euler's criterion makes
  the residue exactly 64 mod p, so the transfer is 64/p = O(1/n) / witness: `bbpReservoirExit_mod_one`.
- idea: route premise (joint support of reservoir and residual) / promising: fresh prime poles
  survive (`fresh_prime_dvd_head_den`) / fails as a lever: the reservoir is within 10/(n+1) of the
  x16 orbit of a fixed constant rho (`bbpPrimeReservoir_near_orbit`), so the premise forces
  base-16 disjunctivity of rho (`reservoirConst_disjunctive_of_support`), an open problem of the
  sink's own kind / possible next inputs: `ReservoirConstDisjunctive` or a special identity for rho.

## Review, 2026-10-26

`reservoirConst_disjunctive_of_support` is a necessary-condition theorem.  Together
with the π transfer it gives two consequences of the same premise; it does not
compare the difficulty of disjunctivity of ρ and π, or prove the approach impossible.
The O(1/n) exit-collapse theorem is a concrete obstruction to the proposed large
transfer mechanism **for the cutoff 4n**.

The cutoff is a real lever left untested by the lane.  Replacing 4n by 6n keeps
each selected prime above 4n, preserving denominator uniqueness, but changes
the exit congruence.  `ReservoirCutoffReview.lean` proves the exact sole-exit
witness at n=14: p=89 contributes 2945 + 39/89, not an integer plus 64/89.
It also proves the p=24k+1 cubic identity.  `CutoffSixCubicLaw` records the general
formula: exit numerator cubed is 64³ mod p for p=1 mod 6 and 1024 mod p for
p=5 mod 6.  That general formula is a formal unproved node; the exact probe
`scripts/pi_route2_cutoff_review.py` verifies all 1123 applicable primes ≤20000,
with the original 1125-prime cutoff-4 theorem as its control.  471 new residues
lie between p/4 and 3p/4.  Finite data do not prove infinitely many large transfers.

The new transfer still acts along (1,-1), so it cancels in R+S.  A proof about
transverse motion alone cannot establish density of the π projection.  The
cutoff variation escapes this specific resonance, not the whole digit problem.

Before a blind integer-relation search, the recurrence offers an exact candidate
regrouping: ρ = Σ_{p=1 mod 4} 4 q_p / 2^{p-1}, where
q_p = ((2|p) 2^{(p-1)/2} - 1)/p is an integer.  The infinite identity is the
unproved node `RhoDyadicIdentity`; the script checks each finite-prime contribution
exactly through p≤200.  This exposes dyadic Fermat-quotient summands, not a proof
of a useful identity with π.

Independent axiom audit: the original denominator theorem, support transfer,
exit collapse, orbit shadow, necessary condition, and diagonal transfer use only
`propext`, `Classical.choice`, and `Quot.sound`.  An intentional sorry control
reported `sorryAx`.  Audit source is in `tmp/20261026-review/Axioms.lean`.
