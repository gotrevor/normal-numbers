# Route 2 false-starts

(idea / why promising / why it fails / witness) — none yet.

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
  sink's own kind / reopen: `ReservoirConstDisjunctive` or a special identity for rho.
