# Route 2 false-starts

(idea / why promising / why it fails / witness) — none yet.

- idea: joint-uniformity probe vs composite control / promising: primes are the uncancellable source /
  fails: composite-denominator control is equally uniform (N=1500), so the statistic cannot credit
  primality / witness: `scripts/pi_route2_joint.py` output in HANDOFF lap 1.
- idea: primes leaving the window inject an O(1) "random" transfer R→S / promising: residues of 16^k
  mod distinct primes look uncorrelated / fails: only p = 4n+1 leaves, and Euler's criterion makes
  the residue exactly 64 mod p, so the transfer is 64/p = O(1/n) / witness: `bbpReservoirExit_mod_one`.
