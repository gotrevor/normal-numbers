# HANDOFF — pi route 2 (prime reservoir) — lap 3, 2026-10-26

## Node graph (all green unless noted; axioms = propext, Classical.choice, Quot.sound)
- `fresh_prime_dvd_head_den` (PrimeReservoir.lean): fresh prime poles survive (p-adic norm).
- `PiPrimeReservoirSupport` (premise, 70%→ see below) ⇒ `IsDisjunctive 16 π`
  (`pi_disjunctive_of_primeReservoirSupport`, with PiBBP).
- `PiReservoirDiagonalSupport` (PrimeReservoirDiagonal.lean): premise ⇒ node ⇒ sink.
- PrimeReservoirStep.lean:
  - `bbpPrimeReservoir_succ`: R_{n+1} = 16R_n − exit_n + entry_n.
  - `bbpResidual_succ`: S_{n+1} = 16S_n + exit_n + 16·kick_n − entry_n.
  - **`bbpReservoirExit_mod_one` (key finding)**: exit_n ≡ [4n+1 prime]·64/(4n+1) (mod 1).
    Only p = 4n+1 leaves the window, and 16^{(p-1)/4} = 2^{(p-1)/2} ≡ (2|p) cancels the
    coefficient sign (Euler's criterion).  Probe `scripts/pi_route2_exit.py`: 1125/1125,
    base-3 control 2/1125.

- PrimeReservoirOrbit.lean (lap 4): `bbpPrimeReservoir_eq_orbit`: R_n ≡ 16ⁿ·ρ_n (mod 1) exactly,
  ρ_n = Σ_{k<n} reservoirKick k / 16^{k+1}, kick_k = −[4k+1 prime]·64/(4k+1) + entry_k = O(1/k).

## What the finding means (the lane's research question, partial answer)
The "uncancellable O(1) arithmetic transfer" between R and S does not exist: mod 1 both
coordinates are ×16 pseudo-orbits with O(1/n) kicks.  Hence fract R_n = fract(16ⁿ ρ) + O(1/n)
for the FIXED constant ρ = Σ_k 16^{-k}·(kick of R at step k), a prime-indexed BBP-type
series, and S_n ≈ 16ⁿ(π − ρ).  The premise is then joint base-16 disjunctivity of the pair
(ρ, π − ρ): at least as hard as disjunctivity of ρ itself, which is open.  Route-2 confidence
that it gives leverage over plain digits: low (~10%).

## Next move
Bound |reservoirKick k| ≤ C/(k+1), define ρ := lim ρ_n (summable), prove
16ⁿ|ρ − ρ_n| ≤ C'/(n+1), then
state the obstruction node `PiPrimeReservoirSupport ↔ joint disjunctivity of (ρ, π−ρ)` and
add the route-2 Maze row (reopen condition: a lever on ρ's digits not available for π).
