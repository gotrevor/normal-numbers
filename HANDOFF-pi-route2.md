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

- Lap 5: `abs_reservoirKick_le` (|kick_k| ≤ 144/(k+1)), `reservoirConst` ρ := Σ' kick_k/16^{k+1},
  `bbpPrimeReservoir_near_orbit`: ∃ z, |R_n − z − 16ⁿρ| ≤ 10/(n+1).  All green, clean.

- Lap 6: **`reservoirConst_disjunctive_of_support`**: premise ⇒ IsDisjunctive 16 ρ (obstruction,
  green).  Reopen node `ReservoirConstDisjunctive`.

## What the finding means (the lane's research question, partial answer)
The "uncancellable O(1) arithmetic transfer" between R and S does not exist: mod 1 both
coordinates are ×16 pseudo-orbits with O(1/n) kicks.  Hence fract R_n = fract(16ⁿ ρ) + O(1/n)
for the FIXED constant ρ = Σ_k 16^{-k}·(kick of R at step k), a prime-indexed BBP-type
series, and S_n ≈ 16ⁿ(π − ρ).  The premise is then joint base-16 disjunctivity of the pair
(ρ, π − ρ): at least as hard as disjunctivity of ρ itself, which is open.  Route-2 confidence
that it gives leverage over plain digits: low (~10%).

## Status: lane closed under rule 9 (obstruction in Lean). Optional reopen probe:
## Next move
Lap 7: probe whether ρ has extra structure (closed form? rational? relation to π, e.g.
ρ − c·π rational) — any such identity would be the only lever left.  Also consider
state the obstruction node `PiPrimeReservoirSupport ↔ joint disjunctivity of (ρ, π−ρ)` and
add the route-2 Maze row (reopen condition: a lever on ρ's digits not available for π).

## Cutoff-six follow-up — 2026-10-26 (brief: docs/pi-routes/opus-cutoff-six-followup.md)
- **Proved** `CutoffSix.exit_six_not_eventually_small` (ReservoirCutoffSix.lean): ∀ C>0 ∀ N ∃ n≥N,
  C/(n+1) < ‖rationalExit 6 n‖ℤ.  Axioms: propext, Classical.choice, Quot.sound (sorry control
  shows sorryAx).  Mechanism: primes p=120m+89 (mathlib Dirichlet, unconditional), n=20m+14,
  full exit = 2^(20m+18)/p exactly (`rationalExit_six_eq`), A³≡1024 (`dvd_cube_sub`), 1024 not a
  cube ⇒ p ≤ |b|³+1024 (`le_abs_cube`).  Witness m=0 matches 2945+39/89.
- Independent adversarial review (subagent): no defects; caveat that `range n` drops primes
  only for n ≤ 2 (irrelevant).
- **Vanishing vs nonvanishing: open.**  Nodes `ExitSixVanishing`, `ExitSixNonvanishing`
  (ReservoirCutoffSixVanishing.lean), `not_vanishing_of_nonvanishing`, and the sufficient
  arithmetic node `CubicRootEscape` (2^((p+31)/6) mod p stays ε·p from 0 for infinitely many
  p≡89 mod 120) with `nonvanishing_of_cubicRootEscape` proved.  No mechanism known for the node.
- **Implication for π's digits: none established.**  Exits act along (1,−1) and cancel in R+S.
- Next: exact cutoff-six R/S recurrence (generalize PrimeReservoirStep to cutoff s), Maze row
  for the cutoff-six variant, and whether CubicRootEscape follows from any proved
  equidistribution of 2^k mod p (it resembles open Artin-type questions).
- Lap 2: `ReservoirCutoffSixStep.lean` proves the exact cutoff-s recurrences `reservoirS_succ`,
  `residualS_succ`, `reservoirS_add_residualS` (R+S = 16ⁿ·piPartial n, exit-free), `sub_succ`
  (R−S kicked by −2·exit), and `exitS_six_eq` (exit = rationalExit 6 n).  So the cutoff-six
  arithmetic acts only on the R−S direction; nothing transfers to the π sum.  Remaining: Maze row.
