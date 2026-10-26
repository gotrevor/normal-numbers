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
- Lap 3: Maze row "Cutoff-six prime reservoir as an arithmetic source for pi" (wall, kernel),
  linked in MazeAudit (which now imports the cutoff-six files, so they build in the default target).
  Brief's deliverables complete; open node: `CubicRootEscape` (no known mechanism).

## BLOCKER (box stuck, 2026-10-26)
Operator brief docs/pi-routes/opus-cutoff-six-followup.md is fully delivered (commits bcd2af3e,
3fa836a4, 8bbdc428).  The session's operator scope is that brief only; other src sorries belong to
other campaigns (DIRECTION.md gate-5 directive, other branch).  The one open item from the brief,
`CubicRootEscape`, is an Artin-type equidistribution statement with no known mechanism.
Ask: operator decides whether to continue route 2 (e.g. attack CubicRootEscape or a coupling
to R+S) or reassign this run.

## Lap 4 (2026-10-26)
- Committed the pending rho PSLQ probe (no relation found; numerical with planted control).
- **Proved** `CutoffSix.cubicRootEscape_iff` (ReservoirCutoffSixRoot.lean; axioms clean):
  `CubicRootEscape ↔ CubeRootEscape`.  Since p ≡ 2 mod 3, cubing is bijective on ZMod p
  (`cube_inj`, x = (x³)^(80m+59)), so 2^(20m+18) is THE cube root of 1024 = 8³·2.  The open
  node is exactly a Hooley-type distribution statement for roots of x³−2 to prime moduli
  p ≡ 89 mod 120 (quadratic analogue is DFI/Tóth; cubic-to-primes open).  This is the
  "exact additional statement about cubic residues" the brief asked to isolate.
- Next attack: the p ≡ 1 mod 24 class has exit r with r³ ≡ 64³, so r = 64ζ; when 2 is not a
  cube mod p, ζ is a root of x²+x+1 and nonvanishing would follow from DFI-type
  equidistribution restricted to a ray class of Z[ω] — a quadratic (proved-literature-adjacent)
  lever, unlike the cubic node.  State that as a hypothesis Prop and reduce to it.
- **Proved** (ReservoirCutoffSixQuadratic.lean, axioms clean): `rationalExit_six_eq_one`
  (p=120t+1 prime, n=20t: exit = 2^(20t+6)/p exactly, one term), `dvd_quadratic` (if
  2^(20t) ≠ 1 mod p, numerator is a root of x²+64x+4096), and
  `nonvanishing_of_quadraticRootEscape`.  So nonvanishing now has two sufficient nodes: the
  cubic `CubeRootEscape` (Hooley-type, open) and the quadratic `QuadraticRootEscape`
  (DFI-type, restricted to p≡1 mod 120 with 2 not a sixth power; restricted form open but
  only a liminf).  Finite evidence (not proof): 2893/3651 such p < 2.4e6 have ‖E‖ ≥ 0.1.
- Next: state DFI (Annals 1995) faithfully as a cited hypothesis Prop and identify exactly the
  gap (Chebotarev restriction) between it and QuadraticRootEscape.
- **Proved** (ReservoirCutoffSixDFI.lean, clean): `quadraticRootEscape_of_rootFar`,
  `nonvanishing_of_restrictedRootFar`: ONE root ν with ‖ν/p‖ℤ ≥ 1/4 for infinitely many
  p = 120t+1 (2 not a sixth power) ⇒ nonvanishing (other root is −64−ν).  Stated (unused)
  `DFIWeak`, a weaker consequence of Duke–Friedlander–Iwaniec 1995 for x²+64x+4096.
  Exact remaining gap: `RestrictedRootFar` = DFIWeak restricted to the Chebotarev set.
  Next: find (ON-LINE-REQUEST) a source for DFI with ray-class/splitting restrictions
  (e.g. Tóth 2000, or Duke–Friedlander–Iwaniec ideal-class versions) and check whether the
  sixth-power condition on 2 is covered; if so, cite it as a hypothesis Prop.
