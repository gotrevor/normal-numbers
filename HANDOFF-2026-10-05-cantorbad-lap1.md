# HANDOFF 2026-10-05 cantorbad lap 1 (branch proof/cantor-bad-normal)

Target: `CantorBadNormal.exists_mem_cantorSet_bad_isNormal_coprime_three` (frozen, unchanged).

## Done (59f8c6e0)
- Headline is now PROVED from leaves: `exists_of_law descentLaw casselsPower_descent`.
- Proved wiring: `Law` (coins → digit selector φ, measurable, surely Bad), `CasselsPower`
  (per-h power saving `C N^{2-δ}`), `summable_sched_rpow`, `ae_isNormal_of_casselsPower`, `exists_of_law`.
- Concrete descent: `cylLeft`, `cyl`, `Alive` (stage window 3^{L-r} ≤ q² < 3^{L+r}, obstacle 2c/q²),
  `sel`, `build`, `descent`, `measurable_descent` (proved), constants r = 5, `c₀ = 3⁻¹⁵/2`.
## Open leaves (all in CantorBadNormal.lean, linked in BarrierAudit)
- `exists_alive` (85%, counting: 490 < 1024), `cpt_mem_cyl` (95%), `descent_bad` (90%, wiring) — tractable.
- **Crux** `casselsPower_descent` (55%). Guard: Bad₂ sibling (sweep §2.3) — must use arithmetic of p/q.
## Next attack
1. Crux: expand E|S_N|² = Σ ν̂(h(bⁿ−bᵐ)); write ν = μ_K-descent as μ_K-product perturbed by the
   replacement map; isolate the "dead-pick" event per block and bound the Fourier transform of the
   correction measure by Σ_p e(ξ p/q)-cancellation (Kaufman-style). State that correction bound as a
   named sub-leaf first.
2. Record the Bad₂ sibling as a Lean theorem (currently prose only in the docstring).
3. Discharge the three tractable leaves.

## Update 2026-10-06
- K ∩ BAD half fully proved (exists_alive via card_dead_le ≤ 488, descent_bad, cpt_mem_cyl).
- Crux is now `fourierPairRate_descent` (rate W summable along sched; reduction proved).
- Refutation in Lean: `perStage_deadCount_not_enough` (base-2 dyadic descent: ≤4/1024 dead, never
  2-normal) — registered barrier `perStage_dead_not_enough` on the crux.
- Closed route: `not_exists_timesThree_law_on_bad` (cited EFS), Maze row.
- Next: state the arithmetic sub-leaf (orbit cancellation of Σ e(h(bᵏ−bˡ)p/q) over dead centres);
  see PENDING_WORK 2026-10-06.
