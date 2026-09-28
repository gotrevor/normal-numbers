# PENDING WORK — the queue

Concrete next moves, cheapest and most clear-cut first.  Front context is in `STATUS.md`.  The
lap-by-lap log from before the 2026-09-27 merge is `archive/PENDING_WORK-to-2026-09-27.md`.
Treadmill laps append dated notes **below the queue**, and a review lap folds them back into it.

## Queue

1. **Moshchevitin-Shkredov refutation.**
   - Prove `moshchevitinShkredov_cf_false` with the witness `[0;1,2,3,…]`.  It is elementary.
   - Wire the file into the root import and add a `Maze.lean` row marked "false as stated".
2. **C3/MRT headline without `hURM`.**
   - Instantiate `conjC3_of_geom_input_band` with `uniformResonantMass_holds`.
   - Retire `highResonantMass_le_narrow` / `C3MrtURMLowHigh.lean` as a redundant second route,
     with a Maze row.
3. **Vandehey: retire `exists_jointFreq_limit`.**  Its `Synchronizing` hypothesis cannot hold,
   so it needs a Maze row citing the probe.
4. **Vandehey crux `vandeheyUniformFreq_holds`.**
   - First evaluate the Smith-normal-form shortcut: `GL₂(ℤ)` maps, where CF tails agree
     (Serret), plus `x ↦ Dx` for prime `D`, which the class automaton already covers.
   - Otherwise, follow the NEXT list in `archive/handoff/HANDOFF-2026-09-28-vandehey-bridge-CLOSED.md`.
5. **Joint Lambert, unconditional.**  Discharge `AGP` and `PrimeIntervalSupply` from PNT+
   (`WeakPNT_AP`, PNT).  After that, the quantitative §6 count is a separate target.
6. **C3/MRT `CharTailCancellation`.**  This is the only C3 input with a standard-literature proof:
   Euler product, then `L(1,χ) ≫ q^{-1/2}`, then arg-L winding.
7. **Elliott margin check.**  A Littlewood-strength `ζ'/ζ ≪ log t / log log t` would suffice if
   every consumer in `ElliottZetaTheta.lean` tolerates a `log log log` margin.  Check that.  If
   one doesn't, record "Vinogradov or nothing" in the Maze.
8. **SwingC2 triage.**  Delete or restate `tauMomentPrimesShiftStruct_of_primeDensity`, which
   takes the vacuous `PrimeDensityAP`, and `survivorLeaf_of_struct`.
9. **OVERVIEW refresh.**  Add Joint Lambert, Wall, Philipp, Vandehey §3 and the merged C3/Elliott
   state.

## Lap notes (newest first)
