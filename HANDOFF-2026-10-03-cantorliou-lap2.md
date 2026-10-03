# HANDOFF 2026-10-03 — Cantor–Liouville (Bugeaud 10.37) lap 2 — DONE

`src/NormalNumbers/CantorLiouville.lean` is sorry-free.  `#print axioms` on both
`exists_liouville_mem_cantorSet_isNormal_two` and `exists_computable_liouville_mem_cantorSet_isNormal_two`:
propext, Classical.choice, Quot.sound.

## This lap
* `SchedDerandomize.exists_computable_normal_sched`: generic derandomizer along a primrec slow schedule
  `Ns` (ratio → 1) at resolution `nr → ∞`, from a second moment `≤ κ|h|N²W(N)` (W antitone) with
  `nr^6 W(Ns j) ≤ (j+1)^{-4}` eventually, plus an extra avoided primrec test family `bad'` of mass ≤ 1/(j+1)².
* CL application (section `Computable`): `secondMoment_le_explicit` (κ = 16 via 3^{v₃ h} ≤ |h|),
  digit reader `clNum/clA/clΨ` (primrec via `primrec_runStart`, `primrec_isFree`), schedule
  `clNs j = 4^s(4s+6t+4)` (`clNs_step`, `exp_sqrt_le_clNs`), `clNr = √j + 8`, `cl_ev`
  (free-count bound `sqrt_le_freeCount`, `M_ge`), Liouville window test `clBad` (`clBad_mass`,
  `frequently_free_of_clBad`).
* Headline docstring still says "Confidence 60%" (statement/docstring left untouched as frozen).

## Checkpoint
Branch `proof/cantorliou`, HEAD `39a0c5af` (+ this note).  Scoped target met; stop signalled.
Next (optional, outside scope): refresh the "Confidence 60%" docstring on the computable headline
(text only, if the operator un-freezes it); write `docs/notes/` entry for 10.37.
