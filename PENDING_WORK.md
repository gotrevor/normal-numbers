# PENDING WORK — B5′ / W2 campaign (staged 2026-08-23)

**Campaign**: discharge the 10 sorries in `src/NormalNumbers/CFDigitLaw.lean`
(work package W2 of expedition B5′ — see `HANDOFF.md` for the route and
`KHINCHIN.md` for the full plan).  Everything else in `src/` is sorry-free:
Stoneham ✅ and W1 (`CFCylinder.lean`, 12/12 axiom-clean, judge-verified) ✅
both landed 2026-08-23; records in `ROADMAP.md`, `JUDGE.md`, and
`archive/handoff/` (W1 per-lemma record:
`archive/handoff/PENDING_WORK-2026-08-23-W1-final.md`).

**Open (10/10)**: `volume_digit_cylinder` · `cfCylinder_disjoint` ·
`volume_eq_tsum_extensions` · `gaussMeasure_le_volume` ·
`volume_le_gaussMeasure` · `gaussMeasure_univ` · `cfK_le_prod` ·
`tsum_mul_log_cfK_le` · `half_mass_long_extensions` ·
`volume_append_mul_fib_le`

**Crux candidates**: `volume_eq_tsum_extensions` (irrational orbit → genuine
digits → countable-null bookkeeping; W1 proved the needed digit lemmas as
`private` in `CFCylinder.lean` — re-prove locally or lift them into a shared
module, both fine) and `tsum_mul_log_cfK_le` (per-position digit marginals +
a summable majorant for `Σ log(k+1)/(k(k+1))`).  The rest are
specializations and `withDensity` plumbing.

**Done-when**: `src/` sorry-free (the default self-stop gate) + the 10
axiom-clean.  Toolchain: v4.33.1, present in the box store — no gate.
