# PENDING WORK — B5′ / W3 campaign (staged 2026-08-23)

**Campaign**: discharge the 4 sorries in `src/NormalNumbers/CFMixing.lean`
(work package W3 of expedition B5′, **the core** — see `HANDOFF.md` for the
route and `KHINCHIN.md` "W3 route" for the plan).  Everything else in
`src/` is sorry-free: Stoneham ✅, W1 (12/12) ✅, W2 (10/10) ✅ — all
axiom-clean, judge-verified; records in `ROADMAP.md`, `JUDGE.md`, and
`archive/handoff/`.

**Open (4/4)**: `measurePreserving_gaussMap` ·
`volume_inter_preimage_eq_integral` · `cylinder_mixing` · `gauss_kuzmin`

**Crux**: `cylinder_mixing` (the cone/ratio-contraction — expect it to be
most of the campaign; ⚠️ it carries the judge-governed escape valve, see
HANDOFF).  `volume_inter_preimage_eq_integral` is the real-analysis
substitution (LFT image measure).  `measurePreserving_gaussMap` is the
classical telescoping branch sum.  `gauss_kuzmin` should fall out of the
`cylinder_mixing` development (`t = 0` start), not get its own machinery.

**Done-when**: `src/` sorry-free (the default self-stop gate) + the 4
axiom-clean.  Toolchain: v4.33.1, present in the box store — no gate.
