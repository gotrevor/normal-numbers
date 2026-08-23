# PENDING WORK — B5′ / W1 campaign (staged 2026-08-23; lap 1 landed the algebra batch)

**Campaign**: discharge the 12 sorries in `src/NormalNumbers/CFCylinder.lean`
(work package W1 of expedition B5′ — see `HANDOFF.md` for the route and
`KHINCHIN.md` for the full plan).  Everything else in `src/` is sorry-free
(Stoneham ✅ landed 2026-08-23; its record lives in `ROADMAP.md` and
`archive/handoff/`).

**Open (3/12)**: `volume_cfCylinder` · `volume_cylinder_append_le` ·
`le_volume_cylinder_append`

**Done (9/12, axiom-clean, 2026-08-23)**: `cfK_append` (list induction via
`cfK.induct`, no α_{r,s} combinatorics — worked exactly as planned) ·
`cfK_drop_one_le` · `cfK_dropLast_le` · `cfK_mul_le_append` ·
`cfK_append_le` · `fib_le_cfK` · `cfVal_eq_div` · `tailDensity_mem_Icc` ·
`cylMap_denom_ratio_le`.  Helpers added: `cfK_cons` (head recursion for
nonempty tails), `one_le_cfK`.  Technique note: revert `hpos`/`hw` before
`induction w using cfK.induct` so the IHs carry the hypotheses.

**Crux next**: `volume_cfCylinder`.  Route (HANDOFF step 8): digit-reading
bridge `cfDigit x 0 = k ⇔ x ∈ (1/(k+1), 1/k]`, then induct with
`cylMap`/`gaussMap`; endpoint junk is countable → null.  Determinant
identity `qₙpₙ₋₁ − pₙqₙ₋₁ = ±1` needed for the interval length — derivable
from `cfK_append` specializations or its own two-step induction.  Then 3.2's
two distortion lemmas fall out of the volume formula + quasi-mult (done).

**Done-when**: `src/` sorry-free (the default self-stop gate) + the 12
axiom-clean.  Toolchain: v4.33.1, present in the box store (verified
2026-08-23) — no gate.
