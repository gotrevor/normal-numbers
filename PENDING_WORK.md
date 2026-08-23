# PENDING WORK — B5′ / W1 campaign (staged 2026-08-23; laps 1-2: algebra batch + crux volume formula)

**Campaign**: discharge the 12 sorries in `src/NormalNumbers/CFCylinder.lean`
(work package W1 of expedition B5′ — see `HANDOFF.md` for the route and
`KHINCHIN.md` for the full plan).  Everything else in `src/` is sorry-free
(Stoneham ✅ landed 2026-08-23; its record lives in `ROADMAP.md` and
`archive/handoff/`).

**Open (2/12)**: `volume_cylinder_append_le` · `le_volume_cylinder_append`
— both are B–Y Lemma 3.2 one-pagers from the volume formula (now proved) +
quasi-multiplicativity (done): |I_w| = 1/(q(q+q⁻)), so the ratio
|I_{wu}|/(|I_w||I_u|) is a product of the K-ratios already bounded.

**Crux DONE (2026-08-23)**: `volume_cfCylinder`, axiom-clean.  Route as
planned: `bumpLast` endpoint + determinant computation in ℚ
(`abs_cfVal_sub_bumpLast`), digit bridge `cfDigit_zero_eq_iff`, two
inclusions `cfCylinder_subset_uIcc` / `uIoo_subset_cfCylinder` (irrational
points only for the lower one), squeeze with `Real.volume_interval` /
`Real.volume_uIoo` and null countability of ℚ — no measurability of the
cylinder needed anywhere (outer-measure monotonicity suffices)

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
