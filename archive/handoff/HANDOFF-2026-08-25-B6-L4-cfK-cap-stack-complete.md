# HANDOFF — 2026-08-25 — B6 L4: cfK-cap STACK COMPLETE (bridge + layers 1/2/3 + hcfK discharge)

**Branch:** `master`  **HEAD:** `90dc9d4`  **Build:** 🟢 8757 jobs, clean tree.
**Sole open `src/` sorry:** the DEAD two-stream `schedA_block_linear`
(`CFScheduleA.lean:4083`), excised once L4 lands `exists_interleaved_affine_witness`.
Both B5′ headlines trust-triple; B6 target `exists_cfNormal_and_affine_cfNormal` = `+ sorryAx`.

## This lap (fresh-mind REVIEW lap + grind)

Validated the single-stream L4 route SOUND, re-pointed DIRECTION at the real crux
`schedL4_block_linear`, and BUILT the entire cfK-cap stack — the block-linear crux's one
open sub-obstruction. All additive, axiom-clean, build green.

**Proved this lap (all in `CFScheduleA.lean`):**
1. `cfK_le_of_notMem_cfKbadExtSet` (bridge, ~:1790) — avoiding `cfKbadExtSet wx κ ntop`
   in `cfCylinder(wx++u)` (u genuine, |u|=ntop) ⇒ `cfK u ≤ e^{κ·ntop}`.
2. `exists_multiscale_freq_good_block_steer_len_cfK` (layer 1, ~:1810) — mirror of `..._len`,
   swaps in the cfK selection core, exposes `cfK u ≤ e^{κ|u|}`.
3. `exists_uniformly_freq_good_block_steer_cfK` (layer 2) — cfK passes through the
   quadScales interpolation.
4. `exists_uniformly_freq_good_block_steer_len_rel_cfK` (layer 3) — relative-β steer block
   WITH cfK. HALVED regularizer `β = γtar·δ²/(2(S+γwx))` so freq mass targets `γtar/2`;
   caller supplies uniform cfK room `hcfK : ∀ n, γ(cfKbadExtSet wx κ n) ≤ γtar/2`. Exposes
   `cfK u ≤ e^{κ|u|}` + `|u|=n₁+m²` + `m² ≤ 6(L+Nfib)+2+2⌈4/β⌉⁴` + `Nfib ≲ log`.
5. `exists_kappa_cfKbadExtSet_le_half_middle` (~:3885, ROUTE-DECISIVE) — a single
   WORD-INDEPENDENT κ (ε=1/32) discharging layer 3's `hcfK` for every genuine cylinder in
   any hull `Icc c d`. Bound routes through hull width `d−c` (vol(wx) ≤ d−c;
   γtar ≥ ¼γ(c,d) ≥ (d−c)/(8ln2)), NO γwx / atom bookkeeping. **This settled the last
   feasibility doubt of the cfK-cap approach: YES.**

## NEXT (hardest-first) — assemble `schedL4_block_linear`, then downstream reuse

The cfK-cap machinery is all in place. Remaining assembly:

1. **Extend `StepSpecL4`** (`CFScheduleA.lean:~3892`) to carry the length + cfK fields:
   the block `u = S'.wx.drop S.wx.length` satisfies `|u| = n₁+m²`, the `m²` word-independent
   bound, and `cfK u ≤ e^{κ|u|}` (κ from `exists_kappa_cfKbadExtSet_le_half_middle`, fixed
   once globally). Thread the layer-3 cfK builder's extra return values through.
2. **Rewire `schedStepL4_exists`** (`:~3907`) to call
   `exists_uniformly_freq_good_block_steer_len_rel_cfK` instead of the non-cfK `..._len_rel`.
   Discharge its `hcfK` via `exists_kappa_cfKbadExtSet_le_half_middle` — the self-hull target
   (a,b) from `exists_Ioo_irrational_subset_cfCylinder` gives `cfCylinder wx ⊆ Icc a b`, the
   exact hull hypothesis the discharge needs. (Fix κ at the schedule level so it's the SAME
   for every step.)
3. **Seed + `wxSeq_L4`**: `exists_seedStateL4` (mirror `exists_seedStateA`, drop wz), then
   `wxSeq_L4` by `Nat.rec` on `schedStepL4_exists.choose` (mirror `schedA`/`wxSeq`).
4. **`schedL4_block_linear`**: from StepSpecL4's exposed `|u|=n₁+m²` + `m²` bound
   (word-independent via `two_div_beta_rel_le`, ratio=1/8) + `Nfib ≲ |wx|` via
   `four_div_volume_cfCylinder_le` + `exists_fib_threshold_linear_of_cfK` (its `hK` cfK-cap
   discharged by threading `cfK(u_s) ≤ e^{κ|u_s|}` through the recursion with `cfK_append_le`:
   `cfK(wxSeq s) ≤ 2^s·∏cfK(u_i) ≤ C₀·e^{(κ+log2)|wxSeq s|}`, using `s ≤ |wxSeq s|`)
   ⇒ `|chainApp| ≤ K₁|w|+K₂`, LINEAR.
5. **Downstream = REUSE**: x-side `chain_orbit_equidist_uniform`; z-side scale-coverage
   (`tendsto_of_scale_coverage` + brick-4a transfer lemmas); assemble the NEW
   `exists_interleaved_affine_witness`; excise the two-stream `sorry` (dead code).

## Notes
- ADDITIVE ONLY 🧊: re-`#print axioms exists_absolutely_normal_cf_normal_khinchin` after any
  schedule wiring — MUST stay `[propext, Classical.choice, Quot.sound]`.
- Fast local check: scratch `.lean` importing `NormalNumbers.CFScheduleA` with
  `open NormalNumbers MeasureTheory Filter Asymptotics`, run `lake env lean <abs-path>`
  FROM THE PROJECT ROOT (cd into scratchpad breaks lake's project detection) — CFScheduleA
  stays cached, iterate in seconds.
- DIRECTION.md CURRENT DIRECTIVE governs (this review lap set it to the cfK-cap graft; items
  1/2 now DONE, item 3 = the assembly above). PENDING_WORK top has the full attack path.
- Reference corpus: `~/personal/claude/knowledge/core/projects/lean-journey/reference/`.
