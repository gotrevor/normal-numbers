# HANDOFF — 2026-08-29 — B6 L4: schedL4_block_linear INGREDIENTS COMPLETE

**Branch:** `master`  **HEAD:** `c1b4757`  **Build:** 🟢 8757 jobs, clean tree.
**Headlines:** both B5′ re-verified trust-triple `[propext, Classical.choice, Quot.sound]`
(`exists_absolutely_normal_cf_normal_khinchin` checked this session).
**Sole open `src/` sorry:** the DEAD two-stream `schedA_block_linear`
(`CFScheduleA.lean`), excised once L4 lands its own `exists_interleaved_affine_witness`.

## The one thing to read first

DIRECTIVE (unchanged, `DIRECTION.md`): close `schedL4_block_linear` via the cfK-cap graft,
single-stream L4 route. This session built the ENTIRE prerequisite stack for that crux and
made the route-decisive structural fix. **Next lap = the final assembly** (no new
infrastructure needed — all lemmas exist and are green/axiom-clean).

## What landed this session (11 commits, all additive + axiom-clean)

Recursion skeleton + all analytic ingredients of `schedL4_block_linear`:

1. `acdcb19` — rewired `schedStepL4_exists` onto the cfK builder
   `exists_uniformly_freq_good_block_steer_len_rel_cfK`; `StepSpecL4` now exposes the hull
   `(a,b)`, `|u|=n₁+m²`, the **cfK cap** `cfK u ≤ exp(schedKappaL4·|u|)`, the `m²` bound,
   `Nfib` bound. Global rate `schedKappaL4` + `schedKappaL4_spec` fixed once.
2. `e36786a` — recursion skeleton: `exists_seedStateL4`, `schedL4`, `schedL4_step`,
   `wxSeq_L4` (+ `_ne`/`_pos`/`_ext`).
3. `faa179a` — `cfK_wxSeq_L4_le`: `cfK(wxSeq_L4 s) ≤ cfK(wxSeq_L4 0)·exp((κ+log2)·|wxSeq_L4 s|)`
   (recursion of the per-block cap via `cfK_append_le`, absorbing `2^s`).
4. `29fe63c` — `four_div_width_le_cfK` (+ `cfCylinder_volume_toReal_le_width`):
   `4/(b-a) ≤ 8·cfK(w)²` for a cylinder in hull `Icc a b`.
5. `02e1445` — `block_len_le`: `|b| ≤ 2m²+7` (from `|b|=n₁+m²` + `n₁²≤|b|√|b|`).
6. `6bfc234` — `gaussMeasure_middle_half_hull_ge` (+ `gaussMeasure_singleton`):
   `γtar ≥ ¼·γ(cfCyl w)` — the `ratio=1/4` input for `two_div_beta_rel_le`.
7. `f501de1` — `logb_golden_sqrt_le`: `logb φ(√5√a+1)+1 ≤ (κ/logφ)ℓ + C_φ` given `a≤8K²`,
   `K≤exp(κℓ)`. Bounds the per-step `Nfib` affinely in `|wx|`.
8. `ea69daf` — **ROUTE-DECISIVE STRUCTURAL FIX.** `slack_telescoping` genuinely needs
   `blk(s) ≤ ρ·word(s)`, which was FALSE under `L:=s` (blocks ~poly(s), word only ~s²).
   Changed the block builder's min length to **`L := S.wx.length + s`**: each block is now
   ≥ the accumulated word, so word ≥ doubles each step. `StepSpecL4` exposes the geometric
   seed `S.wx.length ≤ |block|`; `m²` bound carries `L=|wx|+s`.
9. `fe0c01b` — `wxSeq_L4_length_ge`: `2^s ≤ |wxSeq_L4 s|` (from the geometric seed).
10. `03202e7` — `exists_const_pow_le_two_pow`: `∀k, ∃C≥0, ∀s, s^k ≤ C·2^s`
    (via `isLittleO_pow_exp_pos_mul_atTop`).
11. `c1b4757` — `sum_gaussMeasure_boundedWords_le_one` (same-length cylinders disjoint ⇒
    mass ≤1) + `sum_gaussMeasure_wordFamily_le`: `Σ_{v∈wordFamily s} γ(cfCyl v) ≤ s`.
    ⇒ the family sum `Sg_s := Σ 7(8|v|+80)γ(cfCyl v) ≤ 7(8s+80)·s` is polynomial.

## NEXT (hardest-first): assemble `schedL4_block_linear`

State (mirror `schedA_block_geom`/`schedA_block_linear` but for `wxSeq_L4`):
`∃ ρ ≥ 0, ∀ s, ((chainApp (wxSeq_L4 hq hr) s).length : ℝ) ≤ ρ * (wxSeq_L4 hq hr s).length`.
`chainApp (wxSeq_L4) s = (schedL4 (s+1)).wx.drop (schedL4 s).wx.length` = the step block.

Chain (all pieces proved; this is bookkeeping, ~1-2 laps):
- `|b_s| ≤ 2m_s²+7`  (`block_len_le`, with `|b_s|=n₁+m²`, `n₁²≤…` from `StepSpecL4`).
- `m_s² ≤ 6(|w_s|+s+Nfib_s)+2+2(⌈inner_s⌉+1)⁴`  (`StepSpecL4` m² conjunct, `L=|w_s|+s`).
- `Nfib_s ≤ logb φ(√5√(4/(b_s-a_s))+1)+1`  (`StepSpecL4`); feed
  `four_div_width_le_cfK (schedL4 s).wx … hIcc` (`a:=4/(b-a) ≤ 8cfK²`) + `cfK_wxSeq_L4_le`
  (repackage `cfK(w_s) ≤ exp(κ'·|w_s|)`, κ'=(κ+log2)+log cfK(w_0), using `|w_s|≥1`) into
  `logb_golden_sqrt_le` ⇒ `Nfib_s ≤ (κ'/logφ)|w_s| + C_φ`.  LINEAR in `|w_s|`.
- `inner_s ≤ 16(Sg_s+1)(s+1)²`  via `two_div_beta_rel_le` (Sg:=Σ7(8|v|+80)γ(cfCyl v),
  ratio=1/4 from `gaussMeasure_middle_half_hull_ge`, δ=schedEps s=1/(s+1)). Then
  `Sg_s ≤ 7(8s+80)s` (`sum_gaussMeasure_wordFamily_le` + `|v|≤s`) ⇒ `inner_s ≤ Q(s)` poly ⇒
  `2(⌈inner_s⌉+1)⁴ ≤ P(s)` poly.
- **absorb**: `P(s) + 6s ≤ (poly) ≤ C·2^s ≤ C·|w_s|` (`exists_const_pow_le_two_pow` per
  monomial + `wxSeq_L4_length_ge`); the `6|w_s|`, `6Nfib_s`, `+2` terms are already `O(|w_s|)`.
  Sum ⇒ `|b_s| ≤ ρ·|w_s|` for a uniform `ρ` (take `∃`; small-s handled by the same C·2^s).
- CHECK `schedEps s` def (is it `1/(s+1)`? confirm `1/δ² = (s+1)²`). See `CFSchedule.lean`.

Then (downstream = REUSE, per DIRECTIVE item 4):
- `chain_orbit_equidist_uniform` (HDOM-FREE, `CFChainFreq.lean:731`) via
  `slack_telescoping` (`CFScheduleA:3206`, needs the geom bound just built) +
  `chain_slack_littleO` (C=o(blk) from `n₁²≤|b|√|b|`) + `blk→∞` (from `|b_s|≥|w_s|+s→∞`).
- z-side scale-coverage (`tendsto_of_scale_coverage` + brick-4a transfer lemmas).
- Assemble NEW `exists_interleaved_affine_witness`; excise the two-stream `sorry` (dead code).

## Notes
- ADDITIVE ONLY 🧊: re-`#print axioms exists_absolutely_normal_cf_normal_khinchin` after any
  schedule wiring — MUST stay `[propext, Classical.choice, Quot.sound]`.
- Fast check: scratch `.lean` importing `NormalNumbers.CFScheduleA`, `lake env lean <abs>`
  from project ROOT (CFScheduleA stays cached).
- All ingredient lemmas are in `CFScheduleA.lean`. `two_div_beta_rel_le` @ ~2339,
  the L4 helpers cluster @ ~4098–4230.
- DIRECTION.md governs; PENDING_WORK.md top has the cfK-cap attack path (now largely done).
