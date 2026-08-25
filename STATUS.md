# STATUS — normal-numbers 📊

**B5′ COMPLETE + axiom-clean (10 headlines); B6 campaign OPEN — Vandehey §7 affine images, additive. ROUTE PIVOTED (2026-08-25): the schedule crux `variance_blockCount_psi_pushed` is PROVABLY FALSE (counterexample), so B6 pivots to the MEASURE route — the stated theorem is bare existence, trivially true a.e.; new crux = `ae_isCFNormal` (a.e. CF-normality via L²→a.e. from the PROVED `variance_blockCount_le`, Birkhoff-free).** · **Build**: 🟢 green (8757 jobs) · **Updated**: review lap #2b · 2026-08-25 · `59a04e6`+

## Where it stands

**B5′ is DONE; B6 is the active frontier — single-stream L4 route (the two-stream
construction was proven infeasible), and the whole z-side has now been narrowed to
ONE precisely-stated analytic obligation.** The whole B5′ expedition (ten headline
theorems) is proved and `#print axioms`-clean (trust triple only). The LIVE work is
the **additive B6 campaign** (Vandehey, Compositio 2017, §7): a real `x` with BOTH
`x` and its affine image `ψ(x)=q·x+r` CF-normal, for `q>0`. The block-linear crux
`schedL4_block_linear`, the x-side (`exists_xA_L4_orbit_equidist`), ψ(xA)
irrationality (`exists_xA_L4_psi_irrational`), and the ENTIRE clean single-stream
z-selector (`psi_pushed_chebyshev_brick` → `gaussMeasure_aggregate_psi_pushed_le` →
`exists_scale_cfCylinder_psi_avoid_zbad_poly`, all axiom-clean) are PROVED. **The
whole clean z-side now reduces to ONE disclosed analytic sorry:
`variance_blockCount_psi_pushed` (`CFScheduleA.lean:4254`)** — the ψ-pushed L²
second-moment estimate `∫_{cfCyl wx'} (blockCount n (ψ·) − nγv)² dγ ≤
(8|v|+80)·n·γv·γ(cfCyl wx')`. This is the genuine research core: affine-invariance of
CF-normality via ψ-conjugated Gauss-map mixing. **Two `src/` sorries remain:** THE
crux above, plus the DEAD two-stream `schedA_block_linear` (`:5630`) that B6's
`sorryAx` currently flows through, excised once the L4 z-selector wires in (reuse,
not the crux). The crux decomposes (DIRECTION.md CURRENT DIRECTIVE): (1) restricted
ψ-pushed 2nd-moment identity (routine, mirror `integral_blockCount_sq`), (2)
ψ-conjugated interval-base mixing via change-of-variables bounded density ratio
extending `gaussMeasure_cylinder_mixing` (THE hard core), (3) geometric-sum assembly
mirroring `variance_blockCount_le`.

- **Track A** (base-b normality): Wall, the ln 2 reduction (conditional on the
  correct equidistribution hypothesis), Stoneham — axiom-clean.
- **Tier 1 = Becher–Yuhjtman** (IMRN 2019): `exists_absolutely_normal_cf_normal`
  — an explicit real absolutely normal ∧ CF-normal. Apparently the first
  formalization in any prover. Axiom-clean.
- **Tier 2 = expedition headline**: `exists_absolutely_normal_cf_normal_khinchin`
  — additionally Khinchin-typical. Axiom-clean.
- **B6 = affine images (active)**: `exists_cfNormal_and_affine_cfNormal` — target
  proved MODULO the crux `sorry`; depends on `sorryAx` until the schedule closes.

## What's happened (newest first)

- 2026-08-25 (review lap #2b): **ROUTE PIVOT — schedule crux is FALSE, B6 goes to the
  measure route.** While driving step 1c of the "prove the variance crux" plan, the
  pushforward structure yielded a rigorous counterexample to `variance_blockCount_psi_pushed`
  (`v=[1]`, `ψ(cfCyl wx')⊆cfCyl[2,…,2]` ⇒ pushed count `≡0` at scales `n≤|wx'|` ⇒
  `LHS=n²γv²γ(wx') > RHS` once `n>88/γv≈212`). The crux is FALSE — a deep cylinder is a tiny
  interval, so `blockCount n(ψ·)` is near-constant over it for `n≲|wx'|` at a value ≠ `nγv` ⇒
  2nd moment `Θ(n²)`. So `psi_pushed_chebyshev_brick`/`_poly` establish nothing; both schedule
  z-routes are dead. Took the 2026-08-24-pre-registered "escape #3": pivoted B6 to the MEASURE
  argument (existence is a.e.-trivial). New crux = `ae_isCFNormal` (a.e. CF-normality via
  L²→a.e. Borel–Cantelli from the PROVED `variance_blockCount_le`, no ergodic theorem), then
  ψ⁻¹-preserves-null ⇒ two co-null sets meet ⇒ witness. Wrote OBSTRUCTION + ROUTE-ESCALATION
  docs, rewrote CURRENT DIRECTIVE, marked the false crux REFUTED in-source (kept, not deleted).
  Charter trigger FIRED and handled by pivot, not stop.

- 2026-08-25 (review lap #2): **Whole clean z-side reduced to ONE analytic crux;
  direction re-pointed at it.** Inventory by real `#print axioms`: build green 8757,
  both B5′ headlines trust-triple = DONE, B6 still `+sorryAx` (now via the DEAD
  two-stream `schedA_block_linear`, `:5630`). Confirmed the last ~10 laps were
  genuine crux-narrowing, not leaf-fixation: ψ(xA) irrationality PROVED, the
  Chebyshev/Markov budget + transfer engine built axiom-clean, the conditional-at-`wz`
  route walled by a density-vs-coverage obstruction (`5816044`) then corrected, and
  the clean local-density architecture found — collapsing the entire single-stream
  z-selector (`psi_pushed_chebyshev_brick`→`_poly`) onto ONE disclosed sorry
  `variance_blockCount_psi_pushed` (`:4254`). Found the prior directive STALE (its
  step 1 done, steps 2–3 collapsed); rewrote DIRECTION to mandate PROVING the crux,
  hardest-first, decomposed into (1) restricted ψ-pushed 2nd-moment identity
  (routine), (2) ψ-conjugated interval-base mixing via change-of-variables bounded
  density ratio, (3) geometric-sum assembly. Base-mass factor `γ(cfCyl wx')`
  MANDATORY (its loss walled every prior route). No charter trigger fired.

- 2026-08-25 (review lap): **B6 L4 crux PROVED; direction re-pointed at the z-side
  (ψ(xA) irrationality first).** Inventory by real `#print axioms`: build green
  8757, both B5′ headlines trust-triple = DONE, B6 still `+sorryAx` via the DEAD
  two-stream `schedA_block_linear` (`:4823`, sole `src/` sorry). Found the CURRENT
  DIRECTIVE stale: its mandated crux `schedL4_block_linear` is PROVED (`030d8fb`)
  and its step-4 "z-side = REUSE" is REFUTED (`b178653`). Validated the grind
  ON-PATH (last ~10 laps proved the block-linear crux, landed the x-side, built the
  Z-I engine — genuine crux work). Rewrote DIRECTION to mandate z-side
  re-integration, hardest-first = force ψ(xA) irrational via a per-stage
  diagonalization filler digit over an enumeration of `ψ⁻¹(ℚ)`, keeping the
  freq-good block on the FULL hull (target-shrink RULED OUT: breaks the `¼γwx≤γtar`
  balance). No charter trigger fired.

- 2026-08-24 (review lap): **B6 L4 crux collapsed to the cfK-cap graft; bridge +
  layer 1 PROVED.** Inventory by real `#print axioms`: build green 8757, both B5′
  headlines trust-triple, sole `src/` sorry = the DEAD two-stream
  `schedA_block_linear`. Validated the L4 pivot SOUND and the grind ON-PATH (the
  last ~5 laps located + proved the block-linear support layer and started the
  recursion — genuine crux work, not leaf-fixation). Found the CURRENT DIRECTIVE
  stale in specifics (mandated L4 measure bricks all since DONE) and re-pointed it
  at the real crux `schedL4_block_linear`, whose ONE open sub-obstruction is the
  **cfK cap** (`cfK u ≤ e^{κ|u|}` ⇒ `Nfib` affine in `|wx|`). Confirmed it is a
  positive-measure selection (NOT the refuted hard digit-cap) with its whole
  measure/selection stack already proved, then de-risked it: proved the bridge
  `cfK_le_of_notMem_cfKbadExtSet` + the layer-1 variant
  `exists_multiscale_freq_good_block_steer_len_cfK` (exposes `cfK u ≤ e^{κ|u|}`),
  build green, additive. Rewrote DIRECTION to mandate the graft (layer 2 → 3 →
  `schedL4_block_linear`). No charter trigger fired.

- 2026-08-24 (review lap): **B6 PIVOT RATIFIED — two-stream route DEAD, RESUME
  single-stream L4; broke a FALSE STOP.** Inventory by real `#print axioms`: build
  green 8757, both B5′ headlines trust-triple, sole `src/` sorry = the B6 crux
  `schedA_block_linear` (`:2537`). The prior grind laps hit a genuine obstruction
  (two-stream forces super-exponential blocks, `OBSTRUCTION-2026-08-24`) and
  correctly proposed the single-stream pivot, but then declared the crux
  "operator-gated" and stopped — a false stop (no operator on an autonomous run).
  Discovered the single-stream "L4" route is the ORIGINAL module design
  (`CFScheduleA.lean:24–31`) whose L3 foundation `volume_preimage_affineMap`
  (`CFAffine:94`) is already proved; the two-stream layer was a later drift into
  the wall. Rewrote DIRECTION.md CURRENT DIRECTIVE to resume L4 (brick 1 = the
  ψ-pullback Gauss distortion bound `gaussMeasure(ψ⁻¹ S) ≤ (2/q)·gaussMeasure S`,
  ingredients confirmed present), decomposed the full L4 path in PENDING_WORK, and
  forbade grinding the dead two-stream lemmas / any further box-stuck. Item-2
  (integer-shift, all real `r`) + both signposts remain DONE. No charter trigger
  fired (L4 additive, no forbidden import).

- 2026-08-24 (review lap): **B6 route pivot (hdom refuted).** Inventory (real
  `#print axioms`): build green 8757,
  both B5′ headlines trust-triple, sole `src/` `sorry` = the B6 crux
  `exists_interleaved_affine_witness`. Confirmed the grind laps since the last
  review CORRECTLY diverged from the prior directive: they refuted `hdom`
  (`ec0875d` — steer blocks are `Θ(word)`, dominance impossible) and PROVED the
  replacement crux crack `exists_uniformly_freq_good_block_steer` (`f2b4b33`,
  axiom-clean) + the full uniformly-good-block toolkit (`quadScales*`, multiscale
  measure, interpolation arith) + `chainTail_dev_split_var`. The CURRENT DIRECTIVE
  was STALE (still mandated `chain_orbit_equidist` WITH dominance); rewrote it to
  the **hdom-free `chain_cf_digit_freq_tendsto` variant** (step-4 assembly),
  FORBADE more block/measure atoms, named the route-decisive case (mid-block bound
  closing via `addslack₂` + `o(word)` boundary slack dividing out). No charter
  trigger fired.

- 2026-08-24 (review lap): **B6 course-correction — PIVOT TO THE CRUX.**
  Inventory: build green 8756, B5′ headlines re-verified trust-triple, sole
  `src/` `sorry` = the B6 crux `exists_interleaved_affine_witness`. Diagnosed
  crux-neglect: 11 straight grind laps (11–21) each proved a geometric ATOM
  (axiom-clean, green) but the crux stayed untouched and the recursion/telescoping
  was deferred "next lap" ~7×. Declared the atom toolkit COMPLETE; reset the
  CURRENT DIRECTIVE to build the frequency telescoping hardest-first via an
  abstract generic-chain lemma `chain_orbit_equidist`, naming the route-decisive
  case (dominance vs growing fillers + alternation). No charter trigger fired.

- 2026-08-24 (reflection lap → COMPLETION): **Tier 2 CLOSED — the whole
  expedition is done, axiom-clean.** Steps 1–3 all landed this lap. (1) Rewired
  `CFSchedule.lean` to the summable-**family** refinement (fixed cutoffs
  `khinchinK j`, no level-tied `K_t→∞`). (2) Built the log-tail telescoping in
  `CFCorrect.lean` (`logTailMass` + monotonicity, `uSched_logTail_le`,
  `tailSched_logTail_le`, `xstar_logTail_prefix_bound`, `logTailMass_cfPrefix`)
  and assembled the crux `xstar_log_tail_uniform`, hence `xstar_khinchinTypical`
  (axiom-clean). (3) Route D′: relocated the frozen `khinchinK₀`/`KhinchinTypical`
  defs byte-identical to a new upstream `KhinchinDefs.lean`, dropped Khinchin's
  `import Headline`, and closed the Tier-2 headline
  `⟨xstar, xstar_isAbsolutelyNormal, xstar_isCFNormal, xstar_khinchinTypical⟩`.
  All 10 headlines re-`#print axioms`-verified trust-triple. Also (earlier in the
  lap): ratified route C′ and de-staled the CURRENT DIRECTIVE (it still named the
  superseded Chebyshev/variance plan). ROUTE VERDICT: CONTINUE → reached the
  destination.
- 2026-08-24 (grind run, route C′): **FAMILY machinery COMPLETE + axiom-clean.**
  `volume_logBadZone_le_vol` (Lebesgue bridge), three-zone combine
  (`exists_good_avoiding_bad_khinchin` + `_family`), `exists_refinement_uniform_khinchin_family`
  (log-tail payload at every `j<tK`), `CFLogTail.lean` layering (khinchinK₀-free
  upstream). Found+fixed the level-tied-cutoff design bug via the summable family
  (geometric budget `≤1/7`). CFSchedule still carries the SUPERSEDED single-zone
  threading (true, green, unused) — next lap rewires it to the family form.
- 2026-08-24 (review lap): **Tier-2 route SETTLED, schedule fence relaxed, moment
  seed proved.** Broke the 3-lap "operator-gated" stall (fc801ba/17dc2c9/7d6740f
  were pure route-analysis ending in a false "need operator" stop). Confirmed the
  only route is the additive W6 log-concentration bad zone; relaxed the
  `DIRECTION.md` "don't touch the schedule" fence to additive-only with a
  Tier-1-axiom invariant. Proved `summable_gaussKuzmin_logsq` (moment condition
  `E[(log a₁)²]<∞`, axiom-clean) — the analytic seed of the tail bound.
  Re-verified Tier 1 axiom-clean (trust triple), build green (8735 jobs).
- 2026-08-24 (grind laps): **Tier 1 LOCKED** (`b3bc2c4`,
  `exists_absolutely_normal_cf_normal`, axiom-clean) + Tier-2 assembly seeded:
  `gaussMeasure_Ioo`/`gaussMeasure_digit_cylinder` (Gauss–Kuzmin single-digit
  law), `Khinchin.lean` (geometric-mean⟺log-average reduction `khinchinTypical_iff_log_tendsto`,
  `khinchinK₀_pos`), `prod_le_cfK`+`wSched_log_sum_le` (total log-mass bound),
  `xstar_log_digit_avg_truncated_tendsto` (finite-truncation slice).
- 2026-08-24 (review lap): **Pillai crux `windowCount_eq_sum_phaseCount` PROVED**
  (axiom-clean) — the `Q`-scale↔`N`-scale phase-count identity, via a
  `Finset.card_nbij'` bijection `i ↔ i/r`; dodged last lap's `r*(i/r)` vs
  `(i/r)*r` omega-atom trap by anchoring on `Nat.div_add_mod` + one explicit
  `Nat.mul_comm`. Re-verified headlines axiom-clean (trust triple), build green
  (8743 jobs). Directive refreshed (it still named the closed `m`-growth
  estimate as THE crux) → FINISH Pillai, now double-limit-first. No trigger fired.
- 2026-08-24 (grind laps): **d-ary side CLOSED** — `xstar_dary_freq_tendsto`
  (base-`d` simple normality every base, axiom-clean); the `m`-growth interior
  crux (`tendsto_gain_div_mSched_sub`) + Pillai combinatorial core
  (`phaseWindowFreq_tendsto`, `card_straddling_phases`, window/slice
  correspondence, `card_matchingValues`).
- 2026-08-23 (reflection lap): re-verified 10 headlines axiom-clean (trust
  triple), build green (8742 jobs), src/ sorry-free. Found DIRECTION/STATUS/
  PENDING_WORK badly STALE — they still named the Lemma-13 assembly the
  "untouched crux", but Lemma 13 + schedule + `xstar` + CF normality all landed
  since. Refreshed all three; reframed the destination into Tier 1 (B–Y
  abs-normal + CF-normal, source-backed) vs Tier 2 (Khinchin, campaign-original
  stretch); set directive to LOCK Tier 1 via the d-ary `m`-growth estimate.
  ROUTE VERDICT: CONTINUE (no trigger fired; strong forward motion).
- 2026-08-23: **CF NORMALITY OF `xstar` PROVED** (`CFCorrect.lean`,
  `xstar_cf_freq_tendsto`) + **d-ary digit extraction / payload accessors**
  (`DaryDigits`/`DaryCorrect`): digit windows are literally the base-d digits;
  each active stage gives a good block. All axiom-clean.
- 2026-08-23: **THE SCHEDULE + Lemma 13 + limit point** — `CFSchedule.lean`
  (uniform Lemma 13, brick sequence, invariants, dominance), `xstar`
  irrational in every scheduled cylinder (`CFLimit` applied). Axiom-clean.
- 2026-08-23: **B–Y Lemma 13 PROVED** (`TBrick.lean`, both `t'=t` and `t→t+1`)
  — the measure-balance selection lemma (good mass ½|I_w| beats CF + Σ d-ary bad
  zones) made UNCONDITIONAL; seed brick + refinement toolkit (`TBrickRefine`).
- 2026-08-23 (review lap): diagnosed input-gathering fixation, redirected to the
  Lemma-13 measure-balance assembly (now proved).

## Outstanding

### Short-term (mirror PENDING_WORK top — B6 via the MEASURE route, in `CFAeNormal.lean`)
- ⚠️ **REFUTED / RETIRED** — the schedule crux `variance_blockCount_psi_pushed` is FALSE
  (`OBSTRUCTION-2026-08-25`); the whole `psi_pushed_*`/`_poly`/two-stream chain is off-path,
  kept in-src marked REFUTED, NOT to be attacked.
1. **`ae_isCFNormal` — THE new crux.** `∀ᵐ y ∂gaussMeasure, IsCFNormal y`, via L²→a.e.:
   `variance_blockCount_le` (`CFBlockFreq:401`) + Chebyshev + Borel–Cantelli on `p=k²` + monotone
   gap-squeeze ⇒ a.e. `blockCount(cfCyl v) p·/p→γv`; intersect over countable valid `v` + a.e.
   orbit-in-`(0,1)` ⇒ `isCFNormal_of_orbit_freq` (`CFOrbitFreq:34`). Birkhoff-free.
2. **`ae_isCFNormal_affine`.** `∀ᵐ x, IsCFNormal(ψx)` via `ψ⁻¹` preserves γ-null
   (`volume_preimage_affineMap` `CFAffine:94` + γ≈volume bounded density).
3. **Assemble** `exists_cfNormal_and_affine_cfNormal`: two co-null sets on `(0,1)∩ψ⁻¹(0,1)` meet ⇒
   witness; plug into the feasible branch (integer-shift reduction for `r∉(-q,1)` already present).
   First probe: stub 1+2 as `sorry`, prove step-3 assembly + wire in ⇒ B6 reduces to the two a.e. sorries.

### Long-term
- B6 general family / Tier-2 image-Khinchin stretch (detaches freely; after the
  single-map crux closes).

### To completion
- B5′ (Track A + Tier 1 + Tier 2): **DONE**, all axiom-clean.
- B6 single-map (`exists_cfNormal_and_affine_cfNormal`): crux `sorry` open →
  close via the single-stream L4 route (block-linear crux + x-side DONE; z-side
  re-integration, 4 items above, remaining).

## Axiom ledger (fidelity spine — all from real `#print axioms`, 2026-08-25 review lap #2, HEAD `8673338`+)

| headline theorem | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `exists_absolutely_normal_cf_normal` (**Tier 1 = Becher–Yuhjtman**) | uncond | trust triple | 🟢 DONE (re-verified this lap) |
| `exists_absolutely_normal_cf_normal_khinchin` (**Tier 2 headline**) | uncond | trust triple | 🟢 DONE (re-verified this lap) |
| `exists_cfNormal_and_affine_cfNormal` (**B6 affine image**, active) | uncond (q>0) | `[propext, sorryAx, Classical.choice, Quot.sound]` | 🔨 `sorry`; NOT a math axiom — disclosed. ROUTE PIVOTED: the schedule crux `variance_blockCount_psi_pushed` is PROVABLY FALSE (counterexample, `OBSTRUCTION-2026-08-25`), so B6 now goes via the MEASURE route (`ROUTE-ESCALATION-2026-08-25`): bare existence is a.e.-trivial, new crux `ae_isCFNormal` (a.e. CF-normality, Birkhoff-free from `variance_blockCount_le`). Schedule chain kept in-src marked REFUTED. |
| `isNormal_iff_equidistributed_orbit` (Wall) | uncond | trust triple | 🟢 DONE |
| `isNormal_log_two_of_equidistributed` | cond (orbit equidist.) | trust triple | 🟢 DONE (hypothesis is the open conjecture, correctly a hypothesis) |
| `isNormal_two_stoneham23` (Stoneham) | uncond | trust triple | 🟢 DONE |
| `xstar_cf_freq_tendsto` (CF normality of x\*) | uncond | trust triple | 🟢 DONE |
| `xstar_dary_freq_tendsto` (d-ary simple normality, every base) | uncond | trust triple | 🟢 DONE |
| `pillai` (simple-to-all-powers ⇒ full normality) | uncond | trust triple | 🟢 DONE |
| `gaussMeasure_digit_cylinder` (Gauss–Kuzmin single-digit law) | uncond | trust triple | 🟢 DONE |
| `summable_gaussKuzmin_logsq` (Tier-2 moment seed) | uncond | trust triple | 🟢 DONE |

Math-axiom count (🟢+🟡+🟠, excluding trust base + native_decide artifacts):
**0** proven-but-cited axioms across all 10 B5′ headlines (every one 🟢, trust
triple only). The B6 target carries `sorryAx` — a **disclosed decomposition
`sorry`**, NOT a cited math axiom — being actively discharged (the interleaved
schedule). No 🟡/🟠 debt, no 🔴. Trust triple = propext, Classical.choice,
Quot.sound throughout.

## Pointers
DIRECTION.md (CURRENT DIRECTIVE) · ROADMAP.md · KHINCHIN.md (B5′ plan W1–W6) ·
JUDGE.md · papers/literature-review.md · newest HANDOFF (`ls HANDOFF-*.md | sort | tail -1`) ·
PENDING_WORK.md · papers/becher-yuhjtman-2019-*.md
