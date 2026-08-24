# DIRECTION — normal-numbers 🧭

Altitude laps (review/reflection) are the ONLY writers of the CURRENT DIRECTIVE
section. Grind laps READ and OBEY it; it OUTRANKS the HANDOFF. Keep it short —
detail lives in PENDING_WORK.md.

## CURRENT DIRECTIVE (set 2026-08-24 review lap — B6: HDOM REFUTED, ASSEMBLE THE HDOM-FREE LIMIT)

- **Objective (unchanged): B6 — affine images (Vandehey §7).**  Prove the crux
  `exists_interleaved_affine_witness` (`CFScheduleA.lean:1559`, sole open `sorry`
  in `src/`), whence `exists_cfNormal_and_affine_cfNormal`.  Both B5′ headlines
  stay proved + axiom-clean (re-verified this review: trust-triple).
- **ROUTE PIVOT RATIFIED — the `hdom` route is DEAD, uniform-goodness is MANDATORY.**
  The prior directive mandated `chain_orbit_equidist` *with* a DOMINANCE
  hypothesis (`|chainApp w s| < ε·|w s|`).  Commit `ec0875d` REFUTED that as
  unattainable: steering resolves each stream to the other's metric scale at cost
  `Θ(log_φ cfK) = Θ(word)`, so blocks are `Θ(word)`, growth is geometric,
  `block/word → κ ≠ 0` — `hdom` CANNOT hold.  The crux crack that replaces it,
  **`exists_uniformly_freq_good_block_steer`** (a steer block whose EVERY prefix
  is `δ·k + (4√k+2|v|)`-good, slack `o(k)`), is PROVED + axiom-clean (commit
  `f2b4b33`).  Do NOT resurrect `hdom` or the `filler` framing anywhere.
- **THE MANDATED MOVE — build the hdom-FREE chain limit (step 4 assembly); the
  block/measure toolkit is CLOSED.**  The uniformly-good-block toolkit
  (`exists_uniformly_freq_good_block_steer` + `quadScales*` + multiscale measure +
  interpolation arith) is COMPLETE and axiom-clean; **proving another block or
  measure atom is the forbidden drift** (the crux crack already landed — polishing
  more block lemmas is leaf-work now).  Every lap advances ONE of, hardest-first:
  1. ✅ **DONE (2026-08-24 review-lap grind, commits `2c61e7c`/`5fe8f09`).** The
     hdom-free chain limit is BUILT and axiom-clean: `chainTail_dev_prefix_var`
     (recursion core), `chain_cf_digit_freq_tendsto_uniform` (window freq limit,
     mid-block via `addslack₂` not `cfDiscLt_append_take`), and
     `chain_orbit_equidist_uniform` (the `CFOrbitEquidist` payload).  Hypotheses it
     needs from the schedule: `hblock` (uniform block prefix-goodness, margin→0) +
     `hslack` (`∑_{i≤k}(C(s₀+i)+(|v|−1)) < ε·|w(s₀+k)|`, the `o(word)` telescoping).
     **The next grind lap goes straight to item 2/3 — do NOT rebuild item 1.**
  2. **ψ-round `_uniform` (NOW hardest-first)** — rebuild `exists_freq_good_extend_affine_steer` to
     emit uniformly-good blocks (call `exists_uniformly_freq_good_block_steer` per
     stream; choose `n₁,s ~ poly(1/δ_s)` for the measure budget and `m_s` so
     `n₁+m²` reaches resolution length `~κ|w_s|`).  Per-round feasibility
     `(m+1)·A₁(n₁) < γ(c',d')` holds once `|w_s|` large (geometric beats poly).
  3. **`SchedStateA`/`schedStepA`/`schedA`/limit** — the two-stream recursion
     (mirror `CFSchedule.sched`) → two uniformly-good chains → step-1 limit →
     `CFOrbitEquidist` both streams → assemble `exists_interleaved_affine_witness`.
     Gluing toolkit READY (`eq_of_mem_iInter_Icc`, `cfCylinder_chain_volume_tendsto`,
     `irrational_mem_Ioo_of_mem_iInter_cfCylinder`).
- **ROUTE-DECISIVE UNCERTAIN CASE (updated — item 1's is now SETTLED in-kernel):**
  the item-1 mid-block question ("does `addslack₂` close hdom-free") is PROVED YES
  (`chainTail_dev_prefix_var`).  The remaining decisive case is **per-round
  feasibility of the ψ-stage**: can each round pick `n₁,s` and `m_s` that
  SIMULTANEOUSLY satisfy (a) the measure budget `(m+1)·A₁(n₁) < γ(target)` (wants
  `n₁` large `~ poly(1/δ_s)`) and (b) the resolution `4/(d−c) < fib(|wx|+n₁+m²+1)²`
  (wants top-scale `n₁+m² ≳ κ|w_s|`) — AND does `hslack` (`∑ C = o(word)`, with
  `C_s = 4√|block_s|+2|v|+n₁,s`) then follow from the resulting geometric block
  growth?  Smallest probe: instantiate `exists_uniformly_freq_good_block_steer`
  for ONE ψ-round with explicit `n₁,s ≈ (s+1)^a`, `m_s` from
  `exists_nat_goldenRatio_pow_gt`, and check both budget inequalities hold for
  `|w_s|` past a threshold (geometric beats poly).  If (a) and (b) CONFLICT
  (block forced simultaneously short and long), THAT is the real crux — escalate.
- **SIGNPOST RULE (attended, 2026-08-24, Trevor-ratified)**: a refuted route gets
  a PROVED negation, not just a prose note — a named theorem (e.g.
  `..._unrestricted_false : ¬ (∀ …)`) stating the exact refuted shape, landed
  directly beside the restricted/replacement lemma, docstrings pointing both
  ways.  Land it AT the moment of refutation when the witness is concrete; if
  only an asymptotic/measure argument exists, a docstring naming the informal
  witness suffices (label the evidence tier honestly).  Never as standalone
  leaf-quests.  **Concretely owed now**: (a) the `r ∉ (-q,1)` counterexample
  beside the restricted crux (a single explicit (q,r) witness is enough);
  (b) the `hdom` refutation (`ec0875d`) — kernel-tier if a concrete witness is
  cheap, else the docstring-tier signpost on the replacement crack.
- **ADDITIVE ONLY 🧊**: B5′ is COMPLETE and LOCKED.  Never edit/weaken a frozen
  decl or landed module (`TBrick*`, `CFSchedule`, `CFCorrect`, `CFLogTail`,
  `Headline`, `KhinchinDefs`, the existing `chain_cf_digit_freq_tendsto` /
  `chainTail_dev_split`, …); copy-extend into `CFChainFreq`/`CFScheduleA`/new files.
  After ANY schedule work re-`#print axioms exists_absolutely_normal_cf_normal_khinchin`
  — MUST stay trust-triple `[propext, Classical.choice, Quot.sound]`.
- Escape valves (judge-governed, see brief): Tier 2 may drop to a finite
  family; the image-Khinchin stretch detaches freely.
- **Why**: the block toolkit is worthless if the limit doesn't telescope, and the
  hdom-free limit (step 1) is the ONLY piece whose feasibility is still in real
  doubt — its mid-block bound must close without the (refuted) `hdom`.  Settling it
  early is worth more than more block scaffolding.  Historical B5′-wiring directive
  preserved below for provenance.

<details><summary>Superseded directive (route C′ wiring — now DONE)</summary>

- **TIER 1 IS LOCKED**: `exists_absolutely_normal_cf_normal` (Becher–Yuhjtman,
  IMRN 2019, apparently first formalization) is **proved and axiom-clean**
  (`propext, Classical.choice, Quot.sound` only) — `Headline.lean:109`
  (re-verified this lap). Do NOT reopen or MODIFY any of it.
- **THE objective**: **Tier 2 — Khinchin-typical**, the frozen headline
  `exists_absolutely_normal_cf_normal_khinchin` (`Headline.lean:136`, `sorry`).
  The analytic reduction is DONE; the whole headline funnels to ONE crux
  **`xstar_log_tail_uniform`** (`Khinchin.lean:527`, `sorry`): the empirical
  log-mass of CF digits `> K` is `≤ ε` uniformly in `n`.
- **ROUTE — C′ (summable Markov log-tail family), RATIFIED, machinery COMPLETE**:
  frequencies-only is REFUTED (`KHINCHIN.md` large-digit counterexample); the
  needed ingredient is uniform integrability of `log a`, enforced *in the
  construction* by an ADDITIVE family of log-tail bad zones. **This lap noted the
  route SIMPLIFIED** from the prior directive's Chebyshev/variance plan to a
  **Markov first-moment bound on the nonnegative log-tail** (the tail past a
  cutoff is `≥0`, so first moment suffices — no two-sided variance). The design
  bug of a level-tied cutoff (`K_t→∞` never transfers to a fixed external `K`) is
  FIXED by a summable family with FIXED cutoffs `khinchinK j` (`KhinchinFamily`).
  All of `KhinchinBrick`/`KhinchinFamily`/`KhinchinRefineFamily`/`CFLogTail` is
  proved axiom-clean. **The remaining gap is pure WIRING, not more machinery.**
- **Mandated next move — WIRE, do NOT build more upstream lemmas**:
  1. **Rewire `CFSchedule.lean`** from the superseded single-zone
     `TBrick.exists_refinement_uniform_khinchin` to the FAMILY form
     `TBrick.exists_refinement_uniform_khinchin_family`, with `tK := ` the level
     `t`. `sched_refinement`/`nFn_spec`/`SchedStep`'s final log conjunct becomes
     `∀ j<t, (Σ_{a∈u, a>khinchinK j} log a) ≤ khinchinEta j·|u|`; the `KFn t` /
     `∃K₀` layer disappears. `sched_step` destructures end in trailing `-` (safe);
     `DaryCorrect.lean:48` needs one more `-` (same fix as commit `949f0b1`).
  2. **Assemble `xstar_log_tail_uniform`** (`Khinchin.lean:527`): pick
     `j(ε):=⌈1/ε⌉`, fix `K₀:=khinchinK j(ε)`; split the length-`n` prefix at the
     stage where level first exceeds `j(ε)` (`sched_t_eventually`). Early stages
     bounded via the `goodC`-telescope (`wSched_log_sum_le`-style, `CFCorrect.lean`);
     late stages use the family guarantee AT index `j(ε)`. Monotonicity of the
     nonneg tail in `K` gives the `∀K≥K₀`. WEAKEN the lemma to `∃N,∀n≥N` (internal;
     its one consumer `xstar_log_digit_avg_tendsto` uses `Metric.tendsto_atTop`).
  3. **Route D′**: move `KhinchinTypical`/`khinchinK₀` upstream so
     `Headline.lean:136` invokes `xstar_khinchinTypical` — trivial after (2).
- **FORBIDDEN DRIFT**: do NOT add MORE standalone Khinchin machinery (the
  `KhinchinBrick`/`Family`/`RefineFamily` layer is DONE); every lap must now
  advance the WIRING (step 1 or 2) — the crux, not the scaffold. The
  route-decisive uncertain case is whether the per-stage family guarantee
  transfers to a mid-stage prefix (the analogue of the CF/d-ary prefix-frequency
  transfer already solved via `sched_dominance`); the smallest probe is step 2's
  early/late split. Do NOT retreat to easier off-path leaf work.
- **Fence (unchanged, sticky)**: additive extension of `TBrick`/`CFSchedule` IS
  authorized. **Hard invariant**: NEVER edit/weaken an existing Tier-1 decl or any
  JUDGE-frozen statement (`IsAbsolutelyNormal`, `IsCFNormal`, `khinchinK₀`,
  `KhinchinTypical`, both headlines). After ANY schedule edit, re-run `#print
  axioms exists_absolutely_normal_cf_normal` — MUST stay `[propext,
  Classical.choice, Quot.sound]`; a change means locked machinery was modified —
  revert. Constants: distortion `2`, γ-mixing `(9/10)`, brick ratio `1/(2d)`.
- **Why**: Tier 1 is banked (first formalization, axiom-clean). Tier 2 is the
  sole open obligation, the route is source-backed (KHINCHIN.md W6, uniform-
  integrability), the machinery is proved, and only bookkeeping (schedule rewire +
  a `3ε`/telescope assembly) remains. This is tractable multi-lap work, NOT a
  generational wall. Descoping to "Tier 1 is the deliverable" would be
  miscalibrated caution.

</details>

### Directive history
- 2026-08-24 (review lap, grind portion): after retargeting, PROVED item 1 end to
  end — `chainTail_dev_prefix_var` (`2c61e7c`) then `chain_cf_digit_freq_tendsto_uniform`
  + `chain_orbit_equidist_uniform` (`5fe8f09`), all axiom-clean, build green 8757.
  The route-decisive mid-block question is settled YES in-kernel.  Marked item 1
  DONE, repointed the mandated move to item 2 (ψ-round `_uniform`) hardest-first,
  and updated the route-decisive case to per-round ψ feasibility.
- 2026-08-24 (review lap → HDOM REFUTED, ASSEMBLE HDOM-FREE LIMIT): validated the
  executed route pivot. Confirmed one open `sorry` (the crux) + both B5′ headlines
  axiom-clean via real `#print axioms`. The prior directive's item (1) mandated
  `chain_orbit_equidist` WITH a dominance hypothesis — but the grind laps (correctly
  following the math) refuted `hdom` as unattainable (`ec0875d`) and PROVED the
  replacement crux crack `exists_uniformly_freq_good_block_steer` (`f2b4b33`,
  axiom-clean). So the directive was STALE (a literal grind lap would chase the dead
  hdom route). Rewrote the mandated move to the **hdom-free `chain_cf_digit_freq_tendsto`
  variant** (step-4 assembly), named the route-decisive case (does the mid-block bound
  close via `countOccurrences_append_addslack₂` without hdom, and does the `o(word)`
  boundary slack divide out), and FORBADE proving further block/measure atoms (the
  toolkit is closed). No charter route trigger fired (route needs a `CFChainFreq`
  copy-extend, not a forbidden import). Build green 8757; not-complete (open crux) so
  no self-stop despite ALLOW_STOP=1.
- 2026-08-24 (review lap → B6 PIVOT TO CRUX): 11 straight grind laps (11–21)
  proved geometric/analytic ATOMS (each axiom-clean, each a green commit) but
  the crux `sorry` `exists_interleaved_affine_witness` stayed untouched and the
  recursion/telescoping was deferred "next lap" ~7 times — textbook crux-neglect
  (tractable leaves over the headline). Declared the atom toolkit COMPLETE;
  redirected to build the **frequency telescoping** hardest-first via an abstract
  generic-chain lemma `chain_orbit_equidist`, and named the route-decisive case:
  does CFCorrect's dominance survive the growing per-stage FILLERS + x/ψ
  ALTERNATION (both absent in B5′). No charter route trigger fired (route needs
  a CFCorrect port, not a forbidden import). Build green 8756; B5′ headlines
  re-verified trust-triple; B6 target = `sorryAx` (disclosed crux).
- 2026-08-24 (reflection lap → COMPLETION): **Tier 2 CLOSED — expedition
  complete, axiom-clean.** Executed the wiring directive to the finish in one lap:
  CFSchedule family-rewire (step 1), log-tail telescoping + crux
  `xstar_log_tail_uniform` (step 2), route-D′ layering + Tier-2 headline (step 3).
  All 10 headlines re-`#print axioms`-verified trust-triple. No proof obligations
  remain; ran the completion self-stop.
- 2026-08-24 (reflection lap): **route C′ RATIFIED; directive de-staled to force
  WIRING.** The prior directive still named the Chebyshev/variance plan, but grind
  laps correctly pivoted to the simpler Markov first-moment tail route and BUILT
  the full family machinery (`KhinchinBrick`/`Family`/`RefineFamily`/`CFLogTail`),
  all axiom-clean, finding+fixing a real level-tied-cutoff design bug same-run.
  Confirmed genuine forward motion (whole lemmas closing, crux shrinking), not a
  false summit. ROUTE VERDICT: CONTINUE (no charter trigger fired). Rewrote the
  mandated move to the CFSchedule family-rewire + `xstar_log_tail_uniform`
  assembly; forbade building more upstream machinery.
- 2026-08-24 (review lap): **Tier-2 route SETTLED, schedule fence RELAXED.** Last
  3 laps (fc801ba/17dc2c9/7d6740f) diagnosed the step-2 crux as "operator-gated"
  and stopped — a false stop (no operator on an autonomous run). Ratified the
  "goodC total-mass suffices" insight as REFUTED; confirmed the only route is the
  original W6 log-concentration bad zone, which is ADDITIVE (Tier-1 stays
  byte-identical/axiom-clean) so the prior "don't touch the schedule" fence is
  relaxed to "additive only, never modify locked decls." Proved the moment seed
  `summable_gaussKuzmin_logsq` (`E[(log a₁)²]<∞`). No charter route trigger fired
  (route needs Chebyshev/γ-mixing, not a forbidden Birkhoff import).
- 2026-08-26 (review lap): **Tier 1 LOCKED** — `exists_absolutely_normal_cf_normal`
  proved, axiom-clean (Pillai + xstar_dary_freq_tendsto + xstar_cf_freq_tendsto
  wired via a List.count/Finset.filter bridge lemma). Redirected to Tier 2
  (Khinchin-typical, W6), now unfenced. No route trigger fired (Tier 1 closed
  clean on the first attempt this lap).
- 2026-08-24 (review lap): d-ary chain + `m`-growth crux + Pillai window/phase
  count identity (`windowCount_eq_sum_phaseCount`) ALL closed & axiom-clean since
  last directive. Refreshed the stale directive (it still named the closed
  `m`-growth estimate as THE crux). Redirected to FINISH Pillai: the double-limit
  assembly (new crux), then the theorem statement, then the headline. No route
  trigger fired (whole-lemma targets closing fast; finishability improving).
- 2026-08-23 (review lap): Track A certified complete + axiom-clean; kept Track
  B / B5′ direction; sharpened next move to the W4 block-frequency Chebyshev
  assembly (`CFBlockFreq.lean`). No route trigger fired.
- 2026-08-24 (review lap): W4 + ALL Lemma-13 inputs certified proved & axiom-
  clean (8 headlines trust-triple only, 8735 jobs green). Diagnosed input-
  gathering fixation: crux (Lemma 13 assembly) untouched for ~10 laps. Redirected
  from "prove inputs" to "ATTACK the measure-balance selection lemma" — the
  route-decisive test. No route trigger fired (both deep imports discharged).
- 2026-08-23 (reflection lap): the measure-balance crux CLOSED — Lemma 13 +
  schedule + `xstar` + CF normality (`xstar_cf_freq_tendsto`) all proved
  axiom-clean since. ROUTE VERDICT: CONTINUE (no trigger fired; whole-lemma
  targets closing fast, finishability IMPROVED). Refreshed the stale directive
  (it still named the closed crux). Reframed destination: Tier 1 = B–Y
  abs-normal + CF-normal (source-backed, lockable) vs Tier 2 = + Khinchin
  (campaign-original stretch). Redirected to the d-ary side, hardest-first at
  the `m`-growth estimate; Khinchin fenced off until Tier 1 is stated + proven.

## JUDGE addendum (2026-08-23, post-kill judge pass) ⚖️

- Directive item (3)'s "stage the conjunction for JUDGE to freeze" is **DONE —
  by the judge, in `src/NormalNumbers/Headline.lean`**: frozen defs
  (`IsAbsolutelyNormal`, `IsCFNormal`, `khinchinK₀`, `KhinchinTypical`) + two
  frozen ∃-form statements — Tier 1 `exists_absolutely_normal_cf_normal`
  (B–Y) and Tier 2 `exists_absolutely_normal_cf_normal_khinchin` (the
  expedition headline).  **Deliberately witness-existence form** (does not
  name `xstar`), so a W6 capped rebuild discharges the same statements.
  Laps prove TOWARD these; do not restate or duplicate them.
- The Tier-1/Tier-2 framing is ratified **as sequencing, not descoping**:
  Tier 2 stays the expedition destination (its sorry now holds the
  self-stop gate open); the directive's W6 fence until Tier 1 is locked
  stands.
- `IsCFNormal` is the general-`x` form of the proven `xstar_cf_freq_tendsto`
  shape; discharging Tier 1's CF conjunct from it should be a wrapper, not
  new math.  `IsAbsolutelyNormal` is Track A's FULL `IsNormal` — the
  Pillai (or direct-blocks) obligation is unchanged.

### JUDGE note on the Tier-2 route question (2026-08-23) ⚖️

The directive's route-decisive question — "can `KhinchinTypical xstar` be
derived from already-proved frequency data alone?" — has a **known NO in
general**: `KHINCHIN.md` §"Both expansions at once" holds the
counterexample (planting digit `⌈e^{2^j}⌉` at position `2^j` is a
density-zero change that preserves EVERY pattern frequency yet breaks the
geometric mean).  Pattern frequencies can never suffice as a formal
implication; the missing ingredient is **large-digit tail control /
uniform integrability of `log a`**.  So the honest fork is: (a) find a
digit-size/tail-mass bound already implicit in the schedule's good-block
selection (the `uSched_log_sum_le`-style log-sum telescopes are the right
family), or (b) the W6 digit-cap re-plumb per `KHINCHIN.md` W6.  Do not
spend laps attempting the frequencies-only derivation.

## Standing charter (destination)

Two classical harvests of one machine — Birkhoff-on-[0,1] applied to two
digit-reading dynamical systems:

- **Track A — base-b normality** (✅ COMPLETE, axiom-clean): Wall's theorem
  (`isNormal_iff_equidistributed_orbit`), the ln 2 reduction
  (`isNormal_log_two_of_equidistributed`), Stoneham's constant unconditional
  (`isNormal_two_stoneham23`).
- **Track B — CF metric theory / Khinchin** (🔨 active): the B5′ expedition
  (W1–W6, plan in `KHINCHIN.md`). **Tier 1 (source-backed, lockable)** =
  `xstar` absolutely normal ∧ CF-normal (Becher–Yuhjtman, first formalization).
  **Tier 2 (stretch, original even on paper)** = + Khinchin-typical (W6 graft).
  W1✅ W2✅ W3✅ W4✅ + W5 core ✅ (Lemma 13, schedule, `xstar`, CF normality —
  all axiom-clean). Remaining Tier 1: d-ary simple normality + Pillai + stated
  conjunction. Governance: statement freezing is JUDGE-owned (`JUDGE.md`);
  grind laps prove frozen statements and add intermediate lemmas.

Route-level abort/escalate triggers: (a) γ-mixing rate collapses below summable
→ escalate (would break W4/W5); NOT fired (geometric proven). (b) W5/W6 needs a
deep import the charter forbids (CLT/KPW/Birkhoff) → escalate; not yet reached.
