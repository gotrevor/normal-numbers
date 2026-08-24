# JUDGE — the attended architect/judge role for the B5′ campaign ⚖️

The treadmill grinds; **statement authority stays with the attended judge
sessions** (the goodstein "judge mode" pattern).  A monitor thread loads this
file and works the checklist.  Laps never edit this file above the Ledger.

## Division of authority

- **Laps (unattended)**: prove the frozen statements; add any private
  intermediate lemmas; commit green; flag suspected-wrong statements in
  HANDOFF and move on.  Laps do NOT reshape, weaken, re-hypothesize, or
  delete a frozen statement, and do not change the W-plan or this file.
- **Judge (attended)**: adjudicates flags, owns every statement change, owns
  route changes, owns the W-plan (`KHINCHIN.md`), decides stop/continue.

## Per-visit checklist

1. **Status**: `lean-treadmill status normal-numbers` — lap/kind, sorry
   count, HEAD; then `git-safe -C ~/src/normal-numbers log --oneline
   <last-judged>..HEAD` for what's new.
2. **Statement integrity** (the non-negotiable): diff the frozen statement
   file(s) against the last judged SHA —
   `git-safe diff <last-judged> -- src/NormalNumbers/CFCylinder.lean` —
   every frozen statement and every anchor must be **character-identical**
   (docstrings/intermediates may change freely).  Any drift: stop the
   treadmill, adjudicate, restore or ratify explicitly here.
3. **Axiom hygiene** on newly discharged sorries: `#print axioms` = exactly
   `propext`, `Classical.choice`, `Quot.sound`.  No `native_decide` (prefer
   `decide +kernel`), no new axioms, no unexplained `maxHeartbeats` bumps —
   `/lean-review` covers the smell list.
4. **Silent-restriction scan**: a frozen statement whose proof suddenly
   delegates to a reshaped private lemma can hide a weakening ("a
   generalization can be a silent restriction").  Skim the load-bearing
   intermediates of anything newly discharged.
5. **HANDOFF flags**: read the newest `HANDOFF-*.md`.  A lap claiming a
   frozen statement is *wrong* is the highest-priority item — adjudicate
   against `papers/becher-yuhjtman-2019-abs-normal-cf-normal.md` and the
   source paper before touching anything.
6. **Ledger**: append a dated line below (SHA judged through + verdict).

## Architecture guardrails (enforce; laps must not cross)

- **No efficiency machinery.**  B5′ deliberately drops B–Y's O(n⁴) claim:
  no Morita/Vallée CLT, no B–Y Lemma 4/5 analogs.  Length control is the
  Markov + Fibonacci substitute (W2).
- **W3 route is decided** (`KHINCHIN.md` "W3 route"): the `tailDensity`
  family + ratio-contraction, Kuzmin √n-rate as fallback.  No Philipp, no
  Merlevède–Peligrad–Rio, no KPW imports; no ergodicity or pointwise
  Birkhoff anywhere in B5′.
- **Conventions are load-bearing**: digit `0` = junk marker (rationals /
  out-of-range), so `∀ a ∈ w, 1 ≤ a` hypotheses stay; cylinder-vs-interval
  mismatches are null sets — measure-zero handling, not set equalities.
- **Constants**: the frozen distortion/quasi-mult constant is `2` (B–Y's
  own proofs deliver exactly 2).  A lap that can only reach a weaker
  constant has a proof problem, not a statement problem — judge decides.

## Stop / escalate

- `lean-treadmill stop normal-numbers` (graceful) · `--after-lap` ·
  `--now`.  Stop for: statement drift (check 2), axiom drift (check 3), or
  thrashing (a lap burning its budget on `volume_cfCylinder` without
  committed intermediates → consider an attended session to split the
  bridge into its own scaffold).
- Campaign self-stops when `src/` is sorry-free (= W1 done).  Then the
  judge runs the close-out: full `#print axioms` sweep of the 12,
  `/lean-review` on the whole W1 diff, ROADMAP/`KHINCHIN.md` status update,
  and stages the W2 scaffold (new frozen statements = judge work).

## Ledger (append-only, newest last)

- 2026-08-23 · judged through `4ad5f8e` (scaffold + briefs, pre-campaign
  baseline) · 12 sorries open · statements/anchors as frozen.
- 2026-08-23 11:20 · judged through `8fa056f` (lap 1 algebra batch, 9/12
  discharged) · statements + anchors character-identical vs `4ad5f8e` (only
  `sorry` lines replaced; private helpers `cfK_cons`, `one_le_cfK` added —
  in-charter) · smell scan of the Lean diff: greps clean (no `axiom`, no
  `native_decide`, no `maxHeartbeats`, no import changes) · kernel-tier
  `#print axioms` NOT run this visit (lap live, avoiding build contention) —
  box's "axiom-clean" stands at its tier; full sweep owed at close-out ·
  no wrongness flags in HANDOFF · lap grinding the 3 measure sorries
  (`volume_cfCylinder` crux) · verdict: healthy, continue.
- 2026-08-23 ~11:45 · **W1 CLOSE-OUT** · judged through `f76a1b1` (laps 2–3;
  campaign complete, self-stopped after lap 3) · statements + anchors
  character-identical vs baseline across the whole campaign (only the 12
  `sorry` lines ever removed in `CFCylinder.lean`) · **kernel-tier
  `#print axioms` sweep run by the judge on all 12: every one a subset of
  {propext, Classical.choice, Quot.sound} — axiom-clean, verified
  2026-08-23** · `/lean-review` on `4ad5f8e..HEAD`: no heartbeat bumps, no
  `native_decide`, no `axiom` decls, no trust escapes, no silenced linters,
  no Prop-def laundering, no import changes; residue = style lints only
  (unused `hwpos`/`hupos` binders forced by the frozen shapes, a few
  `<;>`/`simpa`/unreachable-tactic nits) · no wrongness flags · verdict:
  **W1 ratified**.
- 2026-08-23 ~11:50 · **W2 scaffold staged by the judge** (new frozen
  statements): `CFDigitLaw.lean` — `genWords` def + 10 sorry'd statements
  (digit law, disjointness, partition `tsum`, Gauss/Lebesgue two-sided
  comparison, `γ(univ)=1`, `K ≤ ∏(aᵢ+1)`, conditional `E[log qₙ] ≤ Cn`,
  Markov half-mass Lemma-5 substitute, Fibonacci relative-length bound) ·
  4 kernel-checked anchors frozen · builds green (10 sorries expected) ·
  these shapes are now the frozen trust surface for the W2 campaign.
- 2026-08-23 ~12:15 · **W2 CLOSE-OUT** · judged through `2c8daa4` (laps
  1–3; campaign complete, self-stopped) · `CFDigitLaw.lean`: only the 10
  `sorry` lines removed — statements + anchors character-identical ·
  `CFCylinder.lean`: two `private` helpers lifted public (`one_le_cfK`,
  `irrational_gaussMap`), signatures identical, frozen statements
  untouched — in-charter shared-scaffold lift · **kernel-tier
  `#print axioms` sweep run by the judge on all 10: exactly
  {propext, Classical.choice, Quot.sound} on every one — axiom-clean,
  verified 2026-08-23** · smell scan of the campaign diff: clean (no
  heartbeats, native_decide, axioms, trust escapes, silenced lints) ·
  no wrongness flags · verdict: **W2 ratified**.
- 2026-08-23 ~12:20 · **W3 scaffold staged by the judge** (new frozen
  statements): `CFMixing.lean` — 4 sorry'd statements
  (`measurePreserving_gaussMap` = B1 flag · the conditional-density
  identity `|I_w ∩ T^{-|w|}A| = (∫_A h_t)·|I_w|`, `t = K(w⁻)/K(w)` ·
  `cylinder_mixing` = cylinder-conditioned quantitative
  Gauss–Kuzmin–Lévy, multiplicative `1 ± Cρᵏ` envelope, uniform in `w` ·
  `gauss_kuzmin` = unconditioned corollary = B4 flag) · 4 kernel-checked
  anchors (incl. the `t`-direction anchor `t([2]) = 1/2`) · builds green
  (4 sorries expected) · ⚠️ **escape valve pre-authorized on
  `cylinder_mixing` ONLY**: if laps evidence that geometric `ρᵏ` resists
  and Kuzmin `e^{-c√k}` is what materializes, the JUDGE (never a lap)
  weakens the rate to a summable-error form — W4 accepts either · these
  shapes are now the frozen trust surface for the W3 campaign.
- 2026-08-23 15:05 · **mid-run visit (lap 5 live)** · judged through
  `6539c55` (textual tier; kernel sweeps owed at close-out — lap live,
  avoiding build contention) · **W3 COMPLETE at `a7a68b1`, 8 laps,
  GEOMETRIC rate achieved (C = 8·log 2, ρ = 9/10) — escape valve unused** ·
  `CFMixing.lean`: only the 4 `sorry` lines removed, statements + anchors
  character-identical; imports of new proof modules added (in-charter) ·
  `CFCylinder.lean`/`CFDigitLaw.lean`: 12 more pure privacy lifts,
  signatures identical, frozen statements untouched · smell scan of the
  full range: ONE local `set_option maxHeartbeats 1600000 in` on
  `CFContraction.stepOp_lipschitz` (the analytic crux; scoped to the one
  theorem, full proof-sketch docstring — 🟡 accepted, revisit if it rots) ·
  **scope note**: box did NOT self-stop at W3-complete (src/ sorry-free,
  eligible) — elected to continue into W4 groundwork; discipline good
  (no fake-frozen scaffolds, ratification requested, per-lemma axiom
  claims), bounded by the 12-lap breaker; continuation tolerated, close-out
  will re-scope · **W4 shapes PROVISIONALLY RATIFIED** (box request):
  `tChain` + `setIntegral_inter_preimage` (s-started identity) ·
  `gaussMeasure_cylinder_mixing` (exact γ-correlation decay, geometric,
  `≤ (9/10)^g·4|A|·γ(I_v)` — stronger than the planned Leb-only route,
  accepted as the W4 engine) · `blockCount`/`variance_blockCount_le`
  (`≤ (8|v|+80)·n·γ(I_v)`; the factor-2-for-simplicity trade accepted —
  any n-independent K(v) suffices) · `chebyshev_blockCount` +
  `chebyshev_blockCount_brick` (the per-stage B–Y `< ¼` inputs; brick
  version's constant 7 fine) · nit for close-out: `chebyshev_blockCount`
  docstring still displays `4|v|+80` while the statement says `8|v|+80` —
  fix the docstring · full ratification (kernel sweep + /lean-review)
  at close-out.
- 2026-08-23 ~18:35 · **post-kill judge pass** (treadmill stopped by Trevor,
  token budget; last lap landed `9e7d0e4`) · reflection lap's doc refresh +
  Tier-1/Tier-2 reframing reviewed — **ratified as SEQUENCING, not
  descoping** (Tier 2 = the expedition destination; W6 fence until Tier 1
  locked stands) · **HEADLINE SURFACE FROZEN by the judge**:
  `src/NormalNumbers/Headline.lean` — defs `IsAbsolutelyNormal` (full
  `IsNormal`, every `b ≥ 2`), `IsCFNormal` (general-`x` window-frequency
  form), `khinchinK₀` (tprod, index `k` ↦ digit `k+1`), `KhinchinTypical`;
  frozen statements `exists_absolutely_normal_cf_normal` (Tier 1, B–Y) +
  `exists_absolutely_normal_cf_normal_khinchin` (Tier 2, headline) — both
  ∃-form, deliberately not naming `xstar`, so W6's capped rebuild
  discharges the same statements · 4 kernel-checked anchors (overlapping
  window count; K₀ factor alignment at digits 1 and 2) · builds green
  (2 sorries expected — the self-stop gate now encodes the full
  conjunction) · DIRECTION.md judge addendum added (laps prove toward
  Headline.lean, never restate) · relaunch prepped: model swap fable/low →
  **sonnet/high** (Trevor's token budget; altitude laps stay opus) —
  frozen-statement + directive + judge stack is exactly the harness that
  makes a weaker grinder safe to try.
- 2026-08-23 21:25 · **mid-run visit (sonnet lap 4 live)** · judged through
  `ed2b9cc` (textual tier) · **TIER 1 DISCHARGED at `b3bc2c4`** —
  `exists_absolutely_normal_cf_normal` proved (Pillai.lean sorry-free +
  `xstar_dary_freq_tendsto` + the count-bridge lemma) · statement
  integrity: the ONLY minus line in `Headline.lean` since the freeze is
  Tier 1's `sorry`; defs/anchors/Tier-2 statement character-identical;
  added imports + one public bridge lemma in the frozen file (in-charter;
  bridge should be `private` — hygiene nit for close-out) · smell scan of
  the range: clean · axiom tier: review lap claims kernel-verified
  trust-triple; **judge's independent `#print axioms` attempt hit the live
  lap's rebuild (missing olean) — owed at close-out on a settled tree** ·
  box now on Tier 2 per directive (Khinchin.lean: geometric-mean →
  log-average reduction, schedule log-sum telescopes, `khinchinK0_pos`) ·
  judge route-note added to DIRECTION: frequencies-alone derivation is
  provably impossible (KHINCHIN.md counterexample); tail-control or W6
  caps required · verdict: healthy, continue.
- 2026-08-23 22:45 · **mid-run visit (lap 6 review live)** · judged through
  `6f18228` (textual tier) · **fence flag adjudication CONCURRED**: grind
  laps hit the old "don't touch the schedule" fence, raised `JUDGE-FLAG`
  (`fc801ba`) and STOPPED rather than crossing — correct charter behavior;
  the review lap adjudicated within its directive authority: fence relaxed
  to ADDITIVE-ONLY with the hard invariant (never modify a Tier-1 decl or
  a JUDGE-frozen statement; re-run `#print axioms` on Tier 1 after any
  TBrick/schedule edit).  Judge concurs — the ∃-form headline freeze
  anticipated exactly this W6 rebuild · route findings ratified: the
  "goodC total-mass suffices" claim REFUTED quantitatively (`7d6740f`);
  Birkhoff import correctly rejected as charter-forbidden; route = the
  original W6 log-concentration bad zone · Tier-2 funnel is now clean:
  `gaussKuzmin_logsum = log K₀` proved, `khinchinTypical_iff_log_tendsto`
  + value-count bridge proved — **the crux is ONE staged schedule lemma
  (`xstar_log_tail_uniform`, a pure tail-mass bound) + the additive
  union-bound plumbing + assembly** · src/ 1→2 sorries is the sanctioned
  decomposition pattern, not regression · verdict: healthy, continue;
  breaker has ~6 laps.
- 2026-08-23 22:50 · **mid-run visit (lap 7 grind live, 06m in)** · judged
  through `f505a11` + the live uncommitted WIP (textual tier) · **no `src/`
  commits since `6f18228`** — the two commits in range are doc/ledger only
  (`a96c575` judge ledger, `f505a11` handoff), so **statement integrity is
  trivially clean**: zero minus lines in any frozen file, Tier-1 decl
  untouched · **WIP under the lap** (`Khinchin.lean`, +60/-1): the box is
  building the Markov first-moment machinery behind the crux —
  `logTailTerm` / `logTailFn` (private defs), `logTailTerm_integrable`,
  `integral_norm_logTailTerm` (both proved), and a new **staged** theorem
  `integral_logTailFn_eq` (`∫ logTailFn K dγ = log K₀ − Σ_{k<K} γ([k+1])·log(k+1)`)
  carrying a `sorry` · smell scan of the added lines: **clean** (no
  `native_decide`, no `maxHeartbeats`/`maxRecDepth`, no `axiom`/`admit`, no
  new `set_option`) · `src/` sorries 2 → **3** — sanctioned decomposition,
  NOT regression, but ⚠️ **`integral_logTailFn_eq` is currently an orphan**:
  nothing references it yet, the crux `xstar_log_tail_uniform` is still a
  bare `sorry`.  Close-out check item — it must end up either discharged
  and *used* by the crux, or deleted; a proved-but-unreferenced tail lemma
  is dead weight, an unproved-and-unreferenced one is a second obligation
  masquerading as progress · untracked scratch `src/NormalNumbers/ZZTest.lean`
  (3 lines, a `summable_nat_add_iff` name probe) — harmless, must not be
  committed; close-out nit · breaker: lap 7/12, prev lap +7 commits in 54m,
  ~5 laps of headroom · verdict: **healthy, continue** — funnel unchanged,
  one crux + plumbing + assembly still the whole remaining distance.
- 2026-08-23 23:43 · **mid-run visit (lap 8 grind live, 27m in)** · judged
  through `ce7fe12` (textual tier) · **ON TARGET — funnel unmoved, machinery
  grew under it** · statement integrity over `f505a11..HEAD`: **zero changed
  lines in ANY frozen file** (`Headline`/`CFCylinder`/`CFDigitLaw`/`CFMixing`)
  — headline surface and Tier-1 decl untouched across +1385 lines · **crux
  `xstar_log_tail_uniform` is character-identical** to the 22:50 reading —
  the whole lap's output is machinery *beneath* it, not a restatement of it ·
  **my lap-7 orphan flag CLOSED inside the lap**: `integral_logTailFn_eq` is
  now PROVED (via `integral_logTailFn_eq_of_hasSum` + `gaussKuzmin_logsum_hasSum`)
  and USED by `integral_logTailFn_tendsto`; `src/` sorries 3 → **2**, the two
  sanctioned ones · route relabelled **C′** and now fully visible as
  A′ first-moment integral → B′ Markov bad zone → C′ union plumbing → D′
  schedule layering, in 4 new modules (`CFLogTail` 552, `KhinchinBrick` 254,
  `KhinchinRefine` 200, `KhinchinFamily` 110) + `CFSchedule` threading —
  **A′/B′/C′ landed; D′ threading landed (`949f0b1`: xstar carries the
  guarantee); what remains is the final assembly into the crux** · schedule
  WAS edited (`CFSchedule.lean`, payload conjunct added to
  `exists_refinement_uniform`/`kminFn_spec`/`sched_step`) — in-charter under
  the relaxed additive-only fence, no frozen statement touched, build green at
  every commit, but this **arms the hard invariant: `#print axioms` on Tier 1
  is now OWED at close-out** (was already owed for W4→Tier 1; the schedule
  edit makes it non-optional) · smell scan: clean except **2 NEW localized
  `set_option maxHeartbeats 800000 in`** (`CFLogTail.lean:397,406`) — scoped
  form, acceptable, logged 🟡 for close-out review (repo total now 4) · doc
  nit: `integral_logTailFn_tendsto` docstring says "route B′" while the
  commits say C′ · breaker: lap 8/12, prev lap +8 commits in 32m — **~4 laps
  of headroom against one remaining lemma, and it is the hardest one**
  (schedule-dependent assembly).  ⚠️ `ce7fe12` is a late DESIGN FIX (summable
  family replaces level-tied cutoff) — a redesign this deep in the breaker is
  the one genuine schedule risk on the board · verdict: **healthy, on target,
  continue**.

## 🏁 CLOSE-OUT RATIFICATION — B5′ expedition COMPLETE

- 2026-08-24 06:15 · **CLOSE-OUT VISIT** (treadmill stopped; self-stop gate
  cleared — `src/` sorry-free) · judged through `4abec6d`, then `33cbd06`
  (judge nit commit) · **VERDICT: RATIFIED at KERNEL TIER.**

  **What landed**: `exists_absolutely_normal_cf_normal_khinchin` (Tier 2, the
  headline) PROVED at `4629029`, closing the expedition — one explicit real
  `xstar` that is simultaneously **absolutely normal ∧ CF-normal ∧
  Khinchin-typical**.  Tier 1 (Becher–Yuhjtman) had landed at `b3bc2c4`.
  The crux `xstar_log_tail_uniform` fell at `ed1a3e0` via route C′
  (A′ first-moment integral → B′ Markov bad zone → C′ family union plumbing →
  D′ schedule layering), after the `ce7fe12` design fix I flagged as the
  campaign's one real schedule risk — it was the right call, not a thrash.

  **Kernel verification (the tier this claim is now entitled to):**
  `#print axioms` on a settled tree (`lake build` green, 8751 jobs, exit 0),
  eight declarations, ALL `[propext, Classical.choice, Quot.sound]` — the
  mathlib-admissible trust triple, no `sorryAx`, no bespoke axiom, no
  `ofReduceBool`:
  `exists_absolutely_normal_cf_normal` · `exists_absolutely_normal_cf_normal_khinchin` ·
  `xstar_isAbsolutelyNormal` · `xstar_isCFNormal` · `xstar_khinchinTypical` ·
  `xstar_log_tail_uniform` · `xstar_log_digit_avg_tendsto` · `xstar_dary_freq_tendsto`.
  **This discharges the W4 → Tier 1 kernel debt AND the schedule-edit
  invariant** (both were owed from the 22:45 and 23:43 ledger entries).
  🧪 **Instrument red-tested**: the same harness was run against a deliberately
  `sorry`'d canary and its downstream consumer — both correctly reported
  `sorryAx`.  The sweep can fail, so its green means something.

  **Statement integrity, freeze (`9e7d0e4`) → HEAD**: the ONLY minus lines in
  any frozen file across the entire campaign are **three privacy lifts**
  (`bumpLast`, `cfCylinder_subset_uIcc`, `uIoo_subset_cfCylinder`:
  `private X` → `X`, statements byte-identical) — explicitly in-charter.
  The frozen defs (`IsAbsolutelyNormal`, `IsCFNormal`, `khinchinK₀`,
  `KhinchinTypical`) and both ∃-form tier statements are **character-identical
  to the freeze**.  Tier 2 was proved by discharging the frozen statement, not
  by weakening it — which is exactly what the ∃-form freeze was built to
  guarantee, and it held through a full W6 construction rebuild.

  **`/lean-review` over `3460cd7..HEAD`** (151 commits, +11593 lines, 33 files):
  🔴 zero · 🟡 three `maxHeartbeats` (all LOCAL `set_option … in` form:
  `CFContraction.lean:280` @1600000 previously accepted, `CFLogTail.lean:397`
  and `:406` @800000, new — accepted, the Markov integral swap is genuinely
  expensive) · zero `native_decide`, zero hand-declared `axiom`, zero
  `unsafe`/`partial`/`implemented_by`, zero silenced linters, zero bare
  `#print axioms` in built sources.
  **Check 10 (Prop-def laundering) audited explicitly** — the smell no axiom
  gate can see.  Six added Prop-defs, ALL discharged: the three headline defs
  by the three proved `xstar_*` theorems above; `SchedStep` by `schedStep_exists`
  + `sched_step` (both proved); `HasDiscLt`/`CFDiscLt` are constructed
  predicates with proved `.mono`/`.append` API.  **No laundered holes.**

  **Nits closed** (`33cbd06`): `chebyshev_blockCount` docstring `4|v|+80` →
  `8|v|+80` (two sites) · count-bridge helper `count_map_range_eq_card_filter`
  privatized in `Headline.lean` (used only at :117; statement byte-identical —
  a privacy NARROWING by the judge, logged here as a frozen-file touch) ·
  unused simp arg at `Khinchin.lean:445` fixed.  ⚠️ The naive fix (deleting
  the whole `simp only`) BROKE the build — the tactic was really reducing
  `if True`; correct fix was `simp only [if_true]`.  Axioms re-swept after
  these edits: unchanged, still the clean triple.  Scratch `ZZTest.lean` was
  cleaned up by the fleet on its own.  **Retracted nit**: the
  `integral_logTailFn_tendsto` "route B′" docstring I flagged at 23:43 is
  CORRECT (B′ *is* the bad-zone stage; that lemma is its input) — no change.

  **Residual debt**: none blocking.  Remaining build warnings
  (`HotSpot.lean`, `Stoneham.lean`: unused simp arg, deprecated `push_neg`,
  unreferenced binders) are all in files **untouched by this campaign** —
  pre-existing, not this expedition's to fix.

  **Outward status**: this is a major milestone — apparently the first
  formalization of Becher–Yuhjtman in any prover, and the three-way
  conjunction appears to be new even on paper.  Write-up + outreach
  (Becher, Yuhjtman, Scheerer) is DRAFT-ONLY; **all outward posts are
  Trevor's to send.**

- 2026-08-24 · **CORRECTION to the close-out entry above (novelty claim
  withdrawn)** · The close-out entry states "the three-way conjunction appears
  to be new even on paper."  **That claim is withdrawn.**  Trevor, 2026-08-24:
  *"I'd be careful making a big deal about this.  Perhaps the implication is
  simply trivial & unstated.  Better to be understated in any public
  announcement than overly excited."*  He is right, and the judge's error was
  an **instrument mismatch**, not a degree of confidence: the survey greps
  provers, mathlib, Zulip and AFP, so it can support a claim about
  FORMALIZATIONS and is structurally blind to the paper literature.
  "Unstated because trivial to an expert" is exactly the case it cannot see —
  and Becher and Yuhjtman are precisely the readers who would know whether the
  implication is routine.  **Standing rule for this repo**: claim only
  *apparently the first formalization of Becher–Yuhjtman in any prover* (survey
  named + dated, re-verified before outward use).  Describe the conjunction as
  "no write-up found," never as new.  Scrubbed from `STATUS.md`, `KHINCHIN.md`
  (×2) and the KB leaf; the historical `HANDOFF-*.md` batons still carry the
  old phrasing and are left as-is, being a dated record of what was believed at
  the time — a reason to archive them out of a public repo root rather than to
  rewrite them.
- 2026-08-24 · **Pre-public audit (no Lean touched)** · PDFs: 5 in `papers/`,
  **never committed**, correctly ignored by `.gitignore:3` (`papers/*.pdf`) —
  this repo is NOT on the expunge-PDFs-from-history todo, verified not assumed.
  Secret/enclave scan of all tracked files: clean (only two `/Users/gotrevor/...`
  path strings in handoff batons).  Repo has **no git remote at all**.
  ⚠️ **`CLAUDE.local.md` is TRACKED** (committed at `bbdec5a`) — content is the
  harmless one-line `@`-import, but it is the documented never-commit file and
  should be untracked; the `git rm --cached` fix is currently blocked by the
  bare-`rm` PreToolUse guard (false positive), so it is Trevor's to run or the
  hook's to fix.  28 `HANDOFF-*.md` batons sit in the repo root with drifted
  future dates — archive before publishing.
