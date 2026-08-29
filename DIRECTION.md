# DIRECTION — normal-numbers 🧭

Altitude laps (review/reflection) are the ONLY writers of the CURRENT DIRECTIVE
section. Grind laps READ and OBEY it; it OUTRANKS the HANDOFF. Keep it short —
detail lives in PENDING_WORK.md.

## CURRENT DIRECTIVE (set 2026-08-29 — the conjecture-graph objective)

- 🎯 **The objective is novel PROOFS — new mathematics.  Novel *formalization* is not the point
  here, at all** (operator, 2026-08-29: "The entire point is novel *proofs*.  This is different
  from other lean repos, where formalization *is* the point.").  Same doctrine as
  collatz-moonshot.  Weigh every candidate move by its probability of producing new mathematics;
  "first in any prover" carries no weight in prioritization.  Until the architecture points at a
  novel result, proving existing known math is uninteresting (lane 2 at best).
- **This repo's product is a machine-checked conjecture GRAPH, not a proof queue.**  A unit of
  progress = one green **node** (a named Prop - working hypothesis, novel axiom candidate, or
  interface - kernel-elaborated, with provenance docstring, an odds estimate, and a refutation
  probe under `experiments/`), one green **edge** (a sorry-free, axiom-audited wiring
  implication), or one **probe-refuted node**.  Each unit ends in a build + `#print axioms`,
  exactly like a grind lap.  Sink nodes: `IsNormal 2 (Real.log 2)` and its disjunctivity
  weakenings.  Every lap answers the standing question: *what is the weakest open node on each
  path to the sink - can we add a weaker node, or an edge, or kill one?*
- **Do NOT grind known mathematics here** unless it discharges a named node; that work is
  lane 2 (KB two-lanes doctrine): phase 1 tolerates warnings/`native_decide`/step boosts,
  distribution prep is a separate later pass.
- **Graph frontier (2026-08-29):** the ln-two ladder `Equidistributed lnTwoOrbit` →
  `LnTwoHypothesisFreq w` → `LnTwoHypothesisD w` / `Λ` (`LnTwoFreq.lean`,
  `ConditionalDisjunctive.lean`) and the run tower `LnTwoExpSep` / `LnTwoPolySep` with proved
  run-bound edges (`LnTwoRuns.lean`, `docs/lnTwo-kick-blueprint.md`).  Open architecture moves:
  the shared Diophantine-wall interface (joint with collatz-moonshot), the unconditional
  sliver-recurrence node family, mixing/discrepancy rungs.
- Phase-3 publishing state: complete locally; outward actions (PRs, Zulip, announcements)
  remain operator-owned.  The 2026-08-26 directive below is accurate history.

## SUPERSEDED DIRECTIVE (set 2026-08-26 — Phase 3 publishing-prep pass)

- **Operator scope:** complete the Phase 3 publishing-prep pass without pushing,
  opening PRs, posting announcements, mutating sibling repositories, touching
  the two known-false `CFScheduleA.lean` sorries, or changing headline theorem
  statements.
- **Facts-first state:** image-Khinchin, Track D, and
  `IsNormal.isDisjunctive` are complete. `ae_tail_average_tendsto` is proved;
  the older directive below that calls it open is explicitly superseded history.
  The formal-conjectures definition correction is PR-ready local work at sibling
  commit `c6126c56`, with its empty-block boundary test follow-up at branch HEAD
  `5d5832d0`; neither commit is merged upstream. The Champernowne contribution is
  likewise staged and externally unpublished.
- **Comparator state:** the exact Wall theorem and exact conditional ln-two
  theorem are harnessed with a Mathlib-only Challenge containing faithful real
  definition bodies, an import-only Solution, three semantic anchors, exactly
  `[propext, Quot.sound, Classical.choice]` permitted, and nanoda enabled. The
  non-default Comparator library, Lean-v4.33.1 pinned Linux CI, local identity
  probe, missing-name teeth test, README disclosure, and formalization metadata
  are present. Challenge/Solution compilation and the five-name identity/teeth
  gates pass locally; landrun plus nanoda is honestly CI-only.
- **Completion gate passed locally:** the full NormalNumbers and Comparator
  builds, five-name statement-identity probe, missing-name teeth test, exact
  headline axiom gate, config/YAML validation, and independent artifact audit
  all pass. The pinned landrun + nanoda execution remains configured for Linux
  CI and was not run locally because the complete pinned verifier binary set is
  not available offline. Leave a clean committed checkpoint; publication, PRs,
  and announcements remain operator-owned. No other roadmap objective is in scope.

## SUPERSEDED DIRECTIVE (set 2026-08-25 REVIEW LAP #3 — B6 measure route DONE + EXCEEDED; drive the ONE open crux: image-Khinchin's tail-average SLLN)

- **State (ground truth, real `#print axioms` this lap, HEAD `53e454c`, build 🟢 8760):**
  ALL of B5′ (10 headlines), B6 single-map `exists_cfNormal_and_affine_cfNormal`, AND
  B6 Tier-2 full family `exists_cfNormal_and_affine_family_cfNormal'` (any real `r`, `q>0`)
  are trust-triple `[propext, Classical.choice, Quot.sound]` — **DONE + axiom-clean.**
  The prior directive (B6 via the measure route) is FULLY DISCHARGED and EXCEEDED
  (the general affine family + full-`r` generality were bonus). The three remaining
  `src/` sorries: `CFAeKhinchin.lean:230` (THE live crux, below) and TWO dead/REFUTED
  schedule sorries (`CFScheduleA.lean:4400`, `:5774`) — directive-FORBIDDEN, leave untouched.
- **THE ONE OPEN OBLIGATION — `ae_tail_average_tendsto K` (`CFAeKhinchin.lean:226`).**
  `∀ᵐ x ∂γ, logBirkhoffSum K n x / n → ∫ logTailFn K dγ`. Only `K=0` is consumed (g-direct):
  it closes `ae_khinchinTypical` (currently `+sorryAx`) ⇒ the **image-Khinchin headline**
  (witness CF-normal + all affine images CF-normal + Khinchin-typical) via one graft into
  `exists_cfNormal_and_affine_family_cfNormal'`. This IS the crux: a strong law (a.e. Birkhoff
  convergence) for the UNBOUNDED log-digit function under the Gauss measure — no ergodic theorem
  in mathlib, so it goes through an L²→a.e. variance argument, mirroring the PROVEN `ae_orbit_freq`.
- **MANDATED ROUTE — the L² variance bound `variance_logBirkhoffSum_le K n`, via FINITE
  TRUNCATION (Approach B — avoids fragile nested `integral_tsum`).** Everything Finset until one
  MCT limit. Let `A_a := cfCylinder [K+1+a]`, `u_a := log(K+1+a)`, `S_n^M := Σ_{a<M} u_a·blockCount(A_a) n`
  (finite ⇒ `= Σ_{i<n} f_M∘gaussMapⁱ`, `f_M := Σ_{a<M} logTailTerm K a`). Then:
  1. `integral_blockCount_cross A B` : `∫ blockCount A n·blockCount B n dγ = Σ_{i,j<n} γ.real(T⁻ⁱA∩T⁻ʲB)`
     — two-cylinder generalization of the PROVEN `integral_blockCount_sq` (bounded, clean).
  2. `abs_cov_two_cyl_pair_le a b i j` : `|γ.real(T⁻ⁱ[a]∩T⁻ʲ[b]) − γ[a]γ[b]| ≤ 4·vol[b]·γ[a]·(9/10)^{dist(i,j)∸1}`
     for `i≠j` — general-`(i,j)` two-cylinder covariance, from PROVEN `gaussMeasureReal_pair_shift₂`
     (reduce to gap `m=dist`) + PROVEN `abs_cov_two_cyl_le` (aligned gap `m≥1`). Diagonal `i=j`
     handled separately (below).
  3. `variance_truncated_le K M n` : `|∫(S_n^M)² − (n·μ_M)²| ≤ n·(C₃ + 80·C₁·C₂)` UNIFORM in M.
     Split `Σ_{i,j<n}` into i=j (diagonal: `n·Var(f_M) ≤ n·∫f_M² ≤ n·C₃`, using distinct cylinders
     DISJOINT so cross a≠b vanish) and i≠j (off-diag: fold brick 2 via `sum_range_dist_le`+
     `geom_trunc_sum_le`, `|v|=1`). Constants: `C₁=Σ' u_aγ(A_a)` (`summable_gaussKuzmin_log` tail),
     `C₂=Σ' u_a vol(A_a)` (`summable_logMul_vol_cfCylinder`), `C₃=Σ' u_a²γ(A_a)`
     (`summable_sqLog_gaussMeasure_cfCylinder`) — finite partial sums `≤` tsum (nonneg).
  4. `variance_logBirkhoffSum_le K n` : `|∫(logBirkhoffSum K n)² − (n·μ)²| ≤ n·(C₃+80C₁C₂)`,
     from step 3 by MCT: `S_n^M ↑ logBirkhoffSum K n` a.e. (from `logTailTerm_tsum_ae_eq` at each
     `Tⁱx`, γ-preserving) ⇒ `∫(S_n^M)² ↑ ∫(logBirkhoffSum K n)²`, `μ_M→μ`; pass the bound to the limit.
  5. `chebyshev_logBirkhoffSum` + `ae_tail_average_tendsto` : TRANSCRIBE `chebyshev_blockCount` +
     `ae_orbit_freq` (`CFAeNormal.lean:81`) with `blockCount A p` ↦ `logBirkhoffSum K p`, `γv` ↦ `μ`.
     The monotone gap-squeeze is available because `logTailFn K ≥ 0` ⇒ `logBirkhoffSum K n` ↑ in n.
  6. **Graft**: intersect `ae_khinchinTypical`'s co-null set into `exists_cfNormal_and_affine_family_cfNormal'`
     (one more null set in the `BadAll` union) ⇒ image-Khinchin headline; re-`#print axioms` clean.
- **Hardest-first THIS lap**: bricks 1–2 are the decisive decorrelation machinery (route-decisive:
  if the two-cylinder pair bound folds to `O(n)` the whole route stands). Land them first; brick 3–4
  (MCT) and 5 (transcription) follow. A disclosed sub-`sorry` on brick 3/4 is a valid checkpoint.
- **FORBIDDEN DRIFT:** do NOT touch the dead schedule sorries (`CFScheduleA.lean:4400`,`:5774` — REFUTED,
  kept as dead code); do NOT re-attempt `variance_blockCount_psi_pushed` (FALSE); do NOT chase an
  explicit witness. Do NOT try to import/prove a general ergodic theorem — the variance route is
  self-contained over PROVEN bricks. ADDITIVE ONLY 🧊; re-`#print axioms` after changes (trust triple).
- **Why:** this is the LAST open obligation in the repo. Closing it upgrades the whole B6 result to
  the image-Khinchin headline (the campaign-original stretch) and leaves `src/` sorry-free except the
  two dead schedule stubs. The route reuses the exact machinery already proven for `ae_orbit_freq`;
  the only genuinely new content is the two-cylinder (vs single-cylinder) covariance, which the landed
  mixing bricks already supply. Finite truncation sidesteps the one Lean hazard (tsum-integral interchange).
- Historical directives below are SUPERSEDED.

## SUPERSEDED DIRECTIVE (set 2026-08-25 REVIEW LAP #2b — B6 PIVOTS TO THE MEASURE ROUTE; schedule crux REFUTED)

- **State (ground truth, real `#print axioms` this lap):** build 🟢 8757; both
  B5′ headlines `exists_absolutely_normal_cf_normal` (Tier 1 = Becher–Yuhjtman)
  and `exists_absolutely_normal_cf_normal_khinchin` (Tier 2) are trust-triple
  `[propext, Classical.choice, Quot.sound]` — **DONE**.  B6
  `exists_cfNormal_and_affine_cfNormal` = `+ sorryAx`.
- **🚨 ROUTE-DECISIVE FINDING — the schedule crux `variance_blockCount_psi_pushed`
  (`CFScheduleA.lean:4254`) is PROVABLY FALSE** (counterexample:
  `OBSTRUCTION-2026-08-25-variance-psi-pushed-FALSE.md`).  Take `v=[1]`, `wx'` deep with
  `ψ(cfCyl wx') ⊆ cfCyl [2,…,2]`: the pushed block count is `0` for all `x∈cfCyl wx'` at
  scales `n≤|wx'|`, so the LHS `= n²γv²γ(cfCyl wx')` beats the RHS `88 n γv γ(cfCyl wx')`
  once `n>88/γv≈212`.  Structural reason: a deep `cfCyl wx'` is a tiny interval, so
  `blockCount n(ψ·)` is near-CONSTANT over it for `n≲|wx'|`, at a value the affine map hands
  us (need not be `≈nγv`) ⇒ second moment is `Θ(n²)`, not `O(n)`; the base-mass factor cannot
  rescue that.  So `psi_pushed_chebyshev_brick`/`_poly` do NOT establish their conclusions
  (they carry disclosed `sorryAx`).  Both schedule z-routes are dead (two-stream super-exp
  `OBSTRUCTION-2026-08-24`; single-stream refuted here).  The 2026-08-24 review pre-registered
  this: escalate to the measure route (`ROUTE-ESCALATION-2026-08-25.md`).
- **THE MANDATED MOVE — prove B6 by the MEASURE argument (existence is trivially true a.e.).**
  The frozen headline is bare EXISTENCE (no explicit witness demanded).  The whole obligation
  collapses to ONE new core lemma; everything else is elementary measure theory over PROVED
  ingredients (Birkhoff-FREE — uses `variance_blockCount_le`, NOT any ergodic theorem):
  1. **`ae_isCFNormal` — THE new crux (a.e. CF-normality).**  `∀ᵐ y ∂gaussMeasure, IsCFNormal y`.
     Route (classic L²→a.e.): for a FIXED valid word `v`, `variance_blockCount_le`
     (`CFBlockFreq.lean:401`) + Chebyshev ⇒ `γ{|blockCount(cfCyl v) p ·/p − γv|≥δ} ≤ (8|v|+80)γv/(δ²p)`;
     along `p=k²` this is summable, Borel–Cantelli ⇒ a.e. convergence on `k²`, fill gaps by
     monotonicity of `p↦blockCount(cfCyl v) p x` + `(k+1)²/k²→1` squeeze ⇒ a.e.
     `blockCount(cfCyl v) p ·/p → γv`.  Intersect over the COUNTABLE set of valid `v` + the a.e.
     orbit-in-`(0,1)` condition (rationals null) ⇒ hypotheses of `isCFNormal_of_orbit_freq`
     (`CFOrbitFreq.lean:34`) hold a.e. ⇒ `IsCFNormal y` a.e.
  2. **`ae_isCFNormal_affine`:** `∀ᵐ x, IsCFNormal(ψx)`.  `{x:IsCFNormal(ψx)}=ψ⁻¹{IsCFNormal}`,
     complement `= ψ⁻¹(null)`; `volume_preimage_affineMap` (`CFAffine.lean:94`, PROVED) ⇒ ψ⁻¹
     preserves volume-null, and `γ≈volume` on `(0,1)` (bounded density) ⇒ preserves γ-null ⇒ co-null.
  3. **Assemble `exists_cfNormal_and_affine_cfNormal`:** on the feasible interval `(0,1)∩ψ⁻¹(0,1)`
     (positive measure when `-q<r<1`) both co-null sets meet ⇒ nonempty witness.  Plug into the
     SAME feasible branch where `exists_interleaved_affine_witness` sits; the existing integer-shift
     reduction handles `r∉(-q,1)`.  Then B6 is `sorryAx`-free.
- **FORBIDDEN DRIFT:** do NOT attempt to prove `variance_blockCount_psi_pushed` or any downstream
  `psi_pushed_*` / `_poly` / conditional-`wz` lemma — they are FALSE / rest on the false crux; do
  NOT grind the two-stream `schedA_block_linear` or the schedule `exists_interleaved_affine_witness`
  (obstructed, explicit-witness route retired); do NOT DELETE them (leave in `src`, mark REFUTED —
  nothing is deleted); do NOT chase an explicit/constructive witness (not required by the theorem,
  and obstructed for the affine case).  Do NOT "box stuck": the measure route is doable — drive it.
- Both B5′ headlines stay proved + axiom-clean; re-`#print axioms` after any change
  (trust triple, else revert).  ADDITIVE ONLY 🧊.
- **Why:** B6's stated theorem is mere existence, which is a.e.-trivial (a.e. `x` is CF-normal and
  a.e. `x` has `ψx` CF-normal, two co-null sets that must intersect).  The schedule aimed at an
  EXPLICIT witness — a bonus the theorem never asked for — and its crux is now provably false, so
  chasing it further is proving a falsehood.  The measure route honestly discharges the stated
  theorem from the already-proven variance engine with no forbidden import, and its one real lemma
  (`ae_isCFNormal`) is classical.  This is the fastest path to an axiom-clean B6.
- Historical directives below are SUPERSEDED (L4 measure bricks, cfK-cap graft, ψ(xA) irrationality,
  Chebyshev/transfer engine all DONE-but-now-off-path; capped-digit, two-stream, conditional-`wz`,
  and x-cylinder-relative fallbacks all refuted/obstructed).

## SUPERSEDED DIRECTIVE (2026-08-24 attended — B6 ENDGAME: CAPPED-DIGIT ROUTE, refuted + two-stream obstructed)

- **State (baton `HANDOFF-2026-08-24-B6-crux-assembled.md`)**: the crux
  `exists_interleaved_affine_witness` is ASSEMBLED and machine-checked except
  TWO `sorry`s.  Build green, B5′ headlines untouched (trust-triple).  Close
  them in this order:
  1. **`schedA_block_linear` (`CFScheduleA.lean:2386`) — THE math obligation,
     hardest-first.  Ratified route: DIGIT-CAPPED steering.**  Steer blocks
     restricted to digits ≤ D have `log K(u) ≤ n·log(D+1)` — linear by
     construction, killing the Lévy-rate obstruction (the cfK finding).
     Freq-goodness survives the cap: for target blocks v containing a digit
     > D the count is 0 and the requirement `< δn + |v|` holds once the
     γ-tail mass past D is < δ (pick D = D(δ)).  **ROUTE-DECISIVE CASE, probe
     FIRST**: *navigation under the cap* — landing `cfCylinder(w·u)` inside a
     target interval can force one large first digit when the target sits in
     the small-x corner.  Two candidate discharges, in order: (a) the
     recursion CHOOSES its target cells — co-design targets away from the
     corner (bounded first-digit cells); (b) allow ONE uncapped entry digit
     per block (a single digit adds `log(a)` = O(1)·log(scale), still o(n)
     amortized — check it against the budget).  If BOTH fail, that is the
     real crux: record the obstruction precisely and STOP for an attended
     review — do not grind substitutes.
  2. **`TODO(shift)` (`:2584`)**: `IsCFNormal_add_int` (Gauss orbit ignores
     the integer part) + the `(-q,1)`-representative reduction.  Bounded and
     well-posed — OFFLOAD TO ARISTOTLE at lap start, prove locally only if
     the poll comes back empty.
  3. **Signpost negations (owed, see SIGNPOST RULE below)**: the
     `r ∉ (-q,1)` falsity theorem beside the restricted crux; the hdom
     refutation marker (kernel-tier iff a concrete witness is cheap).
- Both B5′ headlines stay proved + axiom-clean; re-`#print axioms` after any
  schedule work (trust triple, else revert).
- Historical review-lap directive below still governs anything it covers that
  this endgame note doesn't.

## PREVIOUS DIRECTIVE (2026-08-24 review lap — B6: HDOM REFUTED, ASSEMBLE THE HDOM-FREE LIMIT)

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
- 2026-08-25 (review lap #3 → drive image-Khinchin's tail-average SLLN, the ONE open crux): inventory by
  real `#print axioms` (HEAD 53e454c, build 🟢 8760) confirmed the measure route DONE and EXCEEDED — B6
  single-map AND the full affine family (`exists_cfNormal_and_affine_family_cfNormal'`, any `r`, `q>0`)
  are all trust-triple. The only open obligation in the whole repo is `ae_tail_average_tendsto`
  (`CFAeKhinchin.lean:230`), feeding `ae_khinchinTypical` (+sorryAx) ⇒ the image-Khinchin headline. Set
  the directive to PROVE it via the L² variance bound `variance_logBirkhoffSum_le`, decomposed into 5
  bricks under the KEY INSIGHT that a FINITE-truncation formulation (Approach B) reduces the whole
  second-moment computation to Finset algebra + one MCT limit, sidestepping nested `integral_tsum`.
  Hardest-first = the two-cylinder covariance bricks (`integral_blockCount_cross`, `abs_cov_two_cyl_pair_le`),
  which are the route-decisive decorrelation core. No charter trigger fired (additive, self-contained).
- 2026-08-25 (review lap #2b → B6 PIVOTS TO THE MEASURE ROUTE; schedule crux REFUTED): while
  driving step 1c of the "prove the variance crux" directive, analysis of the pushforward
  structure produced a RIGOROUS COUNTEREXAMPLE to `variance_blockCount_psi_pushed` (v=[1], ψ(cfCyl
  wx')⊆cfCyl[2,…,2] ⇒ pushed count ≡0 at scales n≤|wx'| ⇒ LHS=n²γv²γ(wx') > RHS once n>88/γv). The
  crux is FALSE, hence `psi_pushed_chebyshev_brick`/`_poly` establish nothing; both schedule z-routes
  are dead. The 2026-08-24 review pre-registered exactly this escalation to "escape #3 (measure
  argument)". Wrote `OBSTRUCTION-2026-08-25-variance-psi-pushed-FALSE.md` + `ROUTE-ESCALATION-2026-08-25.md`.
  Rewrote CURRENT DIRECTIVE to pivot B6 to the MEASURE route: the stated theorem is bare existence,
  trivially true a.e., so prove `ae_isCFNormal` (a.e. CF-normality via L²→a.e. Borel–Cantelli from
  the PROVED `variance_blockCount_le`, Birkhoff-free) + ψ⁻¹-preserves-null ⇒ two co-null sets meet ⇒
  witness. Retires the entire schedule/explicit-witness chain (kept in src, marked REFUTED, not
  deleted). Charter trigger FIRED (mandated crux false) and handled by pivot, not stop.
- 2026-08-25 (review lap #2 → B6: PROVE ψ-PUSHED L² VARIANCE CRUX): inventory by real
  `#print axioms` — build green 8757; both B5′ headlines trust-triple = DONE; B6
  `+sorryAx` via the DEAD two-stream `schedA_block_linear` (`CFScheduleA.lean:5630`).
  Found prior directive STALE-in-a-good-way: its step 1 (ψ(xA) irrationality) is PROVED
  and steps 2–3 (Chebyshev budget + transfer) COLLAPSED — the grind narrowed the whole
  clean single-stream z-selector (`psi_pushed_chebyshev_brick`→`_poly`) to ONE disclosed
  analytic sorry `variance_blockCount_psi_pushed` (`:4254`). Validated as genuine crux
  work, not leaf-fixation (last ~10 laps: Markov wrapper proved, conditional-at-`wz` route
  walled + corrected honestly, clean local-density architecture found). Rewrote CURRENT
  DIRECTIVE to mandate PROVING the crux, hardest-first, decomposed: (1) restricted ψ-pushed
  2nd-moment identity (routine, land first), (2) ψ-conjugated interval-base mixing via
  change-of-variables (bounded density ratio) extending `gaussMeasure_cylinder_mixing` (THE
  core), (3) geometric-sum assembly mirroring `variance_blockCount_le`. Base-mass factor
  `γ(cfCyl wx')` MANDATORY (its loss walled every prior route). No charter trigger fired.
- 2026-08-25 (review lap → B6 L4: CRUX PROVED, RE-INTEGRATE Z-SIDE, ψ(xA) IRRATIONALITY FIRST):
  inventory by real `#print axioms` — build green 8757; both B5′ headlines
  (Becher–Yuhjtman Tier 1 + Khinchin Tier 2) trust-triple = DONE; B6
  `exists_cfNormal_and_affine_cfNormal` still `+sorryAx` via the DEAD two-stream
  `schedA_block_linear` (`CFScheduleA.lean:4823`, sole `src/` sorry). Found the CURRENT
  DIRECTIVE STALE: its mandated crux `schedL4_block_linear` is PROVED (`030d8fb`) and
  its step-4 "z-side = REUSE" is REFUTED (`b178653`: cfK-rewired `StepSpecL4` carries
  zero z-control). Validated the grind as ON-PATH, not leaf-fixated: last ~10 laps
  proved the block-linear crux, landed the x-side, built the Z-I measure engine + Z-III
  ingredients — genuine crux work. Rewrote CURRENT DIRECTIVE to mandate z-side
  re-integration, hardest-first = force ψ(xA) irrational via a per-stage diagonalization
  filler digit (`exists_digit_cfCylinder_notMem` over an enumeration of `ψ⁻¹(ℚ)`),
  keeping the freq-good block on the FULL hull (target-shrink RULED OUT: breaks the
  `¼γwx≤γtar` balance via `gaussMeasure_middle_half_hull_ge`/`hIcc`). Then Chebyshev
  budget + z-bad record (Z-I), Z-II transfer, Z-III assemble + excise. No charter
  trigger fired.
- 2026-08-24 (review lap → B6 L4: CLOSE `schedL4_block_linear` VIA cfK-CAP GRAFT):
  inventory by real `#print axioms` — build green 8757, both B5′ headlines
  trust-triple, sole `src/` sorry = the DEAD two-stream `schedA_block_linear`.
  Validated the L4 pivot as SOUND and the grind as ON-PATH (not leaf-fixated): the
  last ~5 laps located + proved the block-linear support layer (relative
  regularization) and started the recursion skeleton — all genuine crux work. Found
  the CURRENT DIRECTIVE STALE in specifics (it mandated L4 measure bricks 1/2a/3,
  all since DONE) while the grind had correctly advanced to the recursion +
  block-linear crux. Diagnosed the ONE open sub-obstruction as the cfK cap (turns
  `Nfib` affine in `|wx|`), confirmed it is a positive-measure selection (NOT the
  refuted hard digit-cap) with its entire measure/selection stack already proved.
  De-risked it in-lap: proved the bridge `cfK_le_of_notMem_cfKbadExtSet` + layer-1
  `exists_multiscale_freq_good_block_steer_len_cfK` (build green, additive).
  Rewrote CURRENT DIRECTIVE to mandate the cfK-cap graft (layer 2 → 3 →
  `schedL4_block_linear`), forbade grinding the dead two-stream lemmas. No charter
  trigger fired.
- 2026-08-24 (review lap → B6 PIVOT RATIFIED, RESUME SINGLE-STREAM L4): inventory
  by real `#print axioms` — build green 8757, both B5′ headlines trust-triple, sole
  `src/` sorry = the B6 crux `schedA_block_linear`. Diagnosed a FALSE STOP: the last
  grind laps hit a genuine, well-analysed obstruction (two-stream forces
  super-exponential blocks, `OBSTRUCTION-2026-08-24`), correctly proposed the
  single-stream pivot, then "box stuck" awaiting an operator ratification that never
  comes on an autonomous run. Discovered the single-stream "L4" route is the ORIGINAL
  module design (`CFScheduleA.lean:24–31`) whose L3 foundation `volume_preimage_affineMap`
  (`CFAffine:94`) is already proved; the two-stream layer was a later drift into the wall.
  RATIFIED the pivot: rewrote CURRENT DIRECTIVE to resume L4 (brick 1 = the ψ-pullback
  Gauss distortion bound `gaussMeasure(ψ⁻¹ S) ≤ (2/q)·gaussMeasure S`, all ingredients
  confirmed present), forbade grinding the dead two-stream lemmas and any further
  box-stuck. No charter route trigger fired (L4 is additive, no forbidden import).
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

- **Track C — affine images / Vandehey §7** (spec in `KHINCHIN.md` "B6"): pre-reads done
  2026-08-24; literature standing findings + the crawl recipe in `papers/README.md`.

Route-level abort/escalate triggers: (a) γ-mixing rate collapses below summable
→ escalate (would break W4/W5); NOT fired (geometric proven). (b) W5/W6 needs a
deep import the charter forbids (CLT/KPW/Birkhoff) → escalate; not yet reached.
