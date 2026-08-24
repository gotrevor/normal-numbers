# PENDING WORK — B5′ campaign

> **GRIND (2026-08-24 — CRUX PROVED; only route D′ remains).** Directive steps
> 1+2 DONE this reflection lap. `xstar_log_tail_uniform` is PROVED (the sole
> schedule-dependent Tier-2 crux), so `xstar_khinchinTypical : KhinchinTypical
> xstar` is PROVED axiom-clean `[propext, Classical.choice, Quot.sound]`. New
> log-tail telescoping lives in `CFCorrect.lean` (`logTailMass` + nonneg/append/
> take-mono/cutoff-mono, `uSched_logTail_le`, `tailSched_logTail_le`,
> `xstar_logTail_prefix_bound`, `logTailMass_cfPrefix`). Build green (8750 jobs).
>
> **THE ONLY REMAINING SORRY**: `Headline.lean:134`
> (`exists_absolutely_normal_cf_normal_khinchin`). It needs `xstar_khinchinTypical`,
> which lives DOWNSTREAM (`Khinchin.lean`), so Headline can't import it (cycle).
> **Route D′ (layering)**: move the frozen defs `khinchinK₀` + `KhinchinTypical`
> BYTE-IDENTICAL into a new upstream `KhinchinDefs.lean` imported by both sides;
> drop Khinchin.lean's `import Headline` (it only needs those defs + the CF
> machinery), so Khinchin no longer depends on Headline; then Headline imports
> Khinchin and closes the headline via `⟨xstar, <abs-normal ∧ cf-normal as in
> exists_absolutely_normal_cf_normal>, xstar_khinchinTypical⟩`. Keep the frozen
> STATEMENT + def CONTENT identical (JUDGE invariant); after wiring, `#print
> axioms exists_absolutely_normal_cf_normal_khinchin` must be trust-triple and
> Tier-1 must stay trust-triple. Grep Khinchin.lean for any non-def Headline
> references before dropping the import.

## Reflection — 2026-08-24 (deep reflection lap) 🧘

**Ground truth re-derived** (not taken from handoffs): `lake build` green (8750
jobs); `#print axioms exists_absolutely_normal_cf_normal` = trust triple (also
`xstar_cf_freq_tendsto`, `xstar_dary_freq_tendsto`, `pillai`); frozen headline
statements read faithfully vs source (khinchinK₀ tprod index alignment k↦k+1
verified via the in-file anchors; `KhinchinTypical`=geom-mean→K₀; `IsAbsolutelyNormal`
=full normality every base; `IsCFNormal`=window-freq→γ). Only two real `src/`
sorries: `Headline.lean:136` (Tier-2 headline) and `Khinchin.lean:527`
(`xstar_log_tail_uniform`, the crux). The rest are docstring mentions.

**DIRECTION CALL — CONTINUE route C′; the directive was STALE and is now fixed.**
The prior CURRENT DIRECTIVE still described the Chebyshev/variance bad-zone plan,
but the grind laps correctly pivoted to the simpler **Markov first-moment bound on
the nonnegative log-tail** and built the entire summable-family machinery
(`KhinchinBrick`, `KhinchinFamily`, `KhinchinRefineFamily`, `CFLogTail`) —
all axiom-clean. This is genuine forward motion, NOT a false summit: whole lemmas
close lap-over-lap (Lebesgue bridge → three-zone combine → refinement-family), the
crux keeps SHRINKING (whole log-average → one tail-mass bound → schedule wiring),
and this run's real design bug (level-tied cutoff `K_t→∞` can't transfer to a fixed
external `K`) was found AND fixed same-run via the fixed-cutoff summable family.
ROUTE VERDICT: **CONTINUE** — neither charter trigger fired (route uses
Markov+γ-mixing, explicitly Birkhoff-free; γ-mixing rate is proven geometric).

**KEEP doing**: the route C′ family graft; treating Tier 1 as banked/untouchable.

**STOP doing**: building MORE upstream Khinchin lemmas. That layer is COMPLETE
(handoff items 6–8 confirm `exists_good_avoiding_bad…_family` +
`exists_refinement_uniform_khinchin_family` are proved axiom-clean). Every further
lap that adds standalone machinery instead of WIRING is drift. The value is now
100% in the plumbing.

**HIGHEST-VALUE NEXT TARGET**: rewire `CFSchedule.lean` to the family refinement
(`tK := level`), then assemble `xstar_log_tail_uniform` from the schedule's family
payload. Reasoning: this is the route-DECISIVE test. The one genuinely uncertain
step is whether the per-stage family guarantee (each good block avoids all `j<t`
log zones) transfers to a **mid-stage prefix** of `xstar` — the exact analogue of
the CF/d-ary per-block→prefix-frequency transfer ALREADY solved via
`sched_dominance` + the `goodC`-telescope, so precedented and tractable, but the
last untested link. If it goes through, Tier 2 closes; if it walls, that wall is
the real obstacle to surface (and Tier 1 remains a complete standalone deliverable).
The crux's `∀K≥K₀` is handled by monotonicity of the nonnegative tail in `K`, so
controlling it at the single fixed cutoff `khinchinK j(ε)` suffices. Weaken
`xstar_log_tail_uniform` to `∃N,∀n≥N` — its only consumer works via
`Metric.tendsto_atTop`.

---

> **GRIND (2026-08-24 — value-count bridge PROVED; crux is now a pure
> tail-mass bound).** Landed three axiom-clean lemmas in `Khinchin.lean`:
> - `countOccurrences_singleton`: `countOccurrences [a] l = l.count a`.
> - `logTail_list_eq` (general list, by induction): for positive-digit `w`,
>   `(Σ_{x∈w} log x) − Σ_{a≤K} (w.count a)·log a = Σ_{x∈w} (if K<x then log x else 0)`.
> - `xstar_logTail_eq`: the difference INSIDE `xstar_log_tail_uniform` equals the
>   nonnegative empirical tail `Σ_{i<n} (if K < cfDigit xstar i then log(cfDigit
>   xstar i) else 0)`.
> **Consequence**: `xstar_log_tail_uniform` now reduces (via `xstar_logTail_eq`)
> to a pure **upper bound on the nonnegative empirical tail**: `∀ε>0 ∃K₀ ∀K≥K₀
> ∀n, (1/n)·Σ_{i<n, cfDigit xstar i>K} log(cfDigit xstar i) ≤ ε`. All the
> value-count/bookkeeping is discharged; what remains is exactly the schedule
> guarantee that each good block's large-digit log-mass is `≤ η·(block length)`,
> delivered by the Markov `logBadZone`. NEXT is unchanged (A′ first-moment
> integral → B′ bad zone → C′ union plumbing → D′ layering); the bridge means
> C′ can target the clean tail-mass form directly.

> **GRIND (2026-08-24 — route SIMPLIFIED to Markov; plumbing scoped).** Two
> route improvements that make `xstar_log_tail_uniform` markedly more tractable
> than the "variance/Chebyshev" framing:
>
> 1. **Markov, NOT Chebyshev — first moment suffices.** The tail
>    `Σ_{i<n, aᵢ>K} log aᵢ` is NONNEGATIVE and we only need an UPPER bound on it
>    (the `limsup ≤ log K₀` direction; `liminf ≥` is free from frequencies). So
>    the bad zone `logBadZone K n η := {x : Σ_{i<n, digit>K} log(digit) > η·n}`
>    (relative to the brick cylinder) is controlled by **Markov's inequality**:
>    `γ(logBadZone) ≤ (1/(η·n))·∫ tail dγ = (1/η)·Σ_{a>K} γ([a])·log a`, using
>    T-invariance + `integral_blockCount` (∫ blockCount(cfCylinder[a],n) dγ =
>    n·γ([a])) — **FIRST MOMENT ONLY**. No `Var(Σ log aᵢ)` bound, no covariance
>    double-sum, no L²-observable γ-mixing extension needed. `summable_gaussKuzmin_logsq`
>    (2nd moment) is therefore NOT on the critical path (still a correct lemma).
>    The `K`-selection input `Σ_{a>K} γ([a])·log a → 0` is now proved:
>    `gaussKuzmin_logtail_tendsto` (`Khinchin.lean`, axiom-clean).
> 2. **The general union lemma needs NO change.** `exists_mem_notMem_union_of_bounds`
>    (`TBrick.lean:244`) already takes TWO zones B₁,B₂ with `p+q<1/2`. Add the
>    Khinchin zone B₃ by **unioning it into B₂** (the d-ary group):
>    `vol(B₂∪B₃) ≤ ofReal(q+r)·vol0` by subadditivity, needing `p+q+r<1/2`. So
>    the only edits are: `exists_good_avoiding_bad` (union B₃ in, tighten the two
>    `<1/4` coeff thresholds so the three sum `<1/2` — e.g. `<1/6` each, larger
>    N/kmin), its `_of_large` corollary, `exists_refinement_uniform`, and the
>    schedule/`xstar` rederivation carrying the extra guarantee. All ADDITIVE
>    (new hypotheses + new conclusion conjunct); Tier-1 decls untouched.
>
> **CONCRETE NEXT (in order):**
> - (A′) First-moment integral: `∫ x, (Σ_{i<n} if cfDigit x i > K then
>   log(cfDigit x i) else 0) dγ = n·Σ_{a>K} γ([a])·log a`. Express the tail
>   observable via `blockCount (cfCylinder [a])` summed over `a>K` with `log a`
>   weights; interchange ∫ with the (Tonelli, nonneg) sum; apply
>   `integral_blockCount` per `a`. NEW file (`CFLogTail.lean`), no TBrick edit.
> - (B′) `logBadZone` def + Markov measure bound `≤ (1/η)Σ_{a>K}γ([a])log a`
>   (via `MeasureTheory.mul_meas_ge_le_integral`-style Markov on the nonneg tail).
> - (C′) Union B₃ into `exists_good_avoiding_bad`; tighten coeffs; thread through
>   `exists_refinement_uniform` + schedule; discharge `xstar_log_tail_uniform`.
> - (D′) Layering refactor: move frozen `KhinchinTypical`/`khinchinK₀` defs to an
>   upstream module so `Headline.lean:134` can close with `xstar_khinchinTypical`.

> **GRIND (2026-08-24, same lap follow-on — REDUCTION (C) COMPLETE, crux
> isolated to ONE schedule lemma).** The entire Tier-2 headline now provably
> rests on a single, precisely-stated lemma. Landed (all in `Khinchin.lean`):
> - `gaussKuzmin_logsum_hasSum` / `gaussKuzmin_logsum_tendsto` (axiom-clean):
>   the assembly's **target limit value** `Σ_a γ([a])·log a = log K₀` (HasSum +
>   `Icc 1 K` partial sums `→ log K₀`). Key identity: `γ([a])·log a` = the term
>   of `khinchinK₀`'s series (logb/log factors swap), reused verbatim.
> - `xstar_log_digit_avg_tendsto` — **PROVED** via a clean `3ε` interchange over
>   `xstar_log_digit_avg_truncated_tendsto` (fixed-K, proved) +
>   `gaussKuzmin_logsum_tendsto` (K→∞, proved) + the tail lemma. The value-count
>   identity is ABSORBED into the tail lemma (stated with `abs`, so no separate
>   nonneg/identity lemma needed).
> - `xstar_khinchinTypical : KhinchinTypical xstar` — **PROVED** via
>   `khinchinTypical_iff_log_tendsto` (digit positivity from `one_le_cfDigit`).
> `#print axioms` of both: `[propext, sorryAx, Classical.choice, Quot.sound]` —
> the ONLY non-trust-triple dependency is `sorryAx`, sourced entirely from:
>
> **THE SOLE REMAINING TIER-2 CRUX** — `xstar_log_tail_uniform` (disclosed
> `sorry`, `Khinchin.lean`): `∀ε>0 ∃K₀ ∀K≥K₀ ∀n, |(1/n)Σ_{i<n}log aᵢ −
> (1/n)Σ_{a≤K}count[a]·log a| ≤ ε`. This is the uniform log-tail control the
> schedule must deliver — exactly what the W6 log-concentration bad zone
> provides (variance bound via γ-mixing, moment input `summable_gaussKuzmin_logsq`).
>
> **NEXT**: the construction work, steps (A)+(B) from the review entry below —
> (A) `Var(Σ_{i<n} log aᵢ) ≤ C·n` under γ-mixing (adapt `CFBlockFreq`'s
> covariance machinery to the L² observable `log a₁`); (B) `logBadZone` +
> Chebyshev measure bound + additive union-bound wrapper; then instantiate at
> `xstar`'s schedule to discharge `xstar_log_tail_uniform`. Also a mechanical
> layering refactor is needed to close `Headline.lean:134` itself: the frozen
> `KhinchinTypical`/`khinchinK₀` defs live in `Headline.lean` (which `Khinchin.lean`
> imports), so the headline `sorry` can only be closed after moving those defs
> to an upstream module (verbatim — preserves the frozen statement) so the
> assembly + `xstar_khinchinTypical` become upstream of the headline.

> **REVIEW LAP (2026-08-24 — route DECISION + moment seed proved).** The last
> three laps (fc801ba/17dc2c9/7d6740f, all pure route-analysis) converged on
> "step-2 crux is operator-gated, need Trevor to authorize a schedule touch —
> stop." That is a **false stop**: this is an autonomous run, there is no
> operator, and the review lap owns exactly this call. DECISION (now binding in
> `DIRECTION.md`):
>
> 1. **The route is settled** — the diagnosis of the last laps is CORRECT and
>    ratified: frequencies + the `goodC` total-mass bound provably cannot give
>    the uniform tail control (`limsup(1/n)Σ_{aᵢ>K} log aᵢ ≤ goodC−log K₀ > 0`;
>    plus the frequencies-only counterexample). The ergodic route is a forbidden
>    import. So the ONLY route is the original `KHINCHIN.md` W6 log-concentration
>    bad zone. The `44fb8bb`/`e018429` "goodC suffices, no re-plumb" insight is
>    formally **REFUTED** (docstring in `Khinchin.lean` step-2 block records it).
> 2. **The schedule fence is RELAXED** — additive extension of `TBrick.lean`/
>    `TBrickRefine.lean`/`CFSchedule.lean` for the W6 graft is authorized. The old
>    blanket "don't touch the schedule" was over-broad; its real purpose is
>    protecting locked Tier-1, which an additive lemma cannot threaten (the JUDGE
>    froze witness-existence form precisely to permit a W6 rebuild). Hard
>    invariant: never edit/weaken an existing Tier-1 decl or frozen statement;
>    after any schedule edit re-run `#print axioms exists_absolutely_normal_cf_normal`
>    and confirm it stays the trust triple.
> 3. **Proof landed this lap**: `summable_gaussKuzmin_logsq` (`Khinchin.lean`,
>    axiom-clean) — the moment condition `E[(log a₁)²] = Σₐ γ([a])·(log a)² < ∞`
>    that the Chebyshev/variance bad-zone bound needs. Comparison with
>    `1/(k+1)^{3/2}` via `log(1+x)≤x` and `(log(k+1))²≤16√(k+1)`.
>
> **NEXT ATTACK (in order; start analytic, defer the invasive plumbing):**
> - (A) **Variance bound** `Var(Σ_{i<n} log aᵢ) ≤ C·n` under γ-mixing — adapt
>   `CFBlockFreq.lean`'s `variance_blockCount_le`/covariance machinery from a
>   cylinder-indicator observable to the unbounded L² observable `log a₁`. This
>   is the real new estimate; `summable_gaussKuzmin_logsq` is its moment input.
>   The γ-mixing covariance bound must be checked to hold for L² (not just
>   bounded) observables — likely the one genuine subtlety. NEW file
>   (`CFLogMoment.lean` or similar), no TBrick edit.
> - (B) **`logBadZone` + Chebyshev measure bound** `≤ C/(η²n)`; then the additive
>   union-bound wrapper (`exists_good_avoiding_bad_khinchin`), re-balancing the
>   coefficient budget in `exists_mem_notMem_union_of_bounds` from 2 zones to 3
>   (each `<1/6`, or keep `<1/4`+`<1/4` and add the log zone with the surplus of
>   a stronger half-mass — check the exact threshold the general lemma needs).
> - (C) **Elementary reduction (parallelizable, `Khinchin.lean`)**: reduce
>   `xstar_log_digit_avg_tendsto` to a single clean tail-control lemma
>   `xstar_log_tail_uniform : ∀ε>0, ∃K, ∀n, (1/n)Σ_{aᵢ>K} log aᵢ ≤ ε` via the 3ε
>   argument over `xstar_log_digit_avg_truncated_tendsto` (done) + the
>   value-count identity `Σ_{i<n} log aᵢ = Σ_a count[a]·log a`. This isolates
>   the schedule-dependent piece (the tail-control, delivered by A+B) from the
>   elementary analysis (wireable now).

> **ANALYSIS LAP (2026-08-24, part 2, no code — construction survey).**
> Traced the previous entry's option (1) (dig into `kminFn_spec`) down to
> the actual selection mechanism: `TBrick.exists_refinement_uniform`
> (`TBrickRefine.lean:432`) builds the extension word `u` by picking a
> point `x` that simultaneously **avoids a union of finitely many small-
> measure "bad zones"** — `exists_good_avoiding_bad_of_large` unions one
> `cfBadZone B.w v n δ` per `v ∈ F` (the frequency-deviation zones) plus
> the d-ary `daryBadZoneWide` zones, then a measure/counting argument
> (`goodExtSet`, the Markov good-length machinery) shows a point avoiding
> ALL of them exists. **The per-`v` error bound is a DIRECT consequence of
> which bad zones got unioned in** — `F = wordFamily t` only, so there is
> no log-weighted zone to inherit; option (1) as "just read harder" is a
> dead end confirmed — the existing construction genuinely does not carry
> the needed fact implicitly.
>
> **Concrete, additive next step (supersedes both prior options)**: this
> union-bound architecture is EXTENSIBLE without touching any frozen Tier-1
> statement — add ONE more bad zone to the union, a `logBadZone B.w n η`
> analogous to `cfBadZone`, defined so avoiding it bounds `|Σ_{i<n}
> log(digit_i) - n·log khinchinK₀| < η·n` (a large-deviation / concentration
> statement for the log-digit sum under `gaussMeasure`, needing an
> exponential-moment / Chernoff-type bound — `Σ_a γ([a])·a^θ < ∞` for small
> `θ` would give it via Markov's inequality on `exp(θ·Σlog a_i)`). Package
> this as a NEW theorem `TBrick.exists_refinement_uniform_khinchin` (or a
> `khinchinBadZone` variant of the existing union-bound lemma) that returns
> everything `exists_refinement_uniform` does PLUS this log-average
> guarantee — purely additive, doesn't reshape `IsAbsolutelyNormal`,
> `IsCFNormal`, `khinchinK₀`, or any Tier-1 theorem statement, so it does
> NOT violate `DIRECTION.md`'s "forbidden drift" (that clause bars
> RE-ATTACKING/reshaping Tier 1, not building a new corollary on top of its
> existing machinery). This is a genuine new measure-theory lemma (the
> concentration bound), not mechanical assembly — realistically the size of
> a fresh work package (comparable to W1-W6 in `KHINCHIN.md`), likely
> multiple laps just for the concentration estimate before even touching
> the union-bound plumbing. Record as the leading candidate; if the
> concentration estimate itself proves intractable, THAT is the point to
> escalate to an altitude/review lap for a route call, not before.

> **ANALYSIS LAP (2026-08-24, no code — route-refutation only).** Chased
> route (a) from the previous entry (escaping-mass argument from
> `uSched_spec`'s existing frequency bound) to a concrete numeric
> conclusion: **it does NOT work**, and the failure is quantitatively
> precise, not just a vague gap. Worked out by hand (not yet formalized):
> `uSched_spec`'s per-digit-value error bound is `|count[a] - γ([a])·n_s| <
> schedEps(t_{s+1})·n_s + 1` for every `a ≤ t_{s+1}`, i.e. `schedEps(t)·n +
> 1` with `schedEps(t) = 1/(t+1)`, **uniform in `a`** (not shrinking as `a`
> grows toward `t`). Summing the log-weighted error over `a = 1..t`:
> `Σ_{a≤t} |err_a|·log a ≤ (schedEps(t)·n + 1)·Σ_{a≤t} log a ≈ (n/t)·(t log
> t) = n·log t` (Stirling, `log(t!) ~ t log t`). As a FRACTION of the block
> length `n`, this error is `~ log t_{s+1} → ∞` as `s → ∞` (since
> `t_{s+1} → ∞` is required for Tier 1's own base-coverage) — the error
> does NOT vanish relative to `n`, for ANY choice of cutoff (fixed or
> growing with `s`). This kills the naive combination outright, not just
> weakly.
>
> **Also checked**: `goodC` (the `wSched_log_sum_le` total-mass cap) is an
> unrelated Markov constant from `half_mass_long_extensions`
> (`exists_C_half_le_volume_goodExtSet.choose`, `CFSchedule.lean:108`) —
> it has NO known relation to `khinchinK₀`/`log khinchinK₀` (not proven
> `= log khinchinK₀`, almost certainly strictly larger with real slack), so
> `Σ log(digit) ≤ goodC·n` cannot by itself pin the limit to exactly
> `log khinchinK₀` even before worrying about tails.
>
> **Conclusion — route-decisive**: the Tier-1 schedule's EXPOSED interface
> (`uSched_spec`/`nFn_spec`'s packaged frequency + total-mass facts) does
> not carry enough quantitative information for the Khinchin log-average
> limit; the per-word error bound was built for FIXED-length pattern
> frequency (Tier 1's `IsCFNormal`, no log-weighting) and is provably too
> weak once digit magnitude enters as a weight. Two live options for the
> NEXT lap, in order of preference:
> (1) **Dig into `kminFn_spec` / the underlying Lemma-13 refinement
>     construction** (`TBrickRefine.lean`) for a genuinely finer,
>     log-weighted quantitative estimate — e.g. does the actual
>     construction (not just its packaged `nFn_spec` corollary) support a
>     bound like `Σ_{a≤t} err_a·log a = o(n)` via cancellation the crude
>     triangle-inequality packaging discards? This is READING/extending
>     Tier-1 internals for a NEW corollary, not modifying the frozen
>     schedule or its statements — allowed under `DIRECTION.md`'s "forbidden
>     drift" clause (which bars re-attacking/reshaping Tier 1, not reading
>     it for a new Tier-2 fact). Needs real investment (Lemma-13's actual
>     proof, likely `TBrickRefine.lean`'s badBlocks/daryCell combinatorics)
>     — budget a full lap just to understand what's provable there before
>     attempting a new lemma.
> (2) If (1) turns up nothing usable: the honest conclusion is Tier 2
>     genuinely needs a schedule re-plumb (the ORIGINAL W6 assessment this
>     campaign's `44fb8bb` route-insight had set aside) — but that is a
>     `DIRECTION.md`-level call (touches locked Tier-1 machinery), not a
>     grind-lap decision; flag for an altitude/review lap rather than
>     unilaterally reopening the schedule.
> Do NOT retry route (a) as stated (fixed-or-growing cutoff `K` against the
> existing frequency bound) — it is refuted above with an explicit
> divergent-error computation, not merely "not yet tried."

> **GRIND LAP (2026-08-24, `76e042e`).** Continued the step-2 assembly
> (log-average crux). Two sub-lemmas landed, both axiom-clean, no `sorry`:
> `xstar_log_digit_avg_truncated_tendsto` (`Khinchin.lean`) — the `≤ K`
> finite-truncation slice of the empirical log-digit average converges to
> the matching finite Gauss–Kuzmin sum (direct from `xstar_cf_freq_tendsto`
> + `tendsto_finsetSum`); `getElem_le_cfK` (`CFCylinder.lean`) — every digit
> in a genuine word is `≤` the word's continuant.
>
> **Route-scoping insight this lap (important, changes the difficulty
> picture)**: chased whether `wSched_log_sum_le`'s total-mass bound
> (`Σ log(digit) ≤ goodC·n`) alone suffices for the K→∞ tail-vanishing that
> `xstar_log_digit_avg_tendsto` needs. It does **not**, obviously — a bounded
> total doesn't imply the mass concentrated on large digits shrinks as `K`
> grows; that needs a genuine per-magnitude decomposition. Checked whether
> `getElem_le_cfK` + `uSched_spec`'s `cfK(uSched s) ≤ exp(goodC·n_s)` gives
> that decomposition: it gives a per-block digit CAP `exp(goodC·n_s)`, but
> that cap is far LOOSER than the block's frequency-control threshold
> `t_{s+1}` (recall `t² < nFn t = n_s`, i.e. `t_{s+1} < √(n_s)`, while the
> continuant cap is exponential in `n_s`) — so `uSched_spec`'s per-word
> frequency bound (4th clause, only proven `∀ v ∈ wordFamily t_{s+1}`, i.e.
> digits `≤ t_{s+1}`) does NOT cover digits between `t_{s+1}` and
> `exp(goodC·n_s)`, which is exactly where "escaping mass" could hide.
> **This is the precise open question**, sharper than the handoff's vague
> "Markov/Chebyshev" framing: either (a) find a genuine escaping-mass bound
> — e.g. show the CONTRIBUTION of digits `> t_{s+1}` to the block's log-sum
> is itself `o(n_s)` (not just capped by the loose exponential bound), using
> `uSched_spec`'s frequency-control on the complementary low digits to
> squeeze the high-digit contribution via the SAME total (`wSched_log_sum_le`
> minus the low-digit part, itself estimated via the frequency bound) — this
> looks tractable and is the next thing to try; or (b) conclude the current
> schedule construction genuinely lacks the control needed and a tighter
> digit-cap re-plumb (the ORIGINAL W6 assessment, which this campaign's
> `44fb8bb`/`e018429` route insight had set aside) is unavoidable after all.
> Try (a) first — do NOT re-open the schedule construction (route (b))
> without exhausting (a); the frequency-bound-on-the-complement trick is a
> standard measure-theory move (bound the tail of a nonneg sum by
> total-minus-known-part) and hasn't been attempted yet.

> **GRIND LAP (2026-08-24, `42ec6a7`).** ✅ **Gauss-Kuzmin single-digit law
> PROVED** (step 1 of HANDOFF-2026-08-26-0730.md's Tier-2 NEXT list):
> `gaussMeasure_digit_cylinder` (`CFCylinder.lean`) — closed form
> `γ(cfCylinder [a]) = logb 2 (1 + 1/(a(a+2)))` for `a ≥ 1`, matching
> `khinchinK₀`'s tprod term exactly (`a(a+2)+1 = (a+1)²`), axiom-clean.
> Route: `gaussMeasure_cfCylinder` mirrors `volume_cfCylinder`'s
> `uIcc`/`uIoo` squeeze verbatim but for `gaussMeasure` — endpoints and the
> rational range are `gaussMeasure`-null via
> `MeasureTheory.withDensity_absolutelyContinuous` (`gaussMeasure ≪ volume`,
> so every Lebesgue-null set is `gaussMeasure`-null; no need for the
> one-directional `gaussMeasure_le_volume`/`volume_le_gaussMeasure` bounds
> the original plan cited). **Refactor gotcha**: `gaussMeasure_Ioo` had to
> move from `CFDigitLaw.lean` to `CFDefs.lean` (right after `gaussMeasure`'s
> def) — it's pure real analysis on the definition with no `cfCylinder`
> dependency, but `CFCylinder.lean` needed it and `CFDigitLaw.lean` imports
> `CFCylinder.lean` (not the reverse), so leaving it in place would have been
> circular. **Lean gotcha**: multi-line `calc` first-step terms
> (`calc ENNReal.ofReal\n  (long arg)\n  = ... := ...`) mis-parse in this pin
> — the continuation line reads as a new command, producing bogus "expected
> ℝ got ENNReal" / "left-hand side is true : Bool" errors far from the real
> bug. Fix: `set T := <the long RHS term>` once, then write the whole `calc`
> in terms of the short name `T` (no multi-line calc heads at all).
>
> **NEXT (step 2, the genuine remaining crux)**: assemble
> `xstar_cf_freq_tendsto [a]` (single-digit frequency, already proved,
> `CFCorrect.lean`) with `gaussMeasure_digit_cylinder`'s closed form and
> `wSched_log_sum_le`'s uniform tail bound (`CFCorrect.lean`, from the
> `goodC` schedule payload) into
> `Tendsto (fun n => (1/n)·Σ_{i<n} log(cfDigit xstar i)) atTop (nhds (log
> khinchinK₀))`. This is a dominated-convergence-style interchange: for each
> `ε`, truncate at digit `K` (using `Σ_a p_a·log a` convergence, i.e.
> `khinchinK₀_summable_log` in `Khinchin.lean`, to bound the tail
> `Σ_{a>K} p_a·log a`), get finite-truncation convergence of the empirical
> log-average from `xstar_cf_freq_tendsto` on each `a ≤ K`, and bound the
> empirical tail `(1/n)Σ_{i<n, cfDigit xstar i > K} log(cfDigit xstar i)`
> using `wSched_log_sum_le`'s `≤ goodC·n` mass bound plus a Chebyshev-style
> "few large digits" argument (or a cruder direct bound if the `goodC`
> bound alone suffices — check whether `uSched_log_sum_le`'s per-stage
> bound already gives what's needed without further partitioning). Likely
> the hardest remaining step; budget 2-3+ laps. Then
> `khinchinTypical_iff_log_tendsto` (`Khinchin.lean`, already proved)
> converts this limit to `KhinchinTypical xstar`, closing
> `exists_absolutely_normal_cf_normal_khinchin` (`Headline.lean:136`, the
> ONLY remaining `sorry` in `src/`).

> **GRIND LAP (2026-08-26, `44fb8bb`).** ✅ **TIER 1 LOCKED** —
> `exists_absolutely_normal_cf_normal` proved, axiom-clean (`b3bc2c4`; see
> HANDOFF-2026-08-26-0630.md for the full route). ✅ **Khinchin (Tier 2) seed
> landed**: `prod_le_cfK` (`CFDigitLaw.lean`, the missing continuant lower
> bound `∏aᵢ ≤ K(a₁…aₙ)`) + `uSched_log_sum_le` (`CFCorrect.lean`): each
> appended schedule block's total `log`-digit mass is `≤ goodC·(block
> length)`. **Route insight this lap**: KHINCHIN.md's W6 assessment expected
> a digit-cap re-plumb of the schedule for uniform-integrability control —
> but the existing `cfK(uSched s) ≤ exp(goodC·n)` payload (already proved for
> Tier 1) directly bounds the average `log`-digit per stage via
> `prod_le_cfK`, with **no construction change needed**. This significantly
> de-risks Tier 2: `xstar`'s *existing* schedule may already be
> Khinchin-typical.
>
> **NEXT (Tier 2, `Headline.lean:134`, `exists_absolutely_normal_cf_normal_khinchin`)**:
> assemble `uSched_log_sum_le` into the actual geometric-mean limit
> `KhinchinTypical xstar`:
> 1. Sum `uSched_log_sum_le` over stages `0..s-1` to bound `(wSched
>    s).map log |>.sum` (telescoping `nFn`/length identities already exist,
>    cf. `wSched_length_succ`) — gives an UPPER bound on the log-digit sum at
>    stage boundaries, matching the schedule's word length.
> 2. Need the MATCHING lower/limit bound: use `xstar_cf_freq_tendsto`
>    (already proved) to get, for every digit value `k` (or every `v = [k]`
>    cylinder), the frequency of digit `k` in the length-`p` prefix `→
>    γ(cfCylinder [k])` = the Gauss–Kuzmin law. The target sum `Σ log(cfDigit
>    xstar i)` should then match `p · Σ_k γ([k])·log k = p · log K₀` in the
>    limit, PROVIDED a uniform-integrability interchange (dominated/bounded
>    convergence style, using the `goodC` bound to truncate the tail) can be
>    justified — this interchange (finite-pattern convergence + bounded tail
>    ⇒ full log-average convergence) is now THE remaining crux, not a
>    digit-cap graft. Likely needs: (a) a truncation argument bounding
>    `Σ_{k>K} γ([k])·log k` uniformly small (from `Σ log k / k²  < ∞`,
>    `CFDigitLaw.lean`'s existing summability work may be reusable), (b) an
>    ε/δ argument combining finite-truncation convergence (from CF-normality)
>    with the tail bound (from `uSched_log_sum_le`/`goodC`).
> 3. Convert the log-average limit to `KhinchinTypical`'s geometric-mean form
>    (`(∏...)^(1/n) → K₀` ⟺ `(1/n)Σlog → log K₀`, via `Real.exp`/`Real.log`
>    continuity — should be short once the log-average limit is in hand).
> Prior Tier-1 material (Pillai, d-ary chain, CF normality, measure balance,
> schedule/Lemma-13) is CLOSED — do not reopen; see DIRECTION.md.

> **GRIND LAP (2026-08-26, `e7705ee`).** ✅ **PILLAI'S THEOREM PROVED** —
> `Pillai.lean` is now **sorry-free**. Chain landed this lap (all axiom-clean):
> `windowCount_eq_sum_phaseCount` → `phaseOccCount_{tendsto_atTop,div_tendsto}` →
> `phaseWindowFreq_div_N_tendsto` → `sum_{nonStrad,strad}_..._tendsto` →
> `windowCount_div_sandwich` → **`windowFreq_tendsto`** (THE double-limit crux,
> block freq → b^{-L} via ε-in-r squeeze) → **`pillai`** (`∀ r≥1 simple normal at
> b^r ⇒ IsNormalSequence b (digitOf b y)`; bridge via `countOccurrences_range_map`
> + `MatchesAt ↔ ofFn-window`). See HANDOFF-2026-08-26-0600.md for the full route
> + gotchas.
>
> **NEXT = Tier-1 headline conjunction** (`Headline.lean:93`, ONLY classical
> wiring): `∃ x, IsAbsolutelyNormal x ∧ IsCFNormal x`, witness `xstar`.
> (1) `IsAbsolutelyNormal xstar` = `∀ b≥2, IsNormal b xstar` = pillai (y :=
> Int.fract xstar) fed by `xstar_dary_freq_tendsto (b^r)`; FIRST check the exact
> form of `xstar_dary_freq_tendsto` vs pillai's `hsn`, and `digitOf d xstar =
> digitOf d (Int.fract xstar)`. (2) `IsCFNormal xstar` = wrapper of
> `xstar_cf_freq_tendsto` (JUDGE: not new math). (3) `refine ⟨xstar, ?_, ?_⟩`.
> Tier 2 (`:100`, Khinchin/W6) stays `sorry` — fenced.

> **REVIEW LAP (2026-08-24).** ✅ **`windowCount_eq_sum_phaseCount` PROVED**
> (axiom-clean) — the `Q`-scale↔`N`-scale phase-count identity, closing last
> lap's disclosed `sorry`. Winning move on the `r*(i/r)` vs `(i/r)*r` omega-atom
> trap: `Finset.card_nbij' (fun i => i/r) (fun q => r*q+s)`, anchoring EVERY
> decomposition on `Nat.div_add_mod i r` (canonical `r*(i/r)`); the ONLY place a
> `(i/r)*r` appears is right after `Nat.le_div_iff_mul_le`, where a single
> `rw [Nat.mul_comm]` normalizes it back BEFORE `omega`. Mod dir:
> `Nat.add_comm (r*q) s` → `Nat.add_mul_mod_self_left` + `Nat.mod_eq_of_lt hsr`.
> Div dir: `Nat.mul_add_div hrpos` + `Nat.div_eq_of_lt hsr`. (omega never has to
> reconcile the two factor orders — the rewrite does it first.)
>
> **NEXT (the new crux — the double-limit assembly)**: Pillai's phase→block
> frequency limit. `freq_w(N) = windowCount/N`. Route:
> (a) `windowCount_eq_sum_phaseCount / N = Σ_{s<r} phaseCount_s(N)/N`;
> (b) non-straddling `s ≤ r−L`: `phaseCount_s(N)/N =
>     (phaseCount_s/phaseOccCount_s)·(phaseOccCount_s/N)`; factor 1 → `b^{-L}` by
>     `phaseWindowFreq_tendsto` (a `Q→∞` limit — needs `phaseOccCount r L s N →∞`
>     as `N→∞`, then `Filter.Tendsto.comp`); factor 2 `phaseOccCount r L s N / N
>     → 1/r` (since `phaseOccCount ≈ (N−s−L)/r`);
> (c) straddling `s` (`r < s+L`, `L−1` of them by `card_straddling_phases`):
>     bound each `phaseCount_s(N)/N ≤ phaseOccCount/N → 1/r`, total ≤ `(L−1)/r`;
> (d) sum finite phases; then `r→∞` (ε-manage via `Metric.tendsto_atTop`: pick
>     `r` with `(L−1)/r < ε/2` and `|((r−L+1)/r − 1)·b^{-L}| < ε/2`, then `N`
>     large). Simpler than `xstar_dary_freq_tendsto`'s metric proof — no schedule.
>     Decompose into named sub-`sorry`s in `Pillai.lean` if not one lap.

> **LATEST LAP (2026-08-25/26, `674ff52`).** Pillai's theorem build-out,
> continuing from the digit-power foundation (`b537edd`). New in
> `Pillai.lean`, all axiom-clean:
> - `digitOf_pow_digitAt`: atomic single-digit phase correspondence.
> - `blockNatVal_slice`: pure list/nat lemma generalizing `blockNatVal_digit`
>   (L=1) to an arbitrary L-digit sub-block slice.
> - `digitOf_pow_slice_eq_blockNatVal`: the non-straddling window/slice
>   correspondence — a length-L window of y's base-b digits at phase s
>   equals w iff c_q's (=digitOf(b^r) y q) shifted+masked value equals
>   blockNatVal b w. This is the combinatorial core connecting simple
>   normality at b^r to block frequency at base b.
> - `card_matchingValues`: among c<b^r, exactly b^(r-L) have a fixed L-digit
>   slice value — proved via explicit bijection c ↔ (c/D/b^L, c%D).
> **Next**: combine `digitOf_pow_slice_eq_blockNatVal` + `card_matchingValues`
> into the phase-s window-frequency limit (via `tendsto_finsetSum` over the
> `b^(r-L)`-element matching set, using simple normality at base b^r), then
> the straddling-density bound (O(L/r)→0) and the double limit (r→∞ then
> N→∞) assembling the full Pillai theorem. See docstring route in
> `Pillai.lean`. GOTCHA: `List.getElem_ofFn` + `congr 1` on Fin-coerced
> indices needs an explicit `simp only [Fin.val_mk]` before `congr 1` —
> omitting it (even though the linter flags it "unused" in some
> elaborations) causes a nondeterministic omega failure on rebuild; keep it
> despite the lint warning. Also: `Nat.add_mul_div_right`/
> `Nat.add_mul_mod_self_right` need the term in `x + y*z` form with the
> VARIABLE first and the fixed multiplier as the LAST factor before the
> modulus/divisor — commute explicitly before rw, don't rely on `_left`
> variants when the target's factor order doesn't match.

> **CURRENT STATE (2026-08-25 grind lap, `e832d1d`).** Everything below the
> "── ARCHIVE ──" divider is the W3/W4/W5-input history, kept for the proven-lemma
> record but SUPERSEDED. Live state:
>
> - ✅ W1–W4 done. ✅ **W5 core done**: B–Y Lemma 13 (`TBrick.exists_refinement`),
>   THE SCHEDULE (`CFSchedule`), limit point `xstar` (irrational, in every
>   scheduled cylinder), **CF normality of `xstar`** (`xstar_cf_freq_tendsto`).
>   All axiom-clean.
> - ✅ **(c) THE d-ary `m`-growth CRUX IS CLOSED** (`9d8f265`): the interior
>   ratio `k_{s+1}/(m_d(s)−m_d(s₀)) → 0` is proved
>   (`tendsto_gain_div_mSched_sub`). This was the only genuinely-new-math
>   obligation for Tier 1.
> - ✅ **(d) THE d-ary CHAIN IS CLOSED** (`e832d1d`): `xstar_dary_freq_tendsto`
>   is proved axiom-clean — for every base `d ≥ 2` and digit `c < d`, the
>   frequency of `c` among the first `p` base-`d` digits of `xstar` tends to
>   `1/d`. This is **simple normality of `xstar` in every base simultaneously**,
>   the FIRST machine-checked formalization of the Becher–Yuhjtman d-ary
>   result. Built from: `dBlock`/`dBlock_spec` (per-stage good block via
>   choice), `dTailList` (tail decomposition), `dTailList_hasDiscLt` (chain),
>   `dFixedPrefix_append_dTailList_hasDiscLt` (boundary),
>   `dBlock_short_of_dTailList` + `dTailList_append_take_hasDiscLt` (interior),
>   `exists_mSched_stage` (locator), `count_map_val_eq` (Fin-d → ℕ digit count
>   bridge), assembled via a 3-way `List.range` split matched to the real
>   digit sequence.
> - 🔨 **Frontier = Tier 1 completion** (item 3 below): only classical labor
>   and statement-staging remain — no more genuinely-open math for Tier 1.
>   - **Pillai**: simple-normal-to-all-`b^k` ⇒ normal-to-`b`. NOT in
>     mathlib/repo — check `Sandwich`/`Counting`/`Wall` for reusable
>     window-frequency pieces before formalizing from scratch (classical,
>     self-contained; combines `xstar_dary_freq_tendsto` at every base `d`
>     with a block-frequency argument reducing general blocks to single-digit
>     frequencies at higher bases).
>   - **Headline conjunction**: stage `(∀ b≥2, IsNormal b xstar) ∧
>     CF-normal xstar` for JUDGE — note `Headline.lean` already has
>     witness-existence-form frozen statements
>     (`exists_absolutely_normal_cf_normal` etc.) with two `sorry`s (lines
>     91, 98) waiting for exactly this route to discharge them.
>   - `IsCFNormal`'s wrapper from `xstar_cf_freq_tendsto` and
>     `IsAbsolutelyNormal`'s wrapper from `xstar_dary_freq_tendsto`+Pillai
>     should both be short once Pillai lands.
>
> ## Attack path (hardest-first) — mirrors DIRECTION CURRENT DIRECTIVE
>
> 1. **(c) THE CRUX — the `m`-growth estimate** (interior condition; the only
>    genuinely-new-math left). Need: `k_{s+1}(d) ≤ ε·(m_d(s) − m_d(s₀))`
>    eventually. Route (source-verified): numerator `d^{k} ≤ 32d·cfK(u)²`
>    (good-length upper bound + brick containment); denominator
>    `Σ k_j ≳ (log2/(4 log d))·(L_s − L_{s₀})` via `two_pow_le_cfK`
>    (`cfK ≥ 2^{(n−1)/2}`, proved); ratio ≲ `goodC·n_{s+1}/L_s → 0` by
>    `sched_dominance`. It is the exact analogue of the CF interior condition
>    already closed by the schedule dominance — high confidence it closes.
>    - ✅ **FOUNDATION LANDED** (2026-08-23, `dpow_mSched_bracket`, axiom-clean):
>      per-stage bracket `cfK(wSched s)²/(2d) ≤ d^{mSched s d} ≤ 4·cfK(wSched s)²`,
>      straight from the brick ratio field + `≤2`-cell containment. Dividing the
>      bracket at `s+1` by the bracket at `s` (with `cfK_append_le` /
>      `cfK_mul_le_append`, both in `CFCylinder`) gives the per-stage
>      `cfK(uSched s)²/(8d) ≤ d^{k_{s+1}} ≤ 32d·cfK(uSched s)²`.
>    - ✅ **(c1) LANDED** (2026-08-23, `dpow_gain_bracket` + `uSched_pos`,
>      axiom-clean): per-stage gain, cleared/division-free form —
>      `cfK(uSched s)² ≤ 8d·d^k` and `d^k ≤ 32d·cfK(uSched s)²` where
>      `k = mSched(s+1)d − mSched s d`. Proof = quotient of `dpow_mSched_bracket`
>      at `s+1` over `s`, with `cfK_append_le`/`cfK_mul_le_append` along
>      `wSched_succ`. (Takes `hk : mSched(s+1)d = mSched s d + k` — supplied by
>      `xstar_dary_step`.)
>    - ✅ **(c2) LANDED** (2026-08-23, `log_gain_bracket`, axiom-clean): log of
>      (c1), division-free `k·log d` form —
>      `2 log cfK(u_s) − log(8d) ≤ k·log d ≤ 2 log cfK(u_s) + log(32d)`. Via
>      `Real.log_le_log`/`Real.log_pow`/`Real.log_mul`.
>    - ✅ **(c3a) LANDED** (`gain_le`, axiom-clean): numerator —
>      `k·log d ≤ 2·goodC·nFn(tSched(s+1)) + log(32d)`, via `uSched_spec`'s
>      good-length bound `cfK(uSched s) ≤ exp(goodC·nFn(tSched(s+1)))` + (c2).
>    - ✅ **(c3b) LANDED** (`le_mSched_mul_log`, axiom-clean): denominator
>      building block — `m_d(s)·log d ≥ 2·⌊L_s/2⌋·log2 − log(2d)` where
>      `L_s = |wSched s|`, via the bracket lower half + `two_pow_le_cfK` on
>      `wSched s`. (So `m_d(s) ≳ (log2/log d)·L_s`.)
>    - NEXT: **(c4) close the interior ratio → 0**. Assemble: for fixed `d, ε`,
>      ∃ s₁, ∀ s ≥ s₁, `(mSched(s+1)d − mSched s d) < ε·(mSched s d − mSched s₀ d)`.
>      Numerator ≤ `(2goodC·nFn(tSched(s+1)) + log32d)/log d` (c3a). Denominator
>      ≥ `(2⌊L_s/2⌋log2 − log2d)/log d − mSched s₀ d` (c3b), and `L_s → ∞`
>      (`sched_length_mono`/`wSched_length_ge`). Ratio ≲ `2goodC·n_{s+1}/(log2·L_s)`;
>      `n_{s+1}/L_s → 0` by `sched_dominance` (`t·nFn t ≤ L`) since `t → ∞`
>      (`sched_t_tendsto`). This is the `hshort` feeding `hasDiscLt_append_take`.
>      Then (d) the d-ary chain (mirror `xstar_cf_freq_tendsto`).
> 2. **(d) d-ary chain → `xstar_dary_freq_tendsto`**: TRANSCRIBE the proven
>    `xstar_cf_freq_tendsto` skeleton (chain via `tailSched_*` analogue,
>    boundary `hasDiscLt_short_append`, interior `hasDiscLt_append_take` + (c),
>    `exists_stage` locator, metric limit). Lemma 9 pieces are in `BaryConcat`.
>    Do NOT reinvent the chain — it is a 1:1 port with CFDiscLt→HasDiscLt.
> 3. **Pillai** (`simple normal to all b^k ⇒ normal to b`) + **headline
>    statement**. Pillai NOT in mathlib/repo. Then state + JUDGE-freeze the
>    conjunction `(∀ b≥2, IsNormal b xstar) ∧ CF-normal xstar` and add a
>    Statement/audit surface (currently NONE for Track B).
> 4. **(Tier 2, LATER) W6 Khinchin graft** — digit caps `D_t` in Def 11. Revisits
>    the construction; do only after Tier 1 is stated + axiom-clean.
>
> ## Reflection — 2026-08-23 (deep reflection lap)
>
> - **Direction call: CONTINUE the route; refresh the docs.** No abort/escalate
>   trigger fired. Both of B–Y's deep imports are discharged; the γ-mixing rate
>   is geometric (stronger than the summable trigger threshold); no forbidden
>   import (CLT/KPW/Birkhoff) has been reached. The route is not spinning — the
>   OPPOSITE: whole-lemma targets (Lemma 13, schedule, `xstar`, CF normality)
>   have been CLOSING lap over lap, and finishability has IMPROVED, not declined.
>   The prior reflection's "route-decisive crux" (measure balance) is proved.
> - **The one real defect this lap caught**: DIRECTION/STATUS/PENDING_WORK were
>   all stale — they still named the Lemma-13 assembly the untouched crux, work
>   the grind laps had already blown past. A grind lap literally obeying the old
>   directive would have redone finished work. FIXED: all three refreshed; the
>   binding directive now points at the d-ary `m`-growth estimate.
> - **KEEP**: hardest-first on the d-ary interior estimate; the `Statement.lean`-
>   style faithfulness discipline (10/10 headlines trust-triple, re-verified);
>   the discharge-not-cite ethos (both deep imports gone); mirroring proven
>   skeletons instead of re-deriving (the d-ary chain = the CF chain).
> - **STOP**: treating "abs-normal + CF-normal + Khinchin" as one monolithic
>   goal. Khinchin (W6) is NOT in the source paper — it is a campaign-original
>   graft that must revisit the schedule (digit caps in Def 11) and carries the
>   most feasibility risk of anything left. Fence it behind a LOCKED Tier 1.
>   Also STOP letting the docs lag the git state by a whole review cycle.
> - **Highest-value next target: (c) the `m`-growth estimate.** Reasoning: it is
>   the most uncertain route-decisive blocker for the absolute-normality leg — if
>   it fails, the entire d-ary correctness chain (hence Tier 1's abs-normal half)
>   needs a redesign of the schedule dominance. Everything downstream of it ((d),
>   Pillai) is transcription or classical labor. It is genuinely new math (the
>   log-arithmetic interior estimate), and all its tools (`two_pow_le_cfK`,
>   `sched_dominance`, the good-length upper bound) are already in the repo, so it
>   is both the hardest and the ripest. Expert note: the whole d-ary correctness
>   proof is a transcription of the proven CF proof with THIS as its single new
>   analytic input — spend the lap here, not on re-scaffolding the chain.

── ARCHIVE (pre-2026-08-23-reflection; W3/W4/W5-input history, superseded) ──

# PENDING WORK — B5′ campaign (updated 2026-08-23, post-W3)

**W3 ✅ COMPLETE** (2026-08-23, 8 laps): all four frozen `CFMixing.lean`
statements proved, axiom-clean — `measurePreserving_gaussMap` (B1),
`volume_inter_preimage_eq_integral`, `cylinder_mixing` (C = 8 log 2,
ρ = 9/10, geometric — escape valve unused), `gauss_kuzmin` (B4).
`src/` is sorry-free.  See `HANDOFF-2026-08-23-2040.md`.

**W4 groundwork STARTED (this lap)**: `CFGammaMixing.lean` proves the
KPW-Lemma-6 substitute — the W4 correlation-decay engine — axiom-clean:

- `setIntegral_inter_preimage`: the s-started conditional density
  identity `∫_{I_w ∩ T^{-|w|}B} h_s = (∫_B h_{tChain s w})·(∫_{I_w} h_s)`
  (generalizes aux from `h_0 = 1` to any `h_s`, s ∈ [0,1]).
- `gaussMeasure_cylinder_mixing` (**γ-mixing, geometric rate**):
  `|γ(I_v ∩ T^{-(|v|+g)}A) − γ(I_v)γ(A)| ≤ (9/10)^g·4|A|·γ(I_v)`.
  Route: mixture Fubini γ = ∫₀¹ h_s·Leb dλ(s) + the pin bound, which is
  uniform in the start t — no new analysis was needed.

**W4 frontier — `CFBlockFreq.lean` (lap-authored groundwork).**
`S_n x = blockCount A n x = Σ_{k<n} 1_A(Tᵏx)` (Birkhoff sum). Route DE-RISKED:
γ-mixing is geometric ⇒ covariances summable ⇒ Var(S_n)=O(n).

DONE this lap (all axiom-clean, `#print axioms` = trust triple):
  ✅ `integral_blockCount` — first moment `∫ S_n dγ = n·γ(A)`.
  ✅ `gaussMeasureReal_pair_shift` — `γ(T^{-j}A ∩ T^{-(j+m)}A) = γ(A ∩ T^{-m}A)`.
  ✅ `integral_blockCount_sq` — second moment
     `∫ S_n² dγ = Σ_{j,j'<n} γ(T^{-j}A ∩ T^{-j'}A)`.
  ✅ `abs_cov_le` — **per-pair covariance bound** (the γ-mixing consumer):
     `|γ(I_v∩T^{-m}I_v) − γ(I_v)²| ≤ (9/10)^{m−|v|}·4|I_v|·γ(I_v)` (m≥|v|),
     `≤ 2γ(I_v)` (m<|v|).  ← the route-decisive step; mixing→covariance done.

  ✅ `abs_cov_pair_le` — per-pair bound at gap `|j−j'|`, uniform geometric
     dominator `4γ(I_v)·(9/10)^{|j−j'|∸|v|}` (absorbs the overlap case).
  ✅ `sum_range_dist_le` / `geom_trunc_sum_le` — the Finset gap-count reindex
     (`Σ_{j'} g(dist j j') ≤ 2Σ_d g(d)`) + truncated geometric tail (`≤ L+10`).
  ✅ `variance_blockCount_le` — `Var(S_n) ≤ (8|v|+80)·n·γ(I_v)`.  DONE this lap,
     axiom-clean.  (Constant `8|v|+80` not `4|v|+80`: the clean uniform
     dominator trades a factor 2 for a much shorter proof; harmless — any
     `n`-independent `K(v)` suffices for the construction.)

  ✅ `chebyshev_blockCount` — `γ{|S_n/n − γ(I_v)| ≥ δ} ≤ (8|v|+80)γ(I_v)/(δ²n)`.
     PROVED 2026-08-24 (@2ac0e83), axiom-clean.  Route exactly as planned:
     `MemLp.of_bound` (0 ≤ S_n ≤ n), `variance_eq_sub` + `Pi.pow_apply`,
     set rescale via `abs_div`/`le_div_iff₀`, `meas_ge_le_variance_div_sq`,
     `ENNReal.toReal_mono`/`toReal_ofReal`, final arithmetic by
     `gcongr` + `field_simp`.  **src/ is sorry-free — W4 core COMPLETE.**

  ✅ conditioned-on-brick version — PROVED 2026-08-24 (@c598d81), axiom-clean:
     `gaussMeasure_brick_inter_le` (γ(I_w ∩ T^{-|w|}A) ≤ 7·γ(A)·γ(I_w), via
     g=0 mixing + density window `volume_toReal_le_gaussMeasure`) and
     `chebyshev_blockCount_brick` (bad set inside a brick ≤
     7·(8|v|+80)·γ(I_v)/(δ²n)·γ(I_w)).  Note: much simpler than the planned
     s-started-identity route — the already-proved mixing theorem at gap 0
     absorbs the conditioning.

  ✅ **B–Y Lemma 8 PROVED** 2026-08-24 (@5142f84, `BaryBlockCount.lean`),
     axiom-clean: `card_baryDiscrepancy_ge_le` — #(length-k base-b blocks
     with simple discrepancy ≥ ε) ≤ 2·b^(k+1)·e^{−bε²k/6} for 0 ≤ ε ≤ 1/b.
     Purely combinatorial Chernoff: generating identity
     `sum_exp_digitCount` (Σ_u e^{λ·count} = (e^λ+b−1)^k via
     `Finset.sum_prod_piFinset`), tilt λ = ±bε/2, per-symbol bases from
     `Real.exp_bound` (order 2) + `add_one_le_exp` — both tails give exactly
     −bε²/6 per symbol; no calculus, no measure theory, and B–Y's extra
     hypothesis 6/k ≤ ε is NOT needed.

  ✅ **B–Y Lemma 9 PROVED** 2026-08-24 (`BaryConcat.lean`), axiom-clean:
     `HasDiscLt` (deviation-form simple discrepancy on `List (Fin b)`),
     parts 1/2a/2b as `HasDiscLt.append` / `hasDiscLt_append_take` /
     `hasDiscLt_short_append` (all triangle-inequality counting), plus
     `digitCount_eq_count_ofFn` bridging to Lemma 8's `Fin k → Fin b`
     blocks.  **The W4 b-ary side is now COMPLETE.**

  ✅ **B–Y Lemma 7 PROVED** 2026-08-24 (`CFConcat.lean`), axiom-clean:
     window-count calculus for `countOccurrences` (cons recursion,
     superadditivity, seam bound `count(x++u) ≤ count x + count u + (k−1)`
     by index-set split fit-in-x / shifted-in-u / ≤(k−1) straddle), then
     `CFDiscLt` deviation-form discrepancy and parts 1/2a/2b
     (`CFDiscLt.append`, `cfDiscLt_append_take`, `cfDiscLt_short_append`).
     Parts 2a/2b use hypothesis `|u|+(k−1) < ε|x|` (marginally stronger
     than paper's `|u|/|x| < ε`, absorbs the straddle; trivial for the W5
     schedule).  **All of B–Y Lemmas 7/8/9 are now formalized.**

  ✅ **B–Y Prop 12 PROVED** 2026-08-24 (`TBrickDefs.lean`), axiom-clean:
     `daryCell d m j r` (r consecutive order-m cells), `volume_daryCell`
     (= r/d^m), `interval_subset_daryCell_two` (any interval of length
     < d^{−m} sits inside the 2-cell at ⌊a·d^m⌋).

NEXT ATTACK: W5 t-brick structure (Defs 10–11) + Lemma 13 (main lemma).
Plan sketched from the paper (see scratch/by.txt §2, extracted 2026-08-24):
- Brick: CF word w (σcf = cfCylinder w) + per-base (m_d, j_d, r_d ∈ {1,2})
  with cfCylinder w ⊆ daryCell d m_d j_d r_d and relative length
  ≥ 1/(C·d) (B–Y C = 16e^{4c}; repo distortion constant differs — pick
  concrete C during Lemma 13, keep it a structure field or parameter).
- Lemma 13 inputs already in repo: good-length collection (W2 Markov
  substitute for B–Y Lemma 5 in CFDigitLaw), γ-Chebyshev brick bound
  (`chebyshev_blockCount_brick`, replaces B–Y Lemma 6/KPW — note 1/n
  decay beats the K/√n good mass, so the balance still works), Lemma 8
  (`card_baryDiscrepancy_ge_le`) for the d-ary bad zones.
  ✅ d-ary bad-zone bound PROVED 2026-08-24 (`volume_daryBadZone_le`,
  axiom-clean): inside an order-m0 cell, the union of order-(m0+k)
  sub-cells with ε-bad new blocks has measure ≤ 2d·e^{−dε²k/6}·d^{−m0}
  (`badBlocks` Finset + `card_badBlocks_le` = Lemma 8 restated).
- KEY ROUTE DECISION (recorded 2026-08-24): B–Y's uniform-m_d bookkeeping
  (their tight two-sided length window J_n, constant 16e^{4c}) does NOT
  match the repo's Lemma-5 substitute (`half_mass_long_extensions`, which
  bounds cfK only above; individual lengths spread exponentially).  Fix:
  choose m_d PER CHOSEN cylinder J maximal with |J| ≤ d^{−m_d} (Prop 12
  ⇒ ratio > 1/(2d)), and make the chosen J avoid the union of bad zones
  over ALL orders m ≥ m_min(n) — the geometric sum over m of
  `volume_daryBadZone_le` is still exponentially small vs the ≥ |I_w|/2
  good mass.  Brick ratio constant becomes 1/(2d) (not 16e^{4c}d).
  ✅ (a) sum-over-orders corollary PROVED 2026-08-24 (@6742fb7,
  `volume_iUnion_daryBadZone_le`): ⋃_{k≥kmin} daryBadZone has measure
  ≤ (2d/d^m0)·ρ^kmin/(1−ρ), ρ = e^{−dε²/6}.
  ✅ (c) digit-semantics bridge PROVED 2026-08-24, axiom-clean:
  `exists_block_of_lt` (blockNatVal surjective onto [0,d^k)),
  `floor_subCell_bounds` (a point's own order-(m0+k) sub-cell sits at
  index j0·d^k + v, v < d^k), `exists_goodBlock_of_notMem_badZone`
  (avoiding daryBadZone ⇒ the point's sub-cell carries a GOOD block).
  ✅ neighbor-widened zone PROVED 2026-08-24, axiom-clean:
  `daryBadZoneWide` (+ measure ≤ 6d e^{−dε²k/6}/d^m0, summed version via
  new generic `volume_iUnion_geom_le`), `badBlock_cell_far` (avoiding the
  wide zone puts every bad cell at distance ≥ 2 from x's own cell).
  ✅ CF word bridge PROVED 2026-08-24 (`CFWordBridge.lean`), axiom-clean:
  `iterate_mem_cfCylinder_iff` (cylinder membership = digit-window match),
  `blockCount_eq_card_matches`, `blockCount_sub_countOccurrences_bounds`
  (orbit count vs fitting-window count of the digit word differ ≤ |v|) —
  connects `chebyshev_blockCount_brick` to `CFDiscLt` of the new word.
- ✅ (b) BRICK STRUCTURE + d-ARY SIDE OF THE BALANCE PROVED 2026-08-24
  (review lap, `TBrick.lean`, axiom-clean):
  * `structure TBrick (t)` = Defs 10–11: genuine CF word `w`, per base
    `2 ≤ d ≤ t` an order-`m d` cell block of `r d ∈ {1,2}` cells with
    `cfCylinder w ⊆ daryCell d (m d) (j d) (r d)`, brick-ratio field
    `hratio : d^{-m d} ≤ 2d·|I_w|` (the repo's Prop-12 `1/(2d)` route,
    replacing B–Y's `1/(16 e^{4c} d)`).
  * `volume_aggregate_daryBadZoneWide_le`: ⋃_{2≤d≤t} ⋃_{k≥kmin}
    daryBadZoneWide ≤ Σ_d 6d·d^{-m0 d}·ρ_d^kmin/(1−ρ_d), ρ_d = e^{−dε²/6}
    (via `measure_biUnion_finset_le` + the summed-zone lemma; needs only
    `dε ≤ tε ≤ 1`).
  * `TBrick.volume_aggregate_bad_le`: **the d-ary half of the Lemma-13
    balance** — that aggregate bad zone ≤ (Σ_d 12d²ρ_d^kmin/(1−ρ_d))·|I_w|,
    using `hratio` to turn each `d^{-m0 d}` into `2d|I_w|`.  The constant is
    a finite sum of geometric-in-kmin terms ⇒ →0 as kmin→∞, so the d-ary bad
    mass is eventually an arbitrarily small fraction of |I_w|. ✅ d-ary side
    of the measure balance CLOSED.

- ✅ (i) CF SIDE OF THE BALANCE PROVED 2026-08-24 (review lap, `TBrick.lean`,
  axiom-clean): `cfBadZone w v n δ` (the set `chebyshev_blockCount_brick`
  controls) + `gaussMeasure_aggregate_cfBadZone_le` — for a FINITE family `F`
  of genuine CF words, `γ(⋃_{v∈F} cfBadZone w v n δ) ≤ Σ_{v∈F} 7(8|v|+80)
  γ(I_v)/(δ²n)·γ(I_w)` = O(1/n)·γ(I_w).  Resolves the "infinite alphabet"
  worry: the construction needs only finitely many blocks good per stage
  (length ≤ t, digits ≤ t), so a finite `measure_biUnion_finset_le` aggregate
  suffices — no `CFDiscLt` weighted sum needed for the measure step.
  (`CFDiscLt`/`CFWordBridge` still used later to turn "good frequency for all
  v ∈ F" into the refinement predicate of Def 11.)

- ✅ (ii) GOOD-MASS SIDE + COMBINE CORE PROVED 2026-08-24 (review lap,
  `TBrick.lean`, axiom-clean):
  * `goodExtSet w C n` (biUnion of good-length order-n extensions, bad ones
    sent to ∅) + `volume_goodExtSet` (= the `half_mass` tsum verbatim, via
    `measure_biUnion` + `cfCylinder_disjoint`; the `if..else ∅` trick avoids
    all subtype reindexing) + `exists_C_half_le_volume_goodExtSet`:
    `|I_w| ≤ 2·volume(goodExtSet)`, i.e. good mass ≥ ½|I_w|.
  * `exists_mem_notMem_of_measure_lt` (the COMBINE CORE): if `M ≤ μG`,
    `μB ≤ a`, `a < M`, then `∃ x ∈ G, x ∉ B`.  The logical backbone of
    "balance ⇒ surviving refinement".
  ALL FOUR ingredients of the Lemma-13 measure balance are now proved:
  good mass ≥ ½|I_w|, d-ary bad ≤ (→0)|I_w|, CF bad ≤ O(1/n)γ(I_w), and the
  combine core.  What remains is the ARITHMETIC WIRING (below).

- NEXT concrete step (WIRE THE BALANCE — mechanical, no new deep facts):
  ✅ (α) DONE 2026-08-24 (`TBrick.lean`, axiom-clean): `volume_iUnion_cfBadZone_le`
      — volume(⋃ CF bad) ≤ ofReal(2log2·Σ_v 7(8|v|+80)γ(I_v)/(δ²n)·γ(I_w)),
      i.e. the CF bad zone in LEBESGUE, still O(1/n).  Helpers:
      `volume_le_ofReal_mul_gaussMeasure` (vol s ≤ ofReal(2log2)·γ s on Ioo 0 1)
      + `measurableSet_cfBadZone` (via `measurable_blockCount`).  Still to do
      for the balance: bound Σ_v ... by (const/n)·volume(I_w) via γ(I_v)≤1 and
      γ(I_w) ≤ ofReal((log2)⁻¹)·volume(I_w) (gaussMeasure_le_volume).
  ✅ (β) **kmin(n) link** DONE 2026-08-24 late lap (@10a8c6e,
      `TBrickRefine.lean`, axiom-clean), LOG-FREE form: `4·d^kmin <
      fib(n+1)²` ⇒ `|I_{w++u}| < d^{−(m_d+kmin)}`
      (`TBrick.volume_append_lt_dpow`, via `volume_append_mul_fib_le` +
      brick containment `|I_w| ≤ 2d^{−m_d}`); threshold
      `exists_fib_threshold` (fib(n+1)² → ∞, via `Nat.le_fib_self`).
      Same commit: bad zones now cover BOTH possible base cells
      (j_d, j_d+1; coefficient 24d²), survivors are IRRATIONAL
      (rationals absorbed as a null set), `volume_cfCylinder_ne_zero`
      discharges hpos, and the survivor-unpacking toolkit is proved:
      `exists_word_of_mem_goodExtSet`, `range_map_cfDigit_eq` (digit word
      = u), `abs_blockCount_lt_of_notMem_cfBadZone` (CF side),
      `TBrick.exists_goodBlock_of_avoid` (x's own new d-ary block good at
      every k ≥ kmin, in x's definite cell).
  ✅ (γ-COMBINE) DONE 2026-08-24 (`TBrick.lean`, axiom-clean): the measure
      core is assembled.  `exists_mem_notMem_union_of_bounds` (abstract:
      good ≥ ½vol0, bads ≤ p·vol0, q·vol0, p+q<½ ⇒ ∃ x∈G avoiding both) +
      `exists_good_avoiding_bad` (concrete Lemma-13 core): GIVEN the two
      coefficient thresholds `14ΣL/(δ²n) < ¼` and `Σ_d 12d²ρ^kmin/(1−ρ) < ¼`
      (and `vol(I_w) ≠ 0`), ∃ good-length order-n extension of I_w avoiding
      BOTH the CF bad zone (all v∈F) AND the wide d-ary bad zone (all d≤t,
      k≥kmin).  This is the measure-theoretic heart of Lemma 13.
  ✅ (γ-leftover) DONE 2026-08-24 (`TBrick.lean`, axiom-clean): the two
      coefficient thresholds hold eventually — `exists_N_cfCoeff_lt`
      (14SL/(δ²n) < ¼ for n ≥ N, archimedean), `tendsto_daryCoeff` +
      `exists_kmin_daryCoeff_lt` (Σ_d 12d²ρ^kmin/(1−ρ) < ¼ for kmin ≥ kmin₀,
      finite geometric decay).  `exists_good_avoiding_bad_of_large` bundles
      them: ∃ N kmin₀, ∀ n≥N ∀ kmin≥kmin₀, the surviving good extension
      exists.  **The entire measure side of Lemma 13 is now UNCONDITIONAL.**
  (γ-OLDtext) **choose n₀**: both bad bounds are `< ¼·volume(I_w)` for n ≥ n₀(t,ε)
      (d-ary: geometric in kmin(n)→0; CF: O(1/n)→0).  Then
      `exists_mem_notMem_of_measure_lt` with M = ½vol(I_w) via
      `exists_C_half_le_volume_goodExtSet`, a = ¼+¼ < ½, gives x ∈ goodExtSet
      avoiding all bad zones.
  (δ) **Lemma 13 proper** (NEXT ATTACK — assembly only, all inputs proved):
      from the irrational survivor x (exists_good_avoiding_bad_of_large +
      the TBrickRefine toolkit): (1) extract u (exists_word_of_mem_goodExtSet);
      (2) NEW BRICK: for each d ≤ t (or t+1) choose m'_d maximal with
      |I_{w++u}| < d^{−m'_d} (nonempty by (β) with k := m'_d − m_d ≥ kmin;
      well-defined since |I_{w++u}| > 0); Prop 12
      (`interval_subset_daryCell_two`, needs I_{w++u} ⊆ an interval of that
      length — use `cfCylinder_subset_uIcc` + `volume_cfCylinder`) gives the
      ≤2-cell block + ratio 1/(2d); (3) GOODNESS: x's own new block is good
      (`TBrick.exists_goodBlock_of_avoid` at k) — check the Prop-12 block's
      cells sit within distance 1 of x's cell so `badBlock_cell_far`
      covers the second cell; (4) CF goodness of u: bridge
      `abs_blockCount_lt_of_notMem_cfBadZone` +
      `blockCount_sub_countOccurrences_bounds` + `range_map_cfDigit_eq`
      → countOccurrences bound on u for each v ∈ F (→ `CFDiscLt` form).
      Package as `TBrick.exists_refinement` (statement = repo Lemma 13).
      t→t+1: extra base via Prop 12 alone (no goodness needed at stage 1).

- (OLD framing, superseded by (α)-(δ)):
  (ii) **kmin(n) link**: good-length extensions J have |J| ≤ 2φ^{-2(n-1)}|I_w|
      (Fibonacci upper bound), so for each base d the "new digits" count
      k_d(J) ≥ kmin(n) with kmin(n)→∞; hence the wide-zone union avoided is
      exactly ⋃_{k≥kmin(n)} and `TBrick.volume_aggregate_bad_le` applies.
  (iii) **combine** (Leb↔γ, factor-2 window): ½|I_w| good (Lemma-5 subst)
      minus O(1/n)|I_w| CF minus (→0)|I_w| d-ary is > 0 for n ≥ n₀(t,ε) ⇒
      a surviving good extension J.  Then Lemma 13 proper: J is an
      ε-refinement; t→t+1 via Prop 12 (ratio 1/(2(t+1))).

Tools confirmed: `measurePreserving_gaussMap`, `gaussMeasure_univ`=1 (⇒
`IsProbabilityMeasure gaussMeasure` instance added in CFBlockFreq),
`gaussMeasure_cylinder_mixing`, `measureReal_preimage`, mathlib
`meas_ge_le_variance_div_sq` (Probability/Moments/Variance.lean).
2. Conditioned version on a base cylinder I_w (B–Y need per-stage bad
   measure < ¼ *given the current brick*): same computation under the
   conditional measure — the s-started identity makes every conditional
   a tailDensity mixture, so the same pin applies.  Alternatively work
   with Leb-conditionals directly via `volume_inter_preimage_horizon`.
3. b-ary side: Lemma 8 (Hardy–Wright Thm 148 Chernoff block counting)
   + Lemma 9 (BHS 3.1 concatenation) — check overlap with
   `Counting.lean`/`Visits.lean` first.
4. DRAFT frozen W4 statements for judge ratification (do NOT put
   unratified "frozen" statements in a scaffold file claiming authority;
   put proposals in drafts/).

**Judge attention requested**: ratify W4 statement shapes; note the
γ-mixing bonus (stronger than the planned Leb-only route: it is exact
γ-correlation decay, geometric, multiplicative in γ(I_v)).

> **GRIND (2026-08-24 lap N — route C′ core lemmas PROVED).** Two green
> commits: (1) `volume_logBadZone_le_vol` (new file `KhinchinBrick.lean`) —
> bridges `markov_logBadZone_brick`'s `gaussMeasure` bound into Lebesgue
> `volume` via the same `2 log 2` density-window factor `TBrick.lean` uses
> for the CF bad zone, giving the matching `14·(∫ logTailFn K dγ)/η`
> coefficient form. (2) `exists_good_avoiding_bad_khinchin` — mirrors
> `exists_good_avoiding_bad` (`TBrick.lean:470`) with `logBadZone` folded
> into the d-ary union via `measure_union_le`; NO `TBrick.lean` edits needed
> (as the prior handoff predicted). Coefficients tightened `<¼`→`<⅙` each so
> CF+d-ary+log sum `<½`. Both axiom-clean.
> **NEXT**: thread `exists_good_avoiding_bad_khinchin` through
> `exists_refinement_uniform` (`TBrickRefine.lean`/`CFSchedule.lean`) and the
> `xstar` schedule rederivation — this needs reading how `xstar`'s schedule
> currently invokes `exists_good_avoiding_bad`/`_of_large` (likely in
> `CFSchedule.lean` or `Headline.lean`) and adding the parallel K/η-indexed
> log-zone-avoidance guarantee, choosing `K` via `integral_logTailFn_tendsto`
> to satisfy `hlog`. This is the remaining mechanical (but nontrivial)
> plumbing to close `xstar_log_tail_uniform`.
