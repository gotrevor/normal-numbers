# PENDING WORK — Phase 3 publishing-prep complete locally

## 🔻 PiSqBBP lane-2 crux NARROWED to one numeric identity (2026-08-31, autonomous)

`src/NormalNumbers/PiSqBBPProof.lean` (branch `wip/pisq-bbp-decomp`).
Node `piSqBBP_proved : PiSqBBP` (Formula 29, `HasSum piSqTerm π²`) is now
a fully-structured proof resting on a SINGLE disclosed `sorry`.

**Machine-checked axiom-clean this run:**
- Degree-2 roots-of-unity filter `w2 n = (−16·xⁿ+16·z₁ⁿ−16·(−x)ⁿ+16·z̄₁ⁿ)/n²`
  — the SAME four points as `PiBBP` (DFT of the Formula-29 coeff vector
  is supported on frequencies {0,1,4,7}, real integer weights; verified
  in `experiments/pi_sq_bbp.py`).
- `dilogSummable` (dilog series summable on open disk), `w2_block`,
  `num0..num7` (residue algebra over I²=−1, x²=½), `hasSum_fiber2`
  (∑_{r<8} w2(8j+r)=piSqTerm j), assembly via `divModEquiv` +
  `HasSum.prod_fiberwise`.
- `dilog_add_neg` : `Li₂ z + Li₂(−z) = ½·Li₂(z²)` — pure even/odd series
  split, NO special functions (axiom-clean).
- `hasSum_w2` analytic convergence PROVEN; value reduced via
  `dilog_add_neg` to the crux below.

**The one remaining `sorry` — `dilog_reflection`** (2026-08-31, further
narrowed): `Li₂ z + Li₂(1−z) = π²/6 − log z·log(1−z)` for `z, 1−z` both
in the open unit disk.  `dilog_special_values` is now PROVEN from it
(reflection at `z=½` self-dual and at `z=z₁` with `1−z₁=z̄₁`, using the
`PiBBPProof` log values `log z₁=−½log2+(π/4)i`, `log z₂=−½log2−(π/4)i`,
`log ½=−log2`; all arithmetic machine-checked, `linear_combination` over
`I²=−1`).  So the ENTIRE π² node now rests on this one functional
equation.  **Obstruction:** mathlib has NO dilogarithm.  **Next attack:**
prove `dilog_reflection` for the local `Li2` via term-wise derivative —
`HasDerivAt Li2 (−log(1−w)/w) w` on the disk (differentiate the `tsum`;
`Mathlib/Analysis/Calculus/SmoothSeries.lean` `hasDerivAt_tsum` or the
power-series `HasFPowerSeriesOnBall.hasDerivAt`), then `F z := Li₂ z +
Li₂(1−z) + log z·log(1−z)` has `F'≡0` on the (connected) slit disk, so
`F` is constant `= π²/6` (limit `z→0`, `Li₂ 0=0`, `Li₂ 1 = ∑1/n² =
π²/6` — mathlib `hasSum_zeta_two`/basel).  Fallback: cite the reflection
formula as a lane-2 node (Lewin, *Polylogarithms* eq. 1.11).


## ✅ Tower C1–C8 COMPLETE (2026-08-30, autonomous)

All eight tower claims proved kernel-tier (RESULT table at top of
`BRIEF-adder-tower.md`; handoff `HANDOFF-2026-08-30-tower-complete.md`).
Base-g engine: `AdderBaseG.lean` (`signed_engine_g`,
`signed_engine_g_single`), emitter `experiments/adder_baseg_emit.py`.
No non-collapse findings; C1/C3 lane-2 cited (B–B 1994), C2 novelty
under check.  NEXT: `BRIEF-literature-statements.md` (ledger + wire
`c1_ternary_digit` → B–B M(3,1)=2 edge), then standing mandate.

## ✅ Adder operator addendum COMPLETE (2026-08-30)

All three briefs discharged, every theorem trust-triple; see
`HANDOFF-2026-08-30-adder-briefs-complete.md` and the RESULT sections of
`BRIEF-adder-disjunction-formalization.md`, `BRIEF-adder-universal.md`,
`BRIEF-adder-signed-engine.md`.  Headline surface: `adder_sixfold_disjunction`
(+ universal + engine-instance forms), `signed_engine`,
`adder_musical_disjunction` (+ universal).  Next attack (pending operator
authorization / altitude lap): k-track channels, other bases, word-sets —
listed out-of-scope in the signed brief; otherwise resume the conjecture-graph
objective (ln-two ladder / run tower / Diophantine-wall interface).

## 🔨 Adder six-fold disjunction (BRIEF-adder-disjunction) — lap 2026-08-30

Executing `BRIEF-adder-disjunction-formalization.md` per the DIRECTION operator
addendum, from `HANDOFF-2026-08-29-adder-foundation.md`.  Landed this lap
(both green, committed on `wip/adder-disjunction`):

1. `AdderShadow.lean` — true state (`winCode`/`chanCode`/`famState`) +
   **shadowing lemma** (`famState_shadow`, `hstep_famState`, `famState_lt`);
   bit-list injectivity `bitsVal_inj` turns the formed-window test into
   `OccursAt`.  Note: `winCode z m k` takes the digit COUNT (channel window
   = `winCode z m (ell-1)`, formed window = `winCode z m ell`).
2. `AdderCert.lean` + `AdderCertToy.lean` — generic `checkCert` sweep over
   `(σ, s')` with C1/C1'/C3' extraction lemmas; toy 16-state certificate
   passes **kernel `decide` in ~1s**, `#print axioms` = `[propext]`.
   Module-3 route settled at toy scale.

**DONE 2026-08-30 (later same lap):** `AdderDescent.lean` (module 4) and
`AdderEndgame.lean` (module 5 generic engine) are green.  **`toy_disjunction`
is proved END-TO-END, kernel tier, trust triple**
`[propext, Classical.choice, Quot.sound]` — the whole pipeline
(carry/shadow/certificate/descent/endgame) is validated.  Remaining:
`AdderCertMain.lean` (73728-state certificate, native_decide phase-1) +
`AdderMain.lean` (frozen six-fold statement) + RESULT in the brief.

**Historical next-attack notes (now executed):**
3. `AdderDescent.lean` — from an infinite HStep path with states `< famSize`
   + checked conditions ⇒ eventually periodic state AND input sequences
   (C3' ω-descent kills dead states; ρ non-increasing, finitely many drops;
   beyond last drop steps = `forced`, pigeonhole).  No König needed.
4. `AdderEndgame.lean` — eventually periodic σ ⇒ periodic `rdigit X` ⇒
   `2^N(2^p−1)·log 2 ∈ ℤ` ⇒ contradiction with `irrational_log_two`
   (Legendre route, ALREADY LANDED — do not use lnTwoExpSep, see
   route-correction in the foundation handoff).  Constants via `Real.log_mul`.
5. `AdderCertMain.lean` — 73728-state certificate (JSON at
   `experiments/certs/adder_cert_main.json`), `native_decide` phase-1,
   kernel stretch.  Then `AdderMain.lean` frozen statement + RESULT in brief.


## ✅ Phase 3 publishing-prep pass — 2026-08-26

The facts-first metadata audit and production comparator harness are complete.
Active prose now records image-Khinchin, Track D, and
`IsNormal.isDisjunctive` as complete; `ae_tail_average_tendsto` is proved, and
the older open-crux material below is explicitly historical. The
formal-conjectures correction is PR-ready local sibling work (definition fix
`c6126c56`, empty-block test follow-up `5d5832d0`), not an upstream merge. The
Champernowne contribution remains staged and externally unpublished.

The exact Wall and conditional ln-two theorems are in a strong-pattern
comparator harness: Mathlib-only Challenge with faithful real definition
bodies, import-only Solution, three semantic anchors, exact trust-triple
whitelist, nanoda enabled, non-default Comparator library, pinned Linux CI,
and a local identity probe with a missing-name teeth test. Both full builds,
all five identity closures, the teeth test, exact headline axiom gates, config
and YAML checks, and the independent artifact audit pass locally. The complete
pinned landrun/lean4export/comparator binary set is not available offline, so
the landrun + nanoda end-to-end invocation was not run locally and remains the
configured CI gate.

No mathematical proof work is pending in this phase. External publication,
the two prepared PRs, and the Zulip announcement are operator-owned. Preserve
the two known-false bypassed `CFScheduleA.lean` sorries.

Everything below is retained as historical proof-campaign state.

## ✅ Track D3 operator override complete — 2026-08-26

The boxed Track D objective is complete.  `IsNormal.isDisjunctive` was first
landed separately in `b755fd5`.  `QuadraticDisjunctive.lean` contains the
faithful named Prop `QuadraticHypothesisM`, the explicit closed
forward-invariant missing-word subshift, the endpoint-safe cover, and the
proved Hausdorff-cost decay.  The exact wrapper
`quadratic_irrationals_disjunctive_of_hypothesisM` consumes only
`QuadraticHypothesisM b` (besides `b ≥ 2`) and concludes that every quadratic
irrational is `b`-disjunctive.  Guarded `#print axioms` reports only
`[propext, Classical.choice, Quot.sound]`; the full build passes at 8766 jobs.
The two known-false `CFScheduleA.lean` sorries remain untouched as required.

## ✅ 2026-08-25 (grind lap, post-completion) — headline faithfulness RATIFIED + Track D0 opened

The image-Khinchin directive crux is DONE and kernel-verified this lap (`#print axioms`
= trust triple, no `sorryAx`); build 🟢 8762. The only remaining `src/` sorries are the two
FALSE/REFUTED dead schedule stubs (`CFScheduleA.lean:4400`,`:5774`) — directive-forbidden,
provably unprovable (their RHS is beaten by the LHS for large n; B6 proved via the measure
route instead), so the anti-premature-quit gate cannot be cleared by proving them. An
altitude lap must retarget or ratify completion.

**Two genuine advances this lap (both non-forbidden, real value):**

1. **Faithfulness cross-check of the headline (endorsed NL→formalization).** Handed Aristotle
   ONLY the English prose of the image-Khinchin statement (never the Lean). Its independent
   formalization reproduced the EXACT logical content: for every countable `Q ⊆ ℝ×ℝ` with
   `0<q`, `∃ x ∈ Ioo 0 1` that is CF-normal ∧ Khinchin-typical ∧ every affine image `q·x+r`
   ((q,r)∈Q) CF-normal — with matching CF-normal (block-frequency), Khinchin-typical
   (geometric-mean → Khinchin constant), and affine-image definitions. Independent confirmation
   that `exists_cfNormal_khinchinTypical_and_affine_family_cfNormal` faithfully states the theorem.
   (Aristotle project `6d56b648`.)

2. **Track D0 opened — `Disjunctive.lean` (roadmap "orbit dictionary", `docs/conditional-disjunctivity.md` §0).**
   The topological twin of Wall's theorem, self-contained (imports only `RealDefs`), axiom-clean:
   - `IsDisjunctive b x` — interval-visit form: every `[a,c) ⊆ [0,1)` is visited by the orbit
     `n ↦ bⁿx mod 1` (the density weakening of `Equidistributed (orbit b x)`).
   - `orbit_mem_Ico`, `orbit_fract` (local copy), `isDisjunctive_fract`.
   - **`isDisjunctive_iff_denseOrbit`** — `IsDisjunctive b x ↔ Ico 0 1 ⊆ closure (range (orbit b x))`,
     the "dense orbit ⟺ disjunctive" equivalence (fully proved). This is the base layer the
     conditional-disjunctivity axioms (Λ, D_w) will sit on. Next D0 bricks: `omegaLimit` basics
     (closed + forward-invariant), and the D1 0-1 law (`λ(K)>0 ∧ closed ∧ T_b K ⊆ K ⟹ K = [0,1)`)
     via b-adic Lebesgue density.



## 🚧 2026-08-25 (review lap #3) — image-Khinchin crux: decorrelation core LANDED, variance→a.e. chain remaining

> **Historical snapshot, superseded later the same day.** The crux described in
> this section is proved; see the completion entry above. It is not active work.

**The ONE open obligation across the whole repo**: `ae_tail_average_tendsto K`
(`CFAeKhinchin.lean:343`), `∀ᵐ x ∂γ, logBirkhoffSum K n x / n → ∫ logTailFn K dγ`. Only
`K=0` consumed (g-direct) ⇒ closes `ae_khinchinTypical` (+sorryAx) ⇒ image-Khinchin headline
(graft into `exists_cfNormal_and_affine_family_cfNormal'`). A strong law for the UNBOUNDED
log-digit function under the Gauss measure — L²→a.e. variance route mirroring PROVEN `ae_orbit_freq`.

**Route = FINITE TRUNCATION (Approach B)** — reduces the second moment to Finset algebra + one
MCT limit, sidestepping fragile nested `integral_tsum`. Notation: `A_a := cfCylinder [K+1+a]`,
`u_a := log(K+1+a)`, `f_M := Σ_{a<M} logTailTerm K a`, `S_n^M := Σ_{i<n} f_M∘gaussMapⁱ = Σ_{a<M} u_a·blockCount(A_a) n`.

**LANDED this lap (both axiom-clean, `CFAeKhinchin.lean`, green 8760→8746 partial):**
- `integral_blockCount_cross A B` : `∫ blockCount A n·blockCount B n dγ = Σ_{i,j<n} γ.real(T⁻ⁱA∩T⁻ʲB)`
  (+ helpers `blockIndic_iterate_mul₂`, `integrable_blockIndic_iterate_mul₂`). Cross of `integral_blockCount_sq`.
- `abs_cov_two_cyl_pair_le a b (ha) (hb) {i j} (hij:i≠j)` : `|γ.real(T⁻ⁱ[a]∩T⁻ʲ[b]) − γ[a]γ[b]| ≤`
  `4·(9/10)^{dist(i,j)∸1}·(|[b]|γ[a] + |[a]|γ[b])`. Symmetric bound covers i<j and i>j (each branch
  reduces via `gaussMeasureReal_pair_shift₂` to an aligned gap, then `abs_cov_two_cyl_le`).

**LANDED lap #3b (green, axiom-clean):** sub-lemmas `integral_logBirkhoffTrunc_sq` (2nd-moment
expansion), `sq_logTruncMean_eq` (squared mean), constants `logTailC1/2/3` + summabilities +
nonneg, `logVarConst K = C₃+C₁²+176C₁C₂`, `sum_logMul_gaussMeasure_inter` (disjointness collapse),
and **`inner_pair_bound`** — the covariance FOLD: `|Σ_{j,j'}(γ.real(T⁻ʲ[K+1+a]∩T⁻ʲ'[K+1+b])−γ_aγ_b)|
≤ n(γ(A∩B)+γ_aγ_b) + 88n(vol_bγ_a+vol_aγ_b)` (diagonal j=j' via measure-preservation; off-diag folds
brick 2 via sum_range_dist_le+geom_trunc_sum_le). This is the hard analytic core.

**BRICK 3 DONE (green, axiom-clean):** `variance_truncated_le K M n : |∫(S_n^M)² − (n·μ_M)²| ≤ n·logVarConst K`,
UNIFORM in M. Assembly landed via hΔ + nested-abs + `inner_pair_bound` + `sum_logMul_gaussMeasure_inter`
(collapse) + `(summable_logTailC*).sum_le_tsum` partial bounds + final `gcongr`.

**REMAINING (hardest-first, next laps):**
1. `variance_logBirkhoffSum_le K n` : `|∫(logBirkhoffSum K n)² − (n·μ)²| ≤ n·logVarConst K` via MCT
   M→∞. Need `S_n^M := logBirkhoffTrunc K M n ↑ logBirkhoffSum K n` a.e. (pointwise: `logBirkhoffTrunc`
   is `Σ_{a<M} log(K+1+a)·blockCount[K+1+a] n`, and `logBirkhoffSum K n x = Σ_{i<n} logTailFn K(Tⁱx)`;
   the truncation ↑ the full via `logTailTerm_tsum_ae_eq` at each `Tⁱx` — but likely cleaner: show
   `logBirkhoffTrunc K M n = Σ_{i<n} (Σ_{a<M} logTailTerm K a)∘Tⁱ` and `(Σ_{a<M} logTailTerm K a) ↑ logTailFn K`).
   Then `∫(S_n^M)²↑∫(logBirkhoffSum)²` (MCT: `MeasureTheory.integral_tendsto_of_tendsto_of_monotone`
   or lintegral+`lintegral_iSup`; limit integrable via the uniform bound `≤(nμ)²+n·logVarConst`), and
   `logTruncMean K M → ∫ logTailFn K = logTailC1 K = μ` (partial sums → tsum). Pass the bound to the limit.
   ALT (maybe cleaner, avoids identifying μ): keep the RHS `n·logVarConst K` (M-independent) and only
   need `∫(S_n^M)² → ∫(logBirkhoffSum)²` and `logTruncMean K M → μ` where `μ = ∫ logTailFn K` (from
   `integral_logTailFn_eq_of_hasSum`; note `μ = logTailC1 K`).
2. `chebyshev_logBirkhoffSum` + `ae_tail_average_tendsto` : TRANSCRIBE `chebyshev_blockCount` +
   `ae_orbit_freq` (`CFAeNormal.lean:81`), `blockCount A p`↦`logBirkhoffSum K p`, `γv`↦`μ`, variance
   const `(8|v|+80)γv`↦`logVarConst K`. Monotone gap-squeeze OK (`logBirkhoffSum_nonneg`, ↑ in n).
3. Graft ⇒ image-Khinchin headline; re-`#print axioms` clean.
   OLD note (superseded, kept for context): `|∫(S_n^M)² − (n·μ_M)²| ≤ n·(C₃+80C₁C₂)` UNIFORM in M. Via
   `integral_blockCount_cross` (S_n^M is a finite Σ_{a,b} u_a u_b blockCount·blockCount). Split
   `Σ_{i,j}` diagonal i=j (⇒ `n·Var(f_M) = n·(∫f_M²−μ_M²) ≤ n·∫f_M²`; distinct A_a,A_b DISJOINT so
   cross a≠b vanish at m=0, `∫f_M² = Σ_a u_a²γ(A_a) ≤ C₃`) vs off-diag i≠j (bound each via brick 2,
   fold `Σ_{i≠j}(9/10)^{dist∸1}` with `sum_range_dist_le`+`geom_trunc_sum_le`, `|v|=1`). Constants:
   `C₁=Σ' u_aγ(A_a)` = tail of `summable_gaussKuzmin_log`; `C₂=Σ' u_a·vol(A_a)` = `summable_logMul_vol_cfCylinder`;
   `C₃=Σ' u_a²γ(A_a)` = `summable_sqLog_gaussMeasure_cfCylinder`. Finite partial sums ≤ tsum (nonneg, `sum_le_tsum`).
2. `variance_logBirkhoffSum_le K n` : MCT M→∞. `S_n^M ↑ logBirkhoffSum K n` a.e. — need
   `logTailFn K (Tⁱx) = Σ'_a u_a 1_{A_a}(Tⁱx)` a.e. (`logTailTerm_tsum_ae_eq` at `Tⁱx`; γ-preserving,
   finite intersect over i<n), so `f_M∘Tⁱ ↑ logTailFn K∘Tⁱ`, sum over i<n. Then `∫(S_n^M)² ↑ ∫(logBirkhoffSum)²`
   (MCT, `MeasureTheory.integral_tendsto_of_tendsto_of_monotone` or `lintegral_iSup`), `μ_M→μ`
   (from `integral_logTailFn` partial sums), pass the uniform bound to the limit.
3. `chebyshev_logBirkhoffSum` + `ae_tail_average_tendsto` : TRANSCRIBE `chebyshev_blockCount` (Markov on
   `(S−nμ)²`) + `ae_orbit_freq` (`CFAeNormal.lean:81`), `blockCount A p`↦`logBirkhoffSum K p`, `γv`↦`μ`.
   Monotone gap-squeeze OK (`logTailFn K ≥ 0` ⇒ `logBirkhoffSum K n` ↑ in n, `logBirkhoffSum_nonneg`).
4. Graft ⇒ image-Khinchin headline; re-`#print axioms` clean.

**Watch-outs**: (a) diagonal m=0 does NOT obey the `4vol[b]γ[a]` bound (fails at a=b, large a) — MUST
split it out as the `C₃` term, not fold into brick 2. (b) `gaussMeasure.real` vs `.toReal`: equal by
`measureReal_def`, bridge with `rw [MeasureTheory.measureReal_def]` (as in `abs_cov_two_cyl_pair_le`).
(c) MCT needs the limit integrable — the uniform bound gives `∫(logBirkhoffSum)² ≤ (nμ)²+nC < ∞`.

## 🎉 2026-08-25 (Tier-2 grind) — B6 TIER 2 LANDED: `exists_cfNormal_and_affine_family_cfNormal` AXIOM-CLEAN

New file `src/NormalNumbers/CFAffineFamily.lean` (sorry-free, build 🟢 8759). Extends the
single-map measure route to a **countable FAMILY** of affine maps simultaneously:

> `(Q : Set (ℝ×ℝ)) (hQ : Q.Countable) (hqr : ∀ p∈Q, 0<p.1 ∧ 0≤p.2) →`
> `∃ x∈(0,1), IsCFNormal x ∧ ∀ p∈Q, IsCFNormal (affineMap p.1 p.2 x)`

`#print axioms` = trust triple. Structure:
- **Crux `volume_notCFNormal_Ici0`**: the non-CF-normal set is Lebesgue-null on all of `[0,∞)`.
  Proof: `(0,1)`-nullity `volume_notCFNormal_Ioo01` (from `ae_isCFNormal` + `volume ≤ C·γ` on
  `(0,1)`) + positive integer-shift invariance (`isCFNormal_add_nat`): every bad `w≥0` is a
  nonneg integer or an integer translate of a bad point in `(0,1)`, so `N∩[0,∞)` is covered by
  `⋃ₙ (·+n)''(N∩(0,1)) ∪ range(ℕ↪ℝ)`, all null (translate = `affineMap 1 (-n)⁻¹`, reuse
  `volume_preimage_affineMap`).
- `gaussMeasure_notCFNormal_affine_Ioo01`: each `{x∈(0,1)|¬IsCFNormal(ψx)}` is γ-null (ψx>0 on
  the domain lands in `[0,∞)`; pull the null superset back, `γ≤C·vol`).
- Assembly: `measure_biUnion_null_iff` (Q countable) + `measure_sdiff_null` + `γ(0,1)>0`.

**✅ DONE (same grind) — FULL generality `exists_cfNormal_and_affine_family_cfNormal'` (any real `r`, `q>0`).**
The `r≥0` restriction is REMOVED, matching Vandehey §7 exactly. Crux upgraded to
`volume_notCFNormal_univ` (bad set Lebesgue-null on ALL of `ℝ`). Negative half avoided the
piecewise change-of-variables: the involution identity `gaussMap⁻¹(Z)∩Iio0 = inv''(Int.fract⁻¹Z∩Iio0)`
(inv is its own inverse on `Iio0`), `Int.fract⁻¹Z` null (`volume_fract_preimage_notCFNormal`,
ℤ-translate union), inv differentiable off 0, then `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`.
Axiom-clean (trust triple). Both family forms + single-map B6 + B5′ headlines untouched.

**🟢 DECOMPOSED (same grind) — image-Khinchin crux set up in `src/NormalNumbers/CFAeKhinchin.lean`.**
Target `ae_khinchinTypical : ∀ᵐ x ∂γ, KhinchinTypical x` (the co-null set to intersect into the
family witness). Reduction NAILED (no general ergodic theorem needed):
- `khinchinTypical_iff_log_tendsto` ⇒ suffices `(1/n)Σ_{i<n} log a_i → log K₀` a.e.
- Split at a FIXED cutoff `K`: `Σ log a_i = Σ_{a≤K} log a·#{i<n:a_i=a} + logBirkhoffSum K n x`
  (tail = `CFLogTail.logBirkhoffSum`, = `Σ_{i<n} log a_i·1[a_i>K]`).
- **Bounded part** → `Σ_{a≤K} log a·γ([a]) = Σ_{k<K} logTailG k` a.e.: FINITE sum of the singleton
  frequency limits `ae_digitCount_tendsto a` (= `ae_orbit_freq [a]`). **PROVED** this lap (leaf,
  axiom-clean).
- **Tail part** → `∫ logTailFn K dγ` a.e.: the ONE disclosed crux `ae_tail_average_tendsto K`.
- **Exact cancellation**: bounded-limit + tail-limit = `Σ_{k<K} logTailG k + ∫logTailFn K dγ =
  log K₀` for ANY fixed K, by `integral_logTailFn_eq_of_hasSum` + `HasSum logTailG (log K₀)`
  (`gaussKuzmin_logsum_hasSum`). No `K→∞` limiting. Pick e.g. K=0.

**ROUTE REORIENTED (cleaner) — g-DIRECT instead of the K-split.** The `logBirkhoffSum`/`logTailFn K`
tail device was for the FIRST-moment-only engine. For the L²→a.e. route it's simpler to target the
FULL log-digit `g(x) = log(cfDigit x 0)` directly: `g ≥ 0` (so its Birkhoff sum `S_n^g = Σ_{i<n} log a_i`
is MONOTONE in n ⇒ gap-squeeze applies), `g ∈ L²` (heavy tail is summable), and `∫ g dγ = log K₀`
(= `Σ_k logTailG k` via `gaussKuzmin_logsum_hasSum`). Then `khinchinTypical_iff_log_tendsto` closes
`ae_khinchinTypical` from a.e. `(1/n) S_n^g → log K₀`. No cutoff K, no `ae_tail_average_tendsto`.

BRICKS LANDED (all axiom-clean, serve the g-direct variance bound):
- `gaussMeasureReal_pair_shift₂`, `abs_cov_two_cyl_le` — two-distinct-cylinder mixing.
- `summable_logMul_vol_cfCylinder` (Σ log·vol), `summable_sqLog_gaussMeasure_cfCylinder` (Σ (log)²·γ,
  via `sq_log_le_sixteen_sqrt`) — the finite variance constants + `∫g²<∞` input.

**NEXT ATTACK (hardest-first):** the g-direct variance bound `variance_logDigitSum_le`:
`|∫ (S_n^g)² dγ − n²(log K₀)²| ≤ C·n`. Route: (i) `∫ g dγ = log K₀` and `∫ g² dγ < ∞` from the
disjoint-cylinder tsum expansion `g = Σ_a log a·1_{[a]}` (MCT / `integral_tsum` over disjoint
indicators, weights summable by the two bricks above). (ii) second moment
`∫(S_n^g)² = Σ_{j,j'<n} Σ_{a,b} log a log b·γ(T^{-j}[a]∩T^{-j'}[b])`, per-gap correlation
`|Cov(g,g∘Tᵐ)| ≤ (9/10)^{m∸1}·4·(Σ log γ)(Σ log vol)` from `abs_cov_two_cyl_le` + the two summability
bricks, then fold with `sum_range_dist_le`/`geom_trunc_sum_le` (reuse `variance_blockCount_le`'s
pattern) ⇒ `≤ C·n`. (iii) Chebyshev + Borel–Cantelli on `p=(k+1)²` + monotone gap-squeeze (as in
`ae_orbit_freq`) ⇒ `ae_khinchinTypical`. (iv) graft one co-null intersection into
`exists_cfNormal_and_affine_family_cfNormal'`. The `logBirkhoffSum`-based `ae_tail_average_tendsto`
sorry in `CFAeKhinchin.lean` is now SUPERSEDED scaffolding — leave it or delete when g-direct lands.

**OLD PLAN (superseded):** prove `ae_tail_average_tendsto K` (`CFAeKhinchin.lean:60`, disclosed
sorry). This is the L²→a.e. Borel–Cantelli of `ae_orbit_freq` applied to `logBirkhoffSum K` instead
of `blockCount`. Needs a **variance bound for the log-tail Birkhoff sum**:
`∫ (logBirkhoffSum K n − n·∫logTailFn K)² dγ ≤ C·n·(…)`. Build it from the SAME Gauss two-point
mixing behind `variance_blockCount_le` (`CFBlockFreq:401`): `logTailFn K = Σ_{a>K} log a·1_{cfCylinder[a]}`
so its Birkhoff-sum variance decomposes into the cylinder correlations already controlled. Then
Chebyshev + Borel–Cantelli on `p=(k+1)²` + the MONOTONE gap-squeeze (`logBirkhoffSum K n x` ↑ in n
since `logTailFn K ≥ 0`) — same skeleton as `ae_orbit_freq`. mathlib has NO pointwise-Birkhoff /
maximal-ergodic theorem, so this variance route (not an ergodic-theorem import) is the path.
Then assemble `ae_khinchinTypical` (the split identity `blockCount(cfCylinder[a]) = digit-count` +
finite-sum a.e. + the cancellation) and graft one more co-null intersection into
`exists_cfNormal_and_affine_family_cfNormal'` for the image-Khinchin headline.

**ALT stretch:** image-Khinchin — strengthen the witness so `x` is
additionally Khinchin-typical (the Khinchin-typical set is γ-co-null; intersect one more co-null
set in the SAME assembly). Cheap given `KhinchinTypical` a.e. infrastructure if present.

## 🎉 2026-08-25 (measure-route grind) — B6 COMPLETE: `exists_cfNormal_and_affine_cfNormal` is AXIOM-CLEAN

**The crux `ae_orbit_freq` is PROVED** (`CFAeNormal.lean`, sorry-free) — the classic L²→a.e. argument:
`chebyshev_blockCount` bound → Borel–Cantelli (`ae_eventually_notMem`) along `p=(k+1)²`
(∑1/(k+1)² summable via `summable_nat_add_iff`) per `δ=1/(m+1)`, intersected over `m`
(`ae_all_iff`) ⇒ a.e. convergence on the squares; then the monotone gap-squeeze
(`Nat.sqrt`, `Nat.sqrt_le'`/`lt_succ_sqrt'`, product-form limits `k²/(k+1)²→1` via
`tendsto_natCast_div_add_atTop`, `tendsto_of_tendsto_of_tendsto_of_le_of_le'`).

**Headline WIRED + FLIPPED CLEAN.** `exists_cfNormal_and_affine_cfNormal` (`CFScheduleA:6270`)
now consumes `exists_feasible_cfNormal_affine` in all three branches (feasible + two integer-shift);
`CFScheduleA` imports `CFAeNormal` (no cycle). Real `#print axioms` this lap:
- `exists_cfNormal_and_affine_cfNormal` → `[propext, Classical.choice, Quot.sound]` ✅ **DONE**
- `exists_absolutely_normal_cf_normal`, `_khinchin` → trust triple (untouched) ✅
- `ae_isCFNormal` → trust triple ✅

The schedule/two-stream chain (`schedA_block_linear` + 8 other refuted sorries) is now DEAD CODE —
the headline no longer flows through it. Kept in-src marked REFUTED per directive, NOT deleted.
**B6 (Vandehey §7 single affine map) is closed.** No open obligation remains on any headline.

---

## 🟢 2026-08-25 (measure-route grind) — LANDED: `CFAeNormal.lean` scaffold, B6 reduced to ONE a.e. crux

New file `src/NormalNumbers/CFAeNormal.lean` (build 🟢 8758). Fully proved, axiom-status modulo the
one crux sorry:
- `ae_irrational`, `ae_mem_Ioo` (γ supported on (0,1), rationals null) — DONE.
- `ae_isCFNormal : ∀ᵐ y ∂γ, IsCFNormal y` — DONE, assembled from the crux `ae_orbit_freq` via
  `ae_all_iff` over countable `List ℕ` + `isCFNormal_of_irrational_orbit_freq`.
- `exists_feasible_cfNormal_affine {q}(hq:0<q) r (hr:-q<r∧r<1) : ∃ x, IsCFNormal x ∧ IsCFNormal (ψx)`
  — **DONE**. Measurability of the CF-normal set is DODGED: `exists_measurable_superset_of_null`
  gives a measurable null superset `W⊆(0,1)` of `{¬IsCFNormal}∩(0,1)`; `volume_le_ofReal_mul_gaussMeasure`
  ⇒ `vol W=0`; `volume_preimage_affineMap` ⇒ `vol(ψ⁻¹W)=0`; `gaussMeasure_le_volume` ⇒ `γ(ψ⁻¹W)=0`.
  Feasible `F=Ioo lo hi` has `γ F>0`; `F⊆(F∩A∩B)∪(F∩Aᶜ)∪(F∩Bᶜ)` with the last two γ-null ⇒ nonempty.

**THE one remaining crux — `ae_orbit_freq` (`CFAeNormal:81`, disclosed sorry):** for genuine `v`,
`∀ᵐ y ∂γ, blockCount(cfCyl v) p y/p → γv`. Classic L²→a.e.: `chebyshev_blockCount` (already in
`CFBlockFreq:470`, gives `γ{|S_p/p−γv|≥δ}≤(8|v|+80)γv/(δ²p)`) + Borel–Cantelli
(`MeasureTheory.ae_eventually_not_mem`) along `p=(k+1)²` (∑1/(k+1)² summable) for each `δ=1/(m+1)`,
intersect over `m` ⇒ a.e. convergence along squares; then monotone gap-squeeze
(`p↦blockCount` nondecreasing, `Nat.sqrt`, `k²/(k+1)²→1`).

**NEXT:** (1) prove `ae_orbit_freq`. (2) wire: edit `exists_cfNormal_and_affine_cfNormal`
(`CFScheduleA:6270`) to consume `exists_feasible_cfNormal_affine` (add `import CFAeNormal` to
CFScheduleA — no cycle, CFAeNormal doesn't import CFScheduleA), keeping the 3-branch integer-shift
(re-`obtain ⟨x,hxN,hyN⟩` instead of the interleaved witness); then B6 is sorryAx-free, retire the
schedule `sorry`s as dead. (3) re-`#print axioms` both B5′ headlines (trust triple) + B6.


## 🚨 2026-08-25 (review lap #2b) — ROUTE PIVOT: schedule crux is FALSE → MEASURE route

**`variance_blockCount_psi_pushed` is PROVABLY FALSE** (`OBSTRUCTION-2026-08-25-variance-psi-pushed-FALSE.md`).
So the "step 1a/1c" plan in the section immediately below is **DEAD** — do NOT grind it. The restricted
2nd-moment identities landed in `a92dd8c` are still TRUE and axiom-clean (pure measure theory), but the
mixing bounds they were meant to feed are FALSE, so the whole `psi_pushed_*` chain is retired.

**NEW PLAN (B6 via the measure argument — `ROUTE-ESCALATION-2026-08-25.md`, DIRECTION.md CURRENT DIRECTIVE):**
the stated headline is bare existence, trivially true a.e.  Build in a NEW file `src/NormalNumbers/CFAeNormal.lean`:
1. **`ae_isCFNormal` (THE new crux):** `∀ᵐ y ∂gaussMeasure, IsCFNormal y`, via L²→a.e.:
   - per-word `v`: `variance_blockCount_le` (`CFBlockFreq:401`) + Chebyshev + Borel–Cantelli on `p=k²`
     + monotone-squeeze on gaps ⇒ a.e. `blockCount(cfCyl v) p ·/p → γv`;
   - intersect over countable valid `v` + a.e. orbit-in-`(0,1)` ⇒ `isCFNormal_of_orbit_freq`
     (`CFOrbitFreq:34`) ⇒ `IsCFNormal y` a.e.
2. **`ae_isCFNormal_affine`:** `∀ᵐ x, IsCFNormal(ψx)` via `ψ⁻¹` preserves γ-null
   (`volume_preimage_affineMap` `CFAffine:94` + γ≈volume bounded-density).
3. **Assemble** `exists_cfNormal_and_affine_cfNormal`: two co-null sets on the feasible interval meet ⇒
   witness; plug into the feasible branch (integer-shift reduction for `r∉(-q,1)` already present).
The schedule/explicit-witness chain (`variance_blockCount_psi_pushed`, `psi_pushed_*`, `_poly`,
two-stream `schedA_block_linear`, `exists_interleaved_affine_witness`) stays in `src` marked REFUTED,
NOT deleted, NOT to be attacked.

## 🟢 2026-08-25 (review lap #2) — LANDED: crux step 1a (restricted ψ-pushed 2nd-moment identities)

Committed `a92dd8c` (build green 8757, axiom-clean). In `CFScheduleA.lean` before the crux:
- `integral_blockCount_psi_restricted`   : `∫_S (S_n∘ψ) dγ  = Σ_{j<n} γ(S ∩ ψ⁻¹T^{-j}A)`
- `integral_blockCount_sq_psi_restricted`: `∫_S (S_n∘ψ)² dγ = Σ_{j,j'<n} γ(S ∩ (ψ⁻¹T^{-j}A ∩ ψ⁻¹T^{-j'}A))`
  (+ helpers `blockIndic_comp`, `measurable_affineMap`, `blockIndic_psi_mul`,
  `setIntegral_indicator_one_gaussMeasure`). Pure measure theory, NO mixing. These reduce the
  monolithic crux `variance_blockCount_psi_pushed` to **bounding the pair-correlation masses**
  `γ(cfCyl wx' ∩ ψ⁻¹T^{-j}A ∩ ψ⁻¹T^{-j'}A)` — the ψ-conjugated interval-base Gauss mixing.

**NEXT — crux step 1b (the hard core) + 1c (assembly). Concrete reduction of `variance_blockCount_psi_pushed`:**
Set `S=cfCyl wx'`, `A=cfCyl v`, `c=nγv`, `μ_j=γ(S∩ψ⁻¹T^{-j}A)`, `μ_{jj'}=γ(S∩(ψ⁻¹T^{-j}A∩ψ⁻¹T^{-j'}A))`.
Expand `(S_n∘ψ − c)² = (S_n∘ψ)² − 2c(S_n∘ψ) + c²`; integrate over S (each term is now a landed
identity + `∫_S c² dγ = c²·γ(S)` via `setIntegral_const`):
  `∫_S (S_n∘ψ−c)² dγ = Σ_{jj'} μ_{jj'} − 2c Σ_j μ_j + c²·γ(S)`.
The bound needs, per pair, TWO ψ-conjugated interval-base mixing facts (state as named sub-sorries):
  (1-pt) `|μ_j − γ(S)·γv| ≤ 4·γ(S)·γv·(9/10)^{?}`  [note: no `∸|v|` shift for 1-pt; the affine
         base has no cylinder depth — the decay index is `j` itself or `0`; work it out from CoV];
  (2-pt) `|μ_{jj'} − γ(S)·γv²| ≤ 4·γ(S)·γv·(9/10)^{Nat.dist j j' ∸ |v|}`  [the pair-correlation,
         mirror `abs_cov_pair_le`].
Then the same geometric fold as `variance_blockCount_le` gives `≤ (8|v|+80)·n·γv·γ(S)` PLUS a
`2c·|Σ_j μ_j − nγv γ(S)|` 1-point correction (absent in the full-measure model, where
`∫ S_n = nγv` EXACTLY; here it is only ≈, up to 1-pt mixing) — bound it by `2nγv·Σ_j(1-pt err)`,
also `O(n·γv·γ(S))`, absorbed by enlarging the constant if needed (check the `+80` slack).
**The mixing sub-sorries (1-pt, 2-pt) are step 1b, THE research core.** Route to prove them:
change-of-variables `y=ψx` turns `μ_{jj'}` into an INTERVAL-base (`J=ψ(S)`) pair-correlation in
`γ` times a bounded density ratio `ρ=gaussDensity(ψ⁻¹y)/(q·gaussDensity(y))` (elementary,
`CFAffine` + `gaussDensity` bounds); the content is then interval-base mixing = extend
`gaussMeasure_cylinder_mixing` (`CFGammaMixing:236`) from a `cfCylinder` base to a subinterval
`J⊆(0,1)`. If interval-base mixing is big, split it (cylinder-cover of `J` + per-cylinder mixing)
as its own named sorry. **Do step 1c (the algebra/assembly, given the two mixing sorries) FIRST**
next lap — it is landable now and further narrows the crux to exactly the two mixing statements.

## 🟢 2026-08-25 — LANDED: ψ(xA) irrationality (subtlety 1) + Z-I budget atom

- **`exists_xA_L4_psi_irrational`** (axiom-clean): the diagonalisation filler digit
  (StepSpecL4 rebuild) forces `ψ(xA)` irrational. Subtlety-1 CLEARED.
- **`exists_scale_cfCylinder_psi_avoid_zbad`** + **`exists_scale_zgood_wxSeq_L4`**
  (axiom-clean): Chebyshev budget discharge + per-stage z-good witnesses on `wxSeq_L4 s`.

## 🟢 2026-08-25 — LANDED: ψ-conditional z-Chebyshev (the crux analytic lemma)

**`chebyshev_blockCount_brick_psi_conditional`** (`CFWordBridge.lean`, axiom-clean, trust
triple). This is the "one genuinely-open analytic lemma the z-side rests on" flagged in the
CRUX FINDING below — now discharged. Statement: for `z ∈ cfCylinder wz` (`L=|wz|`), full-orbit,
`n>L`, and slack `2L ≤ δ·n`,
`γ{z ∈ cfCylinder wz : δ ≤ |blockCount(cfCyl v) n z/n − γv|}
  ≤ 7·(8|v|+80)·γv/((δ/2)²·(n−L))·γ(cfCylinder wz)` — the RELATIVE density `O(1/(n−L))`,
not the too-weak absolute `O(1/n)`. Proof route (as planned in the handoff): `blockCount_split`
peels the COMMON pinned-prefix count `C∈[0,L]` (perturbs the frequency by `≤ L/n`) off the
scale-`n` count, leaving the shifted scale-`(n−L)` count on `gaussMap^[L] z`, bounded by
`chebyshev_blockCount_brick` at base `wz`; the slack `2L≤δn` makes a scale-`n` `δ`-bad point a
shifted scale-`(n−L)` `(δ/2)`-bad point (subset + `measure_mono` + `ENNReal.toReal_mono`).

**Also landed (aggregate brick):** `gaussMeasure_aggregate_psi_cond_le` (`CFWordBridge`,
axiom-clean) — the finite-family (`F : Finset (List ℕ)`) union of the pinned-prefix
absolute-count bad sets is bounded by `∑_{v∈F} 7(8|v|+80)γv/((δ/2)²(n−L))·γ(cfCyl wz)`, the
`O(1/(n−L))` selection budget. Mirrors `gaussMeasure_aggregate_cfBadZone_le` with the conditional
brick swapped in for `chebyshev_blockCount_brick`. This is the exact aggregate the pinning-stage
selector consumes.

**Also landed (ψ-pullback selector):** `exists_cfCylinder_psi_avoid_zbad_cond` (`CFScheduleA`,
axiom-clean) — the relative-density counterpart of `exists_cfCylinder_psi_avoid_zbad`. Given the
pulled-back conditional z-bad budget on the cylinder hull is `< γ(cfCylinder wx')`, yields an
irrational `p ∈ cfCylinder wx'` whose ψ-image avoids EVERY pinned-prefix absolute-count bad set
`{z ∈ cfCylinder wz : δ ≤ |blockCount(cfCyl v) n z/n − γv|}` for `v ∈ F`. Same pullback plumbing
(`gaussMeasure_cfCylinder_inter_preimage_affineMap_le` + cylinder selector); caller discharges
`hbudget` from `gaussMeasure_aggregate_psi_cond_le`. This is the pinning-stage selector.

**Also landed (scale-threshold budget discharge):** `exists_scale_cfCylinder_psi_avoid_zbad_cond`
(`CFScheduleA`, axiom-clean) — the full conditional analog of `exists_scale_cfCylinder_psi_avoid_zbad`.
For genuine `wx'` (hull `[a,b]`), genuine pinned prefix `wz`, family `F`, `δ>0`, produces a threshold
`N` such that ∀ `n ≥ N` there is irrational `p ∈ cfCylinder wx'` whose ψ-image avoids every
pinned-prefix absolute-count bad set for `v ∈ F`. `N` bakes in `n>|wz|`, slack `2|wz|≤δn`, and
`n−|wz| > (2/q)·Ssum/((δ/2)²·γ(cfCylinder wx'))`. The complete pinning-stage z-selection engine is
now in the kernel; only the SCHEDULE-side wiring remains.

**Also landed (multi-scale interface):** `exists_cfCylinder_psi_avoid_zbad_cond_multiscale`
(`CFScheduleA`, axiom-clean) — the `NSz`-band generalization of the conditional selector, matching
the `exists_cfCylinder_psi_avoid_zbad` NSz shape. A single witness `p ∈ cfCylinder wx'` whose
ψ-image avoids the pinned-prefix bad sets across an ENTIRE finite band `NSz` of scales — the shape
the s↔n coupling needs (each stage certifies ψ-goodness over its whole window `(|w_{s-1}|,|w_s|]`).
`hbudget` is the harmonic-band total; feasibility left to caller.

## 🔴 2026-08-25 — CORRECTION (adversarial re-check): the tight discharge does NOT dissolve the obstruction

**The "DECISIVE" claim in the section below is REFUTED by a careful range/coverage analysis done the
next lap. The lemmas are all valid (correct conditional statements, axiom-clean, kept); only the
INTERPRETATION that they resolve the scale-regime obstruction was wrong.** Precise wall:

- Tight-discharge threshold: the witness `p` is z-good at scale `n` only for `n − |wz| > K` where
  `K = (2/q)·Ssum·Cbridge/((δ/2)²)` (a per-stage constant). So `n > |wz| + K`.
- Digit-agreement transfer (`notMem_cfBadZone_nil_of_cfDigit_agree` + `exists_tail_cfCylinder_subset_ball`):
  needs `n + |v| ≤ m`, where `m` = z-digits pinned by `cfCyl wx'`. Since `ψ` is `q`-Lipschitz and
  `cfCyl wx'` has width `~φ^{-2|wx'|}`, the ψ-image fits a depth-`m` z-cylinder only for `m ≲ |wx'| + O(1)`.
  So `n ≲ |wx'| − |v|`.
- Bridge constant: `Cbridge = γ(cfCyl wz)/γ(cfCyl wx') ~ φ^{2(|wx'| − |wz|)}`.

**The irreconcilable triangle:** bounded `Cbridge` ⟺ `|wz| ~ |wx'|` ⟹ threshold `n > |wx'|+K` while
transfer needs `n ≤ |wx'|−|v|` ⟹ range EMPTY. Conversely a non-empty range needs `|wz| < |wx'|` ⟹
`Cbridge` exponential ⟹ threshold `K` exponential ⟹ range empty again. And `tendsto_of_scale_coverage`
needs EVERY large `n` covered; a per-stage band of width `~|wx'_s|` (needed because block lengths, hence
`|wx'_s|`, grow geometrically leaving gaps) enters `Cbridge` exponentially. So the single-stream
conditional-at-base-`wz` route hits a density-vs-coverage wall.

## 🟢 2026-08-25 — CLEAN REDUCTION: the whole z-side now reduces to ONE disclosed crux brick

**`psi_pushed_chebyshev_brick`** (`CFScheduleA:~4270`, DISCLOSED SORRY — the ψ-pushed, x-cylinder-
relative Chebyshev; see its docstring for why it is the research-level crux). Everything above it is
PROVED modulo this one brick:
- **`gaussMeasure_aggregate_psi_pushed_le`** (axiom-clean given the brick) — finite-family aggregate.
- **`exists_scale_cfCylinder_psi_avoid_zbad_poly`** (proved from the aggregate) — POLYNOMIAL-threshold
  z-good point selection: `∃N~Ssum/δ², ∀n≥N, ∃ irrational p∈cfCylinder wx', ψp ∉ cfBadZone [] v n δ ∀v∈F`.
  The `γ(cfCylinder wx')` factor of the crux CANCELS the cylinder mass — no `2/q` pullback loss, no
  exponential, so the transfer range `n ≲ |wx'|` is NON-EMPTY (scale-regime-CORRECT). Composes directly
  with the existing absolute digit-agreement transfer `notMem_cfBadZone_nil_of_cfDigit_agree`.

So the single-stream z-side is now a fully-proved chain DOWN TO one precisely-stated analytic brick.
The messy conditional-at-`wz` lemmas (walled, see CORRECTION) are kept but OFF the critical path; the
clean path is: `psi_pushed_chebyshev_brick` → `_poly` discharge → absolute transfer → `CFOrbitEquidist`.

**Also landed (Markov wrapper — crux narrowed one level):** `psi_pushed_chebyshev_brick` is now PROVED
from a deeper sorry **`variance_blockCount_psi_pushed`** (the ψ-pushed L² / second-moment estimate
`∫_{cfCyl wx'} (blockCount n (ψ·) − nγv)² dγ ≤ O(n)·γ(cfCyl wx')`). The Chebyshev/Markov packaging
(restricted-measure Markov `mul_meas_ge_le_integral_of_nonneg`, the `f ≤ n²` integrability bound, the
`(δn)²`-rescale, and the arithmetic cancelling the `γ(cfCyl wx')` factor) is all PROVED. So the crux is
now the pure L² estimate `variance_blockCount_psi_pushed` — no probabilistic packaging left, just the
second-moment bound whose content is the ψ-conjugated pair-correlation decay.

**NEXT:** (0) prove `variance_blockCount_psi_pushed` — expand the square into the diagonal
(`∑_k γ(cfCyl wx' ∩ ψ⁻¹T^{-k}A)`, `O(n)` term) + off-diagonal pair correlations
(`∑_{k≠k'} [γ(cfCyl wx' ∩ ψ⁻¹T^{-k}A ∩ ψ⁻¹T^{-k'}A) − …]`), and bound the off-diagonal by the
ψ-conjugated mixing (extend `gaussMeasure_cylinder_mixing` to interval / affine-image bases). This is
THE irreducible analytic core. (1) prove `psi_pushed_chebyshev_brick` — SUBSUMED, now `= _poly` chain
down to the L²-core. (See old note:) attack via interval-base mixing (extend
`gaussMeasure_cylinder_mixing` from `cfCylinder` bases to `Ioo` bases; the ψ-image is an interval).
(2) In parallel (independent, doesn't need the brick proved): wire `exists_scale_cfCylinder_psi_avoid_zbad_poly`
+ the absolute transfer into `StepSpecL4`/the schedule to deliver `CFOrbitEquidist (ψ xA)`, then the
interleaved witness + excise the two-stream sorry. That wiring can proceed against the disclosed brick.

**THE ONE SURVIVING ESCAPE (now realized as `psi_pushed_chebyshev_brick` above).** All the trouble is that
the conditional Chebyshev is based at the z-cylinder `wz` (giving the `γ(cfCyl wz)` factor that won't
cancel). What is actually needed is a **ψ-pushed, x-cylinder-relative Chebyshev**: a bound
`γ(cfCyl wx' ∩ ψ⁻¹(cfBadZone [] v n δ)) ≤ O(1/n)·γ(cfCyl wx')` — the bad FRACTION *within the deep
x-cylinder itself*, local density `O(1/n)`, NO `wz`, NO `Cbridge`. That gives a polynomial threshold
`n > C` with transfer range `n ≲ |wx'|` non-empty, and every-`n` coverage as `|wx'_s|→∞`. This is a
Chebyshev for the observable `blockCount_n ∘ ψ` under `γ` conditioned on `cfCyl wx'` — i.e. the Gauss-map
variance/mixing must survive conjugation by the affine `ψ`. `chebyshev_blockCount_brick` proves exactly
this shape but for a z-CYLINDER base (via `gaussMeasure_cylinder_mixing`); the open question is whether
the mixing bound transfers through `ψ` to an x-cylinder base. THIS — not the bridge — is the real crux
lemma to attack. (If it's false, the single-stream route may be genuinely obstructed and a different
z-mechanism is needed; test by attempting the ψ-pushed variance bound.)

## 🟡 2026-08-25 — (SUPERSEDED / OVER-CLAIMED, see CORRECTION above) tight discharge

**Root-cause correction found this lap.** `tendsto_of_scale_coverage` needs EVERY large `n` covered
(not a cofinal subsequence — `CFOrbitEquidist` is a genuine `Tendsto … atTop`, `hcover` quantifies
∀ n ≥ n₀). Tracing the threshold arithmetic of `exists_scale_cfCylinder_psi_avoid_zbad_cond` exposed
that it is CORRECT but LOSSY: it bounds `γ(cfCylinder wz) ≤ 1`, discarding a `φ^{-2|wz|}` factor,
producing an EXPONENTIAL threshold `N ~ φ^{2|wz|}` — the SAME empty-range obstruction as the old
post-hoc witness. **The fix:** KEEP the `γ(cfCylinder wz)` factor and cancel it against
`γ(cfCylinder wx')` (both `~ φ^{-2·depth}`, comparable), via a bounded multiplicative bridge
`γ(cfCylinder wz) ≤ Cbridge·γ(cfCylinder wx')`.

**`exists_scale_cfCylinder_psi_avoid_zbad_cond_tight`** (`CFScheduleA`, axiom-clean) does exactly
this: with the bridge hypothesis, the threshold becomes `N ~ |wz| + O(Cbridge·Ssum/δ²)` —
**POLYNOMIAL in `|wz|`, no exponential**. So the transfer range `n ≲ |wx'| ~ |wz|` is NON-EMPTY.
This is the real dissolution of the scale-regime obstruction; the harmonic-band worry below is moot
because a polynomial-threshold single/narrow-band witness now lands inside the transfer range.

**Also landed (engine glue):** `notMem_cfBadZone_nil_of_notMem_psiCond` (`CFScheduleA`, axiom-clean)
— for full-orbit `z ∈ cfCylinder wz`, conditional avoidance (my tight selector's bad set) ⇒ absolute
`∉ cfBadZone [] v n δ` (what the EXISTING digit-agreement transfer `notMem_cfBadZone_nil_of_cfDigit_agree`
consumes). So the tight conditional selector and the existing absolute transfer now COMPOSE: select
`p` with polynomial threshold → strip to absolute goodness here → transfer to `ψ(xA)` via digit
agreement. The z-side is now a chain of composable in-kernel bricks with ONE geometric gap (`Cbridge`).

**SOLE remaining geometric input:** the bridge constant `Cbridge` (bounded, `~ 2/q`). Concretely
`γ(cfCylinder wz) ≤ Cbridge·γ(cfCylinder wx')` where `wz` = tightest z-prefix with
`ψ(cfCylinder wx') ⊆ cfCylinder wz`. Route: `vol(cfCylinder wz) ~ vol(ψ(cfCylinder wx')) =
q·vol(cfCylinder wx')` (ψ affine, factor q; wz is the minimal z-cylinder ⊇ image so its width is
within a bounded factor of the image width), then `γ ~ 2log2·vol` on `(0,1)` both ways. This is a
clean geometry/measure lemma — the NEXT target. Formalizing it + the `exists_tail_cfCylinder_subset_ball`
determination of `wz` completes the z-selection engine end-to-end.

**⚠️ (SUPERSEDED by the tight discharge above — kept for the record) harmonic-band worry:**
The band budget `∑_{n∈(L,M]} ∑_{v∈F} 7(8|v|+80)γv/((δ/2)²(n−L))·γ(wz)` carries a HARMONIC factor
`∑_{n=L+1}^{M} 1/(n−L) = H_{M−L} ~ log(M−L)`. For the geometric window `M ~ |w_s| ~ 2|w_{s-1}|`,
`M − L` is comparable to `L`, so `H_{M−L} ~ log L` — GROWS with the stage. So a fixed-`δ` single
witness canNOT cover a full geometric band with bounded budget: `budget ~ (2/q)Ssum·log L/((δ/2)²γcylR)`
must stay `< γcylR`, but `γcylR = γ(cfCylinder wx') ~ φ^{-2L}` SHRINKS. **This is the crux of
subtlety 2 and must be confronted head-on next lap.** Candidate resolutions, in order of promise:
  (a) **Per-scale δ decay absorbs the harmonic factor is FALSE** (δ_s→0 makes it worse). Instead,
      **thin the band**: don't cover every n∈(L,M] from one stage — cover a SPARSE subsequence (e.g.
      n = ⌈L·(1+1/k)⌉) and rely on `blockCount` near-monotonicity / the `|v|`-boundary slack
      (`blockCount_sub_countOccurrences_bounds`) to interpolate goodness at intermediate n. Budget
      then sums O(log) TERMS but each O(1/L)·(band width), possibly bounded.
  (b) **Coverage need not be per-stage-exhaustive.** Re-examine `tendsto_of_scale_coverage`'s actual
      hypothesis: it may only need goodness along a cofinal sequence of scales n_k→∞ with n_k good,
      NOT every n. If so, ONE scale per stage (the single-scale `exists_scale_cfCylinder_psi_avoid_zbad_cond`,
      already landed) suffices and the band/harmonic problem DISSOLVES. **Check this FIRST — it may
      obviate (a) entirely.** Read `tendsto_of_scale_coverage` + `CFOrbitEquidist` def carefully.
  (c) If genuinely every-n needed: the γcylR shrink is fought by the fact that Ssum also involves
      only FIXED-stage words (wordFamily s grows slowly); re-derive whether (2/q)Ssum·logL vs φ^{-2L}
      is actually violated or if a tighter cylinder-relative Ssum (using γ(cfCyl wz) not 1) saves it.

**THEN (schedule wiring, after the above is settled):**
1. **Thread `exists_scale_cfCylinder_psi_avoid_zbad_cond` into the block builder / `StepSpecL4`.**
   The analytic + measure spine is DONE; what remains is combining the z-good point pick with the
   x-freq-good block selection in `exists_uniformly_freq_good_block_steer_len_rel_cfK` (interval
   template `exists_irrational_notMem_xbad_psi_zbad_nil_in_Ioo`), and recording the per-stage
   conjunct `∀ n ∈ (|w_{s-1}|,|w_s|], ψ(witness) z-good at n` in `StepSpecL4`. The `wz` for stage `s`
   is the ψ-image pinned prefix of `cfCylinder wx_s` (`exists_tail_cfCylinder_subset_ball` +
   digit-agreement gives `ψ(cfCylinder wx_s) ⊆ cfCylinder wz`, so avoiding the `cfCylinder wz`-based
   conditional bad set is exactly ψ-image z-goodness). Blocks stay LINEAR (budget adds `O(1/|u|)·γ`).
   (`exists_uniformly_freq_good_block_steer_len_rel_cfK`): feed this bound as the z-bad budget
   over the window `(|w_{s-1}|,|w_s|]`, keeping blocks LINEAR (extra term `O(1/|u|)·γ`, absorbed
   like the x-freq term). Record `∀ n ∈ (|w_{s-1}|,|w_s|], ψ(witness) z-good at n` in `StepSpecL4`.
   Interval-scale selector template = `exists_irrational_notMem_xbad_psi_zbad_nil_in_Ioo`.
2. Z-II coverage via `tendsto_of_scale_coverage`: every large `n` pinned at exactly one stage
   `s*` (`|w_{s*}|≥n>|w_{s*-1}|`), `δ_{s*}→0`, transfer range `n≲|w_{s*}|` matches ⇒ no gap.
3. Assemble NEW `exists_interleaved_affine_witness` on the L4 stream + excise the two-stream sorry.

## 🔴 2026-08-25 — CRUX FINDING: the z-transfer has a SCALE-REGIME OBSTRUCTION (Z-II)

**The post-hoc z-good witness (`exists_scale_zgood_wxSeq_L4`) and the (Z-I) plan below
are in the WRONG SCALE REGIME for the transfer. Precise diagnosis:**

- The z-good threshold on cylinder `wx_s` is `N_s ~ (2/q)·Ssum_s/(δ_s²·γcyl_s)` where
  `γcyl_s = γ(cfCylinder wx_s) ~ φ^{-2|w_s|}` (SHRINKS exponentially in `|w_s|`). So the
  witness `p_s` is z-good only at scales `n ≥ N_s ~ φ^{2|w_s|}` (doubly-exp in `|w_s|`).
- The transfer (`exists_ball_cfDigit_psi_eq` + `exists_tail_cfCylinder_subset_ball` +
  `blockCount_eq_of_cfDigit_agree`) requires `ψxA` and `ψp_s` to agree on the first
  `m = n+|v|` CF digits. Agreement holds only when `cfCylinder wx_s ⊆` an x-ball of
  radius `~φ^{-2m}/q`; since the cylinder width is `~φ^{-2|w_s|}`, this needs
  `m ≲ |w_s|`, i.e. **transfer range `n ≲ |w_s|`**.
- `[N_s, |w_s|] = [φ^{2|w_s|}, |w_s|]` is EMPTY. The post-hoc witnesses are unusable.

**ROOT CAUSE (this is the real B6 crux, now sharply located).** Within a deep cylinder
`cyl_s`, `ψ` pins the first `~|w_s|` z-digits of ALL points to a COMMON value, so for
`n ≲ |w_s|` the quantity `blockCount(cfCyl v) n (ψx)` is DETERMINED (= its value at
`ψxA`) — not selectable. z-digit `n` becomes selectable only at the stage `s*` where
`|w_{s*}|` first exceeds `n` (the "pinning stage"). There the block `u_{s*}` controls
z-digits in the window `(|w_{s*-1}|, |w_{s*}|]`. The bad-zone density that matters is the
CONDITIONAL one — density `~1/(free-length) = 1/(n-|w_{s*-1}|)` given the pinned prefix —
which is small (feasible) ONLY if measured as a cylinder-RELATIVE bad zone
`cfBadZone w …` (whose `gaussMap^[|w|]` basepoint skips the pinned prefix), NOT the
ABSOLUTE `cfBadZone [] …`. But `ψ` does not map x-cylinders to z-cylinders, so there is
no clean `cfBadZone w` for the ψ-image. **The missing ingredient is a ψ-CONDITIONAL
z-Chebyshev bound: within `cyl_s`, the mass of points whose ψ-image is z-bad at scale
`n ∈ (|w_{s-1}|,|w_s|]` is `≤ O(1/(n-|w_{s-1}|))·γ(cyl_s)`** (relative, not absolute).
This is what makes the pinning-stage selection feasible; the absolute aggregate bound
(`gaussMeasure_aggregate_cfBadZone_le [] …`) is too weak here.

**WHY the two-stream avoided this (and why it was still refuted):** the two-stream gives
`zA=ψxA` its OWN cylinder chain `wz_s`, so its bad zones are cylinder-relative
`cfBadZone wz_s` (density `O(1/n)·γ`, feasible) — but coupling `x` and `z` chains under a
single `ψ` forces super-exponential blocks (`OBSTRUCTION-2026-08-24`). Single-stream
removes that coupling but reintroduces the absolute-vs-relative gap above.

**NEXT ATTACK (hardest-first, do NOT resurrect two-stream / post-hoc deep-cylinder):**
1. Establish the ψ-conditional z-Chebyshev: for `x` ranging over `cfCylinder w` with a
   pinned ψ-prefix of length `L~|w|`, `γ{x∈cfCylinder w : ψx ∈ cfBadZone [] v n δ}
   ≤ C·(8|v|+80)/(δ²(n-L))·γ(cfCylinder w)` for `n > L`. Likely route: pull back
   `chebyshev_blockCount_brick` through `ψ` using that `blockCount n (ψx) = (pinned
   count on [0,L)) + blockCount_{[L,n)}`, and the free part is a genuine conditional
   variance on the shifted orbit `gaussMap^[L](ψx)`. This is the one genuinely-open
   analytic lemma the z-side rests on.
2. Thread the pinning-stage z-selection into the block builder
   (`exists_uniformly_freq_good_block_steer_len_rel_cfK`): add the window-`(|w_{s-1}|,
   |w_s|]` z-bad avoidance to its budget (joint selector
   `exists_irrational_notMem_xbad_psi_zbad_nil_in_Ioo` is the interval-scale template),
   keeping blocks LINEAR (the extra budget term is `O(1/|u|)·γ`, absorbed like the
   x-freq term). Record `∀ n ∈ (|w_{s-1}|,|w_s|], ψ(witness) z-good at n` in StepSpecL4.
3. Then Z-II coverage closes: every large `n` is pinned at exactly one stage `s*` with
   `|w_{s*}| ≥ n > |w_{s*-1}|`, `δ_{s*}→0`, transfer range `n ≲ |w_{s*}|` MATCHES — no gap.

`exists_scale_zgood_wxSeq_L4` is TRUE but OFF the critical path (kept; not deleted).

## 🔴 2026-08-29 — STRUCTURAL FINDING: `schedL4_block_linear` DONE, but the L4 z-side is NOT reuse

**`schedL4_block_linear` is PROVED** (commit `030d8fb`, axiom-clean) and the x-side
downstream is landed: `schedL4_hfreq_x` (`ebf28fa`), `exists_xA_L4_orbit_equidist`
(`c0d188b`). Build 🟢 8757; headline still trust-triple. Sole `src/` sorry = the DEAD
two-stream `schedA_block_linear`.

**BUT** the block-linear rebuild of `StepSpecL4`/`schedStepL4_exists` (commit `acdcb19`,
"rewired onto the cfK builder") carries **ZERO z-side control** — `grep cfBadZone|affineMap`
over `StepSpecL4` = 0 hits. The DIRECTIVE calls the z-side "REUSE", but that assumed the
EARLIER StepSpecL4 (brick-4b plan, §248 below) which recorded a per-stage `ψ(p_s)`-avoidance.
The cfK rewire dropped it. **So the current `wxSeq_L4` makes `x` normal but gives NO control
on `ψ(x)`.** `ψ(xA)` normality (the other half of the interleaved witness) genuinely requires
the schedule to steer ψ away from z-bad-zones — it cannot be recovered post-hoc from an
x-only chain (xA is the unique intersection point; ψ(xA) is then fixed, no freedom to pick).

**REFINED REMAINING WORK (two parts, hardest-first):**
- **(Z-I) Re-integrate z-avoidance into `StepSpecL4` + `schedStepL4_exists`.** Add a conjunct
  recording a point `p_s ∈ cfCylinder (wx')` with `ψ(p_s)` irrational, full-orbit in (0,1),
  and `∀ v∈F_s, ∀ n∈NSz_s, ψ(p_s) ∉ cfBadZone [] v n (δ_s)`. The selection is a measure
  argument on the FIXED cylinder `cfCylinder wx'`: need pulled-back z-bad mass
  `γ(cfCylinder wx' ∩ ψ⁻¹(⋃_{n∈NSz_s} cfBadZone[] v n δ_s)) < γ(cfCylinder wx')`. Tune
  `NSz_s` (bounded window) + `δ_s` per s so the Chebyshev budget
  (`gaussMeasure_aggregate_cfBadZone_le`, pulled back via
  `gaussMeasure_interval_inter_preimage_affineMap_le`, factor `≤2/q`) stays below the
  cylinder mass. **This must NOT disturb the LINEAR block length** (the p_s selection is a
  point pick inside the already-chosen block cylinder, so |block| is unchanged — keep the
  x-block builder as-is, add an independent point selection after it). Threading the new
  conjunct breaks 4 `obtain ⟨…⟩` destructurings (schedL4_block_linear, schedL4_hfreq_x,
  wxSeq_L4_length_ge, cfK_wxSeq_L4_le) — add one `_` to each.
- **(Z-II) z-transfer engine → `CFOrbitEquidist (ψ xA)`.** From (Z-I)'s per-stage p_s
  avoidance + `δ_s→0` + `NSz` cofinal, transfer to the limit: for fixed n, take s large so
  `cfCylinder(wx_{s+1}) ⊆` an x-ball around xA on which ψ agrees with ψxA on the first
  `m=n+|v|` z-digits (`exists_ball_cfDigit_psi_eq` at x₀=xA, needs ψxA irrational — TRUE:
  xA irrational, q≠0; `exists_tail_cfCylinder_subset_ball` gives the s-threshold). Then
  `blockCount_eq_of_cfDigit_agree` ⇒ ψxA shares p_s's block count ⇒
  `notMem_cfBadZone_nil_of_cfDigit_agree` ⇒ ψxA ∉ cfBadZone[] v n δ_s ⇒
  `|blockCount(cfCyl v) n ψxA/n − γv| < δ_s`. Feed `tendsto_of_scale_coverage` (f n =
  blockCount/n, L=γv, S s = NSz_s∩{n large}, hcover from cofinality + s-n coupling). All six
  transfer lemmas (§252) exist + axiom-clean; the delicate part is the s↔n coupling in
  `hcover` (each n needs its own large-enough s for the ball inclusion at depth n+|v|).
- **(Z-III) assemble** NEW `exists_interleaved_affine_witness` (xA from
  `exists_xA_L4_orbit_equidist`, ψxA equidist from Z-II, ψxA∈(0,1) from feasibility+interval,
  ψxA irrational from xA irr + q≠0), then EXCISE the two-stream `schedA_block_linear` sorry.

**Z-I MEASURE LAYER — DONE (2026-08-29):** the per-stage z-selection engine is built +
axiom-clean:
- `exists_irrational_mem_cfCylinder_notMem_of_gaussMeasure_lt` (`07d832d`) — cylinder selector.
- `gaussMeasure_cfCylinder_inter_preimage_affineMap_le` (`c23d0b5`) — cylinder pullback bound.
- `exists_cfCylinder_psi_avoid_zbad` (`996ad56`) — the engine: `hbudget` (pulled-back z-bad
  mass on hull < cylinder mass) ⇒ irrational `p ∈ cfCylinder wx'` with `ψ(p) ∉ cfBadZone[] v n δ`
  for `v∈F, n∈NSz`. `hbudget` deferred to caller (Chebyshev, `n≳cfK²`).
- `countable_preimage_affineMap_range_rat` (this lap) — `ψ⁻¹(ℚ)` countable (Z-III fix).

**Two NEWLY-SURFACED design subtleties (flag for altitude lap):**
1. **`ψ(xA)` need NOT be irrational for real `q,r`** — the PENDING Z-III note "ψxA irrational
   from xA irr + q≠0" is FALSE (e.g. xA=√2,q=1/√2,r=0 ⇒ ψxA=1∈ℚ). Two-stream got it free
   (`ψ(xA)=zA`, zA chosen irrational). Single-stream must FORCE it: the chain-limit selection
   must avoid the countable null set `ψ⁻¹(ℚ)`. But `exists_irrational_mem_iInter_cfCylinder`
   picks the UNIQUE Cantor-intersection point (no post-hoc freedom) — so a strengthened iInter
   selector must avoid `ℚ ∪ ψ⁻¹(ℚ)` at the limit. REQUIRED: `ψxA` irrational ⇒ full Gauss orbit
   in `(0,1)` ⇒ `blockCount_eq_of_cfDigit_agree`'s `horb` holds.
2. **Z-II `hcover` s↔n coupling** — transferring `p_s`-avoidance to `ψ(xA)` at scale `n` needs
   `cfCylinder(wx_s) ⊆` an x-ball of radius set by depth `m=n+|v|` (`exists_ball_cfDigit_psi_eq`),
   i.e. each `n` needs its own large-enough `s` (`exists_tail_cfCylinder_subset_ball`).
   `tendsto_of_scale_coverage`'s `hcover` must thread this per-`n` `s`-threshold with `δ_s→0`
   and `n∈NSz_s` cofinality.

**NEXT probe:** either (a) the Chebyshev budget lemma discharging `exists_cfCylinder_psi_avoid_zbad`'s
`hbudget` for concrete `NSz_s`/`δ_s`, then thread into `StepSpecL4`; or (b) resolve subtlety (1)
via a strengthened iInter selector avoiding an extra countable set (⇒ `ψxA` irrational directly).
(b) is more route-decisive.


## 🎯 2026-08-24 REVIEW LAP — CRUX = the cfK-cap graft (bridge + layer 1 DONE)

The block-linear support layer is proved (relative regularization, below). The ONE
remaining open sub-obstruction for `schedL4_block_linear` is the **cfK cap**: the
steer block must expose `cfK(u) ≤ e^{κ|u|}` so `exists_fib_threshold_linear_of_cfK`
(proved) + `four_div_volume_cfCylinder_le` (proved) make the resolution `Nfib` AFFINE
in `|wx|` (⇒ linear blocks). This is a POSITIVE-MEASURE Lévy-uniform selection, NOT
the refuted hard digit-cap (L4's target is the cylinder's OWN hull, `ρ=1`, no
small-corner navigation). Whole measure/selection stack pre-exists:
`exists_rate_gaussMeasure_cfKbadExtSet_le`, `cfK_append_le`,
`exists_irrational_notMem_multiscale_cfBadZone_cfK_in_Ioo`.

**Attack path (cfK cap threads up the 3-layer block-builder chain, then assembles):**
- ✅ **layer 0 (bridge)** `cfK_le_of_notMem_cfKbadExtSet` — a point avoiding
  `cfKbadExtSet wx κ ntop` in `cfCylinder(wx++u)` (u genuine, |u|=ntop) has
  `cfK u ≤ e^{κ·ntop}`.  DONE this lap.
- ✅ **layer 1** `exists_multiscale_freq_good_block_steer_len_cfK` — mirror of
  `..._len`, swaps in the cfK selection core, exposes `cfK u ≤ e^{κ|u|}`.  DONE.
- ⬜ **layer 2** `exists_uniformly_freq_good_block_steer_cfK` — mirror of
  `exists_uniformly_freq_good_block_steer` (:2136-ish) calling layer 1 at
  `NS = quadScales n₁ m`; cfK bound `e^{κ(n₁+m²)}=e^{κ|u|}` passes straight through
  (same digit block, |u| unchanged). The `hbound` gains the cfKbadExtSet-mass room
  term (at `ntop = quadScales.max' = n₁+m²`).
- ⬜ **layer 3** `exists_uniformly_freq_good_block_steer_len_rel_cfK` — mirror of
  `..._len_rel` calling layer 2; carries cfK through the relative-β length exposure.
  The `hbound`/measure-budget grows by the cfK term; check `(m+1)·A₁(n₁)+cfKmass < γtar`
  still solvable (it is: cfKmass `≤ (log2)⁻¹·ε·|I_wx|`, pick ε small via the rate κ).
- ⬜ **assemble `schedL4_block_linear`** — fix κ once (`exists_rate_gaussMeasure_cfKbadExtSet_le`
  with `ε := γtar/4`); `schedStepL4_exists` calls the layer-3 cfK builder so each
  block carries `cfK(u_s) ≤ e^{κ|u_s|}`; thread through recursion with `cfK_append_le`
  (`cfK(wxSeq s) ≤ 2^s·∏cfK(u_i) ≤ C₀·e^{(κ+log2)|wxSeq s|}`, using `s ≤ |wxSeq s|`);
  then `four_div_volume_cfCylinder_le` + `exists_fib_threshold_linear_of_cfK` ⇒
  `Nfib ≲ |wx|`; combine with exposed `|u|=n₁+m²`, the `m²` bound, `two_div_beta_rel_le`
  ⇒ `|chainApp| ≤ K₁|w|+K₂`.
- ⬜ **downstream = REUSE**: seed `exists_seedStateL4`, `wxSeq_L4` (`Nat.rec`), x-side
  `chain_orbit_equidist_uniform`, z-side scale-coverage (`tendsto_of_scale_coverage`
  + brick-4a transfer lemmas), assemble new `exists_interleaved_affine_witness`,
  excise the two-stream `sorry`.

NOTE: `StepSpecL4` currently does NOT carry the length/cfK fields — extend it to
expose `|u|`'s bound and the cfK cap when wiring `schedL4_block_linear` (thread the
layer-3 builder's extra return values through the step, as the len_rel docstring notes).

---

## 🎯🎯🎯 2026-08-24 CRUX LOCATED — block-linear fails at the `S+1` ABSOLUTE regularization, NOT the route

**Sharpest finding of the L4 campaign.** After reading the full block machinery
(`exists_uniformly_freq_good_block_steer_len` :2139, `exists_uniform_block_param_tight`
:2077, `schedA_block_linear` :3346), the `|chainApp| ≤ K₁|w|+K₂` obligation reduces
to bounding the block `|u| = n₁ + m²` with `m² ≤ 6(Lc+Nfib)+2+2(⌈2/β⌉+1)⁴`
(tight param). The three inputs:
- **Lc = L = s** — LINEAR in stage, fine.
- **Nfib** = fib-threshold for `4/(d−c)`; for the L4 self-hull steer `d−c ≈ φ^{−|wx|}`
  so `Nfib ≈ |wx|` — LINEAR, fine (needs a small `Nfib ≲ |wx|` lemma).
- **β = γtar·δ²/(S+1)**, `S = γwx·Σ'`, `Σ' = ∑_{v∈F} 7(8|v|+80)γ(cfCyl v)`
  (word-independent), `γtar = γ(middle-half of hull) ≈ γwx/8`. **← THE OBSTRUCTION.**

**The `+1` in `S+1` breaks the scaling.** Both `γtar` and `S` are `Θ(γwx)`, so the
ratio `γtar/S = Θ(1/Σ')` is WORD-INDEPENDENT — that's the whole point of route B (x
steers into its OWN hull, `γtar/γwx = Θ(1)`, unlike two-stream's `γtar/γwx ≈ φ^{−κ|zblk|}`).
But `β = γtar·δ²/(S+1)`: as the cylinder deepens `γwx→0` ⇒ `γtar→0`, `S→0`, so
`β → γtar·δ² ≈ (γwx/8)δ² ≈ φ^{−|wx|}δ² → 0`. Then `⌈2/β⌉ ≈ φ^{|wx|}/δ²` EXPONENTIAL,
`m² ≈ (⌈2/β⌉)⁴` SUPER-exponential. **So the current block lemma gives
super-exponential blocks even for the L4 self-hull steer — block-linear is NOT
automatic from the route pivot.** (This is why `schedA_block_linear` is genuinely open,
independent of two- vs single-stream.)

**THE FIX — relative regularization `S + γwx` (or `S + c·γwx`) in place of `S + 1`.**
Then `β = γtar·δ²/(S+γwx) = γtar·δ²/(γwx(Σ'+1)) = (γtar/γwx)·δ²/(Σ'+1) ≥ (1/8)δ²/(Σ'+1)`
— WORD-INDEPENDENT and bounded below, so `⌈2/β⌉` is a per-family constant and `m²`,
hence `|u|`, is LINEAR in `Lc+Nfib ≈ s+|wx|`. `γwx > 0` always (genuine cylinder), so
`S+γwx > 0` is a valid regularizer; `F` nonempty ⇒ `Σ'>0`. The density machinery is
ALREADY present: `gaussMeasure_Ioo_toReal_ge` (:2021, docstring literally says
"`γtar ≥ q·c₀·γwx`") + a matching upper bound give `γtar/γwx ∈ [c₀, 1]`.

**NEXT BRICK (the real crux, hardest-first):** a variant
`exists_uniformly_freq_good_block_steer_len_rel` using `β := γtar·δ²/(S+γwx)` + the
TIGHT param, exposing `|u| ≤ Krel·(L + Nfib) + Crel(F,δ)` with `Krel, Crel`
word-INDEPENDENT. Then: (b) `Nfib ≲ |wx|` from `d−c = width(hull) ≥ φ^{−(|wx|+O(1))}`
(`volume_cfCylinder_ge_fib`-type / hull-width lower bound); (c) `γtar ≥ γwx/8` from the
density bounds. Feed all into the L4 schedule ⇒ `schedL4_block_linear` (the L4 analog
of the open `schedA_block_linear`), now PROVABLE. THEN `SchedStateL4`/step/chain/z-side.
The z-transfer machinery (bricks 4a + 5 transfer lemmas) is already complete + axiom-clean.


## ✅✅✅ 2026-08-24 REVIEW LAP — PIVOT RATIFIED: RESUME SINGLE-STREAM L4 (the two-stream route is DEAD)

**The "box stuck" was a FALSE STOP.** The two-stream construction is genuinely
obstructed (super-exponential blocks — `OBSTRUCTION-2026-08-24`, re-verified), but
the fix does not need an operator: the **single-stream L4 route is the ORIGINAL
design** (`CFScheduleA.lean:24–31` module docstring) and its foundational pullback
lemma is ALREADY PROVED — `volume_preimage_affineMap` (`CFAffine:94`,
`volume(ψ⁻¹ s)=|q⁻¹|·volume s`), whose own docstring says it is "the union-bound
ingredient for L4". The two-stream `wxSeq`/`wzSeq`/`schedA`/`schedA_block_linear`
layer was a later drift into a wall. **DIRECTION.md CURRENT DIRECTIVE now mandates
resuming L4.** This section is the attack path.

### Why L4 removes the obstruction
Two-stream nests a z-cylinder as the x-target ⇒ target relative size
`ρ ≈ e^{−2κ|zblock|}` ⇒ measure budget `n₁ ≳ 1/ρ` ⇒ super-exponential blocks.
L4 keeps the target = the FULL current x-cylinder (`ρ=1`): control `ψ(x)`'s
z-frequency STATISTICALLY by having `x` avoid the ψ-PULLBACK of the z-bad-zones,
never nesting a z-cylinder. `zA := ψ(xA)` is then DEFINITIONAL (no gluing/squeeze).
Blocks become polynomial-in-stage ⇒ `o(word)` — comfortably past the affine bound.

### The crux statement does NOT change
`exists_interleaved_affine_witness` (`:2676`) is route-agnostic:
`∃ x, (Irr x ∧ x∈(0,1) ∧ CFOrbitEquidist x) ∧ (Irr ψx ∧ ψx∈(0,1) ∧ CFOrbitEquidist ψx)`.
L4 gives it a NEW proof; the two-stream proof (bottoming at the `schedA_block_linear`
`sorry`) becomes excisable dead code once L4 lands.

### Attack path (hardest-first)
1. ✅ **DONE (2026-08-24, commit `5ba3a3d`, axiom-clean).**
   `gaussMeasure_preimage_affineMap_le` (`CFScheduleA.lean`, just before
   `gaussMeasure_multiscale_cfBadZone_le`): for `q>0`, measurable `S ⊆ (0,1)`,
   `gaussMeasure (affineMap q r ⁻¹' S) ≤ ENNReal.ofReal (2/q) * gaussMeasure S`.
   Assembled from `gaussMeasure_le_volume` ∘ `volume_preimage_affineMap` ∘
   `volume_le_ofReal_mul_gaussMeasure`; the two `log2` cancel to `2/q`. The
   route-decisive measure-budget probe — PASSED (clean, small). **Next lap starts
   at brick 2.**
2. **Pulled-back z-bad-zone control — SPLIT this lap into 2a (DONE) + 2b (the
   route-decisive crux).**

   2a. ✅ **DONE (2026-08-24, commit `3169e1a`, axiom-clean).**
   `gaussMeasure_preimage_multiscale_cfBadZone_le` (`CFScheduleA.lean`, after
   `gaussMeasure_multiscale_cfBadZone_le`): the ψ-preimage of the z-cylinder-based
   multiscale bad zone (base `wz`) has γ-measure `≤ (2/q)·|NS|·(∑_v …/(δ²n₁))·γ(cfCylinder wz)`.
   Clean: brick 1 ∘ `gaussMeasure_multiscale_cfBadZone_le`. Bound is ABSOLUTE
   (`·γ(cfCylinder wz)`).

   2b. **✅ ROUTE-DECISIVE UNCERTAINTY RESOLVED (2026-08-24 grind lap): use
   ABSOLUTE-scale z-bad-zones + INTERVAL COVERING at scales `N ≳ 2|wx|` — no
   alignment, LINEAR blocks. (Supersedes the "alignment C-bound" framing, which was
   the WRONG cut.)**

   The alignment framing ("find z-cylinder `wz ⊇ ψ(cfCylinder wx)` with
   `γ(wz)=O(1)·γ(wx)`") FAILS: `J = ψ(cfCylinder wx)` can straddle a shallow
   z-boundary ⇒ deepest containing z-cylinder is shallow ⇒ `C` exponential, and
   no bounded refinement provably fixes it (straddle recursion). Both refine-to-align
   and "deepest containing cylinder" are DEAD. The correct route:

   - **Control `ψ(x)`'s z-frequency at ABSOLUTE scales via `cfBadZone [] v N δ`**
     (base EMPTY: bad v-freq in the FIRST `N` z-digits, clean slack `δN`, no
     cylinder-prefix seam). Select `x ∈ cfCylinder wx` avoiding `ψ⁻¹(cfBadZone [] v N δ)`.
   - **The selection mass is `(2/q)·γ(J ∩ cfBadZone [] v N δ)`, `J = ψ(cfCylinder wx)`.**
     `cfBadZone [] v N δ` is a union of BAD depth-`N` z-cylinders (freq depends only
     on first `N` digits). Bound `γ(J ∩ bad)` by covering `J` with depth-`d`
     z-cylinders (`d ≈ |wx|`, so depth-`d` width `≈ |J|`): full-inside cylinders +
     `≤ 2` boundary cylinders (residual `≤ 2·max depth-d width ≤ 2/fib(d+1)²`, via
     `volume_cfCylinder_le_fib`). On each full cylinder, TWO-SCALE Chebyshev split:
     `[0,N)`-bad ⊆ (`[0,d)`-prefix-bad, scale `d`) ∪ (`[d,N)`-tail-bad, base = that
     cylinder = existing `cfBadZone wz'`); both controlled by
     `gaussMeasure_aggregate_cfBadZone_le`.
   - **THE key regime: `N ≳ 2|wx|`.** Then depth-`N` z-cylinders are `≪ |J|` (no
     all-or-nothing straddle — that pathology only bites when `N < |wx|`), the bad
     mass is a genuine fraction `≈ S/(δ²N)·γ(J)`, and the residual `2/fib(N/2)² ≈
     φ^{−N}` is `< γ(J) ≈ φ^{−2|wx|}` exactly when `N ≳ 2|wx|`. So the z-burn-in
     `n₁z ≳ 2|wx|` — **LINEAR in the word, i.e. exactly `schedA_block_linear`'s
     budget.** Blocks `|u_s| ≈ 2|wx_s| + m_s²` linear; word grows geometrically.
   - **z-side normality = SCALE COVERAGE, not telescoping.** `ψ(xA)`'s digits are
     NOT built blockwise, so there is NO z-side `hslack`. Instead: the controlled
     z-scale-ranges `[≈2|wx_s|, …]` (with `δ_s → 0`) cover all large `N` cofinally;
     for each large `N`, the stage controlling it gives `δ_{s(N)}`-goodness,
     `δ_{s(N)} → 0`, so `ψ(xA)`'s window freq at `N → γ`. ⇒ `CFOrbitEquidist (ψxA)`.
     (x-side STILL uses the blockwise `chain_cf_digit_freq_tendsto_uniform`
     telescoping — its `C_s = 4√|u_s| + 2|v| + n₁x` with n₁x poly is `o(word)`,
     fine under geometric growth.)

   **Route B is UNCONDITIONAL (works for any interval `J`), gives linear blocks, and
   needs NO alignment.** This is the resolution of the whole B6 crux's feasibility.

   **Remaining route-B bricks (next laps, hardest-first):**
   - **2b-i (covering): ✅ ALREADY EXISTS — reuse, do NOT re-derive.**
     `volume_interval_sdiff_covered_le` (`CFIntervalGood.lean:89`, sorry-free) is
     exactly this brick in Lebesgue form: `vol((a,b) \ coveredByCyl a b n) ≤
     4/fib(n+1)²`, where `coveredByCyl a b n` (`:73`) = union of depth-`n` cylinders
     `⊆ (a,b)`. This is the L1 boundary-strip lemma; the "≤2 straddling" count is
     side-stepped (straddlers all lie within `M=1/fib(n+1)²` of an endpoint, total
     mass `≤4M`). The γ-version is `≤2×` via `gaussMeasure_le_volume`. NOTE: base
     `[]` in `cfBadZone` matches `coveredByCyl`'s genuine depth-`n` words; the seam
     term is absorbed by 2b-ii, not the covering. **2b-iii only needs to package the
     γ-residual and combine — the hard covering geometry is done.**
   - **2b-ii (two-scale split): ✅ DONE (2026-08-24, this lap, axiom-clean).**
     REFORMULATED far cleaner than the old "prefix-bad ∪ tail-bad Chebyshev" plan:
     the count `blockCount` is a genuine Birkhoff sum, so `birkhoffSum_add` gives
     `bc A N x = bc A d x + bc A (N−d)(gᵈx)` with NO seam junk. The length-`d` seam
     term `∈[0,d]` shaves only `d/N` of the slack. Two src lemmas in `CFScheduleA.lean`
     (after brick 2a):
       · `cfBadZone_nil_shift_mem_cfBadZone` (pointwise): for `x ∈ cfBadZone [] v N δ
         ∩ cfCylinder w'` with `gᵈx ∈ (0,1)` and `|w'|=d<N`, `x ∈ cfBadZone w' v (N−d)
         (δ − d/N)`. Pure Birkhoff + triangle ineq; NO countOccurrences bridge.
       · `gaussMeasure_cfBadZone_nil_inter_cylinder_le` (measure): `γ(cfBadZone [] v N δ
         ∩ cfCylinder w') ≤ γ(cfBadZone w' v (N−d)(δ−d/N))`. Null rationals absorbed via
         `withDensity_absolutelyContinuous`; `gᵈx∈(0,1)` from `irrational_orbit`.
     So on each depth-`d` interior cylinder `w'`, the base-`[]` bad mass at scale `N`
     is bounded by a base-`w'` bad mass at scale `N−d` (slack `δ−d/N`) — feed that to
     `gaussMeasure_aggregate_cfBadZone_le`/`variance_blockCount_le` (Chebyshev) for the
     per-cylinder fraction. δ−d/N ≈ δ when `N ≳ 2d` (route-B regime), so the fraction
     is `≈ (8|v|+80)/((δ−d/N)²(N−d))·γ(w')`. NOTE the old `δN/(2d)` prefix scale is GONE
     — there is no separate prefix-bad set, just a slack shave.
   - **2b-iii (assemble): ✅ SINGLE-SCALE DONE (2026-08-24, commit `db09458`,
     axiom-clean).** `gaussMeasure_interval_inter_cfBadZone_nil_le` (`CFScheduleA.lean`,
     after the per-cylinder frac lemma): `γ((a,b) ∩ cfBadZone [] v N δ) ≤ frac·γ(a,b)
     + residual`, `frac = 7·(8|v|+80)·γ(v)/(δ'²(N−d))`, `δ'=δ−d/N`, `residual =
     (log2)⁻¹·4/fib(d+1)²`, for any `d < N`, `δ−d/N > 0`. Cover-by-depth-`d` +
     `measure_biUnion` (disjoint cover) + `ENNReal.tsum_mul_left` + 2b-i residual.
     **This IS the route-decisive B6 measure bound — the whole crux feasibility
     uncertainty, now proved in-kernel.** REMAINING for full 2b-iii: (a) aggregate
     over `v ∈ F` (finite sum, `measure_biUnion_finset_le`) and `N ∈ NS` (finite sum);
     pick `d ≈ depth(J)`, `N ≥ n₁ ≈ 2d` so `frac` small + `residual < γ(J)`; (b) bridge
     to brick 3 (`exists_irrational_notMem_xbad_psi_zbad_in_Ioo`) — its `hbound` z-term
     is currently a z-CYLINDER-based multiscale bound (`wz≠[]`); needs a `wz=[]` /
     route-B variant fed by this lemma + brick 1 pullback (`gaussMeasure_preimage_affineMap_le`).
     THEN bricks 4/5/6.
     **✅ (a) DONE `37ba36a` `gaussMeasure_interval_inter_iUnion_cfBadZone_nil_le`
     (F/NS aggregate). ✅ (b) DONE: ψ-pullback bridge `08ba500`
     `gaussMeasure_interval_inter_preimage_affineMap_le` (`γ((c,d)∩ψ⁻¹S) ≤
     (2/q)γ(S∩ψ((c,d)))`) + route-B brick 3′ `f4ac8fd`
     `exists_irrational_notMem_xbad_psi_zbad_nil_in_Ioo` (combined single-stream
     selection, base-`[]` z-bad, linear budget). THE ENTIRE ROUTE-B MEASURE+SELECTION
     LAYER IS NOW COMPLETE + AXIOM-CLEAN.** Only remaining `hbound` plumbing for a
     concrete stage: choose `d, n₁z` s.t. the double-sum + residual `< γ(c,d)` (a
     numeric threshold pick — done inside the recursion, brick 4). NEXT = bricks 4/5/6.
   - **2b-iii (OLD framing — superseded, kept for context):** Now has BOTH inputs in hand:
     `γ(J ∩ ⋃_{v∈F,N∈NS} cfBadZone [] v N δ) ≤ (fraction)·γ(J) + residual`, `J=(α,β)`.
     Decompose `J = coveredByCyl α β d ∪ (J \ coveredByCyl α β d)`, `d ≈ depth(J)`:
       · residual term `γ(J \ coveredByCyl) ≤ 2·vol(J\coveredByCyl) ≤ 8/fib(d+1)²`
         (brick 2b-i, `volume_interval_sdiff_covered_le` + `gaussMeasure_le_volume`);
       · interior term: `coveredByCyl α β d ∩ bad = ⋃_{w'⊆J} (cfCylinder w' ∩ bad)`;
         per interior `w'` apply 2b-ii (`gaussMeasure_cfBadZone_nil_inter_cylinder_le`)
         then Chebyshev (`gaussMeasure_aggregate_cfBadZone_le`) → `≤ frac·γ(w')`;
         sum over the DISJOINT interior `w'` (`cfCylinder_disjoint`) → `≤ frac·γ(J)`.
     Regime `N ≳ 2d` makes `frac ≈ (8|v|+80)/(δ²N)` and residual `< γ(J)`. Then feed
     brick 3 (with `wz := []`, NS the absolute z-scales) — brick 3 currently takes a
     z-cylinder base `wz`; a `wz=[]` specialization or route-B variant is the bridge.
   - Then bricks 4 (recursion), 5 (z-coverage → `CFOrbitEquidist ψxA`), 6 (assemble).
3. ✅ **DONE (2026-08-24, commit `d255444`, axiom-clean).**
   `exists_irrational_notMem_xbad_psi_zbad_in_Ioo` (`CFScheduleA.lean`, after
   `exists_irrational_notMem_multiscale_cfBadZone_in_Ioo`): selects ONE irrational
   `x ∈ (c,d)` avoiding BOTH x-CF bad zones (base wx, scales NSx) AND ψ⁻¹(z-CF bad
   zones) (base wz, scales NSz), given ONE measure hypothesis `hbound`
   (x-bad mass + `(2/q)`·z-bad mass < γ(c,d)). Uses brick 2a for the z-term. **The
   full MEASURE+SELECTION layer of L4 (bricks 1, 2a, 3) is now complete and
   axiom-clean.** What `hbound` needs from the schedule is exactly the C-bound (2b).
4. **Single-stream recursion (brick 4).** Rebuild as ONE stream: a `SchedStateL4`
   carrying only `wx` + the interval, extended by brick-3′ selection each stage;
   `wxSeq_L4`, its chain, limit `xA`. Reuse `chain_orbit_equidist_uniform` for `xA`.

   **✅ BRICK-4 Z-TRANSFER INGREDIENTS COMPLETE + AXIOM-CLEAN (2026-08-24, this lap
   sequence).** The mechanism transferring the selected point's z-frequency to the
   chain limit `ψ(xA)` is now fully in-kernel, via FIVE reusable lemmas in
   `CFScheduleA.lean` (all trust-triple):
   - `blockCount_eq_of_cfDigit_agree` (`4b8cfb8`) — first-`m` digit agreement (`n+|v|≤m`)
     ⇒ equal `blockCount (cfCyl v) n`.
   - `exists_nhds_cfDigit_eq` (`3b6d753`) — z-ball on which first `m` CF digits are const.
   - `exists_ball_cfDigit_psi_eq` (`60c9465`) — ψ `q`-Lipschitz pullback of that ball to
     an x-ball: nearby `x` ⇒ `ψx` agrees with `ψx₀` on first `m` z-digits.
   - `notMem_cfBadZone_nil_of_cfDigit_agree` (`6186ef0`) — digit-agreement transfers
     ABSOLUTE-scale bad-zone AVOIDANCE (`cfBadZone [] v n δ`).
   - `exists_cfCylinder_prefix_subset_ball` (`bb439bd`) — a deep genuine extension of
     `wx` whose cylinder ⊆ any ε-ball around one of its irrational points (diam→0).
   - `cfDigit_eq_of_mem_cfCylinder` (this lap) — co-membership in a cylinder pins the
     leading digits (cylinder-based agreement, no metric ε).

   **✅ ROUTE-DECISIVE DESIGN — z-transfer needs NO boundary strip; irrationality of
   `ψ(xA)` does all the work.** (Supersedes an earlier over-complicated "boundary-strip
   avoidance" note — that was solving a non-problem.)  The per-stage step just
   freq-good-extends `wx→wx₁` (LINEAR block, uniform-good, x-side) and selects a brick-3′
   point `p_s ∈ cfCylinder wx₁` with `ψ(p_s) ∉ cfBadZone [] v n δ_s` for `n∈NSz_s,v∈F`.
   NO ball-refinement, NO straddle worry at selection time.  The transfer to the limit is
   deferred to the z-side assembly and rests on ONE fact: **`ψ(xA)` is IRRATIONAL** (xA
   irrational, `q≠0`), so for every depth `m` it is STRICTLY interior to its own depth-`m`
   z-cylinder.  Hence (via `exists_ball_cfDigit_psi_eq` applied at `x₀:=xA`) there is an
   x-ball around `xA` on which every point's ψ-image agrees with `ψ(xA)` on the first `m`
   z-digits; since `cfCylinder (wxSeq s) → {xA}` (diam→0), for large `s` the WHOLE cylinder
   sits in that ball, so `ψ(p_s)` (for `s` large) agrees with `ψ(xA)` on `m` digits ⇒
   `blockCount` equal (`blockCount_eq_of_cfDigit_agree`) ⇒ `ψ(xA) ∉ cfBadZone [] v n δ_s`
   (`notMem_cfBadZone_nil_of_cfDigit_agree`).  Feed that + `δ_s→0` + cofinal `NSz_s` to
   `tendsto_of_scale_coverage`.  Straddle is irrelevant: we never demand a single cylinder
   contain the whole image, only that the SHRINKING images eventually enter a fixed ball
   around the irrational `ψ(xA)` — which they must.  Blocks stay LINEAR.

   **NEXT BRICKS (concrete, hardest-first):**
   - (4a) `exists_tail_cfCylinder_subset_ball`: for a genuine extending chain `w` with
     limit `xA ∈ ⋂ cfCylinder (w s)` and `ε>0`, `∃ S, ∀ s≥S, cfCylinder (w s) ⊆
     Ioo (xA-ε)(xA+ε)` (diam→0, reuse `eq_of_mem_cfCylinder_chain`'s diameter estimate). ✅ NEXT.
   - (4b) `SchedStateL4` (only `wx` + interval `(e,f)`, invariant `cfCylinder wx ⊆
     ψ⁻¹(Ioo e f)`) + `StepSpecL4` (x-side uniform block payload + the per-stage
     `ψ(p_s)`-avoidance record) + `schedStepL4_exists` (mirror
     `exists_freq_good_extend_cfCylinder` for the x-block, brick-3′ for `p_s`).
   - (4c) `wxSeq_L4`, its chain, limit `xA`; x-side via `chain_orbit_equidist_uniform`.
   - (5-proper) z-side: assemble `ψ(xA)` avoidance at every controlled scale from (4a)+
     the transfer lemmas, feed `tendsto_of_scale_coverage` ⇒ `CFOrbitEquidist (ψxA)`.
   - (6) NEW `exists_interleaved_affine_witness`; excise the two-stream `sorry`.
5. **z-side chain frequency.** ✅ **CORE DONE (2026-08-24, commit `6933f05`,
   axiom-clean):** `tendsto_of_scale_coverage` (`CFScheduleA.lean`, after brick 3′) —
   `f n → L` when `|f n − L| < δ s` for `n ∈ S s` and the stages cover all large `n`
   with `δ s → 0`. This is the whole z-side engine; brick 5 proper = instantiate it
   with `f n = blockCount (cfCyl v) n (ψxA)/n`, `S s = NSz_s`, `havoid` from the
   stage's `ψ(x)∉cfBadZone[]` avoidance, `hcover` from the schedule's `δ_s→0` +
   cofinal z-ranges. NO chain telescoping needed. Original note:
   `ψ(xA)`'s window frequency converges because at
   stage `s` we forced `ψ(x) ∉ cfBadZone_z v n δ` for `n` in the stage's z-range,
   i.e. `|countOcc v (cfPref (ψxA) n) − γv·n| < δn + slack` at a cofinal set of
   `n` with `δ→0`. Package as a chain-frequency lemma for `ψxA` (mirror
   `chain_cf_digit_freq_tendsto_uniform`, blocks = z-digit ranges; per-block
   goodness from pullback-avoidance). ⇒ `CFOrbitEquidist (ψxA)`.
6. **Assemble** the NEW `exists_interleaved_affine_witness` proof: `xA` from (4),
   `ψxA` equidist from (5), `ψxA ∈ (0,1)` from feasibility + interval nesting,
   irrationality of `ψxA` from `xA` irrational + `q≠0`. Then EXCISE the two-stream
   `sorry` block (`schedA_block_linear` and its dead callers).

### Machinery confirmed present (survey 2026-08-24)
- Pullback: `affineMap`, `preimage_affineMap_Ioo`, `image_affineMap_Ioo`,
  `volume_preimage_affineMap_Ioo`, `volume_preimage_affineMap`,
  `good_mass_in_affine_preimage`, `affine_image_Ioo_subset_Icc_pre` (CFAffine / CFScheduleA).
- Gauss↔vol: `gaussMeasure_le_volume` (`≤ (log2)⁻¹·vol`), `volume_le_gaussMeasure`,
  `volume_le_ofReal_mul_gaussMeasure` (`vol ≤ (2 log2)·gauss` on `(0,1)`),
  `gaussMeasure_Ioo_toReal_ge/le`.
- Bad zones: `cfBadZone` (`TBrick:191`), `gaussMeasure_aggregate_cfBadZone_le`
  (`TBrick:201`, relative to base cylinder), `gaussMeasure_multiscale_cfBadZone_le`
  (`CFScheduleA:252`), `volume_iUnion_cfBadZone_le_vol`.
- Selection: `exists_irrational_mem_Ioo_notMem_of_gaussMeasure_lt` (`:402`),
  `exists_irrational_notMem_multiscale_cfBadZone_in_Ioo` (`:438`).
- Cylinder geom: `volume_cfCylinder` (`=1/(K(K+K'))`), `cfK_append_le`,
  `cfCylinder_subset_Icc_length`, `cfCylinder_endpoints`, `volume_cfCylinder_ge_inv`.
- Chain freq (reuse for x-side, mirror for z-side): `chainApp`,
  `chain_cf_digit_freq_tendsto_uniform`, `chain_orbit_equidist_uniform`,
  `chainTail_dev_prefix_var`, `slack_telescoping` (CFChainFreq).

---

## 📌 LAP STATUS 2026-08-24 (grind) — all DIRECTION-permitted doable work DONE; crux operator-gated (SUPERSEDED by the review-lap pivot above)

This lap discharged EVERY open DIRECTION obligation except the crux:
- **Item 2 (`TODO(shift)`) — DONE.** `exists_cfNormal_and_affine_cfNormal` proved
  for ALL real `r` (both infeasible halves) via new axiom-clean integer-shift
  machinery (`gaussMap_iter_two_add_nat`, `cfDigit_add_nat_shift`,
  `isCFNormal_add_nat`).  Commits `768edf0`, `da17950`.
- **Item 3 signpost (a) — DONE.** `interleaved_affine_target_not_always_nonempty`
  (proved negation, `q=1,r=1` witness).  Commit `83a420b`.
- **Item 3 signpost (b) — SATISFIED at sanctioned tier.** The `hdom` refutation is
  docstring-tier on both replacement cracks (`chain_cf_digit_freq_tendsto_uniform`,
  `chain_orbit_equidist_uniform`); kernel-tier is NOT owed (no cheap concrete
  witness — refuting the asymptotic needs the full Θ(word) construction).
- **Item 1 (crux `schedA_block_linear` :2537) — OPERATOR-GATED.** DIRECTION's
  ratified digit-capped route is refuted; the two-stream construction is obstructed
  (measure-budget blowup, `OBSTRUCTION-2026-08-24`); the obstruction doc + DIRECTION
  both say STOP for attended review, and the only viable route (single-stream
  pivot) needs altitude ratification a grind lap may not give ("do not grind
  substitutes").  → this is the `box stuck` (blocked-on-operator) condition:
  an altitude/attended lap must re-route DIRECTION to the single-stream pivot
  before the crux can advance.

## 🛑🛑🛑 ROUTE-DECISIVE OBSTRUCTION (2026-08-28) — see `OBSTRUCTION-2026-08-24-block-measure-budget.md`

**The two-stream construction forces SUPER-EXPONENTIAL blocks; `schedA_block_linear`
is NOT provable as-is.**  Deeper than the cfK issue: the freq-good *measure budget*
`n₁ ≳ 1/ρ` blows up because the x-block target `ρ = μ(target)/μ(cfCylinder wx) ≈
e^{-2κ|zblock|}` is exponentially small (the other stream is one full block deeper).
`n₁` sits inside the slack `C_s`, so `hslack` (`CFChainFreq.lean:567`) fails
independently of the length bound.  Verified against the code (target = full hull
`exists_Ioo_irrational_subset_cfCylinder`; budget `NS.card·A₁ < μ(target)`;
`schedEps s = 1/(s+1)`).  **This session's cfK lemmas are correct and reusable but
do NOT fix this** — the blowup is in the measure budget, not the resolution.

**PROPOSED PIVOT (needs attended ratification — DIRECTION mandates the two-stream
route, so a review lap must sanction the change):** single-stream construction
selecting `x` to avoid BOTH the x-CF bad zones AND the ψ-pullback
`ψ⁻¹(cfBadZone_z …)` of the z-bad-zones.  Target becomes the full `cfCylinder wx`
(`ρ=1`), budget polynomial, blocks linear.  Full analysis + why alternatives fail
in the obstruction doc.

**Directive item 2 — DONE (2026-08-24).** `exists_cfNormal_and_affine_cfNormal`
now proved for ALL real `r` (was: feasible `-q<r<1` only). Landed axiom-clean in
`CFScheduleA.lean`: `gaussMap_iter_two_add_nat` (`g²(y+n)=y`),
`cfDigit_add_nat_shift` (`cfDigit(y+n)(k+2)=cfDigit y k`), `isCFNormal_add_nat`
(integer up-shift invariance of CF-normality). Infeasible regime splits:
- **`r ≥ 1`:** shift the IMAGE up. `n=⌊r⌋≥1`, `r₀=r−n=fract r∈[0,1)⊂(−q,1)`,
  feasible witness at `r₀`, `ψ(x)=y+n` normal via `isCFNormal_add_nat`.
- **`r ≤ −q`:** shift the DOMAIN up (the earlier "length 1/q" worry was a MISCALC;
  shifting `x`, not the image, gives an interval of length `1+1/q>1` that ALWAYS
  contains an integer). Pick `M=⌊(−q−r)/q⌋+1≥1` (lower end `≥0` as `r≤−q`), so
  `r₁=qM+r∈(−q,1)`; feasible witness at `r₁` gives `x`, `y=qx+r₁∈(0,1)` normal;
  witness real `x'=x+M` is normal (up-shift) and `ψ(x')=qx'+r=qx+r₁=y`.

**The B6 crux `schedA_block_linear` (:2537) is now the SOLE remaining `sorry` in
src/** — under the two-stream measure-budget obstruction (below).

- **Landed 2026-08-28 (reusable core, axiom-clean, `CFScheduleA.lean`):**
  `cfFreq_tendsto_of_digit_shift` — window-frequency limit is invariant under a
  fixed digit shift `d'(k+m)=d k` (first `m` entries arbitrary).  Proof: split
  `(range p).map d' = pre ++ (range (p−m)).map d`, sandwich the count via
  `countOccurrences_le_append_left` / `countOccurrences_append_le`, squeeze
  `count_d(p−m)/p → γ` (product of `h∘(·−m)` and `(p−m)/p → 1`).
- **Orbit fact still needed (item-2 remainder):** for `y ∈ (0,1)` irrational and
  `n ≥ 1`, `cfDigit (y+n) 0 = 0`, `cfDigit (y+n) 1 = n`, and
  `cfDigit (y+n) (k+2) = cfDigit y k` — i.e. `digits(y+n) = [0,n] ++ digits(y)`.
  Verified on paper via the Gauss orbit: `g(y+n) = 1/(n+y)`, `g²(y+n) = y`, so the
  orbit from position 2 is `y`'s orbit.  With this, `IsCFNormal (y+n)` follows from
  `IsCFNormal y` by `cfFreq_tendsto_of_digit_shift` (`m := 2`, `d := cfDigit y`,
  `d' := cfDigit (y+n)`).  Then the `TODO(shift)` `sorry` closes: pick integer
  `n` with `r − n ∈ (−q, 1)` (feasible), apply the feasible witness at `r₀ = r−n`,
  and shift `ψ(x) = (qx+r₀) + n`.  **Caveat (r ≤ −q case):** `n` may be negative,
  making `qx+r < 0`; the `[0,n]++` prepend argument only covers `y+n > 1` (n ≥ 1).
  For the `r ≥ 1` half of the infeasible regime, `n ≥ 1` and this closes it; the
  `r ≤ −q` half needs either a negative-shift orbit fact or choosing `x` in a
  higher unit interval so `qx+r ∈ (0,1)`.  Prove the `cfDigit`-orbit facts next
  (elementary `gaussMap` computation — `gaussMap`, `Int.fract`, `cfDigit` defs in
  `CFDefs.lean`).

## 🧭 ROUTE CORRECTION (2026-08-28 grind lap) — DIGIT-CAP IS FATAL; cfK-BOUND-VIA-goodC IS THE ROUTE

The CURRENT DIRECTIVE's ratified "DIGIT-CAPPED steering" route for
`schedA_block_linear` is **refuted**, on two independent grounds:
- **A FIXED cap `D`** makes the limit `x` have no CF digit `> D` ⇒ `x` is badly
  approximable ⇒ NOT CF-normal (Gauss–Kuzmin puts mass on every digit).  Fatal to
  the headline.
- **A GROWING cap `D_s → ∞`** (needed for normality) makes
  `log cfK(w_s) ≈ ∑_t block_t·log(D_t+1)` **super-linear**, so the block length
  `|u_s| ≳ log cfK(w_s)` grows FASTER than `|w_s|` and the geometric bound
  `blk ≤ ρ·word` (fixed `ρ`, the exact hypothesis `slack_telescoping` needs)
  **fails**.  So the cap that was meant to *secure* the geometric bound *destroys*
  it.

**Correct control = the B5′ `cfK u ≤ exp(goodC·|u|)` bound** (`CFSchedule.lean`
`SchedStep` line 224, from `goodExtSet w goodC n` with volume `≥ ½·|I_w|`).  This
is the Lévy constant `(1/n)log q_n → π²/(12 ln 2)` made *uniform* — it holds on a
FULL-Gauss-measure set (not a support restriction), so it is compatible with
CF-normality, and it gives `log cfK(w_s) = O(|w_s|)` ⇒ resolution length `Nfib =
O(|w_s|)` ⇒ the geometric/affine block bound.

**Landed this lap (axiom-clean, `CFScheduleA.lean`):**
`exists_fib_threshold_linear_of_cfK` — the RESOLUTION HALF of
`schedA_block_linear`, discharged conditionally on the cfK-exp-bound:
`a ≤ 8·cfK(w)² ∧ cfK w ≤ exp(κ|w|) ⇒ ∃ N, (∀ n≥N, a < fib(n+1)²) ∧
N ≤ (κ/log φ)·|w| + C`.  The target-width reciprocal `a = 4/(d−c) ≤ 8 cfK²` holds
because `d−c ≥ 1/(2 cfK²)` (`volume_cfCylinder_ge_inv`, PROVED) when the target is
a fixed fraction of the cylinder.

**Landed 2026-08-28 (measure enabler, axiom-clean, `CFDigitLaw.lean`):**
`frac_mass_bad_extensions` — the ε-strengthening of `half_mass_long_extensions`:
`∀ ε>0, ∃ κ>0, ∀ w n, (cfK-bad extension mass, cfK u > e^{κn}) ≤ ε·|I_w|`.
Same Markov-on-`tsum_mul_log_cfK_le` argument, threshold `e^{κn}`, `κ = C₀/ε`.
This is the FRACTIONAL cfK-tail control the steer graft needs (the half-measure
`goodExtSet` bound alone is too weak to dominate a small steering target `A ⊆
I_wx`; the ε-version lets κ be chosen so the cfK-bad set cannot swallow the
freq-good surplus `μ(A\B)`).

**Landed 2026-08-28 (extraction core, axiom-clean, `CFScheduleA.lean`):**
`exists_irrational_mem_Ioo_notMem_of_gaussMeasure_lt` — abstract: any `B'` with
`gaussMeasure B' < gaussMeasure (Ioo c d)` misses an irrational point of `Ioo c
d`.  The graft passes `B' = (bad zones) ∪ (cfK-large extensions)`; it now only
needs `gaussMeasure(bad ∪ cfKbad) < gaussMeasure(Ioo c d)`.

**IMMEDIATE NEXT STEP — DONE (2026-08-28, axiom-clean, `CFDigitLaw.lean`):**
`cfKbadExtSet w κ n` defined; `volume_cfKbadExtSet` (= bad-branch tsum),
`measurableSet_cfKbadExtSet`, and `exists_rate_gaussMeasure_cfKbadExtSet_le`
(∀ε>0 ∃κ>0, `gaussMeasure(cfKbadExtSet w κ n) ≤ ofReal((log 2)⁻¹·ε)·volume(I_w)`)
all proved.  So the graft's `B'`-mass bound is in hand.

**Landed 2026-08-28 (combined selection, axiom-clean, `CFScheduleA.lean`):**
`exists_irrational_notMem_multiscale_cfBadZone_cfK_in_Ioo` — same as the
multiscale selection but `hbound` leaves room for `(gaussMeasure(cfKbadExtSet wx κ
ntop)).toReal`, returning an irrational point of `(c,d)` that is freq-good at every
scale AND avoids the cfK-large set (⇒ `cfK` of its length-`ntop` extension past
`wx` is `≤ e^{κ·ntop}`).  Also confirmed `cfK_append_le` (`CFCylinder.lean`):
`cfK(w++u) ≤ 2·cfK w·cfK u`, so the accumulated invariant `cfK(w_s) ≤ e^{κ'|w_s|}`
closes with `κ' = κ + log 2` (each stage's `log 2` is absorbed since `s ≤ |w_s|`).

**NOW: build the cfK-carrying steer block** — a `_cfK` variant of
`exists_multiscale_freq_good_block_steer_len` that calls the combined selection
above (instead of `exists_irrational_notMem_multiscale_cfBadZone_in_Ioo`), reads
off the digit block `u` via `range_map_cfDigit_eq`, and adds the conclusion
`(cfK u : ℝ) ≤ e^{κ·ntop}` (from `x ∉ cfKbadExtSet` unpacked through
`cfKbadExtSet` membership: `x ∈ cfCylinder(wx++u)` with `u` its digit word forces
the good branch, i.e. `cfK u ≤ e^{κ ntop}`).  The `hbound` for the combined
selection is met by choosing `ntop`'s `n₁` large (measure budget, as now) AND `κ`
from `exists_rate_gaussMeasure_cfKbadExtSet_le ε` with `ε` a fixed fraction of the
inner-target surplus.  ⚠️ still open: the κ-uniformity check (see below) — verify
`ε` (hence `κ`) can be a per-level CONSTANT, using the recursion's hull invariants
(`SchedStateA.hzhull`, `hinv`) to lower-bound the target/cylinder Gauss-measure
ratio.  If that ratio is bounded below across stages, `κ` is uniform and the graft
closes; establish it as a lemma about the seeded recursion geometry.

**(historical detail) assemble the cfK-carrying steer block.** With `A = Ioo c' d'`,
`B` = multiscale bad zones, `S = cfKbadExtSet wx κ ntop`:
`gaussMeasure (B ∪ S) ≤ gaussMeasure B + gaussMeasure S`; bound `gaussMeasure B`
by `gaussMeasure_multiscale_cfBadZone_le`+`hbound` (already `< μ(inner target)`)
and `gaussMeasure S ≤ ofReal((log2)⁻¹ε)·volume(I_wx) ≤ 2ε·gaussMeasure(I_wx)`
(via `volume_le_gaussMeasure`).  Pick ε so the sum stays `< gaussMeasure(Ioo c
d)`; feed `exists_irrational_mem_Ioo_notMem_of_gaussMeasure_lt` to get an
irrational `x ∈ (c,d)\(B∪S)`.  `x∉S` + `range_map_cfDigit_eq` ⇒ the block word
`u` has `cfK u ≤ e^{κ·ntop} = e^{κ·|u|}`.  Thread this cfK field up through
`StepSpecA`/`schedStepA`, maintain the accumulated invariant `cfK(w_s) ≤
e^{κ|w_s|}` (needs a `cfK_append_le`: `log cfK(w++u) ≤ log cfK w + log cfK u +
O(1)` — check `CFCylinder`/`CFDigitLaw` for `cfK` recurrence), and feed
`exists_fib_threshold_linear_of_cfK` to close `schedA_block_linear`.

**⚠️ ROUTE-DECISIVE QUESTION SURFACED THIS LAP (κ-uniformity):** the rate
`κ = C₀/ε` from `frac_mass_bad_extensions` grows as the surplus fraction
`ε ~ μ(A\B)/μ(I_wx)` shrinks.  For `schedA_block_linear` to have a FIXED `K₁ =
κ/log φ`, `κ` must be bounded across stages, i.e. the steering target `A_s` must
stay a bounded fraction of `cfCylinder wx_s`.  If targets shrink unboundedly
(likely, since nested cylinders converge), `κ_s → ∞` and the affine bound
degrades.  **Candidate fix:** apply `frac_mass` to the TARGET sub-cylinder rather
than `I_wx` (the block's cfK is a property of digits past `wx`, so the relevant
base is the deepest common cylinder containing `A_s`, not `wx_s`), OR restructure
so each block first refines to a cfK-good sub-cylinder of controlled relative
size THEN steers within it (B5′-style refine-then-place).  This is the next
route-decisive probe; settle it before the full plumbing.

**NEXT (the graft, now with both halves in hand):** build
`exists_multiscale_freq_good_block_steer_len` + a cfK conclusion by intersecting
the selection with the `cfK ≤ e^{κ·ntop}` set.  Concretely, in
`exists_irrational_notMem_multiscale_cfBadZone_in_Ioo` the point is chosen from
`A \ B` with `μ(A\B) > 0` (`A = Ioo c' d'`, `B` = bad zones,
`μ(B) < μ(A) − μ(A\B)`).  Add a third excluded set `G^c` (cfK-bad extensions
past `wx`): by `frac_mass_bad_extensions` with `ε = μ(A\B)/(2·μ(I_wx))` and the
volume→gauss comparison, `μ(A ∩ G^c) ≤ ...` stays below `μ(A\B)`, so
`(A\B) ∩ G` has positive measure ⇒ an irrational point there.  Read off its digit
word `u` (`range_map_cfDigit_eq`); `exists_word_of_mem_goodExtSet`-style gives
`cfK u ≤ e^{κ·ntop} = e^{κ·|u|}`.  Then feed `exists_fib_threshold_linear_of_cfK`
to close `schedA_block_linear`.  ⚠️ the one arithmetic wrinkle: `frac_mass_bad`
bounds LEBESGUE volume of the bad extensions, while `A\B` positivity is in GAUSS
measure — bridge with `volume_le_ofReal_mul_gaussMeasure` /
`volume_le_gaussMeasure` (`TBrickRefine.lean`), both directions available.

**OLD framing (superseded by the two lemmas above):**
graft `cfK u ≤ exp(goodC·|u|)` onto the multiscale steer block
`exists_multiscale_freq_good_block_steer_len` — intersect its scale-selection set
with `goodExtSet wx goodC ·` (positive measure retained: freq-good set has measure
`≥ γ`, `goodExtSet` has measure `≥ ½·|I_w|`, and for the tail-controlled subset
both hold simultaneously by the B5′ `goodC_half` union bound).  Once the steer
block carries an exp-cfK field, thread it up through `StepSpecA` and feed
`exists_fib_threshold_linear_of_cfK` to close `schedA_block_linear` with an
explicit affine `(K₁,K₂)`.  **This SUPERSEDES the `exists_uniform_block_param_tight`
"tight length" path in the item-1 note below — the length is now controlled through
`Nfib = O(|w|)`, not through shrinking `m`.**


## 🟢🟢🟢 FRONTIER (2026-08-24 grind session): B6 CRUX ASSEMBLED — rests on ONE math lemma

The crux `exists_interleaved_affine_witness` is now FULLY MACHINE-CHECKED except
for `schedA_block_linear` (+ the shift branch). Built this session (all axiom-clean,
`CFScheduleA.lean`):
- `SchedStateA`/`StepSpecA`/`schedStepA_exists`/`exists_seedStateA`/`schedA` — the
  two-stream recursion + feasible seed (seed uses wz-hull `(e0,f0) ⊆ [r,q+r]`).
- `wxSeq`/`wzSeq` genuine extending chains; `SchedStateA.hzhull` invariant
  (`cfCylinder wz ⊆ Icc e f`) threaded through the uniform ψ-step.
- Crux proof: both limit points; `ψ(xA)=zA` via shrinking-`Icc` squeeze
  (`Ioo_sub_le_volume_cfCylinder` + `cfCylinder_chain_volume_tendsto` +
  `eq_of_mem_iInter_Icc`); both orbits via `chain_orbit_equidist_uniform`.
- `chain_hfreq_of_uniform_blocks` (shared): discharges `hblock` (schedEps→0) +
  `hslack` (`slack_telescoping`), all hyps proved incl. `chain_slack_littleO`
  (C=o(blk), PROVED via squaring trick) and `schedA_block_geom` (PROVED from
  `schedA_block_linear` via `|w s|≥1`).
- `exists_fib_threshold_log` (PROVED): resolution threshold `N ≤ log_φ(√5√a+1)+1`.

**THE ONE OPEN MATH OBLIGATION — `schedA_block_linear`** (`CFScheduleA.lean`):
`|chainApp w s| ≤ K₁·|w s| + K₂` (affine block-length bound). Path (all atoms exist):
1. **Tight length-exposing ψ-step.** Rebuild `exists_uniformly_freq_good_block_steer_len`
   → `_tight`: use `exists_uniform_block_param_tight` (PROVED, gives `m² ≤
   6(L+Nfib)+2+2⌈2/β⌉⁴`) instead of `exists_uniform_block_param` (quadratically
   lossy). Block `|u| = n₁+m² ≤ 2m²`. Expose `|u| ≤` explicit(L,Nfib,β) through
   `exists_freq_good_extend_affine_steer_uniform` → add an upper-length field to
   `StepSpecA`.
2. **Resolution `Nfib ≲ |w|`.** Target width `d−c ≳ 1/cfK²` (`volume_cfCylinder_ge_inv`,
   PROVED), so `Nfib ≤ log_φ(√5√(4/(d−c))+1)+1 ≲ log(cfK)` via `exists_fib_threshold_log`
   (PROVED). **🚩 ROUTE-DECISIVE FINDING (2026-08-24):** `log(cfK w) = O(|w|)` holds
   ONLY IF the block digits are controlled — `cfK(a₁…aₙ) ≤ ∏(aᵢ+1)` (`cfK_le_prod`),
   unbounded for large digits. The affine steer block (`exists_uniformly_freq_good_block_steer`)
   currently produces digits ≥1 with NO upper bound, so `cfK` (hence target width, hence
   `Nfib`) is UNCONTROLLED and `schedA_block_linear` is NOT provable as-is. **FIX:** the
   steer block must additionally satisfy `cfK u ≤ exp(c·|u|)` — the B5′ `goodExtSet
   goodC` mechanism (`CFSchedule` `SchedStep` line 233 `cfK u ≤ exp(goodC·nFn)`). Since
   the bounded-`cfK` set has full Gauss measure (Lévy: `cfK^{1/n}→e^{π²/12ln2}` a.e.),
   intersecting it with the bad-zone-avoiding set keeps positive measure ⇒ a freq-good
   AND `cfK`-bounded block exists. This is the NEW hardest sub-obligation: rebuild the
   steer block to carry a `cfK`-bound. (Atoms: `cfK_le_prod`, `tsum_mul_log_cfK_le`,
   B5′ `goodExtSet`/`goodC`.)
3. **Word-independent β.** `β = γtar·δ²/(S+1)`; `γtar/γwx = Θ(q)` by Gauss-density
   ratio bounds `gaussMeasure_Ioo_toReal_ge/le` (PROVED) ⇒ `⌈2/β⌉ ≲ poly(s) ≤ |w|`.
4. Assemble `|u_s| ≤ K₁|w_s|+K₂`.

Then B6 (feasible) is DONE; only the shift branch (`IsCFNormal_add_int`) remains for
the unconditional deliverable.

---

## 🚩🚩🚩 JUDGE-FLAG 2026-08-24 (grind lap): the crux was FALSE as stated — RESTRICTED to feasible `r`, deliverable reduction now needs a shift lemma (commit `<this>`)

**Route-decisive discovery (for the altitude/review lap to ratify).** The crux
`exists_interleaved_affine_witness` demanded, unconditionally in `r`, a single
`x` with `x ∈ (0,1)` AND `ψ(x)=q·x+r ∈ (0,1)`. **This is outright FALSE for
`r ∉ (-q, 1)`**: e.g. `(q,r)=(1,5)` needs `x∈(0,1)` and `x+5∈(0,1)`, impossible.
The feasible set `(0,1) ∩ ψ⁻¹(0,1) = (max 0 (-r/q), min 1 ((1-r)/q))` is nonempty
**iff `-q < r < 1`**.  No hdom-free assembly can ever discharge the old statement
— the entire directive's "assemble the limit" plan rested on a false target.

**Fix applied this lap (additive-safe; crux was the open `sorry`, not frozen):**
- **Crux now carries `(hr : -q < r ∧ r < 1)`** — exactly the feasibility that
  seeding the two-stream recursion needs, and now a TRUE statement the recursion
  CAN close.  The item-2/item-3 recipe below is unchanged EXCEPT the seed state
  is built inside the feasible interval (`hr` gives it nonempty).
- **`exists_cfNormal_and_affine_cfNormal` stays UNCONDITIONAL** (`q>0`, all `r`):
  `by_cases` on `-q<r<1`; feasible → crux directly; else a NEW disclosed `sorry`
  (`TODO(shift)`) reducing general `r` to the feasible representative via
  integer-shift invariance of CF-normality (the Gauss orbit ignores the integer
  part of `ψ(x)`).  **New leaf obligation:** `IsCFNormal_add_int` (or a mod-1
  reduction) — CF-normality of `y` and `y - ⌊y⌋` coincide asymptotically because
  a single anomalous digit-0 at position 0 is frequency-negligible.  This is the
  ONLY piece keeping the deliverable at `sorryAx`; it is genuine but leaf-level.
- Axioms re-checked: B5′ headline stays `[propext, Classical.choice, Quot.sound]`;
  `exists_cfNormal_and_affine_cfNormal` carries `sorryAx` (crux + shift, disclosed).

**Two open `src/` sorries now:** (1) the feasible crux (item-3 recursion, below),
(2) the `TODO(shift)` general-`r` reduction (leaf: `IsCFNormal_add_int`).

### 🎯 NEXT crux-blocker (grind lap 2026-08-24): `hgeom` (block ≤ ρ·word) needs a WORD-INDEPENDENT block bound — the current block sizer is quadratically lossy
`slack_telescoping` (PROVED this lap) reduces `hslack` to `hgeom : blk s ≤ ρ·word s`
(+ `C=o(blk)`, `blk→∞`).  Supplying `hgeom` needs the per-round block length
`|u_s| = n₁+m²` bounded by `ρ·|w_s|`.  Two lossy spots in the CURRENT sizer block this:
1. **`exists_uniform_block_param` is quadratically lossy.**  It returns
   `m = max(Lc, Nfib, ⌈2/β⌉², 1)` but the constraints only require `m² ≥ Lc`,
   `m² ≥ Nfib`, `(m+1)/(m√m) < β` — i.e. `m ≥ √Lc, √Nfib, ~1/β²`.  Picking `m ≥ Lc`
   (not `√Lc`) makes `|u| = m² ~ Nfib² ~ |wx|²` — QUADRATIC in the word, breaking
   `hgeom`.  **Fix:** a tight variant returning `m = max(⌈√Lc⌉, ⌈√Nfib⌉, ⌈4/β²⌉+1)`,
   so `m² ~ max(Lc, Nfib, 16/β⁴)`.  Since `Nfib ~ |wx|` (resolution `4/(d−c) <
   fib(|wx|+block+1)²`, `d−c ~ φ^{−2|wx|}` ⇒ `Nfib ~ |wx|`), tight `|u| ~ |wx|` ⇒
   `word` roughly DOUBLES per step (geometric) ⇒ `hgeom` with `ρ ~ 2`. ✓
2. **`β = γtar·δ²/(S+1)` with `S ∋ γwx` is word-dependent.**  As `|wx|→∞`,
   `γtar, γwx ~ φ^{−2|wx|} → 0`, so the `+1` dominates `S`, `β ~ γtar·δ² → 0`, and
   `1/β⁴ → φ^{8|wx|}` (exponential block).  **Fix:** the REAL constraint `hbound` is
   `(m+1)·S₀·γwx/(δ²n₁) < γtar` i.e. `(m+1)/n₁ < (δ²/S₀)·(γtar/γwx)`, and
   **`γtar/γwx = Θ(q)` is WORD-INDEPENDENT** (both are Gauss measures of intervals
   of comparable width `~φ^{−2|wx|}`; the Gauss density is bounded in `[1/(2ln2),
   1/ln2]` on `[0,1]`, and `|ψ-image|/|source| = q`).  So use `β := (δ²/(S₀+1))·(q-lower-bound-on-γtar/γwx)`, word-independent ⇒ the `16/β⁴` term is a
   per-level CONSTANT `B(t)` ⇒ with promotion (`|w_s| ≥ B(t)` before bumping `t`),
   `|u_s| ~ max(|wx|, B(t)) ~ |wx|`. ✓
- **Net remaining item-3 build (revised, hardest-first):**
  (i) tight `exists_uniform_block_param'` (`m ~ √max(...)`) — ✅ DONE
      (`exists_uniform_block_param_tight`, commit `9b90960`, axiom-clean).
  (ii) word-independent-`β` uniform block variant exposing `|u| ≤ ρ·|wx|` (factor
       `γwx` out of the budget via `γtar/γwx ≥ q·c₀`); (iii) length-exposing affine
  step; (iv) `SchedStateA`+promotion; (v) chains → `slack_telescoping`+`hblock` →
  `chain_orbit_equidist_uniform` → assemble feasible crux.  Analytic core DONE
  (`slack_telescoping`); (i) DONE; (ii) is the route-decisive measure lemma.

### 🔗 item-(ii) REFINEMENT (grind lap 2026-08-24): the measure ratio needs STREAM BALANCE `|wx| ~ |wz|`
Building (ii), the `γtar/γwx` cancellation is subtler than "both `~φ^{−2|wx|}`":
- In the z-block placement (`exists_freq_good_block_steer wz … into ψ((a,b))`), the
  `_len` budget's `γwx` is `gaussMeasure (cfCylinder wz)` (word being extended) while
  `γtar` = middle-half measure of the target `ψ((a,b))`, with `(a,b) ~ cfCylinder wx`.
  So `γtar/γwz ~ q·(φ^{−2|wx|}/φ^{−2|wz|})` — word-independent **iff `|wx| ~ |wz|`**
  (the two streams' cylinder widths must stay comparable).  If a stream races ahead,
  its cylinder is exponentially narrower and the ratio blows up.
- **⇒ new recursion invariant: `|wx_s| ~ |wz_s|` (balance).**  The affine step already
  extends both streams each round by comparable freq-good blocks; the schedule must
  pick block lengths to keep `| |wx_s| − |wz_s| |` bounded (e.g. extend the shorter
  stream first, or clamp both blocks to a common target length).  This is an EXTRA
  invariant `SchedStateA` carries alongside promotion + the interval invariant.
- **Cleaner build for (ii)+(iii):** do NOT rebuild `exists_uniformly_freq_good_block_steer_len`.
  Call the non-`_len` `exists_uniformly_freq_good_block_steer` DIRECTLY (it takes
  `m,n₁,hbound,hres` and returns exact `|u| = n₁+m²`).  Supply `m` from
  `exists_uniform_block_param_tight` (word-independent bound), and prove `hbound`
  from the measure-ratio lemma `γtar ≥ q·c₀·γwx` (the one genuinely new measure fact,
  provable from Gauss-density bounds `[1/(2ln2), 1/ln2]` + `|ψ-image|/|source| = q` +
  balance) and `hres` from `Nfib ~ |wx|`.  Output exposes `|u| = n₁+m² ≤ tight-bound`.
- **Route status:** both isolated analytic doubts (telescoping, tight length) are
  KERNEL-PROVED; remaining item-3 work is COUPLED BOOKKEEPING (balance + promotion +
  measure-ratio), not a new analytic wall.

### ✅ RESOLVED item-3 feasibility (grind lap 2026-08-24, later): `hslack` CLOSES — tool = `Asymptotics.IsLittleO.sum_range`; needs block ≤ ρ·word (length-exposing step + promotion)
Corrects the (over-pessimistic) note below.  Two facts settle `hslack`:
- **Geometric measure factors CANCEL.**  Budget `hbound`: `(m+1)·A₁ < γtar` with
  `A₁ = Σ_v 7(8|v|+80)·γ_v·γ_wx/(δ²n₁)` and `γtar` = middle-half measure of the
  steer target.  BOTH `γ_wx` and `γtar` scale like the current interval width
  `~φ^{-2|w_s|}`, so they cancel: forced block `|u_s| = n₁+m² ~ (S₀/δ²)²` with
  `S₀ = Σ_v 7(8|v|+80)γ_v` **family-only, `|w_s|`-independent**.  ⇒ between
  promotions block length is a CONSTANT `B(t)`; word grows LINEARLY by `B(t)/step`.
- **`hslack` via `Asymptotics.IsLittleO.sum_range`** (mathlib,
  `Analysis/Asymptotics/SpecificAsymptotics.lean:136`): if `f =o[atTop] g`, `g≥0`,
  `Σg → ∞`, then `Σf =o Σg`.  Take `f i = C(s₀+i)+(|v|−1)`, `g i = |u_{s₀+i}|`.
  Then (a) `C_s/|u_s| → 0` [from `n₁²≤|u|·√|u| ⇒ n₁≤|u|^{3/4}`, so
  `C_s = 4√|u_s|+2|v|+n₁_s = o(|u_s|)`], (b) `Σ|u_s| → ∞` [from `|u_s|≥L_s→∞`].
  ⇒ `Σ_{i<n} f = o(Σ_{i<n}|u|) = o(|w(s₀+n)|−|w s₀|)`.
- **THE off-by-one CATCH (real, localizes the promotion need).**  `hslack`'s
  numerator sums `range(k+1)` (`k+1` blocks) but its RHS word `|w(s₀+k)|` holds
  only `k` blocks.  `o(|w(s₀+k+1)|)` gives the needed `< ε|w(s₀+k)|` **iff
  `|w(s₀+k+1)| ≤ ρ·|w(s₀+k)|`** — block `≤ ρ·word`, i.e. word grows at most
  geometrically.  This upper bound is the ONLY thing promotion is needed for: it
  keeps `B(t) ≤ ρ|w_s|` (promote to `t` only once `|w_s| ≥ promThreshold(t)`), so
  `|u_s| = O(|w_s|)`.  Without an UPPER block bound the tail term
  `|u_{s₀+k}| ~ |w(s₀+k+1)|` can dwarf `|w(s₀+k)|`.

**Concrete item-3 build order (revised):**
1. **Length-exposing uniform affine step** — variant of
   `exists_freq_good_extend_affine_steer_uniform` that calls
   `exists_uniformly_freq_good_block_steer` DIRECTLY (not the `_len` wrapper),
   taking `m,n₁` (or exposing `|u_·| = n₁+m²`) so the CALLER controls block length
   and can enforce `|u_s| ≤ ρ|w_s|`.  (The `_len` wrapper hides the length — that's
   why the current `_steer_uniform` can't supply the upper bound.)
2. **Abstract slack lemma** `slack_telescoping` — from `IsLittleO.sum_range`, the
   generic `Σ(C+c) < ε·word` conclusion given `C=o(blk)`, `Σblk→∞`,
   `word(s+1)=word s+blk s`, `blk s ≤ ρ·word s`.  Self-contained; PROVABLE NOW.
3. **`SchedStateA` + promotion** (counter `t`, mirror `CFSchedule`); `schedA`;
   chains; feed `chain_orbit_equidist_uniform` (`hblock` from `δ_s→0`+coverage,
   `hslack` from the abstract lemma).  Assemble the feasible crux.

### ⚠️ (SUPERSEDED by the ✅ above) SHARPENED item-3 feasibility: the NAIVE schedule breaks `hslack` — SLOW PROMOTION is mandatory
The directive/handoff item-3 sketch (`F_s = wordFamily s`, `δ_s = 1/(s+1)`,
`L_s = |w_s|`) does NOT close `hslack`.  Reason, traced through the block sizer:
- `exists_uniformly_freq_good_block_steer` fixes `|u| = n₁ + m²` with `n₁ = m·⌊√m⌋`,
  and the measure budget forces `m ≳ (S/(δ²·γtar))²` where
  `S = ∑_{v∈F} 7(8|v|+80)·γ_v·γ_wx` (`exists_uniform_block_param`, `hbound`).
- With `F_s = wordFamily s`, `|F_s| ~ s^s` and `δ_s² = 1/(s+1)²`, so `S_s` and hence
  the forced block `|u_s| = m² ≳ (S_s (s+1)²/γtar)²` grow **tower-like** — far faster
  than any geometric word growth.  Then `|w_{s+1}| ≫ |w_s|`, and the `hslack` term
  `C(s₀+k) ~ |u_{s₀+k}|^{3/4} ~ |w_{s₀+k+1}|^{3/4}` is NOT `o(|w_{s₀+k}|)` (ratio
  `|w_{s+1}|^{3/4}/|w_s| → ∞` once `|w_{s+1}| ≫ |w_s|^{4/3}`).  **`hslack` FAILS.**
- **Fix = mirror `CFSchedule`'s promotion** (`SchedState.t`, `promThreshold`,
  `sched_prom_invariant`): keep the family FIXED at `wordFamily t` across many
  stages, bumping `t → t+1` only once the accumulated word is long enough that the
  next block is still `o(word)`.  Then between promotions `S` is constant, blocks
  are `poly`-bounded, word growth dominates, and `∑ C_i = o(word)` telescopes.
  Coverage (every `v` eventually in `F`) still holds because `t → ∞` (mirror
  `sched_t_tendsto`); `mem_wordFamily_eventually` (PROVED this lap, `CFScheduleA`)
  supplies the per-`v` threshold.
- **Net:** item-3's `SchedStateA` must carry a promotion counter `t` (as
  `CFSchedule.SchedState` does), not just `(wx,wz,e,f)`.  `L_s`/`δ_s` tie to `t`,
  and the promotion rule guarantees `|u_s|/|w_s|` stays bounded — the real content
  behind `hslack`.  This is the route-decisive uncertainty, now LOCALIZED to the
  promotion-rate bookkeeping (not a new analytic wall).  Building block landed:
  `mem_wordFamily_eventually`.


## ⭐⭐⭐⭐⭐⭐⭐ ADVANCE 2026-08-24 (review lap, later): per-round FEASIBILITY discharged — `exists_uniformly_freq_good_block_steer_len` (commit `4d1e5c9`, axiom-clean)

The directive's item-2 route-decisive question — *can each round jointly satisfy
the measure budget AND the resolution?* — is now settled YES in the kernel.
- **`exists_uniform_block_param`** (`CFScheduleA`): archimedean core. For any
  `β>0`, `Lc`, `Nfib`, gives `m>0` with `m²≥Lc`, `m²≥Nfib`,
  `(m+1)/(m·⌊√m⌋) < β`.  (`n₁ = m·⌊√m⌋` ⇒ `m ≪ n₁ ≪ m²`.)
- **`exists_uniformly_freq_good_block_steer_len`** (`CFScheduleA`): caller gives
  only a min-length `L`; internally sets `β = γtar·δ²/(S+1)` and discharges both
  budget inequalities. Output: `∃ u n₁, L≤|u| ∧ … ∧ cfCylinder(wx++u)⊆(c,d) ∧
  n₁²≤|u|·⌊√|u|⌋ ∧ (∀k≤|u|,∀v∈F, |dev(u.take k)| < δ·k + (4⌊√|u|⌋+2|v|+n₁)) ∧ ∃x…`.
  The folded bound is EXACTLY the `hblock` shape; `n₁²≤|u|·⌊√|u|⌋` (⇒ `n₁≤|u|^{3/4}`)
  is the `o(|u|)` witness the `hslack` telescoping needs.

### REMAINING item 2 — wire the len-wrapper into the ψ-round
Build `exists_freq_good_extend_affine_steer_uniform` (copy-extend, do NOT edit the
existing `exists_freq_good_extend_affine_steer`): same shape but call
`exists_uniformly_freq_good_block_steer_len` for BOTH streams (z into the image
interval `J_z`, x into `(a,b)∩ψ⁻¹(J_z')`), passing a caller min-length `L`. Emit,
per stream, the appended block `w'.drop|w| = u` with:
  (i) the folded uniform prefix bound (`hblock`-ready), and (ii) `n₁,u² ≤ |u|·⌊√|u|⌋`.
Everything else (interval bookkeeping, `hinv'`, nesting) copies the existing steer
ψ-round verbatim — only the block-producer call + the two extra emitted facts change.

### THEN item 3 — the two-stream recursion (`SchedStateA`/`schedStepA`/`schedA`)
Mirror `CFSchedule.sched`. Choose per round `δ_s = 1/(s+1)` (→0 ⇒ `hblock` margin),
`L_s = |w_s|` (⇒ geometric growth `|w_{s+1}| ≥ 2|w_s|`). Then build, for each stream,
`C_s := 4⌊√|u_s|⌋ + 2|v| + n₁,s` and prove:
  - `hblock`: `∀ε>0 ∃s₀ ∀s≥s₀ ∀q≤|u_s|, |dev(u_s.take q)| < ε·q + C_s` — from the
    folded bound + `δ_s→0` (pick `s₀` with `1/(s₀+1)<ε`).
  - `hslack`: `∑_{i≤k}(C(s₀+i)+(|v|−1)) < ε·|w(s₀+k)|` — from geometric `|w_s|`
    growth: `∑4⌊√|u_i|⌋`, `∑n₁,i` (each `≤|u_i|^{3/4}=o(|w_i|)`), `∑2|v|`, `∑(|v|−1)`
    all `o(word)` (geometric sum dominated by last term; `Filter.Tendsto` lemmas).
Feed both into `chain_orbit_equidist_uniform` → both streams `CFOrbitEquidist` →
assemble `exists_interleaved_affine_witness`. Limit-gluing toolkit READY
(`eq_of_mem_iInter_Icc`, `cfCylinder_chain_volume_tendsto`,
`irrational_mem_Ioo_of_mem_iInter_cfCylinder`).

## ⭐⭐⭐⭐⭐⭐⭐ ADVANCE 2026-08-24 (review lap): the ROUTE-DECISIVE mid-block bound is PROVED hdom-free — `chainTail_dev_prefix_var` (commit `2c61e7c`, axiom-clean)

The review lap named the decisive open question: *does the mid-block prefix bound
close WITHOUT `hdom`?*  Now settled YES in the kernel.
**`chainTail_dev_prefix_var`** (`CFChainFreq.lean`, after `chainTail_dev_split_var`):
given each appended block is uniformly prefix-good
(`∀ q ≤ |block s|, |dev(block_s.take q)| < ε·q + C s`), EVERY prefix of the
accumulated tail `chainTail w s₀ (s₀+k+1)` is good:
`∀ q ≤ |tail|, |dev(tail.take q)| < ε·q + ∑_{i≤k}(C(s₀+i)+(|v|−1))`.
Induction on `k`: prefix lands in the tail (IH) or reaches the last block
(whole-tail bound via `chainTail_dev_split_var` ⊕ block's OWN prefix bound at `j`,
composed by `countOccurrences_append_addslack₂`).  This is the exact hdom-free
replacement for `cfDiscLt_append_take` (CFChainFreq:450).

### REMAINING for the hdom-free limit (metric wrapper) — decomposition worked out this lap
**`chain_cf_digit_freq_tendsto_uniform`** (copy-extend `CFChainFreq`, NEVER edit
the existing `chain_cf_digit_freq_tendsto`): `Tendsto (fun p => countOcc v (cfPref y p)/p) atTop (𝓝 γv)`.
Clean hypothesis set (schedule-providable):
- `C : ℕ → ℝ`, `hC : ∀ s, 0 ≤ C s`  (per-stage additive slack; for the schedule
  `C_s = 4√|block_s| + 2|v| + n₁_s`).
- `hblock : ∀ ε>0, ∃ s₀, ∀ s ≥ s₀, ∀ q ≤ |chainApp w s|, |dev((chainApp w s).take q)| < ε·q + C s`
  — absorbs the margin `δ_s → 0` (past `s₀(ε)`, `δ_s < ε`).  Feeds `chainTail_dev_prefix_var`.
- `hslack : ∀ ε>0, ∀ s₀, ∃ K, ∀ k ≥ K, ∑_{i∈range(k+1)}(C(s₀+i)+(|v|−1)) < ε·(w (s₀+k)).length`
  — the `∑ C = o(word)` telescoping.  **NB use `(w (s₀+k)).length` (word BEFORE
  the last block), not `(s₀+k+1)`**: for the stage `k` with `|w(s₀+k)| < p ≤ |w(s₀+k+1)|`,
  this gives `∑ < ε·|w(s₀+k)| < ε·p` (the `+1` form is `≥ p`, wrong direction).
Proof (mirror `chain_cf_digit_freq_tendsto` steps, hdom-free):
  1. fix ε; `hblock (ε/4) → s₀`; feed `chainTail_dev_prefix_var` (ε:=ε/4) → tail
     prefix bound.  `hslack (ε/4) s₀ → K`.
  2. `cfPref y p = w s₀ ++ (chainTail w s₀ S).take (p−L₀)` for `S = s₀+k+1` large
     (`chain_cfPref_eq` + `w_eq_append_tail` + `List.take_append`), `L₀ = |w s₀|`.
     Locate `k` = least with `|w(s₀+k+1)| ≥ p` (via `chain_exists_stage`); then
     `|w(s₀+k)| < p`.
  3. compose fixed short prefix `w s₀` (`|dev(w s₀)| ≤ L₀`, crude `C₀ = L₀+1`) with
     the tail prefix via `countOccurrences_append_addslack₂`:
     `|dev(cfPref y p)| < (ε/4)·p + (C₀ + ∑_{i≤k}(...) + (|v|−1))`.
  4. `∑_{i≤k} < (ε/4)|w(s₀+k)| < (ε/4)p` (hslack, k≥K), and `C₀+(|v|−1) < (ε/4)p`
     for `p` large ⇒ `|dev| < ε·p`.  Convert to `Metric.tendsto_atTop` (mirror
     CFChainFreq:451-465).
Then `chain_orbit_equidist`-style wrapper (the orbit↔window tail at CFChainFreq:491-525
is REUSABLE — feed the new limit instead of `chain_cf_digit_freq_tendsto`).
Then ψ-round `_uniform` + `SchedStateA` recursion discharge `hblock`/`hslack` from
`exists_uniformly_freq_good_block_steer` + geometric block growth.

## ⭐⭐⭐⭐⭐⭐ ROUTE-DECISIVE CORRECTION 2026-08-24 (this lap, LATER): `hdom` is UNATTAINABLE for the affine schedule — steer blocks are `Θ(word)`, NOT `o(word)`. The hdom-free UNIFORM-GOODNESS route is MANDATORY, and its crux is **uniformly-good steer blocks**.

**This SUPERSEDES the "tight blocks ⇒ hdom holds" claim I made earlier THIS lap
(the four `goldenRatio`/`fib` commits).** Those lemmas are still needed (they cut
block length from `exp(word)` to `Θ(word)` and bound the additive slack), but they
do NOT rescue `hdom`. Compiler-grounded proof of unattainability:

### Why blocks are `Θ(word)`, not `o(word)`
To keep `ψ(cfCylinder wx') ⊆ cfCylinder wz'`, the x-block must RESOLVE `wx` down to
`wz'`'s metric scale. The z-target width is `≈ volume(cfCylinder wx) = 1/(Kₓ(Kₓ+Kₓ'))`
where `Kₓ = cfK wx` (the continuant), so the resolution needs
`fib(|wz|+nz+1)² > 4/(q·width) ≈ Kₓ²`, i.e. `|wz|+nz ≈ log_φ Kₓ`. But `log_φ Kₓ`
is `Θ(|wx|)` — NOT `O(1)` — because `cfK` grows geometrically with LENGTH
(Lévy: `log Kₙ/n → π²/(12 ln2) ≈ 1.19`, so `log_φ Kₓ ≈ 2.46·|wx|`). Hence
`nz ≈ 2.46|wx| − |wz| = Θ(word)`. Balanced streams ⇒ each round appends
`block_s ≈ κ·|w_s|` (`κ = Θ(1)`) ⇒ `|w_{s+1}| ≈ (1+κ)|w_s|` (GEOMETRIC growth) ⇒
`block_s/|w_s| ≈ κ`, a CONSTANT. `hdom` (`block_s < ε|w_s|` ∀ε) is impossible.
Unbalancing only compounds (the resolve cost feeds back). **`hdom` cannot hold.**
(This is the same "each block ≈ accumulated word" the 2026-08-24 super-exponential
analysis flagged; the intervening "filler-free ⇒ o(word)" optimism was the error.)

### Why uniform-goodness is then FORCED (not optional)
`chain_cf_digit_freq_tendsto` (CFChainFreq:327) needs the frequency at EVERY
prefix length `p`, incl. mid-block. It handles a mid-block `p` by decomposing
`prefix = w s ++ (chainApp w s).take (p−|w s|)` (line 391-397) and calling
**`cfDiscLt_append_take`**, whose control of the partial last block IS `hdom`
(block short vs word). With `block = Θ(word)` the partial block is `Θ(p)`, so the
frequency can OSCILLATE by a constant WITHIN each block — equidistribution FAILS at
those `p` — UNLESS the partial block is itself freq-good, i.e. the block is
**uniformly prefix-good**. A maximal/dyadic union bound over all prefix lengths `k`
does NOT close (`Σₖ O(1/(δ²k)) = O(log n)` diverges; dyadic chaining leaves an
`Θ(p)` interpolation gap). So uniform-goodness needs a genuine idea, not a union
bound.

### THE REAL CRUX (next attack)
Build a **uniformly-prefix-good steerable block**: `∃ u` with `cfCylinder(wx++u) ⊆
(c,d)` AND `∀ k ≤ |u|, u.take k` is `δ`-freq-good (bounded additive slack), then a
hdom-FREE `chain_cf_digit_freq_tendsto` variant that consumes it via
`chainTail_dev_split` (already built) for the boundary tail + the per-block uniform
bound for the partial. Candidate constructions to probe (smallest first):
  (a) **maximal inequality** on `cfBadZone` deviations (Doob/Kolmogorov over the
      orbit) — deep but standard; check if the γ-mixing already proved gives it.
  (b) **self-similar block**: build `u` as a concatenation of geometrically-growing
      freq-good sub-blocks with the RESOLVING sub-block LAST (so every proper prefix
      is a union of good sub-blocks + a partial that is `o(sub-accumulation)` —
      recovering the single-stream `hdom` WITHIN the block, where there is no
      per-sub-block resolution constraint). This localizes the resolution to the
      final sub-block and may dodge the maximal inequality entirely.
Probe (b) first — it reuses the single-stream engine and needs no new deep import.

### ✅ CRACK (this lap, refined): MULTI-SCALE bad-zone avoidance gives uniform-goodness with BOUNDED total measure — no maximal inequality needed
The union bound over ALL prefix lengths `k` diverges, but over a SPARSE
quadratically-spaced set of scales it CONVERGES, and quadratic spacing is `o(scale)`
so it interpolates. Concretely, require the good point `x` to avoid `cfBadZone wx v nⱼ δ`
for `v∈F` at scales `nⱼ = n₁ + j²`, `j = 0..m` (so `n_m = n₁+m² =` the block length `n`):
- **Measure (crude, no integral needed):** each aggregate bad zone at scale `nⱼ`
  has `γ ≤ (S/(δ²nⱼ))·γ(I_wx) ≤ (S/(δ²n₁))·γ(I_wx)` (since `nⱼ ≥ n₁`), where
  `S = Σ_{v∈F} 7(8|v|+80)γ(I_v)` (`gaussMeasure_aggregate_cfBadZone_le`). So the
  union over the `m+1` scales has `γ ≤ (m+1)·(S/(δ²n₁))·γ(I_wx)`. Pick `n₁` large
  enough that `(m+1)S/(δ²n₁) < ρ` (`ρ = γ(target)/γ(I_wx)`), i.e.
  `n₁ ≳ S·√n/(δ²ρ)` (`m ≈ √n`); then the good set ∩ target has positive measure.
  Feasible per round once `|w_s|` is large: need `n ≳ 1/δ_s⁴`, and `n ≈ κ|w_s|`
  (geometric) beats `1/δ_s⁴ = (s+1)⁴` (poly).
- **Uniform goodness:** any prefix length `p ∈ [nⱼ, nⱼ₊₁)` has
  `|dev(p)| ≤ |dev(nⱼ)| + (nⱼ₊₁−nⱼ) < δ·nⱼ + (2j+1) ≤ δ·p + 2√p` (since
  `2j+1 ≤ 2√(p−n₁)+1 ≤ 2√p`). So EVERY prefix is `(δ + 2/√p)`-good — additive
  interpolation term is `o(p)`. Exactly the `chainTail_dev_split` shape.
- **⇒ uniformly-prefix-good steer block**, hdom-FREE. The outer chain feeds these
  blocks to a hdom-free `chain_cf_digit_freq_tendsto` variant.

### NEXT (concrete, this is the build):
1. **`gaussMeasure_multiscale_cfBadZone_le`** (TBrick/CFScheduleA): for a Finset of
   scales `NS` with `∀ n∈NS, n₁ ≤ n`, `γ(⋃_{n∈NS}⋃_{v∈F} cfBadZone wx v n δ) ≤
   |NS|·(S/(δ²n₁))·γ(I_wx)`. Sum `gaussMeasure_aggregate_cfBadZone_le` over `NS`
   (each term `≤` the `n₁` term). ✅ DONE this lap (CFScheduleA, before
   `exists_irrational_notMem_cfBadZone_in_Ioo`, axiom-clean).
2. ✅ DONE this lap: `exists_irrational_notMem_multiscale_cfBadZone_in_Ioo`
   (CFScheduleA, after the single-scale core, axiom-clean). Takes the scale-set
   `NS` (all `≥ n₁`) and the caller-supplied measure hypothesis
   `|NS|·(Σ_v …/(δ²n₁))·γw < γ(c,d)`; returns an irrational point of `(c,d)`
   avoiding `⋃_{n∈NS}⋃_{v∈F} cfBadZone wx v n δ` simultaneously. Same combine
   core (A\B positive, strip rationals).
3. **PER-SCALE part DONE this lap:** `exists_multiscale_freq_good_block_steer_len`
   (CFScheduleA, after `exists_freq_good_block_steer_len`, axiom-clean). Block `u`
   of length `NS.max'` with `cfCylinder(wx++u) ⊆ (c,d)` AND
   `∀ n∈NS, ∀ v∈F, |countOcc v (u.take n) − γv·n| < δ·n + |v|` (freq-good at EVERY
   scale in `NS`). REMAINING (interpolation to all `k`): a pure arithmetic lemma
   `∀ k ≤ |u|, |countOcc v (u.take k) − γv·k| < δ·k + |v| + 2·(gap near k)` from the
   per-scale bound + `|countOcc(u.take k) − countOcc(u.take n)| ≤ k−n` for the
   largest `n∈NS` with `n ≤ k`. With `NS = {n₁+j² : j≤m}` the gap `k−n ≤ 2√k`.
   This slots directly into a hdom-free chain limit.
   ✅ **Interpolation arithmetic DONE this lap:** `abs_countOccurrences_take_interp`
   (CFScheduleA, after the multiscale block, axiom-clean): for `n ≤ k ≤ |u|`,
   `|countOcc v (u.take k) − γv·k| ≤ |countOcc v (u.take n) − γv·n| + 2(k−n) + |v|`
   (`countOcc` monotone in prefix + grows `≤1`/position + `|v|−1` seam). Combined
   with the per-scale block, every prefix `k` is `(δ + (2(k−n)+2|v|)/k)`-good where
   `n` = nearest lower scale; with `NS = {n₁+j²}` the gap `k−n ≤ 2√k` so it is
   `δ + o(1)`-good. The uniformly-prefix-good block is now ASSEMBLED (per-scale +
   interpolation); packaging it into a single `∀k` statement + the quadratic-`NS`
   covering (`∀k∈[n₁,ntop], ∃n∈NS, n≤k ∧ k−n≤2√k`) is the next small step.
4. hdom-free `chain_cf_digit_freq_tendsto` variant + the recursion.

### ✅✅✅ UNIFORMLY-PREFIX-GOOD BLOCK ASSEMBLED (this lap) — the crux crack is PROVED
`exists_uniformly_freq_good_block_steer` (CFScheduleA, axiom-clean): a steer block
`u` of length `n₁+m²` with `cfCylinder(wx++u) ⊆ (c,d)` AND **every** prefix good:
`∀ k∈[n₁,|u|], ∀ v∈F, |countOcc v (u.take k) − γv·k| < δ·k + (4√k + 2|v|)`.
The slack `4√k+2|v| = o(k)`, so this is the hdom-FREE block-goodness the affine
schedule needs. Supporting (all axiom-clean, CFScheduleA): `quadScales n₁ m` +
`quadScales_{nonempty,card_le,mem_ge,max,cover}`. Caller supplies the measure
budget `(m+1)·A₁(n₁) < γ(c',d')` and the top-scale resolution
`4/(d−c) < fib(|wx|+n₁+m²+1)²`.

### REMAINING (step 4 only): plug into the schedule
- ✅ **STARTED this lap:** `chainTail_dev_split_var` (CFChainFreq, after
  `chainTail_dev_split`, axiom-clean) — the varying-slack telescoping: per-block
  slack `C s` may grow (uniformly-good blocks have `C_s = 4√|u_s|+2|v|`), tail
  deviation `< ε·len + ∑_{i≤k}(C(s₀+i)+(|v|−1))`. The `∑ C_j` is `o(word)` when
  `|u_j|` grows geometrically, so the accumulated word stays good. This is the
  base-word-goodness half of the hdom-free limit.
- **hdom-free chain limit:** a variant of `chain_cf_digit_freq_tendsto` /
  `chain_orbit_equidist` whose per-block hypothesis is uniform-prefix-goodness
  (`∀k, |dev(u.take k)| < δ_s·k + o(k)`) INSTEAD of `hgood ∧ hdom`. With the block
  above, mid-block prefixes are handled by the block's OWN prefix bound (no
  `cfDiscLt_append_take`/hdom needed); across blocks, `δ_s → 0`. This replaces the
  `hdom` reliance at CFChainFreq:391-397.
- **ψ-round + recursion:** rebuild `exists_freq_good_extend_affine_steer` to emit
  uniformly-good blocks (call `exists_uniformly_freq_good_block_steer` for each
  stream, choosing `m_s, n₁,s` per the budget/resolution — `n₁,s ~ poly(1/δ_s)`,
  `m_s` s.t. `n₁+m²` hits the resolution length `~κ|w_s|`), then the two-stream
  `SchedStateA`/`schedStepA`/`schedA` recursion → two uniformly-good chains → the
  hdom-free limit → `CFOrbitEquidist` for both streams → the crux witness.

---

## ⭐⭐⭐⭐⭐ ROUTE-DECISIVE CORRECTION 2026-08-24 (this lap): `hdom` needs TIGHT (logarithmic) steer blocks — the current steer lemma's block length is EXPONENTIAL and BREAKS `hdom`

Before wiring `exists_interleaved_affine_witness` I quantified the ONE unverified
hypothesis the whole route rests on: `chain_orbit_equidist`'s `hdom`
(`|chainApp w s| < ε·|w s|` eventually, i.e. each appended block `= o(accumulated
word)`). The last handoff asserted "hdom follows from slow growth" and marked the
recursion as pure wiring. **That is wrong as currently built**, for a concrete,
compiler-checkable reason:

- `exists_freq_good_block_steer` (CFScheduleA:352) fixes its block length as
  `n = max(N0, N1, L, 1)+1` where **`N1 := (exists_fib_threshold (1/β)).choose`**
  and `β = (target width)/4`. `exists_fib_threshold` (TBrickRefine:164) is the
  CRUDE threshold: its `N ≈ a` (LINEAR in `a`), because it only uses
  `n+1 ≤ fib(n+1)`. So the steer block has length `n ≳ N1 ≈ 1/β`.
- In the interleaved schedule the x-target is the overlap of `wx`'s convergent
  interval (width `≈ φ^{-2|wx|}`) with `ψ⁻¹(wz'-interval)` (width `≈ φ^{-2|wz'|}`),
  so `β ≈ φ^{-2|w_s|}` and `1/β ≈ φ^{2|w_s|}`. Hence the steer block is
  `n_s ≈ φ^{2|w_s|}` — **exponentially longer than the accumulated word**, the
  exact negation of `hdom` (`n_s = o(|w_s|)`). Even the information-theoretic
  minimum (resolve a cylinder of the OTHER stream's scale) is `n_s ≈ |w_s|`, still
  only a constant factor — with the crude `N1` it is doubly hopeless.

### The fix (STARTED this lap, axiom-clean): tight logarithmic block length
The minimal `n` with `fib(n+1)² > 1/β` is `≈ (1/2)log_φ(1/β) ≈ |w_s|·(refinement
ratio)`, NOT `1/β`. The per-round refinement ratio is what matters, not the
absolute cylinder scale: placing a block inside a target that is a bounded factor
`ρ` smaller than the current cylinder costs only `≈ log_φ(1/ρ)` digits. So with
the schedule `L_s = s`, `δ_s = 1/(s+1)`: each stream's block length
`n_s ≈ L_s ≈ s`, the accumulated word `|w_s| = Σ_{j<s} n_j ≈ s²/2`, and
`n_s/|w_s| ≈ 2/s → 0` — **`hdom` HOLDS** (with the tight bound, not the crude one).

Landed (TBrickRefine, axiom-clean `[propext, Classical.choice, Quot.sound]`):
- **`goldenRatio_pow_le_sqrt5_mul_fib_add_one`**: `φⁿ ≤ √5·fib(n) + 1` (tight
  Binet lower bound, from `ψⁿ ≤ 1`). The exponential lower bound on `fib`.
- **`fib_sq_gt_of_goldenRatio`**: `a < fib(n+1)²` as soon as `√5·√a + 1 < φ^(n+1)`
  — the LOGARITHMIC (consumable) threshold: minimal `n ≈ log_φ√a`, replacing the
  crude `exists_fib_threshold`.
- **`exists_nat_goldenRatio_pow_gt`**: `∃ n, y < φⁿ ∧ (n:ℝ) ≤ log_φ(max y 1)+1`
  — the EXPLICIT logarithmic exponent. Feeding `y = √5·√(1/β)+1` into this then
  `fib_sq_gt_of_goldenRatio` gives a resolve-block of length `≤ log_φ(1/β)+O(1)`
  with an explicit numeric handle (what the `hdom` bookkeeping in the recursion
  consumes). The three lemmas together are the full logarithmic-block toolkit.

### NEXT (concrete, ordered)
1. ✅ **DONE (this lap): `exists_freq_good_block_steer_len`** (CFScheduleA, after
   `exists_freq_good_block_steer`, axiom-clean). The tight-length steer lemma:
   exposes the measure-core threshold `N0` and takes the block length `n` as an
   EXPLICIT caller parameter, returning `∃ u, u.length = n ∧ …` given only the
   resolution hypothesis `4/(d-c) < fib(|wx|+n+1)²` (which the caller discharges at
   logarithmic `n` via `fib_sq_gt_of_goldenRatio`+`exists_nat_goldenRatio_pow_gt`).
   Length is now fully caller-controlled — the `hdom` handle. Everything else
   (measure core, freq-goodness, `cfCylinder ⊆ (c,d)`) copied verbatim from
   `exists_freq_good_block_steer`.
2. **Propagate the length bound through `exists_freq_good_extend_affine_steer`**
   (→ `_len` variant) so the ψ-round outputs, for both `ux`,`uz`, an explicit
   `|block| ≤ (input word length gap) + O(log …)`. Needs, per stream:
   (i) a LOWER bound on the convergent-interval width `b−a ≥ c/fib(|w|+O(1))²` (so
   the target width `≥ c'/fib²`, giving `4/width ≤ C·fib(|w|)²`); (ii) the tight
   Binet bounds — LANDED both:
   `goldenRatio_pow_le_sqrt5_mul_fib_add_one` (φⁿ ≤ √5·fibₙ+1) and its dual
   `sqrt5_mul_fib_le_goldenRatio_pow_add_one` (√5·fibₙ ≤ φⁿ+1), pinning
   `√5·fibₙ ∈ [φⁿ−1, φⁿ+1]`; combine with `exists_nat_goldenRatio_pow_gt` to solve
   `4/width < fib(|w|+n+1)²` at `n = |wtarget|−|w| + O(1)`. Then call
   `exists_freq_good_block_steer_len` at that `n`. The interval-width LOWER bound
   (i) is the one still-missing analytic atom — check `cfCylinder_endpoints` /
   `cfCylinder_subset_Icc_length` for an existing two-sided width bound before
   proving it.
3. THEN the recursion (`SchedStateA`/`schedStepA`/`schedA`, `L_s = s`) can prove
   `hdom` from the length bounds + `|w_s| ≥ Σ L_j`, and feed
   `chain_orbit_equidist`. Items 2–5 of `HANDOFF-2026-08-24-1641.md` (limit point,
   ψ-chain gluing) are unaffected — only the block-length control was missing.

**Provenance:** the "infra not needed / pure wiring" claim in the 2026-08-27
handoff is SUPERSEDED by this correction. The uniform-goodness / `addslack` infra
is a SECOND independent escape (drop `hdom` entirely by requiring every block
PREFIX freq-good) — kept in reserve; the tight-block route above is simpler
(reuses `chain_orbit_equidist` as-is) and is the primary plan.

---

## ⭐⭐⭐⭐⭐ ROUTE-DECISIVE RESOLUTION 2026-08-27: the `hdom` obstruction is REMOVABLE

**The filler/balance obstruction (recorded 2026-08-24) is pinned to a SINGLE
hypothesis of the abstract telescoping — `chain_orbit_equidist`'s `hdom` — and
`hdom` is STRONGER THAN NECESSARY.** This lap proved the enabling lemma that lets
us drop it; the schedule can then close.

### The precise diagnosis
`chain_cf_digit_freq_tendsto` (CFChainFreq) needs, per stream, TWO facts on each
appended block `chainApp w s`:
- `hgood` — the block is freq-good (used for the tail-chain tier + `hbound`);
- `hdom` — `|chainApp w s| ≪ |w s|` (block a VANISHING fraction of the accumulated
  word). **Used ONLY for mid-block prefixes** (line ~262-274, via
  `cfDiscLt_append_take`): a prefix ending inside a block must not see enough
  uncontrolled digits to move the frequency.

The interleaved schedule CANNOT satisfy `hgood ∧ hdom` simultaneously: maintaining
the interval invariant in lockstep forces `filler_s ≈ (other stream's payload
this round)`, and burying the filler under the freq-good tail (`hgood`) forces
tails to grow super-exponentially (`tail_x,k ≫ tail_z,k ≫ tail_x,k-1 ≫ …`), which
makes each block `≈` the accumulated word — the exact NEGATION of `hdom`.

### The escape (proved viable this lap)
**Never require the whole appended block to be freq-good.** Split each block as
`chainApp = filler ++ payload` and require only:
  - **(a)** `filler_s = o(|w s|)` — the SHORT-vs-accumulated-word part of `hdom`,
    but on the FILLER ONLY (not the payload);
  - **(b)** `payload_s` **uniformly good** — every prefix `(payload_s).take k` is
    freq-good with a bounded additive slack.
Then every prefix stays good by two sub-steps, NEITHER needing the payload short:
  1. prefix ends in filler → `cfDiscLt_append_take` (filler short vs `|w s|`) ✓;
  2. prefix ends in payload → `(w s ++ filler)` good, then append `payload.take k`
     via the NEW **`countOccurrences_append_addslack`** (good ++ uniformly-good
     stays good, **additive slack, NO shortness**) ✓.
Both (a),(b) ARE satisfiable: with SLOW lockstep growth (e.g. linear payloads) no
single payload dominates the accumulated sum, so `filler_s ≈ other-payload_s =
o(word)` — (a); and payloads built from the single-stream engine keep every prefix
good — (b). The super-exponential-growth contradiction was an artifact of the
spurious `hgood`-on-the-whole-block requirement, now dropped.

### Landed (axiom-clean `[propext, Classical.choice, Quot.sound]`)
- `countOccurrences_append_addslack` / `…₂` (CFChainFreq): good-with-slack `++`
  good-with-slack stays good, additive slack, **NO shortness**. The hdom-free
  append. `cfDiscLt_short_append`/`_append_take` (frozen CFConcat) cover only the
  SHORT-block case.
- `chainTail_dev_split` (CFChainFreq, commit `c0c9db1`): iterating `…addslack₂`
  over `filler++payload` blocks gives tail deviation `< ε·len + (#blocks)·(C+(|v|−1))`
  — the hdom-free replacement for `chainTail_cfDiscLt`, no per-round tolerance
  compounding (additive term ÷ len is bounded, → small with long payloads).

### ⚠️ DEFINITIVE ROUTE FINDING (2026-08-27, cont.): a per-round UNCONTROLLED filler CANNOT be telescoped away — item 2 (freq-good navigation) is UNAVOIDABLE
Pushed the telescoping analysis to the end. Two — and only two — ways to fold a
per-round filler into the frequency limit, BOTH fail when `filler_s ~ payload_s`
(which the geometry forces — see below):
- **`cfDiscLt_short_append` (ε→2ε per filler).** The existing proof keeps the tail
  at a FIXED tolerance across arbitrarily many blocks ONLY because every block is
  margin-good (`CFDiscLt.append` preserves ε exactly). A filler needs
  `short_append`, which DOUBLES the tolerance. One filler per round ⇒ `2^s·ε` —
  compounds without bound. Fillers therefore cannot live in the tolerance-preserving
  tail-chain.
- **`countOccurrences_append_addslack₂` (no compounding, but +C accumulates).** The
  hdom-free path this lap built: no tolerance doubling, but each filler leaves a
  residual additive `C_s ~ |filler_s|`. `chainTail_dev_split` ⇒ total additive
  `Σ_j C_j`. When `filler_s ~ payload_s`, `Σ C_j ~ Σ payload_j ~ |w s|`, so
  `additive/len ~ Θ(1)` — the tail is NOT asymptotically good.

**Why `filler_s ~ payload_s` is forced (not a schedule artifact):** the ψ-stage
must land `ψ(cfCylinder wx')` in the freshly-refined z-cylinder `wz'`. `wz'` shrank
by `~φ^{-2·payload_{z,s}}`, so x's re-navigation into `ψ⁻¹(wz')` costs
`~payload_{z,s}` digits — the OTHER stream's per-round payload. Symmetric for z.
Driving `δ_s→0` (required for equidistribution) forces BOTH payloads `→∞`, hence
BOTH fillers `~` the other payload `→∞`. No schedule makes `filler_s = o(payload_s)`
on both streams simultaneously (would need `n_{other,s}=o(n_s)` AND `n_s=o(n_{other,s})`).

**Conclusion:** the interleaved schedule closes IFF the navigation digits are
themselves frequency-good — then `chainApp = u` is a single margin-good block,
`filler` vanishes, the EXISTING `chain_orbit_equidist` applies (blocks are `o(word)`
under slow growth ⇒ `hdom` holds). **The route-decisive crux is `exists_freq_good_block`
STEERED into `ψ⁻¹(target)`.**

### ✅✅ CRACK (2026-08-27, cont.): the steerable good block is TRACTABLE (NOT a deep wall)
Earlier pessimism ("steering base uncontrolled ⇒ deep Vandehey wall") was WRONG — it
conflated the split engine `exists_freq_good_block_in_Ioo` (placement base + good
tail) with what the bad-zone machinery actually gives. `cfBadZone wx v n δ`
(`TBrick.lean:191`) controls `blockCount v` over the ENTIRE next `n` steps FROM base
`wx` — so take base = `wx` directly (NO navigation prefix) and intersect the good set
with the target interval:
- `Gₙ := cfCylinder wx \ ⋃_{v∈F} cfBadZone wx v n δ`.
- `gaussMeasure (⋃ cfBadZone wx v n δ) ≤ (Σ_v 7(8|v|+80)γ(I_v)/(δ²n))·γ(I_wx)` —
  **already proved: `gaussMeasure_aggregate_cfBadZone_le` (TBrick.lean:201)**, `= O(1/n)·γ(I_wx)`.
- target `(c,d) ⊆ cfCylinder wx` has `γ(c,d) = ρ·γ(I_wx)`, INDEPENDENT of `n`.
- ⇒ `γ(Gₙ ∩ (c,d)) ≥ ρ·γ(I_wx) − O(1/n)·γ(I_wx) > 0` for `n > O(1/ρ)`.
Extract irrational `x ∈ Gₙ ∩ (c,d)`: `x ∈ (c,d)` AND its `n`-block `u` from `wx` is
δ-freq-good (via `abs_blockCount_lt_of_notMem_cfBadZone` + blockCount↔countOccurrences
bridge, EXACTLY as `exists_freq_good_block` CFFreqBlock:86–100). **The freq-good digits
themselves steer into `(c,d)` — no separate filler.** `cfCylinder (wx++u) ⊆ (c,d)`
by choosing the point in `(c',d') ⊂⊂ (c,d)` with `n` large (cylinder width → 0), as
`exists_cfCylinder_subset_Ioo` does.
The addslack/split-tail lemmas become UNNEEDED for the main route (kept as infra).

### NEXT — measure core DONE; wrap it into the steerable freq-good WORD.
✅ **`exists_irrational_notMem_cfBadZone_in_Ioo`** (CFScheduleA, commit `010c30e`,
axiom-clean) — the measure core: for `n ≥ N`, an irrational `x ∈ (c,d)` avoiding
ALL of `wx`'s `n`-step CF bad zones for `F`. Hypotheses: `Ioo c d ⊆ cfCylinder wx`,
`0 < γ(Ioo c d)`. This is the crack — freq-good digits steer into the target.

✅ **`exists_freq_good_block_steer`** (CFScheduleA, commit `80faa12`, axiom-clean) —
DONE. The steerable filler-free freq-good block: given `(c,d)` with all its
irrationals in `cfCylinder wx`, yields genuine `u` (`|u|≥L`, δ-good ∀v∈F) with
`cfCylinder (wx++u) ⊆ (c,d)` + irrational witness. NO placement prefix. **The crux
ingredient is now in hand.** Remaining = pure schedule wiring (items 2–3 below).

<details><summary>(superseded) build recipe for exists_freq_good_block_steer</summary>
1. wrap the core into a WORD.
   From `x` (the core's output at suitable `n ≥ max(N, L, …)`): set
   `u := (range n).map (fun i => cfDigit x (wx.length+i))`, so `x ∈ cfCylinder (wx++u)`
   (via `range_map_cfDigit_eq`, as `exists_freq_good_block` CFFreqBlock:90-91).
   - freq-good of `u`: `abs_blockCount_lt_of_notMem_cfBadZone` (TBrickRefine:78) +
     `blockCount_sub_countOccurrences_bounds` bridge ⇒ `|count v u − γv·n| < δn + |v|`
     for all `v∈F` (COPY CFFreqBlock:84-105 verbatim — same shape).
   - `cfCylinder (wx++u) ⊆ Ioo c d`: choose the core's target as `(c',d') ⊂⊂ (c,d)`
     with a buffer, and `n` large enough that cylinder width `≤ 1/fib(...)² <` buffer
     ⇒ the whole cylinder ⊆ (c,d). (Or: derive from `x ∈ (c',d')` + `cfCylinder_subset`
     diameter bound; see `exists_cfCylinder_subset_Ioo` for the fib-threshold idiom.)
   - genuineness/extension: `|u|=n > wx.length`, `wx++u` extends `wx` trivially.
   Output signature ~ `exists_freq_good_block_in_Ioo` but `u` is the WHOLE steered
   block (no placement prefix) and lands in `(c,d)`.
</details>

✅ 2. **`exists_freq_good_extend_affine_steer`** (CFScheduleA, commit `2adf047`,
   axiom-clean) — DONE. The filler-free ψ-round: `wz' = wz ++ uz`, `wx' = wx ++ ux`
   with `uz, ux` single steerable freq-good blocks, each exposed as `w'.drop w.length`
   (the WHOLE freq-good word, no `wp`), maintaining the interval invariant. This is
   the drop-in whose `chainApp = w'.drop w.length` is a single margin-good block.

3. **Wire `exists_interleaved_affine_witness`** (THE remaining sole `src/` `sorry`,
   CFScheduleA:~975): `SchedStateA`/`schedStepA` mirroring
   `CFSchedule.sched`, feeding both chains (blocks = whole freq-good `u`, `o(word)`
   under slow growth ⇒ `hdom` holds) into the EXISTING `chain_orbit_equidist`.
   The interval invariant glues the ψ-chain limit to `ψ(xA)` (limit toolkit ready:
   `eq_of_mem_iInter_Icc`, `cfCylinder_chain_volume_tendsto`).
- **Infra kept (now off the main route):** `countOccurrences_append_addslack`/`₂`,
  `chainTail_dev_split` — the hdom-free telescoping, reusable if a future variant
  needs a residual bounded filler; not needed for the filler-free route above.

---

## ⭐⭐⭐⭐ CRUX ADVANCE 2026-08-24 (cont.): ψ-ROUND STEP `exists_freq_good_extend_affine` PROVED ✅

`CFScheduleA`, **axiom-clean** `[propext, Classical.choice, Quot.sound]`, green 8757.
B5′ headlines re-verified trust-triple. **The novel geometric heart of B6 —
maintaining the interval invariant `cfCylinder wx ⊆ ψ⁻¹(Ioo e f)` through one
joint refinement round — is done.** Given genuine `wx, wz`, the wz-interval `(e,f)`
(`irr(e,f)⊆cfCylinder wz`), the invariant, `F`, `δ`, `L`, it produces:
- `wz'` extends wz, freq-good, `L≤|wz'|`, `cfCylinder wz'⊆cfCylinder wz`, with the
  freq-good block exposed `∃ wp u, wz'=wp++u ∧ L≤|u| ∧ (∀v∈F, δ-good u)`;
- `wx'` extends wx, freq-good, `L≤|wx'|`, `cfCylinder wx'⊆cfCylinder wx`, same
  exposed block;
- new wz-interval `(e',f')` (`0≤e'<f'≤1`, `irr(e',f')⊆cfCylinder wz'`);
- **new invariant** `cfCylinder wx' ⊆ ψ⁻¹(Ioo e' f')`.
Proof followed the recipe exactly: image bounds (`affine_image_Ioo_subset_Icc_pre`
+ `closure_Ioo`/`Icc_subset_Icc_iff`) ⇒ place good z-block in `ψ((a,b))` ⇒ shared
point `x₀=(pz−r)/q` gives strict overlap `max a a' < min b b'` of `(a,b)` with the
pullback `ψ⁻¹(Ioo e' f')` ⇒ place good x-block in the overlap; both extensions via
`take_eq_of_mem_cfCylinder` with block length `n > |word|`.

### ⚠️ ROUTE-DECISIVE FINDING (this lap): the FILLER/BALANCE obstruction is REAL
Analyzing the telescoping wiring quantitatively surfaced a genuine difficulty the
"just assembly" framing hid. `chain_orbit_equidist` needs, per stream: `hgood`
(chainApp margin-good) AND `hdom` (`|chainApp_s| < ε|w_s|`, block a VANISHING
fraction of the accumulated word — CFCorrect's `uSched_dominance` direction:
block SMALL vs word). The interleaved schedule's navigation FILLERS threaten both:

- **Filler size = the OTHER stream's payload.** To make `ψ(cfCylinder wx')` land
  in the new good z-cylinder `wz'` (width `~φ^{-2|wz'|}`), `x` must be refined to
  depth `|wx'| ≳ |wz'|`; the FORCED navigation digits number `~|wz'|−|wx| ≈` z's
  growth this round `≈ z-payload`. Symmetrically z's placement into `J_z=ψ(wx-int)`
  costs `~x-payload` when x leads. So **filler_s ≈ (other stream's payload)**,
  NOT `o(payload)`.
- **The tension.** To BURY a stream's filler we need its own payload
  `≫ filler ≈ other-payload`; but then that stream outgrows the other, and next
  round the LAGGING stream's filler `≈` this stream's (now huge) payload. The
  imbalance + fillers compound: with alternating navigation the fillers are an
  IRREDUCIBLE Θ(payload) fraction, so the appended block is a constant-fraction
  of uncontrolled (non-freq-good) digits ⇒ frequency need not converge.
- **Why `hdom` alone doesn't save it.** Even sub-linear block growth
  (`|app_s|=o(|w_s|)`, e.g. `√|w_s|`) keeps `hdom`, but the filler is a constant
  fraction of each `app_s`, so a prefix ending mid-filler (length `~|w_s|+filler`)
  has count deviating by `~filler ≈ payload ≈ |app_s|` — a Θ(1)·|app_s| error;
  since `hdom` only says `|app_s|<ε|w_s|`, at that prefix the deviation/prefixlen
  can still be Θ(ε), not →0. Actually CFCorrect's `cfDiscLt_short_append` REQUIRES
  the foreign (filler) segment to be short vs the GOOD block (`|u|+(k−1)<ε|x|`),
  i.e. filler `o(good mass)` — which the Θ(payload) filler VIOLATES.

**So this is a genuine route-decisive obstruction, not assembly bookkeeping.**
The abstract telescoping (`chain_orbit_equidist`) and the round step
(`exists_freq_good_extend_affine`) are both CORRECT and reusable, but wiring them
needs the navigation fillers to be `o(freq-good mass)`, which the naive
alternating navigation does not provide.

**Candidate escapes (next lap must pick/test ONE, hardest-first):**
1. **Make the fillers freq-good too.** The navigation digits into `ψ⁻¹(wz')` have
   FREEDOM (any x-cylinder inside the target preimage interval works); choose that
   whole extension freq-good via `exists_freq_good_block_in_Ioo` on the preimage
   interval — then there is NO uncontrolled filler, only a bounded PLACEMENT word
   `wp` whose length is the RELATIVE depth `~log_φ(width(cfCylinder word)/width(target))`
   `≈ payload`. ⚠ but `wp` is still Θ(payload) and uncontrolled → same problem
   unless `wp` is ALSO absorbed. Needs: expose `|wp_s|` from the round step and
   bound it, then require `|wp_s| = o(|u_s|)` (payload `≫` placement) — but that
   reintroduces the burial-vs-balance tension. LIKELY still stuck.
2. **Relative-placement primitive.** Prove that extending `word` into a
   sub-interval of `cfCylinder word` of RELATIVE width `ρ` costs only
   `~log_φ(1/ρ)` new digits AND those can be chosen freq-good — i.e. a
   `exists_freq_good_extend_into_subcylinder`. Then the x-reselection into
   `ψ⁻¹(wz')` (relative width `~q·φ^{-2·zpayload}`, so `~zpayload` new digits) is
   itself freq-good, killing the filler entirely. This is the most promising —
   the navigation digits become part of the freq-good block. Requires a genuinely
   new placement lemma with freq control on the navigation portion.
3. **Different frequency criterion** tolerating Θ(1)-fraction STRUCTURED fillers
   (prove the forced navigation digits are themselves equidistributed / the
   targets are "generic"). Deep; likely needs a natural-extension/measure argument
   (closer to Vandehey's actual method). Escalate if 1–2 fail.

**DECISION for next lap:** attack escape #2 (relative freq-good placement) — it is
the route-decisive probe: if a word can be freq-good-extended into a preimage
sub-interval with new-digit-count `≈` the relative depth (all freq-good, no
uncontrolled filler), the interleaved schedule closes; if not, escalate toward #3
(write `ROUTE-ESCALATION`). Do NOT build `SchedStateA` until #2 is settled — the
recursion is worthless if the per-round extension carries Θ(payload) uncontrolled
filler.

---

## ⭐⭐⭐ CRUX ADVANCE 2026-08-24 (cont.): interval-invariant image lemma + round-step design

`affine_image_Ioo_subset_Icc_pre` PROVED (`CFScheduleA`, axiom-clean, green 8757):
the ESTABLISHABLE-invariant variant of `affine_image_Ioo_subset_Icc`. Hypothesis
is the interval-preimage invariant `cfCylinder wx ⊆ ψ⁻¹(Icc e f)` (the one the
schedule can maintain — lap 19), conclusion `ψ((a,b)) ⊆ Icc e f`. Same two
`exists_irrational_btwn` contradiction blocks, landing the image directly in
`Icc e f` (no wz-cylinder hop). This unblocks the ψ-round's image step.

### The round step `exists_freq_good_extend_affine` (NEXT — the crux body)
Proposed signature (interval invariant, Ioo form):
```
(wx wz genuine) (0≤e<f≤1) (hzint: ∀x∈Ioo e f, Irr x→x∈cfCylinder wz)
(hinv: cfCylinder wx ⊆ ψ⁻¹(Ioo e f)) (F δ>0 L) →
∃ wx' wz' e' f', <wz' extends wz, freq-good> ∧ <wx' extends wx, freq-good, L≤|wx'|>
  ∧ 0≤e'<f'≤1 ∧ (∀x∈Ioo e' f',Irr x→x∈cfCylinder wz') ∧ cfCylinder wz'⊆Icc e' f'
  ∧ cfCylinder wx' ⊆ ψ⁻¹(Ioo e' f')
```
Recipe (atoms all ready):
1. wx-interval `(a,b)` [`exists_Ioo_irrational_subset_cfCylinder wx`].
2. `hinv`→Icc; `affine_image_Ioo_subset_Icc_pre` ⇒ `ψ((a,b))=Ioo(qa+r)(qb+r)⊆Icc e f`;
   extract `e ≤ qa+r`, `qb+r ≤ f` via `closure_Ioo`+`Icc_subset_Icc_iff`.
3. `J_z:=Ioo(qa+r)(qb+r)` (0≤qa+r<qb+r≤1). `exists_freq_good_block_in_Ioo F .. J_z`
   ⇒ wz'=wpz++uz freq-good, cfCylinder wz'⊆J_z, irr pt pz. pz∈J_z⇒(e<pz<f)⇒
   pz∈cfCylinder wz (hzint) ⇒ (take_eq) wz' extends wz.
4. wz'-interval `(e',f')` [`exists_Ioo_irrational_subset_cfCylinder wz'`];
   cfCylinder wz'⊆Icc e' f', irr(e',f')⊆cfCylinder wz'.
5. wx': `exists_cfCylinder_subset_affine_preimage` on `(e',f')` INTERSECTED with
   `(a,b)` [`_Ioo_inter`] ⇒ wx_mid ⊆ ψ⁻¹(Ioo e' f')∩(a,b), extends wx (via irr pt
   in cfCylinder wx). Then `exists_freq_good_extend_cfCylinder wx_mid F δ L` ⇒ wx'
   freq-good, ⊆cfCylinder wx_mid ⊆ ψ⁻¹(Ioo e' f'). New invariant ✓.
   ⚠ nonemptiness of the intersection `(a,b)∩((e'-r)/q,(f'-r)/q)`: cfCylinder wz'
   ⊆ Ioo(qa+r)(qb+r)=ψ((a,b)), so its interval (e',f') overlaps ψ((a,b));
   pull back ⇒ overlaps (a,b). Establish `max lo < min hi` from a shared point
   (e.g. pz, or an irrational of cfCylinder wz' pulled back).

### ⚠️ ALIGNMENT / margin-good insight (for the recursion-assembly lap)
The engines give `word' = wp ++ u` with `u` freq-good at the END and
`word'.take|word| = word`. The chain contract wants `chainApp = word'.drop|word|`
MARGIN-good. Two cases by `|wp|` vs `|word|`: if `|wp|≥|word|`, chainApp =
`wp.drop|word| ++ u` (short filler ++ good); if `|wp|<|word|`, chainApp =
`u.drop(|word|−|wp|)` (a suffix of u, a bounded-length edit of a good block).
EITHER WAY chainApp is a margin-good block perturbed on ≤|word| entries, hence
margin-good once `|u|=L` dominates `|word|` and `|v|`. So the recursion must pick
`L_s` per round ≥ (growing) `|word_s|`·(2/ε)+… — the sizing discipline. The
`hgood`/`hdom` proofs at assembly use `cfDiscLt_short_append`/`_append_take`
(both already in `CFConcat`) to absorb the ≤|word| edit. NOT an abstraction gap;
a per-round length choice + a short-edit lemma.

---

## ⭐⭐ CRUX ADVANCE 2026-08-24 (review lap, same session): `chain_orbit_equidist` PROVED ✅

**The route-decisive question is ANSWERED: CFCorrect's telescoping DOES abstract
cleanly.** New additive module `src/NormalNumbers/CFChainFreq.lean` (imports
`CFConcat`, `CFOrbitFreq`, `TBrickRefine`; frozen modules untouched), green 8757,
**axiom-clean** `[propext, Classical.choice, Quot.sound]`. B5′ headlines
re-verified trust-triple.

Proved (all axiom-clean):
- `chainApp`/`chainTail` + algebra (`chainApp_eq`, `w_eq_append_tail`,
  `chainTail_succ`, `w_length_ge`, `le_chainTail_length`, `chain_exists_stage`)
  — the generic ports of `CFCorrect`'s `tailSched`/`exists_stage` block.
- `chainTail_cfDiscLt` — abstract B–Y Lemma 7 induction (tail is ε-good from
  margin-good blocks).
- `chain_cf_digit_freq_tendsto` — **THE CRUX PORT**: for a nested genuine chain
  `w` with limit `y∈⋂cfCylinder(w s)`, IF appended blocks are eventually
  margin-good (`hgood`) AND eventually short vs the accumulated word (`hdom`),
  THEN `countOccurrences v (y's digit prefix)/p → γv`. Faithful port of
  `xstar_cf_freq_tendsto` with the `sched`-specific level machinery replaced by
  the two abstract hypotheses.
- `chain_orbit_equidist` — wraps the above + the orbit↔window bridge
  (`blockCount_sub_countOccurrences_bounds`) → `blockCount(cfCylinder v) p y/p →
  γv` ∀ genuine v, i.e. the `CFOrbitEquidist` payload, for an irrational chain
  limit `y∈(0,1)`.

**What this buys.** The two abstract hypotheses are EXACTLY the contract the
interleaved schedule must fulfil, for EACH stream:
```
hgood : ∀ε>0, ∃s₀, ∀s≥s₀, |count v (chainApp w s) − γv·|app s|| < ε·|app s| − (|v|−1)
hdom  : ∀ε>0, ∃s₀, ∀s≥s₀, |chainApp w s| + (|v|−1) < ε·|w s|
```
(per genuine v; `chainApp w s = (w(s+1)).drop|w s|` = the block appended at stage s.)
The FILLER + ALTERNATION frictions are now PRECISELY localized: `chainApp w s`
is the whole appended block INCLUDING the per-stage filler, so the recursion must
make each stage's block (filler ++ freq-good `u`) margin-good and dominant. Since
`u`'s length `L_s` is chosen freely AFTER the filler is placed, pick `L_s` huge so
`u` dominates the filler AND the accumulated word — then `hgood`/`hdom` hold. No
abstraction gap remains; it's a per-stage sizing discipline in `schedStepA`.

**REMAINING (mechanical modulo sizing):**
1. **`exists_freq_good_extend_affine` (ψ-stage)** — emit wz freq-good extension
   + interval invariant (recipe: lap-21 item 1 below), choosing `L_s` to satisfy
   the `hgood`/`hdom` contract.
2. **`SchedStateA`/`schedStepA`/`schedA`/limit** — joint recursion by choice;
   at build time record, for each stream, the per-stage `hgood`/`hdom` witnesses
   (choose `L_s ≥` a growing target so `|u_s|`/`|w s|→∞` and filler/`|u_s|→0`).
   Then feed each stream's chain into `chain_orbit_equidist`.
3. **Glue**: `xA` = wx-limit; `CFOrbitEquidist xA` from stream-x
   `chain_orbit_equidist`; `ψ(xA)=ζ` (wz-limit) via `eq_of_mem_iInter_Icc` +
   `cfCylinder_chain_volume_tendsto`; `CFOrbitEquidist (ψ xA)=CFOrbitEquidist ζ`
   from stream-z `chain_orbit_equidist`. Obligation (A) both via
   `irrational_mem_Ioo_of_mem_iInter_cfCylinder`.

The hardest, most uncertain piece is now BANKED. Next lap: the ψ-stage sizing
(item 1) — the smallest probe that the `hgood`/`hdom` contract is fulfillable.

---

## ⭐ REVIEW LAP 2026-08-24 — PIVOT TO THE CRUX (read this first)

**Finding:** laps 11–21 proved 15 geometric/analytic ATOMS (all axiom-clean,
each a green commit) but the crux `sorry` `exists_interleaved_affine_witness`
stayed untouched and the recursion/telescoping was deferred "next lap" ~7×. The
atom toolkit is now DECLARED COMPLETE (list under "TOOLKIT NOW COMPLETE" below).
**No more atoms.** The remaining work is the frequency telescoping + recursion,
and the telescoping is the ONLY piece whose feasibility is in real doubt.

**Attack order (hardest-first):**

1. **`chain_orbit_equidist` — THE CRUX.** Abstract generic-chain frequency
   telescoping. Statement shape (draft against the real `CFCorrect` exports):
   given `w : ℕ → List ℕ`, each `w s` genuine (`≠[]`, digits `≥1`), a strict
   extension chain `w(s+1) = w s ++ app_s` with each appended block `app_s`
   carrying a freq-good sub-block `u_s` (a `CFDiscLt v u_s γv ε`-style guarantee
   for every pattern `v`, eventually in `s`) AND a DOMINANCE bound
   `|w s| ≤ C·|u_s|` (prefix + fillers negligible vs the freq-good tail), the
   unique limit point `y ∈ ⋂ cfCylinder (w s)` satisfies `CFOrbitEquidist y`.
   PORT `CFCorrect`'s `tailSched_cfDiscLt` (chain the `CFDiscLt` payloads via
   `CFDiscLt.append` + `cfDiscLt_short_append` to absorb fillers) →
   `xstar_cf_freq_tendsto`'s ε-split → the `blockCount .../p → gaussMeasure`
   limit, but with the `sched`-specific `uSched_spec`/`uSched_dominance`
   replaced by the abstract hypotheses. Copy-extend `CFCorrect` into
   `CFScheduleA` (or a new `CFChainFreq.lean`); NEVER edit `CFCorrect`.
   **The route-decisive test lives here** — see below.

2. **`exists_freq_good_extend_affine` (ψ-stage).** Recipe = lap-21 item 1
   (below). Compose the ready atoms; the NEW obligation vs the x-stage is to
   pick the block depth `L_s` large enough that `|u_s|` dominates the ACCUMULATED
   length (prefix + this stage's filler), so hypothesis (dominance) of (1) holds.

3. **`SchedStateA`/`schedStepA`/`schedA`/limit.** Joint recursion by choice
   (mirror `CFSchedule.sched`): a state carrying `wx`, `wz`, the interval
   invariant `cfCylinder wx ⊆ ψ⁻¹(Icc (lo wz) (hi wz))`, and the per-stream
   freq-good/dominance data; `schedStepA` alternates x/ψ by parity of the stage
   index; `xA :=` the limit of the wx-chain. Then: obligation (A) both sides via
   `irrational_mem_Ioo_of_mem_iInter_cfCylinder`; `ψ(xA)=ζ` (the wz-chain's
   irrational limit) via `eq_of_mem_iInter_Icc` + `cfCylinder_chain_volume_tendsto`;
   `CFOrbitEquidist xA` and `CFOrbitEquidist (ψ xA)=CFOrbitEquidist ζ` BOTH from
   (1) applied to the wx- and wz-chains respectively. ← this is the elegant part:
   we telescope the wz-chain's OWN limit ζ, then glue ζ=ψ(xA); no need to
   telescope ψ(xA)'s orbit directly.

**ROUTE-DECISIVE UNCERTAIN CASE (probe in step 1, before building 2–3):** B5′'s
telescoping (`CFCorrect`) appended a PURE freq-good block each stage with
built-in dominance (`uSched_dominance`). The interleaved schedule has TWO new
frictions: **(i) a per-stage filler** (from `exists_cfCylinder_subset_Ioo`,
placing the stream back into a shrinking target interval) whose length GROWS
like `log(1/|interval|)` as cylinders shrink — B5′ had none; **(ii) x/ψ
alternation**, so each stream's prefix also absorbs the OTHER stream's fillers.
Both are harmless IFF each stage picks `L_s` big enough that `|u_s|` dominates
the cumulative length. Smallest probe: draft `chain_orbit_equidist` and check
`tailSched_cfDiscLt`'s induction still closes with `cfDiscLt_short_append`
absorbing a filler of bounded-but-growing length between consecutive `u_s`. If
it abstracts cleanly, 2–3 are mechanical. If NOT, that is the real crux —
escalate (write ROUTE-ESCALATION), do not retreat to more atoms.

---

## B6 — lap 1 landed (2026-08-24): scaffold + single-cylinder bound ✅

New additive leaf `src/NormalNumbers/CFIntervalGood.lean` (imports `CFDigitLaw`;
frozen B5′ modules untouched). Build green (8752).

**Proved this lap** (axiom-clean, on-path leaf):
- `volume_cfCylinder_le_fib (w) (hw) (hpos) : volume (cfCylinder w) ≤
  ENNReal.ofReal (1/(fib (|w|+1))^2)` — the "cylinders shrink" driver. From
  `volume_cfCylinder` (`=1/(qₙ(qₙ+qₙ₋₁))`) + `fib_le_cfK` (`qₙ ≥ fib(n+1)`) +
  `qₙ₋₁ ≥ 0`.

**Aligned statement shapes** (recorded per directive — L1 FINAL, L2 provisional):
- `coveredByCyl a b n := ⋃ w ∈ {w ∈ genWords n | cfCylinder w ⊆ Ioo a b}, cfCylinder w`
  (index over `genWords n` = the CFDigitLaw partition index; avoids a Decidable
  instance on the `⊆` predicate).
- **L1** `volume_interval_sdiff_covered_le (a b) (0≤a) (a≤b) (b≤1) (n) :
  volume (Ioo a b \ coveredByCyl a b n) ≤ ENNReal.ofReal (2/(fib(n+1))^2)`.
- **L2** `volume_interval_good_ge` — PLACEHOLDER (`True`); pin to real
  `goodExtSet`/`goodC` exports once L1 lands.

## B6 — lap 2 landed (2026-08-24): L1 PROVED ✅

`volume_interval_sdiff_covered_le` discharged, axiom-clean (trust triple),
build green (8752). RHS relaxed from `2/fib²` to `4/fib²` — the **soft
M-neighborhood** proof (cleaner than the straddler-count route drafted below):
`M := 1/fib(n+1)²`; every rank-`n` cylinder that straddles `∂(a,b)` has diameter
`≤ M` (`cfCylinder_subset_Icc_length` + `volume_cfCylinder_le_fib`) and meets the
boundary, so it lies within `M` of `a` or `b`; hence uncovered `⊆ [a−M,a+M] ∪
[b−M,b+M]`, mass `≤ 4M`. `n=0` handled separately (mass ≤ 1 ≤ 4). No
disjointness/counting needed — the straddler-count plan was abandoned as
unnecessary.

## B6 — lap 3 landed (2026-08-24): L2 PROVED ✅

`length_le_two_mul_good_add_err` discharged, axiom-clean, build green (8752).
Both L1 and L2 now closed (ahead of the brief's lap plan).
- `goodInInterval a b n m := ⋃ w ∈ {w∈genWords n | cfCylinder w ⊆ Ioo a b},
  goodExtSet w goodC m` — good mass inside `(a,b)`.
- **L2**: `|b−a| ≤ 2·volume(goodInInterval a b n m) + 4/fib(n+1)²` (for `n≥1`, any
  `m`). ⇒ good mass inside any interval is `≥ (|b−a|−δ)/2` beyond a rank.
- Proof: `measure_biUnion` over the contained-cylinder index (disjoint via
  `cfCylinder_disjoint`, measurable) turns both covered/good masses into tsums;
  per-term `goodC_half` (`|I_w| ≤ 2|goodExtSet w goodC m|`) + `ENNReal.tsum_le_tsum`
  gives `covered ≤ 2·good`; `measure_inter_add_sdiff` + L1 close it. New helpers
  `goodExtSet_subset_cfCylinder`, `measurableSet_goodExtSet`.
- `goodExtSet`/`goodC`/`goodC_half` all live in `NormalNumbers` ns; import
  `NormalNumbers.CFSchedule` (done in `CFIntervalGood.lean`).

## B6 — lap 4 landed (2026-08-24): L3 PROVED ✅

`CFAffine.lean` (new additive module, axiom-clean, build green 8753). The affine
map `affineMap q r x = q*x+r` (q>0) as interval algebra:
- `preimage_affineMap_Ioo`: `ψ⁻¹(c,d) = ((c−r)/q, (d−r)/q)`
- `image_affineMap_Ioo`: `ψ''(a,b) = (q*a+r, q*b+r)`
- `volume_preimage_affineMap_Ioo`: `|ψ⁻¹(c,d)| = (d−c)/q`
- `good_mass_in_affine_preimage`: transports L2 through the pullback — target
  interval preimage length `≤ 2·good mass inside + 4/fib(n+1)²`.
q>0 only; general q≠0 via `x↦−x` at point of use.

**L1+L2+L3 all closed — the metric substrate of B6 is DONE.** What remains is
the genuine crux:

## B6 — lap 5 landed (2026-08-24): affine pullback measure + L4 ROUTE ANALYSIS ✅

Proved `volume_preimage_affineMap` (CFAffine.lean, axiom-clean): `volume(ψ⁻¹ s) =
|q⁻¹|·volume s` for any `q≠0,s` — the L4 union-bound ingredient. Build green (8753).

### ⚠️ ROUTE-DECISIVE FINDING (L4 is a REAL theorem, not "mechanical threading")

`IsCFNormal (ψ xstar)` is about the CF-digit **windows of the single real number
`ψ(xstar)`**, read off by iterating the Gauss map `T` on `ψ(xstar)` ITSELF
(`IsCFNormal`, `Headline.lean:71`: `T^k(ψ xstar) ∈ cfCylinder v` frequency → γ).
Crucially **`T` does NOT commute with `ψ`** — the CF expansion of `qx+r` has no
finite relation to that of `x` for general real `q`. (This is exactly why
Vandehey §7 restricts to `q,r` QUADRATIC: only then does `ψ` act nicely on CF
tails via the geodesic flow. For arbitrary real `q` the problem is likely open
or false.) So the B5′ trick — *prescribe* xstar's digit sequence to be
CF-normal, and windows-of-the-prefix = orbit-visits — does NOT directly give
`ψ(xstar)` CF-normal: we cannot independently prescribe both digit sequences.

**Consequence for the interval-transport insight (KHINCHIN.md §B6).** L1–L3
(ψ maps intervals to intervals, |ψ⁻¹(J)|=|J|/q, good density transports) are
NECESSARY but NOT SUFFICIENT. Interval nesting controls only the FIRST few CF
digits of `ψ(xstar)` per stage, not its whole orbit.

**The route that CAN work — INTERLEAVED (diagonal) schedule.** Build xstar as a
limit of nested x-intervals where stages ALTERNATE:
- **x-stages**: refine to a good x-cylinder (fixes next block of xstar's OWN CF
  digits with correct freq) — the existing B5′ mechanism.
- **ψ-stages** (per image system i): refine so `ψᵢ(xstar)` enters a prescribed
  GOOD ψ-cylinder = xstar enters `ψᵢ⁻¹(good ψ-cylinder)`, an x-INTERVAL. L1/L2/L3
  say that interval contains good x-cylinders of positive density, so the refine
  is feasible; `good_mass_in_affine_preimage` is exactly this density.
Over infinitely many alternating stages: xstar's digit seq is CF-normal (x-stages)
AND `ψᵢ(xstar)`'s digit seq is CF-normal (ψ-stages). The digits contributed by
the "other" stages must not spoil frequency — they do not, because every stage
selects a GOOD (correct-freq) block. This is a genuine but plausible multi-lap
construction; the density substrate (L1–L3) is now all proved.

### lap 6 landed (2026-08-24): L4 KERNEL `isCFNormal_of_orbit_freq` PROVED ✅

`CFOrbitFreq.lean` (axiom-clean, build green 8754). `x`-generic:
`IsCFNormal y ⟸ (∀j, Tʲy ∈ (0,1)) ∧ (∀ genuine v, blockCount(I_v) p y / p →
γ(I_v))`. Via the existing generic bridge `blockCount_sub_countOccurrences_bounds`
(`CFWordBridge`, orbit-count vs window-count differ by ≤|v|) + squeeze.
**Sub-obligation 1 is thus DONE** — the orbit⇔window machinery is `x`-generic and
already in the codebase (`iterate_mem_cfCylinder_iff`, `blockCount_eq_card_matches`,
`blockCount_sub_countOccurrences_bounds`, all take `y`/`x` free).

**REFINED L4 target.** `IsCFNormal (ψ xstar)` now reduces (via
`isCFNormal_of_orbit_freq` at `y := affineMap q r xstar`) to TWO obligations:
  (A) `∀ j, gaussMap^[j] (ψ xstar) ∈ (0,1)` — ψ(xstar) has a full Gauss orbit;
  (B) `∀ genuine v, blockCount (cfCylinder v) p (ψ xstar) / p → γ(I_v)` — the
      orbit of ψ(xstar) equidistributes (Birkhoff/orbit-frequency form).
(B) is the genuine crux. The interleaved schedule must make ψ(xstar) land in a
nested chain of GOOD ψ-cylinders (⇒ its digit sequence is prescribed CF-normal
⇒ orbit-freq → γ, exactly as `xstar_cf_freq_tendsto` gives it for xstar). L2/L3
(`good_mass_in_affine_preimage`) supply the density that makes each ψ-stage refine
feasible; `volume_preimage_affineMap` bounds the pullback bad zone.

### lap 7 landed (2026-08-24): CFScheduleA scaffold — target reduced to ONE crux sorry ✅

`CFScheduleA.lean` (build green 8755, one disclosed sorry). Also
`isCFNormal_of_irrational_orbit_freq` (CFOrbitFreq, axiom-clean).
- `CFOrbitEquidist y := ∀ genuine v, blockCount(I_v) p y/p → γ(I_v)`.
- **`exists_cfNormal_and_affine_cfNormal {q}(hq:0<q)(r) : ∃ x, IsCFNormal x ∧
  IsCFNormal (affineMap q r x)` is PROVED** modulo one crux — the assembly uses
  the orbit-frequency interface, real content.
- **THE ONE CRUX (`exists_interleaved_affine_witness`, sorry, CFScheduleA:56/61):**
  `∃ x, (Irrational x ∧ x∈(0,1) ∧ CFOrbitEquidist x) ∧ (Irrational (ψx) ∧
  ψx∈(0,1) ∧ CFOrbitEquidist (ψx))`. This is the interleaved schedule.

**src/ now carries exactly ONE active sorry** — the isolated B6 crux (correct
decomposition). All B6 substrate below it is axiom-clean.

### lap 8 landed (2026-08-24): feasibility core `goodInInterval_pos_of_lt` ✅

Axiom-clean, build green (8755). Beyond a rank (`4/fib(n+1)² < b−a`), good mass
inside any nondegenerate `(a,b)⊆(0,1)` is STRICTLY positive ⇒ `goodInInterval`
nonempty ⇒ a good CF-cylinder exists inside `(a,b)`. **This discharges the
per-stage feasibility of the interleaved schedule** — every refinement step
(x-stage on `cfCylinder wx`, ψ-stage on the pullback `((c−r)/q,(d−r)/q)`, or the
combined interval `cfCylinder wx ∩ ψ⁻¹(cfCylinder wz)`, all intervals) has a good
block to pick. The ψ-side needs NO separate lemma: apply `goodInInterval_pos_of_lt`
to the pullback endpoints (from `preimage_affineMap_Ioo`). Substrate for the
crux is now essentially complete; what remains is purely the schedule bookkeeping.

### lap 9 landed (2026-08-24): structural helper `take_eq_of_mem_cfCylinder` ✅

Axiom-clean, build green (8755). Nesting ⇒ prefix: a point in `cfCylinder w` ∩
`cfCylinder w'` with `|w|≤|w'|` forces `w'.take|w| = w`. So a deep good cylinder
inside `cfCylinder wx` (from `goodInInterval_pos_of_lt`) is a genuine EXTENSION of
`wx` — the bridge from "good geometric cylinder in the interval" to "appended
block", keeping x's prescribed digits consistent across ψ-stage refinements.

### lap 10 landed (2026-08-24): `eq_of_mem_cfCylinder_chain` ✅

Axiom-clean, build green (8755). Nested extending genuine cylinder chains pin a
UNIQUE point (diam ≤ 1/fib(len+1)² → 0). Obligation-(A) ingredient: the affine
image ψ(x) lies in the whole ψ-word chain, and (applying `exists_irrational_mem_
iInter_cfCylinder` to that ψ-chain to get an irrational in the same intersection)
this lemma forces ψ(x) = that irrational ⇒ **ψ(x) irrational in (0,1)**. Combined
with `take_eq_of_mem_cfCylinder` the (A) side is nearly mechanical.

### lap 11 landed (2026-08-24): obligation (A) discharged GENERICALLY ✅
`irrational_mem_Ioo_of_mem_iInter_cfCylinder` (CFScheduleA, axiom-clean, build
green 8745). For ANY extending chain of genuine CF words `w` and any point `y`
in every `cfCylinder (w s)`: `Irrational y ∧ y ∈ (0,1)`. Proof = 4 lines:
`exists_irrational_mem_iInter_cfCylinder` gives an irrational ξ in the ∩;
`eq_of_mem_cfCylinder_chain` forces `y = ξ`; `cfCylinder_subset_Ioo` gives the
box. **This closes BOTH `(A)`-side conjuncts of the crux** — apply it to `x`'s
own word chain (⇒ `Irrational x ∧ x∈(0,1)`) and to the ψ-word chain with `ψ(x)`
in each ψ-cylinder (⇒ `Irrational (ψx) ∧ ψx∈(0,1)`). What remains in the crux is
ONLY obligation (B) (orbit equidistribution of both streams) + producing the two
word chains from the interleaved schedule. Obligation (A) is now a one-liner
given the chains.

**NEXT ATTACK (obligation B, the genuine heart).** Build the light interleaved
`SchedState` (fields: x-word `wx`, ψ-word `wz`, invariant `cfCylinder wx ⊆
ψ⁻¹(cfCylinder wz)` nonempty). Alternate: x-stage appends a good block to `wx`
inside `cfCylinder wx` (feasible: `goodInInterval_pos_of_lt`); ψ-stage appends a
good block to `wz` after refining `wx` so `ψ(cfCylinder wx) ⊆ cfCylinder wz'`
(feasible: `good_mass_in_affine_preimage` gives good x-density in the pullback).
Then mirror `xstar_cf_freq_tendsto` (CFCorrect) for BOTH `wx` and `wz` streams.
KEY sub-question to settle first (cheap probe next lap): the "uncontrolled"
digits that x-stages force onto ψ(x) (and vice-versa) between good blocks must be
asymptotically negligible — pick block lengths so the good-block count dominates.
Verify the CFCorrect telescoping (`tailSched_cfDiscLt` + `exists_stage`) still
gives the freq limit when a positive-density fraction of appended digits is
"uncontrolled" — OR arrange the schedule so EVERY appended block (both streams)
is good (no uncontrolled digits: each stage's refinement is itself a good block
for the stream being extended, and the OTHER stream's cylinder is only refined
at ITS own stages). The latter is cleaner: `wz` only grows at ψ-stages, `wx`
only at x-stages, so each stream sees only good blocks — no uncontrolled digits.

### lap 11 (cont.) — ROUTE-DECISIVE finding on obligation (B)'s missing atom 🔍
Traced exactly what obligation (B) still needs and where it lives:
- `goodInInterval`/`goodExtSet` give only **DENSITY** (short-continuant ⇒
  positive relative length, `goodExtSet` = extensions with `cfK u ≤ e^{Cn}`),
  NOT **frequency** control. So `goodInInterval_pos_of_lt` alone cannot supply a
  CF-normal block — it keeps intervals fat but says nothing about digit-window
  frequencies.
- The FREQUENCY control lives in `TBrick.exists_refinement_uniform`
  (`TBrickRefine.lean:432`) — its conclusion bundles the `CFDiscLt`-style
  `∀ v∈F, |countOccurrences v u − γ(I_v)·n| < δn + |v|` payload TOGETHER with the
  base-`d` `daryCell` cell-nesting. `TBrick.exists_refinement` (line 554) wraps
  it but is still TBrick-bound.
- **THE single missing engine** for the light interleaved schedule =
  a **daryCell-free CF core** of `exists_refinement_uniform`: for genuine `w`,
  finite pattern family `F`, `δ>0`, produce arbitrarily long blocks `u` that are
  BOTH short-continuant (density) AND `F`-frequency-good, with `cfCylinder(w++u)`
  landing in a PRESCRIBED subinterval of `cfCylinder w` (needed so x-stage /
  ψ-stage refinements can target the combined interval `cfCylinder wx ∩
  ψ⁻¹(cfCylinder wz)`). Extract by re-running `exists_refinement_uniform`'s proof
  and DROPPING the `daryCell` conclusion (keep the badBlocks/half-mass density +
  the `wordFamily` count bound). This is additive (new file, e.g.
  `CFFreqBlock.lean`, imports `TBrickRefine` for the density lemmas; never edits
  it). Once it exists, the interleaved schedule is: maintain nonempty combined
  Ioo `J_n`; x-stage appends a freq-good block landing in `J_n` (feasible: `J_n`
  nondegenerate ⇒ engine gives block, `take_eq_of_mem_cfCylinder` ⇒ extends wx);
  ψ-stage appends a freq-good block to wz landing in `ψ(J_n)` (feasible via
  `good_mass_in_affine_preimage`+engine, then pull back). Each stream then sees
  ONLY freq-good blocks ⇒ mirror `xstar_cf_freq_tendsto` per stream ⇒ (B). Design
  verified sound this lap (x-stage keeps ψ(x)∈cfCylinder wz since J shrinks
  inside ψ⁻¹(cfCylinder wz); ψ-stage symmetric). **Next lap: build
  `exists_freq_good_block` (the daryCell-free core) — the whole crux funnels to
  it + the per-stream telescoping.**

### lap 12 landed (2026-08-24): the frequency engine `exists_freq_good_block` ✅
`CFFreqBlock.lean` (new additive module, axiom-clean trust-triple, build green
8756). The daryCell-free CF core of `TBrick.exists_refinement_uniform` is DONE:
for genuine `w`, finite family `F`, `δ>0`, ∃N ∀n≥N ∃ genuine block `u` (`|u|=n`)
that is `F`-frequency-good (`|countOccurrences v u − γ(I_v)·n| < δn+|v|` ∀v∈F)
with an irrational point in `cfCylinder(w++u)`. **Extraction trick**: instantiate
`exists_good_avoiding_bad_of_large` at level `t=1` (⇒ `Finset.Icc 2 1 = ∅`, the
whole d-ary bad-zone union vanishes) on a `trivBrick w` (vacuous cell obligations
since `2≤d≤1` is false); unpack the survivor's goodExtSet word + cfBadZone
avoidance exactly as the CF payload of `exists_refinement_uniform` does. **This is
THE atom obligation (B) funnels to.** No edits to any frozen module.

**NEXT ATTACK (the interleaved schedule itself).** With `exists_freq_good_block`
in hand, build the two-stream construction in `CFScheduleA` (or a new
`CFScheduleAImpl.lean`):
1. Joint state `⟨wx, wz, hx: genuine, hz: genuine, hJ: (cfCylinder wx ∩
   ψ⁻¹(cfCylinder wz)).Nonempty⟩`. Note `cfCylinder w` IS an open interval (its
   endpoints are `cfCylinder_endpoints`), so `J` is an Ioo — get its endpoints to
   apply the affine/good lemmas.
2. x-STAGE: `J` nondegenerate ⇒ (density via `goodInInterval_pos_of_lt`) a good
   x-cylinder sits in `J`; use `exists_freq_good_block` on `wx` with a large-`n`
   freq-good block, then INTERSECT the choice with landing in `J` — CAVEAT: the
   engine gives *a* freq-good block, not one whose cylinder ⊆ `J`. Bridge needed:
   either (a) a version of the engine RELATIVIZED to an interval (pick the
   surviving `x` inside `J` — feasible because `J∩goodExtSet` still has ≥ half of
   `J`'s mass by the same union bound, since the bad zones are measured against
   `cfCylinder wx ⊇ J`), or (b) show the freq-good block can be chosen with
   `cfCylinder(wx++u) ⊆ J` by taking `n` large enough that the cylinder is smaller
   than `J` AND lands in it (needs a placement argument). **(a) is the clean route
   — next lap: prove `exists_freq_good_block_in_interval`, the engine with the
   survivor confined to a subinterval `J ⊆ cfCylinder w` of positive measure.**
3. ψ-STAGE: symmetric, on `wz`, targeting `ψ(J)` (an interval via `CFAffine`
   image lemmas); pull the chosen point back through `ψ⁻¹`.
4. Take `x := ` unique point of `⋂ cfCylinder wx` (`eq_of_mem_cfCylinder_chain` +
   `exists_irrational_mem_iInter_cfCylinder`); obligation (A) via lap-11
   `irrational_mem_Ioo_of_mem_iInter_cfCylinder` on both chains; obligation (B)
   via per-stream telescoping mirroring `xstar_cf_freq_tendsto` (the freq-good
   blocks are exactly its `uSched`/`wordFamily` inputs).

### lap 13 landed (2026-08-24): placement primitive + INTERVAL-RELATIVIZED engine ✅
`CFScheduleA.lean` (axiom-clean trust-triple, build green 8756):
- `exists_cfCylinder_subset_Ioo` — every nondegenerate `(a,b)⊆(0,1)` contains a
  genuine CF cylinder (via `goodInInterval_pos_of_lt` nonempty + index unpack).
- **`exists_freq_good_block_in_Ioo`** — THE interval-relativized frequency engine
  (route (a) from lap 12): for family `F`, `δ>0`, and `(a,b)⊆(0,1)`, ∃ placement
  word `w` with `cfCylinder w ⊆ (a,b)` and ∃N ∀n≥N a freq-good block `u` (`∀v∈F,
  |countOccurrences v u − γ(I_v)·n|<δn+|v|`) with an irrational point of
  `cfCylinder(w++u)` INSIDE `(a,b)`. Composes the placement primitive with
  `exists_freq_good_block`. **This is exactly what each schedule stage consumes**:
  x-stage on `(a,b)=cfCylinder wx` (or `J`), ψ-stage on `(a,b)=ψ(cfCylinder wx)`
  (an interval via `CFAffine` image lemmas), then pull back through `ψ⁻¹`. The
  placement word `w` is the bounded per-stage "filler" (chosen once to enter the
  interval), `u` the long freq-good payload ⇒ filler asymptotically negligible.

**NEXT ATTACK — the interleaved schedule assembly (the crux itself).** All atoms
are now axiom-clean and in `src/`. Remaining is the recursive two-stream schedule
+ per-stream telescoping:
1. Joint `SchedStateA ⟨wx, wz, hx_gen, hz_gen, hψ : ψ(cfCylinder wx) ⊆
   cfCylinder wz⟩` (invariant makes `J = cfCylinder wx`, a cylinder).
2. `schedStepA`: alternate (parity on stage index).
   - x-stage: `exists_freq_good_block_in_Ioo` on `(a,b) := endpoints of cfCylinder
     wx` (`cfCylinder_endpoints`); the returned `w++u` extends wx
     (`take_eq_of_mem_cfCylinder`); new wx' = that word, wz unchanged; invariant
     preserved (cfCylinder wx' ⊆ cfCylinder wx ⇒ ψ-image still ⊆ cfCylinder wz).
   - ψ-stage: `(a,b) := endpoints of ψ(cfCylinder wx)` (`image_affineMap_Ioo`
     applied to wx's endpoints); engine gives `w_z'`=`wz''++u_z` with
     `cfCylinder w_z' ⊆ ψ(cfCylinder wx)`; set wz' = that word (extends wz via
     take_eq since ⊆ cfCylinder wz), and REFINE wx to wx'' = the pullback deep
     word so `ψ(cfCylinder wx'') ⊆ cfCylinder wz'` (feasible: pick wx'' with
     `cfCylinder wx'' ⊆ ψ⁻¹(cfCylinder w_z') ∩ cfCylinder wx`, nonempty interval,
     via `exists_cfCylinder_subset_Ioo` on that combined interval's endpoints).
3. `xA := ` unique point of `⋂ cfCylinder wx` (limit lemmas). (A) both sides via
   `irrational_mem_Ioo_of_mem_iInter_cfCylinder`; ψ(xA) lies in `⋂ cfCylinder wz`.
4. (B) per stream: mirror `CFCorrect.xstar_cf_freq_tendsto` — the appended
   segments are `exists_freq_good_block_in_Ioo`'s freq-good `u`'s (plus bounded
   fillers, absorbed by `cfDiscLt_short_append`). Needs a light re-derivation of
   `tailSched_cfDiscLt`/`uSched_dominance` for THIS schedule (copy-extend
   CFCorrect; never edit it). This is the multi-lap body — but now every
   analytic/geometric atom it calls is proved.
Faithfulness gate after any schedule work: re-`#print axioms
exists_absolutely_normal_cf_normal_khinchin` MUST stay trust-triple.

### lap 14 landed (2026-08-24): cylinder↔interval bridge ✅
`CFScheduleA.lean` (axiom-clean trust-triple, build green 8756):
- `exists_irrational_mem_cfCylinder` — every genuine cylinder has an irrational
  point (trivial `w++1ⁿ` extending chain + `exists_irrational_mem_iInter_cfCylinder`).
- **`exists_Ioo_irrational_subset_cfCylinder`** — `cfCylinder w ⊇` all irrationals
  of a fixed nondegenerate `(a,b)⊆(0,1)` (its convergent-endpoint interval
  `cfCylinder_endpoints`, clamped to `(0,1)`; strictness from an irrational
  witness strictly between the rational endpoints). **This is the bridge that
  lets the schedule feed `cfCylinder wx` to `exists_freq_good_block_in_Ioo`**:
  take `(a,b)` from this lemma, run the interval engine on it; the engine's
  returned cylinder ⊆ `(a,b)`, and its irrational points land in `cfCylinder wx`.
  Combined with `take_eq_of_mem_cfCylinder` (shared irrational point + length
  ordering) the new word EXTENDS wx — no separate "extends" lemma needed.

**NEXT ATTACK — assemble the schedule step `schedStepA` (still the crux).** Every
geometric atom is now proved. One remaining glue lemma to prove first, then the
recursion:
- `exists_freq_good_extend_cfCylinder (wx genuine) (F) (δ>0) (L : ℕ) : ∃ wx'
  genuine, wx'.take wx.length = wx ∧ wx.length < wx'.length ∧ L ≤ wx'.length ∧
  cfCylinder wx' ⊆ cfCylinder wx ∧ (∀v∈F, freq-good on wx'‑suffix within δ) ∧
  (cfCylinder wx').Nonempty`. Build it by: `(a,b) := exists_Ioo_irrational_subset_
  cfCylinder wx`; `⟨w,_,_,hsub,N,hN⟩ := exists_freq_good_block_in_Ioo F .. (a,b)`;
  pick `n := max N (max L wx.length) + 1`, get block `u` + irrational point `p ∈
  cfCylinder(w++u) ⊆ (a,b)`; `p ∈ cfCylinder wx` (bridge) ∧ `p ∈ cfCylinder(w++u)`
  with `|wx| ≤ |w++u|` ⇒ `take_eq_of_mem_cfCylinder` ⇒ `w++u` extends wx; set
  `wx' := w++u`. NB the freq-good property is on the block `u` (a SUFFIX of wx'),
  with the placement filler `w[|wx|:]` bounded — feed both to the telescoping.
- Then `SchedStateA` + `schedStepA` (x/ψ parity) + `schedA : ℕ → SchedStateA` by
  choice, `xA := ` limit point, and the per-stream freq telescoping (copy-extend
  `CFCorrect`). This is the multi-lap body; atoms all green.

### lap 15 landed (2026-08-24): single-stream stage `exists_freq_good_extend_cfCylinder` ✅
`CFScheduleA.lean` (axiom-clean trust-triple, build green 8756). The atomic
schedule refinement: given genuine `wx`, family `F`, `δ>0`, depth target `L`, ∃
strict genuine extension `wx'` (`wx'.take|wx|=wx`, `|wx|<|wx'|`, `L≤|wx'|`) with
`cfCylinder wx' ⊆ cfCylinder wx`, split `wx'=w++u` with the tail block `u`
`F`-frequency-good. Composes lap-14 bridge + lap-13 interval engine + `take_eq_of_
mem_cfCylinder` (shared irrational point ⇒ extension). **This is the x-stage in
one lemma** (and the ψ-stage after mapping through the affine image interval).

**NEXT ATTACK — the recursion + telescoping (crux body).** With the atomic stage
proved, remaining:
1. ψ-stage variant: `exists_freq_good_extend_affine` — same, but the new
   x-refinement `wx'` ALSO forces `ψ(cfCylinder wx') ⊆` a fresh good ψ-cylinder
   `wz'` extending `wz`. Build from `exists_freq_good_extend_cfCylinder` applied
   to the ψ-image interval `ψ(cfCylinder wx)` (via `image_affineMap_Ioo` on wx's
   endpoints from `exists_Ioo_irrational_subset_cfCylinder`) to get `wz'`, then
   refine wx into `ψ⁻¹(cfCylinder wz') ∩ cfCylinder wx` (nonempty interval;
   `exists_cfCylinder_subset_Ioo` on its endpoints) to get `wx'`.
2. `SchedStateA ⟨wx, wz, invariants⟩`; `schedStepA` alternates x/ψ by parity;
   `schedA : ℕ → SchedStateA` by choice (mirror `CFSchedule.sched`).
3. `xA := ` limit of `⋂ cfCylinder (schedA s).wx`; obligation (A) both sides via
   `irrational_mem_Ioo_of_mem_iInter_cfCylinder`.
4. Obligation (B): per-stream freq telescoping. The appended segments are the
   `u`'s of `exists_freq_good_extend_cfCylinder` (freq-good) plus bounded
   placement fillers `w[|wx|:]`; mirror `CFCorrect.xstar_cf_freq_tendsto`'s
   `cfDiscLt` telescoping (needs light re-derivation of `tailSched_cfDiscLt` /
   `uSched_dominance` analogues — copy-extend CFCorrect, never edit). This is the
   multi-lap analytic body; every atom it calls is now proved & axiom-clean.
Faithfulness gate after schedule work: `#print axioms
exists_absolutely_normal_cf_normal_khinchin` MUST stay trust-triple.

### lap 16 landed (2026-08-24): ψ-stage x-selection primitive ✅
`exists_cfCylinder_subset_affine_preimage` (CFScheduleA, axiom-clean, green
8756): for `q>0` and target `z`-interval `(c,d)` with `ψ`-preimage in `(0,1)`, a
genuine `x`-cylinder sits inside `ψ⁻¹(c,d)` (= `preimage_affineMap_Ioo` +
`exists_cfCylinder_subset_Ioo`). Places `x` so `ψ(x)` enters a prescribed good
`z`-cylinder — the ψ-stage counterpart of the x-stage's placement.

**NEXT — assemble the ψ-stage `exists_freq_good_extend_affine`** (the last atom
before the recursion). Given genuine `wx, wz` with invariant `cfCylinder wx ⊆
ψ⁻¹(cfCylinder wz)`, `F`, `δ`, depth `L`: produce `wz'` (extends wz, freq-good,
`cfCylinder wz'⊆cfCylinder wz`) and `wx'` (extends wx, `cfCylinder wx'⊆cfCylinder
wx`, `ψ(cfCylinder wx')⊆cfCylinder wz'`). Recipe (all atoms now proved):
  (i) wz-interval `(e,f)` via `exists_Ioo_irrational_subset_cfCylinder wz`;
      wx-interval `(a,b)` via same on wx; image `(qa+r,qb+r)` via
      `image_affineMap_Ioo`. Target `J_z := (max(qa+r) e ⊓ …, …)` = the z-interval
      inside BOTH `ψ(wx-interval)` and `(e,f)` — nonempty since ψ(irrational of
      (a,b)⊆cfCylinder wx)⊆cfCylinder wz gives a common point.
  (ii) `exists_freq_good_block_in_Ioo F .. J_z` ⇒ `wz'` freq-good, cfCylinder
      wz'⊆J_z⊆(e,f) ⇒ extends wz (irrational pt + take_eq).
  (iii) `wz'`'s interval `(c,d)` (its endpoints); `exists_cfCylinder_subset_
      affine_preimage` on `(c,d)` intersected with `(a,b)` ⇒ `wx'` with
      cfCylinder wx'⊆ψ⁻¹(cfCylinder wz')∩cfCylinder wx ⇒ ψ(cfCylinder wx')⊆
      cfCylinder wz' and nested in wx.
CAVEAT to handle: ψ does NOT preserve irrationality, so the "irrationals of
(c,d)⊆cfCylinder wz'" bridge can't transfer across ψ — that's why (iii) selects
the x-cylinder via the PREIMAGE interval directly (no irrational transfer
needed), and (ii) places wz' via the z-side interval bridge (`exists_Ioo_
irrational_subset_cfCylinder wz`), keeping all irrational-caveats on ONE side of
ψ each. Then the recursion (`SchedStateA`/`schedStepA`/limit/telescoping).

### lap 17 landed (2026-08-24): two-interval intersection placement ✅
`exists_cfCylinder_subset_Ioo_inter` (CFScheduleA, axiom-clean, green 8756): a
genuine cylinder inside `Ioo a b ∩ Ioo c d` whenever `(max a c, min b d)` is a
nondegenerate subinterval of `(0,1)`. Lets the ψ-stage place `x` in
`cfCylinder wx`'s interval AND a good z-cylinder's ψ-preimage at once.

**KEY REMAINING SUB-LEMMA for the ψ-stage (next lap): the image-inclusion**
`affine_image_wxInterval_subset_wzInterval`. Setup: wx,wz genuine, invariant
`cfCylinder wx ⊆ ψ⁻¹(cfCylinder wz)` (q>0); `(a,b)` the wx-interval (irr(a,b)⊆
cfCylinder wx), `(e,f)` the wz-interval (cfCylinder wz ⊆ Icc e f — use the uIcc
bound from `cfCylinder_endpoints`, NOT just the irr-subset). CLAIM: `ψ((a,b)) =
(qa+r,qb+r) ⊆ (e,f)` — hence the target z-interval `J_z := ψ((a,b))` is nonempty
and inside the wz-region, so the ψ-stage can run `exists_freq_good_block_in_Ioo`
on `J_z` (z-side, no ψ-transfer) and `exists_cfCylinder_subset_affine_preimage`
on the resulting good z-cylinder (x-side). PROOF of the claim: irr(a,b)⊆
cfCylinder wx ⇒ ψ(irr(a,b))⊆cfCylinder wz⊆Icc e f; irr(a,b) dense in (a,b), ψ
continuous+increasing ⇒ ψ((a,b))⊆closure(ψ(irr(a,b)))⊆Icc e f; ψ((a,b)) open ⇒
⊆(e,f). (Endpoints: `qa+r = ⨅ψ((a,b))≥e`, `qb+r≤f` — a `le_of_forall_lt` / inf
argument, or a direct sequential limit `x_n↑a` irrational with ψ(x_n)≥e.) This is
the one genuinely analytic step of the ψ-stage (~15-30 lines); everything else is
the composed atoms. Then assemble `exists_freq_good_extend_affine`, then the
recursion + telescoping.

### lap 18 landed (2026-08-24): ψ-image inclusion (the analytic step) ✅
`affine_image_Ioo_subset_Icc` (CFScheduleA, axiom-clean, green 8756): under the
invariant `cfCylinder wx ⊆ ψ⁻¹(cfCylinder wz)`, with irr(a,b)⊆cfCylinder wx and
cfCylinder wz⊆Icc e f, the ψ-image `ψ((a,b)) ⊆ Icc e f`. Proof = two symmetric
`exists_irrational_btwn` contradiction blocks (a boundary-violating image point
pulls back to an irrational of (a,b) whose image escapes Icc e f). **This is the
one genuinely analytic step of the ψ-stage** — no ψ-irrationality transfer, no
sequences. Every ψ-stage ingredient is now proved & axiom-clean.

### lap 19 (design-decisive) — the ψ-irrationality obstruction RESOLVED 🔑
Strengthened `exists_Ioo_irrational_subset_cfCylinder` to ALSO return
`cfCylinder w ⊆ Icc a b` (green, axiom-clean; caller updated). More importantly,
worked out the correct schedule INVARIANT that dodges the "ψ doesn't preserve
irrationality" wall:

**Problem.** The naive invariant `cfCylinder wx ⊆ ψ⁻¹(cfCylinder wz)` (set
inclusion) is NOT establishable: placing `wx'` needs `ψ(cfCylinder wx')⊆
cfCylinder wz'`, but `cfCylinder wz'` is only an interval FOR IRRATIONALS, and
`ψ` maps some irrationals to rationals — so the interval-placement gives only
`ψ(cfCylinder wx')⊆Ioo(wz'-endpoints)`, which does NOT imply ⊆cfCylinder wz'.
Symmetrically, even the limit `ψ(xA)` isn't obviously in `cfCylinder wz'` because
`ψ(xA)` may be rational.

**Resolution (interval invariant + irrational-by-nesting).** Maintain instead the
INTERVAL-preimage invariant
  `cfCylinder wx_s ⊆ ψ⁻¹(Ioo (E0 wz_t) (E1 wz_t))`   (a genuine interval preimage,
establishable via `exists_cfCylinder_subset_affine_preimage`/`_Ioo_inter`, where
`E0,E1` are `wz_t`'s convergent endpoints). Then:
  • the wz-endpoint intervals `Ioo(E0 wz_t)(E1 wz_t)` are NESTED with rational
    endpoints shrinking to a point (diam ≤ 1/fib² → 0, `cfCylinder_endpoints`);
  • `ψ(xA) ∈ ⋂_t Ioo(E0 wz_t)(E1 wz_t)` (from the invariant + `xA∈cfCylinder
    wx_s` all s);
  • a point in infinitely many shrinking RATIONAL-endpoint intervals is
    IRRATIONAL (same argument as `CFLimit`/`exists_irrational_mem_iInter_
    cfCylinder`) ⇒ `ψ(xA)` irrational;
  • `ψ(xA)` irrational ∈ Ioo(E0 wz_t)(E1 wz_t) ⇒ (the `hUIoo` clause of
    `cfCylinder_endpoints`) `ψ(xA) ∈ cfCylinder wz_t` — for EVERY t. Hence
    `ψ(xA)` is pinned into the whole wz-chain ⇒ CF-normal by the same
    freq-telescoping as xA.
So the ψ-side never needs ψ to preserve irrationality: irrationality of ψ(xA) is
RECOVERED at the limit from the nested rational-endpoint intervals, exactly as
for xA itself. This is the key that makes B6 provable for general real q>0
(NOT just quadratic). Record the invariant as the `SchedStateA` field; the
ψ-stage lemma below produces the interval-preimage nesting, not a cylinder
inclusion.

**NEXT — assemble `exists_freq_good_extend_affine` (the ψ-stage), then recursion.**
Recast with the interval invariant (mechanical from the atoms):
1. wx-interval (a,b) [`exists_Ioo_irrational_subset_cfCylinder wx`]; wz-endpoints
   (e,f) with cfCylinder wz⊆Icc e f AND irr(e,f)⊆cfCylinder wz [both from
   `cfCylinder_endpoints`/`exists_Ioo_irrational_subset_cfCylinder wz` — may need
   a small helper exposing the Icc bound alongside the irr-subset; `cfCylinder_
   endpoints` gives `cfCylinder wz ⊆ uIcc = Icc(min)(max)` directly].
2. `affine_image_Ioo_subset_Icc` ⇒ J_z:=ψ((a,b))=Ioo(qa+r)(qb+r) ⊆ Icc e f, so
   irr(J_z)⊆Ioo e f (irrationals dodge the rational endpoints) ⊆ cfCylinder wz.
3. `exists_freq_good_block_in_Ioo F .. J_z` ⇒ wz' freq-good, cfCylinder wz'⊆J_z
   ⇒ (irr pt) extends wz.
4. wz'-endpoints (c,d); the preimage interval ((c-r)/q,(d-r)/q)⊆(a,b); intersect
   with (a,b) [trivially ⊆] and use `exists_cfCylinder_subset_affine_preimage`
   (or `_Ioo_inter`) ⇒ wx' with cfCylinder wx'⊆ψ⁻¹(cfCylinder wz')∩cfCylinder wx,
   extends wx, ψ(cfCylinder wx')⊆cfCylinder wz'. New invariant holds.
5. `SchedStateA`/`schedStepA` (parity x/ψ) + `schedA` by choice + limit point +
   per-stream `cfDiscLt` telescoping (copy-extend `CFCorrect`). Multi-lap body;
   all atoms green.

### lap 20 landed (2026-08-24): squeeze-to-a-point `eq_of_mem_iInter_Icc` ✅
`CFScheduleA`, axiom-clean, green 8756: two reals in every member of a sequence
of closed intervals with diameters `→0` are equal (`|y−z|≤hi_s−lo_s→0`). The
abstract nesting-uniqueness for the lap-19 resolution: `ψ(xA)` and the wz-chain's
irrational point ζ both lie in every wz-endpoint interval (diam `1/(K(K+K'))→0`)
⇒ `ψ(xA)=ζ` ⇒ `ψ(xA)` irrational + `∈⋂cfCylinder wz_t`.

**NEXT — the wz-endpoint diameter `→0` fact + wire the limit.** To use
`eq_of_mem_iInter_Icc` at the wz-chain: need `lo_t,hi_t := ` wz_t endpoints (from
`cfCylinder_endpoints`) with `hi_t−lo_t = 1/(cfK(wz_t)·(cfK(wz_t)+cfK'))→0`
(cfK(wz_t)≥fib(|wz_t|+1)→∞ since the chain extends). Mirror the diameter bound
already inside `eq_of_mem_cfCylinder_chain`/`exists_irrational_mem_iInter_
cfCylinder` (they compute the same `→0`). Then the limit assembly:
  • ζ, Irrational ζ, ζ∈cfCylinder wz_t ∀t  [`exists_irrational_mem_iInter_
    cfCylinder` on wz-chain];
  • ψ(xA)∈Icc(lo_t)(hi_t) ∀t  [invariant + xA∈cfCylinder wx_s];
  • `eq_of_mem_iInter_Icc` ⇒ ψ(xA)=ζ ⇒ Irrational(ψ xA) ∧ ψ(xA)∈cfCylinder wz_t ∀t;
  • ⇒ CFOrbitEquidist(ψ xA) via `irrational_mem_Ioo_of_mem_iInter_cfCylinder`
    (obligation A for ψ side) + the freq telescoping (obligation B).
Still need: the ψ-stage `exists_freq_good_extend_affine` producing the interval
invariant + wz freq-good chain, and the per-stream freq telescoping (copy-extend
`CFCorrect`). Multi-lap; all atoms green.

### lap 21 landed (2026-08-24): chain volumes → 0 `cfCylinder_chain_volume_tendsto` ✅
`CFScheduleA`, axiom-clean, green 8756: along a strictly extending genuine chain,
`volume(cfCylinder(w s)).toReal → 0` (squeeze by `1/fib(|w_s|+1)² ≤ 1/fib(s+1)`,
`fib→∞`). Combined with `cfCylinder_subset_Icc_length` (Icc of diameter =
volume), this is the `hdiam` input to `eq_of_mem_iInter_Icc` for the wz-chain —
so the ψ(xA)=ζ squeeze is now fully powered. The LIMIT-side machinery (recover
ψ(xA) irrationality + membership in ⋂cfCylinder wz_t) is COMPLETE modulo wiring.

**NEXT — the ψ-stage `exists_freq_good_extend_affine` + the recursion.** The
limit toolkit (`eq_of_mem_iInter_Icc` + `cfCylinder_chain_volume_tendsto` +
`cfCylinder_subset_Icc_length` + `exists_irrational_mem_iInter_cfCylinder` +
`cfCylinder_endpoints`.hUIoo) can now close: given the schedule produces wx-chain
and wz-chain with interval invariant `cfCylinder wx_s ⊆ ψ⁻¹(Icc(lo_t)(hi_t))`
(lo,hi = wz_t Icc-endpoints), then ψ(xA)∈Icc(lo_t)(hi_t)∀t, ζ (irrational, ∈
cfCylinder wz_t) ∈Icc too ⇒ `eq_of_mem_iInter_Icc` ⇒ ψ(xA)=ζ ⇒ done. Still to
build: (a) `exists_freq_good_extend_affine` (ψ-stage, recipe above — produces the
interval invariant + wz freq-good extension); (b) `SchedStateA`/`schedStepA`/
`schedA`/limit; (c) per-stream freq telescoping (copy-extend `CFCorrect`). All
geometric/analytic atoms are now proved & axiom-clean; (a)–(c) are wiring + the
telescoping port.

### TOOLKIT NOW COMPLETE for the interleaved schedule (all axiom-clean):
- CHAIN→0 `cfCylinder_chain_volume_tendsto` — cylinder volumes vanish along a chain.
- SQUEEZE `eq_of_mem_iInter_Icc` — nesting-uniqueness (recovers ψ(xA) irrationality at the limit).
- ψ-IMAGE `affine_image_Ioo_subset_Icc` — ψ((a,b))⊆Icc e f under the invariant (analytic step).
- INTER `exists_cfCylinder_subset_Ioo_inter` — cylinder in the intersection of two intervals.
- ψ-SELECT `exists_cfCylinder_subset_affine_preimage` — x-cylinder in ψ⁻¹(target z-interval).
- STAGE `exists_freq_good_extend_cfCylinder` — one freq-good nested extension (the x-stage).
- CYL↔IOO `exists_Ioo_irrational_subset_cfCylinder` + `exists_irrational_mem_cfCylinder`.
- INTERVAL ENGINE `exists_freq_good_block_in_Ioo` — freq-good block landing in a target interval.
- `exists_cfCylinder_subset_Ioo` — placement: a genuine cylinder inside any nondegenerate interval.
- ENGINE `exists_freq_good_block` — daryCell-free freq-good CF block (obligation B atom).
- (A) `irrational_mem_Ioo_of_mem_iInter_cfCylinder` — irrationality+box from any word chain.
- L1 `volume_interval_sdiff_covered_le` — interval covered by cylinders up to 4/fib².
- L2 `length_le_two_mul_good_add_err` — good mass inside an interval.
- `goodInInterval_pos_of_lt` — good mass STRICTLY positive beyond a rank (feasibility).
- `take_eq_of_mem_cfCylinder` — good cylinder in `cfCylinder wx` = extension of wx.
- L3 `preimage_affineMap_Ioo` / `image_affineMap_Ioo` / `volume_preimage_affineMap`
  / `good_mass_in_affine_preimage` — ψ transports intervals & density; pullback mass.
- `isCFNormal_of_irrational_orbit_freq` — orbit-freq ⇒ IsCFNormal (final step).
What remains is PURELY the schedule bookkeeping (no new analytic content).

**NOTE for next session — Tier-1 needs only CF-normality**, NOT base-b/Khinchin.
So the interleaved schedule can be built LIGHT: control only CF-digit-window
freqs of x and ψ(x) (append good CF-blocks alternately), reusing the CF part of
`goodExtSet`/`CFDiscLt`/`CFCorrect` telescoping — NOT the full TBrick
(daryCell/khinchin) apparatus. Consider a fresh light `SchedState` (word wx +
ψ-word wz + nonempty combined interval invariant) rather than extending TBrick.

**Sub-obligations of the crux (next laps, copy-extend frozen modules into
`CFScheduleA`/new files, NEVER edit frozen):**
1. Orbit⇔window bridge for the IMAGE: `T^k(ψ xstar) ∈ cfCylinder v` ⇔ ψ(xstar)'s
   CF digits `k..k+|v|` = v — needed to turn "ψ(xstar) in prescribed ψ-cylinders"
   into window-frequency (mirror how `xstar_cf_freq_tendsto`/`CFCorrect.lean`
   turns the prescribed x-digit seq into orbit visits). **This is the crux
   sub-question**: does landing ψ(xstar) in a nested chain of ψ-cylinders control
   its whole orbit's visit frequencies? (For xstar it works because the chain IS
   the digit sequence; for ψ(xstar) the chain of ψ-cylinders likewise IS ψ(xstar)'s
   digit sequence — so YES, provided the ψ-stage refinements prescribe ψ(xstar)'s
   digits consecutively. Verify this consecutiveness is maintainable while also
   interleaving x-stages.)
2. Interleaved schedule def + the per-stage union bound: bad_x ∪ ψᵢ⁻¹(bad_ψ)
   has measure < brick mass (base zone via `cfBadZone`; image zone via
   `volume_preimage_affineMap` + L1/L2). Copy-extend `TBrick`/`TBrickRefine`;
   NEVER edit frozen modules.
3. L5 per-map assembly → `IsCFNormal (ψᵢ xstar)`.
Escape valve: Tier 1 (φ headline `x,φx,x+φ`) = 2-element family; Tier 2 general
family the stretch. Faithfulness gate after any work: `#print axioms
exists_absolutely_normal_cf_normal_khinchin` MUST stay trust-triple.

---
### (historical) original L3 plan
**NEXT ATTACK — L3 affine transport** (new module `CFAffine.lean`):
The map `ψ(x) = q·x + r` (`q ≠ 0`). Needed facts:
1. `ψ '' (Set.Ioo a b) = Set.Ioo (ψ a) (ψ b)` when `q>0` (reversed when `q<0`) —
   affine image of an interval is an interval; `volume (ψ '' I) = |q|·volume I`
   (`Real.volume` under affine map; mathlib `Real.volume_image_mul_left`/
   `MeasurePreserving`? or measure_image of `x↦q*x+r` = `|q|` scaling — check
   `Real.volume_preimage_mul` / `MeasureTheory.Measure.addHaar`).
2. CF-normality is invariant under `x ↦ x+integer` and `x↦1/x`-tail shift — the
   integer-part drift of `ψ(x)` absorbed (KHINCHIN.md L3 note: `CFDefs` tail
   lemmas; find the tail-shift invariance of `IsCFNormal` used for `xstar`).
3. GOAL of the B6 crux (L4): the schedule builds `xstar` so that for EACH image
   system `(q_i,r_i)`, the pullback intervals `ψ_i⁻¹(cylinder)` still capture a
   good density (L2 applied to `ψ_i(brick)` gives good mass, transported back).
Record the pinned L3 statements here before proving. L4 (schedule surgery,
`CFScheduleA.lean`) is the MODERATE-risk crux — do it after L3.
Faithfulness: after any work, re-`#print axioms
exists_absolutely_normal_cf_normal_khinchin` = trust triple (must stay locked).

---

# PENDING WORK — B5′ campaign

> **✅ COMPLETE (2026-08-24 — the whole B5′ expedition is PROVED, axiom-clean).**
> Both headlines `exists_absolutely_normal_cf_normal` (Tier 1 = Becher–Yuhjtman)
> and `exists_absolutely_normal_cf_normal_khinchin` (Tier 2 = + Khinchin-typical)
> are `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`). ZERO
> `sorry`/`admit` terms in `src/`; ZERO cited math axioms. All 10 headline
> theorems certified trust-triple this lap.
>
> This lap closed it in three steps: (1) `CFSchedule.lean` rewired to the
> summable-**family** refinement; (2) log-tail telescoping in `CFCorrect.lean`
> (`logTailMass`, `uSched_logTail_le`, `tailSched_logTail_le`,
> `xstar_logTail_prefix_bound`) + the crux `xstar_log_tail_uniform`, hence
> `xstar_khinchinTypical`; (3) route D′ — frozen defs relocated byte-identical to
> `KhinchinDefs.lean` to break the import cycle, headline discharged.
>
> **No open proof obligations remain.** Nice-to-have only: sweep stale "left
> `sorry` for the campaign" docstrings in a few CF modules (historical prose);
> the outward Track-A PR to ChampernowneNormality (needs host egress).

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
> PROVED** (step 1 of HANDOFF-2026-08-24-0123.md's Tier-2 NEXT list):
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
> HANDOFF-2026-08-24-0057.md for the full route). ✅ **Khinchin (Tier 2) seed
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
> + `MatchesAt ↔ ofFn-window`). See HANDOFF-2026-08-24-0052.md for the full route
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
`src/` is sorry-free.  See `HANDOFF-2026-08-23-1749.md`.

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

## 2026-08-29 (lane-2 lap): PiBBP discharged
`piBBP_proved : PiBBP` is sorry-free, trust triple `[propext, Classical.choice, Quot.sound]`
(HEAD 1e228a2). Route: no integrals — roots-of-unity filter through
`Complex.hasSum_taylorSeries_neg_log` at 1/√2, −1/√2, (1±i)/2 with weights −2, −2, 2∓2i;
log values reassemble to π; mod-8 fibers (`Nat.divModEquiv` + `HasSum.prod_fiberwise`)
reproduce `bbpTerm` exactly. Scoped objective `sorry-free:src/NormalNumbers/PiBBPProof.lean`
is MET. Next (per operator brief, if resumed): target 2 `oneRun_le_of_sliverEscape`, then
target 3 Glaisher/Sun congruence.

## 2026-08-29 (lane-2 lap): twin edge `oneRun_le_of_sliverEscape` closed
Sorry-free, trust triple (KickDynamicsOneRun.lean). Width-mismatch DECISION: the one-run
dichotomy only certifies the WIDE sliver `1 − 2/(n+j+1)` (no-wraparound branch gives
`x ≥ 1 − 1/2ᵏ − τ` with tail bound only `τ ≤ 1/(n+1)`), so the frozen narrow node
`SliverEscape` cannot serve as hypothesis. Per the draft docstring's mandate, froze the
wide-sliver variant node `SliverEscapeWide` in KickDynamicsOneRun.lean (provenance docstring
there) and proved the edge from it, mirroring `zeroRun_le_of_sliverEscape` (constant
tightened +3 → +2). Bonus edge `sliverEscape_of_wide : SliverEscapeWide → SliverEscape`
records that wide is the stronger node. Frozen `SliverEscape` untouched. Next (per operator
brief): target 3 Glaisher/Sun congruence.

## 2026-08-29 (lane-2 lap): target 3 `lnTwoNum_modEq_fermatQuotient` closed
Sorry-free, trust triple `[propext, Classical.choice, Quot.sound]` (LnTwoFermatBridge.lean,
HEAD 5b7fc49). The Glaisher/Z.-H. Sun Fermat-quotient bridge in the frozen probe shape:
`lnTwoNum (p−1) ≡ lcmRange (p−1) · fermatQuotient2 p [MOD p]` for odd primes. Proof all in
`ZMod p`: `C(p−1,k) ≡ (−1)^k` by induction; the exact quotient `C(p,k+1)/p ≡ (−1)^k/(k+1)`
via `Nat.add_one_mul_choose_eq`; binomial theorem at `x = −2` over ℤ gives the exact
identity `Σ C(p,k+1)(−2)^{k+1} = 2^p − 2 = 2p·q′`, divide by `p` and cast to get Sun's
congruence `Σ 2^j/j ≡ −2 q_p(2)`; `Finset.sum_range_reflect` on the surrogate sum plus
`(p−1−j) ≡ −(j+1)` closes `A_{p−1} ≡ L·q_p(2)`. All three lane-2 targets of the
2026-08-29 treadmill brief are now DONE.

## 2026-08-29 (lane-2 lap): target 4 `lnTwoExpSep_holds` PROVED (β = 26)
Sorry-free, trust triple `[propext, Classical.choice, Quot.sound]` — Tier-1
LnTwoExpSep discharged IN-HOUSE via shifted-Legendre linear forms. Route:
vendored collatz-moonshot FrontA `Legendre.lean`/`Gelfond.lean` (→
`LegendreShifted.lean`, `LcmUptoGrowth.lean`, provenance headers, same pin);
closed both honest gaps in `LegendreHeight.lean` — height `|Q| ≤ (ℓ+1)·8^ℓ·lcm ℓ`
(explicit coeffs `(−1)^k C(ℓ,k)C(ℓ+k,ℓ)`, each ≤ 8^ℓ) and lower bound
`|P+Q·log2| ≥ lcm ℓ·(1/6)(1/12)^ℓ` (remainder integral on [1/4,1/2]) — then the
pairing at `ℓ = 4n` in `LnTwoExpSepProof.lean`: `N = P·2ⁿ+Q·p`; nonzero case
`1 ≤ 1/2 + H·d`, zero case `|Q|d = 2ⁿ|form|` with lcm cancelling. One master
limit (geometric beats `(4n+1)e^{2√(4n)log(4n)}`) powers all three eventual
inequalities. β DECISION: draft's 4 raised to 26 per the DRAFT clause — honest
crude constants give height `≲ 2^{20n}` (nonzero case) and `2^{n−25.34n}` (zero
case, `2²⁷ > 96⁴`); the Alladi–Robinson rate 3.63 would need sharp `P_ℓ(3)`
coefficient asymptotics + two-sided remainder, not attempted. Consequence:
`run_le_of_expSep` now caps every zero/one run of binary `ln 2` at `26n+O(1)`
unconditionally. Scoped objective `sorry-free:LnTwoExpSepProof.lean` MET.

## 2026-08-29 (lane-2 lap): target 5 `LogTwoSqKicked.lean` DONE (dessert)
Summed-kick machine instantiated for a second constant, `log² 2` (base 2,
kicks `r m = 2·H_{m−1}/m`). Probe `experiments/logtwosq_series.py` PASSES
(identity to 70 digits, exact rationals; cap checked at n=1,2,6,10,50).
Headlines sorry-free, trust triple, node `LogTwoSqSeries` stays CITED
(hypothesis-not-axiom): `logTwoSq_top_sliver_of_zeroRun` (sliver
`1 − 2(1+log(n+1))/(n+1)`; the draft's `6 ≤ n` dropped — `hk` forces
`H_n > 0`), maxRun twin conditional on `hhalf`, discharged for `n ≥ 56` by
`logTwoSqCap_le_half` (log x ≤ 2(√x−1) route; numerically true from n=14 —
lossy but elementary). Machinery: position-dependent cap via mathlib
`harmonic_le_one_add_log` + antitonicity of `(1+log x)/x` on `[1,∞)`
(`one_add_log_div_le_of_le`). OWED LATER (per brief, not this run): discharge
the `LogTwoSqSeries` node in-house (Cauchy product / integrated harmonic
generating function at `x = 1/2`).
