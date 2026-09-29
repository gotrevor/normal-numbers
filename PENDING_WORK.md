## CRUX (2026-09-29) — joint Lambert quantitative count

Open obligation: `jointWords_quantitative` in
`src/NormalNumbers/JointLambertQuantitative.lean` (one `sorry`).  It is the §3 ARITHMETIC
ASSEMBLY only — every estimate it needs is now proved and `#print axioms`-clean:
`exists_candidate_indices_every_height`, `three_range_tail_le`, `card_good_ge_half`,
`eventually_rate_le`, `iteratedLog_rate_le_eps_log`.

Advance this lap: the whole analytic spine of §§1–5 went from paper to kernel, and two
defects in the note's plan were found and repaired (the far range needs no `τ(n) ≤ 2√n`;
feasibility and rate need *different* bounds on `log B`, crude `k³` and sharp `k² log k`).

Decomposition as of the latest commit: the crux is ONE named statement in `src`,
`exists_good_starts_at_height` (chosen-height, steps 1–4).  Its §5 transfer to every `N`
is PROVED (`exists_joint_small_tail_count`), so the whole route now hangs on the
chosen-height theorem alone.  `JointLambertQuantitative.lean` itself is sorry-free and
both headlines are proved from these.  `countK_le_countK` (monotone above `log X ≥ 1`; the
threshold is load-bearing, since `Real.log` is not monotone through `0`) is proved and is the
transfer's first ingredient.

Advance, lap 1 of the 2026-09-29 count campaign: the crux's steps 1–2 are now PROVED, not
just planned.  `exists_candidate_data_at_height` (in `JointLambertCountAssembly.lean`)
delivers, at every large caller-chosen `X`, the pool prime, the allocation, the CRT solution
`R, u`, the divisor data, the near-range coprimality, `Q ≤ (2k³)^(a-1)`,
`B ≤ (2k³)^(1+ck²)` and the candidate count `≥ M/(4 log X)`.  Also proved:
`binTail_eq_three_range`, the identity that the digit reader's tsum
`∑' t τ(n+k+t)/2^(k+t)` *is* the three-range expression `three_range_tail_le` bounds — the
bridge that lets the counting route reuse the frozen tail estimate verbatim.

What is left inside `exists_good_starts_at_height` is therefore steps 3–4 only: feed
`three_range_tail_le`, show the total is `≤ θ·(M/(4 log X))/2` (this is the one arithmetic
inequality still open, and the choice of `J` is a free parameter there), then
`card_good_ge_half` and the injection `m ↦ R + mA`.

Next attack: steps 3–5 of "Exact next boundary" in
`HANDOFF-2026-09-29-joint-lambert-count.md`.  The only remaining analytic items are the two
limits `(log X)² 2^(-k) → 0` and `(log X)² (a+1)(c+1)^(k²) 2^(-k³) → 0`, both of the same
shape as the already-proved `eventually_cube_log_le_sqrt`.

---

# PENDING WORK — the queue

## Current Lambert status, 29 September 2026

The bounded qualitative Lambert objective is complete: `f6fbf87` proves the original
common-position theorem unconditionally.  [Completed proof](docs/JOINT-LAMBERT-RESCALED-PROOF.md).
The [next quantitative target](docs/JOINT-LAMBERT-QUANTITATIVE-NEXT.md) has a paper derivation
of `N exp(-C (log log N)^2 log log log N)` occurrences for every sufficiently large N.
No new treadmill is launched by this documentation update.  The older AGP-only status
below is historical; proving AGP is not the next Lambert obligation.  Vandehey work is
separate, in the main checkout.


Concrete next moves, cheapest and most clear-cut first.  Front context is in `STATUS.md`.  The
lap-by-lap log from before the 2026-09-27 merge is `archive/PENDING_WORK-to-2026-09-27.md`.
Treadmill laps append dated notes **below the queue**, and a review lap folds them back into it.

## ✅ LAP 7 (2026-09-28, bounded joint-Lambert objective): `PrimeIntervalSupply` IS A THEOREM

Scoped operator objective `DIRECTION.md` 2026-09-28 (c), ≤ 2 laps, **not** Vandehey assembly.
Vandehey's queue below is untouched and remains the main line.

`3ddc0b6` **`src/NormalNumbers/JointLambertPrimeInputs.lean`** — the joint Erdős–Borwein headline
now rests on `AGP` **alone**:

* `primeIntervalSupply_holds : PrimeIntervalSupply`, from **ordinary PNT** via the installed
  `Erdos446.eventually_dyadicPrimes_card_bounds` (itself from
  `BoundedGaps.PrimeNumberTheorem.primeCounting_natCast_isEquivalent`).  Two bookkeeping steps:
  `dyadicPrimes_eq_filter_Ioo` (for `2 ≤ L` the endpoint `2L` is even and `> 2`, hence composite,
  so half-open `(L,2L]` = open `(L,2L)` as FINSETS) and the free `1/2 → 1/3` constant.
* `jointLambertDisjunctivity_of_agp`, `jointWords_two_four_of_agp`.

All three at the exact frozen types (compiler-pinned by the file's `Audit` section), axiom-clean,
every pre-existing `JointLambert*.lean` byte-identical to `7b17c44`.  Reproducible check:
`scripts/check-joint-lambert-inputs.sh`.

**`docs/JOINT-LAMBERT-AGP-GAP.md`** — the AGP gap map against the *installed* pins.  Findings:

1. Interval supply was never PNT-in-AP strength; the old `STATUS.md` row saying so is corrected.
2. Bombieri–Vinogradov is **only a `def`** in the installed `BoundedGaps`
   (`BombieriVinogradov/Statement.lean:66,76`; the sibling `Challenge.lean` has 3 `sorry`s).
3. `Erdos4.FGKMT.exists_exponential_prime_distribution` is genuinely stronger than BV in the error
   factor *and* has the AGP exceptional-set shape (one excised conductor, chosen before the
   modulus) — but it is an **absolute** error bound, `≤ C x e^{−c√log x}`, and AGP wants a
   **relative** lower bound whose main term `x/(φ(B) log x)` shrinks with `B`.  So it yields AGP
   only for `φ(B) ≲ e^{c√log x}`, not `B ≤ x^{1/4}`.  **Structural, not a constant loss**:
   improving the error factor to `x/(log x)^A` makes the admissible range *worse*.
4. The `D > log X` clause is a second, smaller gap: the `Erdos4` excision chain drops the Page
   witness, whose conductor bound `log Q < c·2^22·√m·(log m)^4`
   (`Erdos48.PageExceptionalWitness.log_scale_lt_quadraticGapDenom`) gives `m ≫ (log Q)^{2−ε}`.
   Re-threading it is adapter work.
5. `ElliottPrimeDensityAP.exists_primeDensityAP` is a theorem of the **wrong shape** (fixed finite
   modulus, reciprocal-prime mass) — not a lead.  No AGP-shaped declaration exists anywhere in
   `~/src/lean-proofs` or `~/src/FormalPantheon`, so there is no copy to mistake for progress.

**→ NEXT on this front (one target, fully quantified in §6 of the gap doc): `AGPExpRange`** —
`AGP` verbatim with the modulus range `X^{1/4}` cut to `exp(c√log X)` and `D0 = 1`.  Route: (★)
at a single modulus via `Finset.single_le_sum` off `exists_exponential_prime_distribution`,
`eventually_primeCounting_tenth_bounds` for the main term, and the Page-witness re-thread for
`log X < D`.  Proving it discharges the whole exceptional-set/choice-order architecture of `AGP`
against real analytic input and reduces the remaining gap to the single named implication
`AGPExpRange + (log-free zero-density: range extension) ⟹ AGP`.  That density estimate is the
substantial missing theorem and a multi-lap analytic campaign, deliberately out of scope here.

**Opened, same lap: `src/NormalNumbers/JointLambertAGPRange.lean`** — the named next target, now
decomposed in `src/` rather than only described in prose.  Proved and axiom-clean there:

* `AGPExpRange` (the def), faithful to `AGP` in every respect but the modulus range;
* `agpCount_eq_primeCountUpTo` — `AGP`'s prime count and `BoundedGaps.Maynard.primeCountUpTo`
  are literally the same filter, so the two libraries' encodings need no reconciliation;
* `mod_mem_coprimeResidues`, `progressionDiscrepancy_le_max`, `maxDisc_le_excisedPrimeSum`;
* **`exists_pointwise_exponential_distribution`** — the (★) of the gap doc: the installed
  `Erdos4.FGKMT.exists_exponential_prime_distribution` read at a SINGLE modulus, giving, for one
  excised conductor `B` and every `q ≤ x^{1/3}` coprime to it and every reduced `u`,
  `|π(x;q,u) − π(x)/φ(q)| ≤ C x e^{−(a/2)√log x}`.  This is the analytic content `AGPExpRange`
  needs, and it also confirms §2b of the gap doc in-kernel.

Two disclosed `sorry`s remain in that file, both named and both documented:

1. **`exceptionalModulus_gt_log`** — `AGP`'s `D > log X` clause.  **Route correction, same lap:**
   my first diagnosis (the `Erdos4` chain projects away `Erdos48`'s Page witness, so re-threading
   it is adapter work) was WRONG, and the real obstruction is worse.  Tracing the chain to its
   root, `Erdos4/FGKMTPrimeExcision.lean:8` excises `B := (χ.modulus).minFac` — the *smallest
   prime factor* of the exceptional conductor — with the exclusion stated as coprimality.  No
   lower bound on `B` is possible even in principle: `m` can be huge with `minFac m = 2`, giving
   `B = 2 ≤ log X` always.  A Landau–Siegel bound on `m` does not help because `m` is not what is
   excised.
   **The repair is proved sound in-kernel this lap:** `exists_modulus_excision_of_unique` and
   `exists_uniform_modulus_excision` excise `m` itself with `AGP`'s own **divisibility** exclusion
   `¬ D ∣ d`, which is also the mathematically correct one — a character mod `d` is induced by a
   primitive character of conductor dividing `d`, so an exceptional conductor `m` pollutes only
   *multiples* of `m`.  Coprimality-to-`minFac` is strictly cruder than needed.
   Cost, stated plainly: `¬ m ∣ d` does not imply `d.Coprime (minFac m)`, so the new excision
   cannot feed the existing chain.  Using it means re-deriving `exists_uniform_twisted_sum` …
   `exists_exponential_prime_distribution` with divisibility excision — five upstream theorems in
   a dependency this campaign does not modify.  **That is the honest size of this item**, and it
   is no longer describable as adapter work.
2. `agpExpRange_holds` — the quantitative assembly, blocked on (1) and on that re-derivation.  The
   arithmetic is written out in its docstring: (★) +
   `Erdos446.eventually_primeCounting_tenth_bounds` + `φ(q) ≤ q ≤ exp((a/4)√log x)` reduces it to
   `(5/2) C log x ≤ exp((a/4)√log x)`.

**Box gotcha (new).** The wide cold builds of `Util.Linnik.Theorem` / the `Erdos4`–`Erdos48`
analytic trees hit `EMFILE` ("too many open files", errno 24) persistently, and **`taskset -c 0-2`
did NOT fix it** here — contrary to the reference corpus's `taskset` remedy.  The failure also
surfaced inside **`lake` itself** reading `.trace` files, not only in `lean` workers.  Our own
`src/` build is unaffected (the pre-commit full `lake build` is green, 10352 jobs); only the
unimported analytic dependency trees are hard to bring up.  This is why §2b–§2d of the gap doc are
marked *stated-and-sourced* rather than in-kernel axiom-audited; `probes/AgpAudit.lean` is the
prepared audit, to be run once that tree converges.

---

## ✅ LAP 6 (2026-09-28): `hjs` IS CLOSED, and `hlen` is a corollary

`54610ea` **`VandeheyTransport.lean`** — the parity machinery of lap 5 transported back to the
genuine Raney transducer.  The bridge is `runState_lrDelta_eq`
(`runState lrDelta M.toRState w = ι^{|w|} (runState rplusDelta M w).toRState`), and the
determinant PINS the phase (`runState_lrDelta_eq_iff`), so
`jointSet lrDelta s₀ t q x n = jointSet (prodStep rplusDelta) (s₀,0) (tPlus t, tPhase t) q x n`
as FINSETS — an ext, not an estimate.  Hence `jointStateFreq_lrDelta` (= `hjs`) and
`subWindow_rhoLR` (= `hρ`), both `#print axioms`-clean.

**`VandeheyOutLen.lean`** — `hlen` reduced to `hjs`, as the lap-4 finding predicted and with no
cone perturbation: `outLen δ out s₀ x n = Σ_t wCount δ s₀ t (blockLen out t) 1 x n`
(`outLen_eq_sum_wCount`), so the length-1 engine `tendsto_wCount_div` gives
`tendsto_outLen_div` with limit `c = Σ_t wLimit ρ t (blockLen out t) 1`, needing only a uniform
block-length bound `hB`.

**ARCHITECTURAL FINDING (lap 6).**  The concrete `out` of `VandeheyLRTrigger` is `lrOutN`, which
emits `L/R` LETTERS.  Its `outLen` is therefore the LETTER count, and that diverges per input
digit (infinite Gauss digit mean — `VandeheyRunCount`'s own finding).  So `hB`/`hlen` can NEVER
hold for `lrOutN`, and the capstone must be driven by the RUN clock.
`VandeheyRunBirkhoff.lean` (lap 6) supplies that clock:

* augment the state with the last emitted letter, `lrB (M,b) j = (lrDelta M j, last (lrOut M j))`;
* `altOut (M,b) j = numAlt (b :: lrOut M j) ≤ 2D + 1` (Lemma 2.2, `altOut_le`);
* `numAlt_lrWord_eq_sum` : `numAlt (b₀ :: lrWord hD s₀ x n) = Σ_{i<n} altOut (stateAt lrB … i) (cfDigit x i)`.

That is exactly the `wCount` shape, with a BOUNDED weight.  So the run count has an
`x`-independent Cesàro limit as soon as `JointStateFreq` holds for `lrB`, and positivity comes
from `outLenLimit_pos`'s argument.

**LAP 6 CLOSED THAT TOO.**  `VandeheyTransportB.lean`: the involution acts on the augmented
state by `ι'(M,b) = (ι M, !b)` (`lrOut_swapState` + `getLast?_map_not`), so the whole phase
argument is verbatim; `rplusB_common_reach` is the length-3 reach (2 digits to `diag(1,D)`, one
more digit whose block `lrOut ⟨diag(1,D)⟩ j = Lᴰʲ` is nonempty, which overwrites the remembered
letter).  Hence `jointStateFreq_lrB`, `subWindow_rhoLRB`, and

> `tendsto_numAlt_lrWord_div` — **Vandehey's Lemma 6.1 for the TRUE clock**: the emitted RUN
> count has an `x`-independent Cesàro limit along every CF-normal orbit.

**POSITIVITY (`hc`) IS ALSO CLOSED (lap 6, `VandeheyFirstLetter.lean`).**  The probe found two
exceptionless structural facts, and both are now theorems:
`Mat2.det_pos_iff_branch` (for a balanced matrix `0 < det` iff the branch is `c < a ∧ b < d`)
and `head_lrOut_eq_true_iff` (**the first letter of a nonempty block is `L` iff `det M > 0`**).
Since `det` flips at every digit, consecutive nonempty blocks start with OPPOSITE letters, so
`one_le_altOut_add` : `altOut i + altOut (i+1) ≥ 1` — internally if the first block alternates,
at the SEAM otherwise (a constant block ends where it starts).  Blocks are nonempty for digits
`≥ D` (`lrOut_ne_nil_of_le`), so every position with 2-digit window `[D,D]` is charged, each
step at most twice: `winCard [D,D] x n ≤ 2 · numAlt(… (n+1))` (`winCard_le_two_mul_numAlt`),
hence `γ(I_[D,D]) ≤ 2c` and `zero_lt_runRate : 0 < c`.

**NEXT: the ASSEMBLY.**  Everything the capstone asks for now exists for the run clock except
the final wiring, and the wiring is where the remaining design question is:
`mobiusUniformFreq_of_transducer` is stated for a transducer whose `outLen` is `|outWord|`, i.e.
the LETTER count.  The run clock is not of that form — `out` would have to emit one ℕ per
COMPLETED run, and the value of a run is not a function of a finite state (the partial run
length is unbounded).  So the capstone needs a variant whose rescaling clock is supplied
SEPARATELY from the output word:
* keep `out := lrOutN` (letters) for `hkK`/`hK`/`hgen`/`htail`/`hout` — all already proved or
  near-free there, and the occurrence counting goes through `VandeheyLRPattern`'s
  `card_cf_eq_card_patWord` (CF occurrences ↔ `patWord` occurrences in the letter stream);
* replace `hlen` by the RUN clock `tendsto_numAlt_lrWord_div` + `zero_lt_runRate`, and feed
  `Rescale.tendsto_div_of_tendsto_comp_of_monotone` with the run count as `ℓ`.
That restatement of the capstone is the next lap's work; nothing analytic is left.

**What is left of the capstone**What is left of the capstone**What is left of the capstone**What is left of the capstone's hypothesis list** (`mobiusUniformFreq_of_transducer`):
1. `hc : 0 < c` — the ONE piece `tendsto_outLen_div` does not give.  `c ≥ 0` is
   `outLenLimit_nonneg`; strict positivity is combinatorial (some state/digit pair of positive
   Gauss mass emits a nonempty block).  Route: pick one genuine one-letter window `w` and a
   state `t` with `ρ [w] t > 0` and `out t w ≠ []`, and bound `wLimit` below by that single
   term (`le_csSup` with `Q = {[w]}`) — the `wLimit` sSup is over finite subfamilies, so a
   one-element `Q` suffices.
2. `hB` for the `L/R` machine (uniform block length) — expected from the same alternation count
   that gives `K = 2D + 2 + |v|` in `VandeheyLRTrigger`.
3. `hgen` (near-free, `patWord_alternation`), `htail` (a cylinder estimate), `hcof`.

## ⚠ THE LAP-5 ROUTE FINDING (2026-09-28) — the crux is an ALTERNATING PIN

Lap 5 first de-factorized the output side (commit `39b452f`: `JointStateFreq δ s₀ ρ`,
`SubWindow ρ`, `tailMass` without `ν`), which F2 below forced.  Then
`probes/raney_parity_split.py` (3.5M CF digits, `D = 3`) settled the shape of what is left, and
it is NOT what the lap-4 handoff predicted.

**Three numeric facts, one table.**
1. The **signed density is ZERO**: `(1/n) Σ_{i<n} (−1)^i 1[w_i = q] 1[P⁺_i = t] ≤ 0.003` for
   every state and every short `q` (vs. a signal size of `0.25`).  So `lrDelta`'s joint law is
   exactly **half** the phase-corrected one, `ρ(q,t) = ½ ρ⁺(q, ι^p t)`, `p` the phase of `t`.
2. The **phase-corrected law itself does NOT factorize**: the two states `(1,2,0,3)` and
   `(2,1,1,2)` (at `D = 3`) split a joint mass of exactly `¼·γ(I_q)` between them in a
   `q`-DEPENDENT way (`0.158/0.092` at `q=[1]` vs `0.138/0.112` at `q=[4]`).  So F2 is real, but
   it is **not a parity artifact** — it is non-factorization of `rplusDelta` itself.
3. That is **consistent with the kernel**: `VandeheyCocycle.ClassEquidistribution δ t q` binds its
   reference constant `L` **inside** the per-`q` statement, so `classEquidistribution_rplusDelta`
   never claimed a `q`-independent `ν`.  De-factorizing was exactly the right repair, and the
   kernel already supplies the de-factorized `ρ⁺(q,t) = L(q,t)·γ(I_q)`.

**So the remaining content of `hjs` is the PARITY SPLIT, and it is irreducible.**  Since
`stateAt lrDelta … i = ι^i (stateAt rplusDelta … i)` and `det` pins the phase,
`1[stateAt lrDelta = t]` lives on ONE parity of `i`; the joint count is therefore the joint count
of the **product automaton** `δ* := rplusDelta × (ε ↦ ε+1)` on `RPlus D × ZMod 2` at the state
`(ι^p t, p)`.  Two dead ends, both checked this lap:
* the plain pin fails for `δ*` (its `n`-step kernel is `1[η+n=p]·(c + O(θⁿ))γ`, which oscillates),
  so `classEquidistribution_of_pin` does not apply — the period-2 wall reappears at the product;
* summing the signed identity over states gives `(1 − Σ_t c_t)·signedWin = o(n)`, i.e. `0 = o(n)`.
  The window-only parity balance `Σ_{i<n}(−1)^i 1[w_i=q] = o(n)` (the CF analogue of "normal to
  base `b` ⇒ normal to base `b²`") cannot be bootstrapped from the state statistics.

**THE ROUTE (identified lap 5, all inputs already in the kernel).**  Do not generalize the pin;
work with the product automaton's `devFun` written in the ORIGINAL automaton's events:

> `jointEvent δ* (d,η) (t,p) q k = if η + k = p then jointEvent δ d t q k else ∅`,
> hence `devFun δ* … k y = 1[η+k=p]·1[J_k] − L·1[W_k]`.

Write `σ_k := (−1)^{k+η−p} = ±1`, so `1[η+k=p] = (1+σ_k)/2`, and take the reference constant
`L := c/2` where `c` is the `rplusDelta` pin's constant.  Expanding
`∫ devFun*_k · devFun*_{k'}` against the FOUR existing estimates inside
`abs_integral_devFun_mul_le` (`hT1`–`hT4`: `|T1 − cγPJ| ≤ CθⁿγPJ`, `|T2 − γPJ| ≤ .79ⁿγPJ`,
`|T3 − cγPW| ≤ CθⁿγPW`, `|T4 − γPW| ≤ .79ⁿγPW`) the constant parts cancel EXACTLY at `L = c/2`
and what survives is

>  `mean part = (σ_{k'}/4)·( c·γ_q·PJ(k)·(1 + σ_k) − c²·γ_q·PW(k) ) =: σ_{k'}·R(k)`,  `|R| ≤ ½`.

`R` depends on `k` only.  So in the variance double sum
`∫ devAvg*² = K⁻² Σ_k Σ_{k'} ∫ devFun*_k devFun*_{k'}` the mean part contributes
`Σ_k R(k)·Σ_{k'∈[k+ℓ,K)} σ_{k'} = Σ_k R(k)·O(1) = O(K)` — **the alternating factor cancels over
the inner range**, which is exactly the cancellation the plain pin performed for free.  The rest
is the existing `Mρ^{gapExp}` majorant, also `O(K)`.  Hence `∫ devAvg*² = O(1/K)`, and from there
`classEquidistribution_of_pin`'s downstream half (`sum_gaussMeasure_windowBound_le`, the orbit
split, `tendsto_weighted_window_freq`) is **unchanged** and gives
`ClassEquidistribution δ* (ι^p t, p) q`, hence `hjs` for `lrDelta`.

**Work items, in order.**
1. Extract `hT1`–`hT4` out of `abs_integral_devFun_mul_le` as four named lemmas in
   `VandeheyTwoPoint.lean` (pure refactor; the existing proof then cites them).
2. `VandeheyParity.lean`: the product automaton (`prodStep`, `runState`/`stateAt` lemmas,
   `jointEvent_prod_eq`), the `devFun*` product identity, the two-point bound with the
   `σ_{k'}·R(k)` residue, and the alternating variance bound `∫ devAvg*² ≤ B/K`.
3. `classEquidistribution_prod` (re-run the `classEquidistribution_of_pin` endgame against the
   new variance bound), then `jointStateFreq_lrDelta`.
4. Only then `hlen` (corollary of `hjs`), `hgen`, `htail`.

## ⚠ TWO ROUTE-DECISIVE FINDINGS (2026-09-28 lap 4) — read before touching the supply side

### F1. The Raney automaton is PERIODIC: no uniform-length common reach, ever

`det (M · B j) = − det M`, so the determinant's sign is a **deterministic period-2 phase** on
`RState D`.  States of opposite phase are never simultaneously occupied, so no single target `z`
is reachable from EVERY state by words of one fixed length — and
`VandeheyTwo.classEquidistribution_of_common_reach` (whose hypothesis is exactly that) can never
be applied to `lrDelta`.  Equivalently `stateHorizonIntegral_pin_of_reach` is FALSE for a periodic
chain: the `n`-step kernel oscillates instead of converging.  Numeric: `probes/raney_reach.py`
(common targets exist for `D = 2,3,5,7,11,13`; no uniform length does).

**Repair, in the kernel as of lap 4** (`VandeheyRaneyReach.lean`, sorry-free):
* `Mat2.balanced_decomp_unique` — the Raney (L/R word, balanced matrix) factorization is UNIQUE.
  This pins the `Classical.choose`-defined `lrDelta`/`lrOut` for the first time
  (`VandeheyLR.lrStep_pin`), which is what makes any concrete computation with them possible.
* `Mat2.swapRows` (`ι M = J·M`) is an involution of the state set with `det (ι M) = −det M`,
  `lrDelta (ι M) j = ι (lrDelta M j)` (`lrDelta_swapState`) and
  `lrOut (ι M) j = (lrOut M j).map not` (`lrOut_swapState`) — an automaton isomorphism swapping
  the two phases, so the **phase-corrected** automaton `rplusDelta P a := ι (lrDelta P a)` on
  `RPlus D = {det = +D}` is a genuine finite automaton with `stateAt lrDelta … i = ι^i (stateAt rplusDelta … i)`.
* The arithmetic core: `lrDelta M j = [[0,D],[1,0]] ↔ D ∣ a + b·j ∧ D ∣ c + d·j`
  (`lrDelta_eq_zMinus` / `dvd_of_lrDelta_eq_zMinus`), solvable over `ZMod D` for prime `D`
  because `D ∣ det M` makes the two congruences equivalent (`exists_digit_zMinus`); the one
  exceptional state is `diag(1,D)` (`eq_zPlus_of_dvd`), and it steps to `diag(D,1)` whatever the
  digit (`lrDelta_zPlus`), which then returns on the digit `D` (`lrDelta_zDiag`).
* **✅ LANDED (lap 4).**  `RPlus D` (a `Fintype`), `rplusDelta`, and `rplus_common_reach` —
  every `P ∈ RPlus D` reaches `diag(1,D)` in EXACTLY 2 genuine digits (one step off the
  exceptional state, one step home).  Hence **`classEquidistribution_rplusDelta`**: the crux
  input of Theorem 1.1, `VandeheyCocycle.ClassEquidistribution (rplusDelta hD) t q`, is PROVED
  for every prime `D` and every genuine window `q`, and `tendsto_jointCount_rplusDelta` turns it
  into the `x`-independent joint frequency.  All axiom-clean (trust triple).

### F2. `JointStateFreq`'s PRODUCT form is FALSE for the concrete machine

`VandeheyOut.mobiusUniformFreq_of_transducer` assumes
`jointCount(t,q,x,n)/n → ν t · γ(I_q)` with a **single** `ν` independent of `q`.  That shape was
adopted on lap 1 because it makes countable additivity of the output limit free.  It is not
available: `probes/raney_joint_product.py` measures `ρ(q,t)/γ(I_q)` over 2.1M Gauss-distributed CF
digits and finds, for `D = 3`, four states whose ratio moves by up to **20 %** across
`q ∈ {[1],[2],[3],[4],[1,1],[1,2],[2,1]}` — a ~15σ effect (the other ten states are flat to 0.3 %).
For `D = 2` it DOES factorize, and the reason is visible: there the stationary law is uniform
(`1/6` on each reachable state) and a uniform law is invariant under every individual digit's
action, so the state decouples from the adjacent window.  The Raney digit steps are **not**
injective, the `D = 3` stationary law is `(0.125 ×6, 0.073 ×2, 0.052 ×2)`, and the state at `i` is
genuinely correlated with the digits just before `i` — which abut the window at `i`.

**Consequence.**  The capstone must be restated with a general
`ρ : List ℕ → S → ℝ`, i.e. Vandehey's own un-factorized `ρ ≪≫ μ̃`.  **The factorization is not
needed:** the reason it was adopted — controlling the escape mass of the countably infinite
alphabet — is recovered for free from the pointwise bound

> `ρ(w,t) ≤ γ(I_w)`  (because `jointCount ≤ winCard` at every `n`),

so `Σ_{w ∉ F} ρ(w,t) ≤ 1 − Σ_{w ∈ F} γ(I_w)`, and `exists_boundedWords_sum_gt` (already proved)
supplies an `F` with `Σ_F γ(I_w) > 1 − ε`.  Every `ν t * γ(I_w)` in `VandeheyOutputFreq.lean`
becomes `ρ w t`, and `wLimit` becomes a sup over finite subfamilies of `Σ_{w∈F} a w * ρ w t`.

**Next, in order.**
(i) ~~Finish `rplus_common_reach`~~ — DONE (lap 4).
(ii) Generalize `JointStateFreq` → `JointStateFreq'` with `ρ`, and port `VandeheyOutputFreq.lean`
     (~1100 lines, mechanical: the only real change is the escape bound above).
(iii) Restate `mobiusUniformFreq_of_transducer` against `ρ`.
(iv) Then `hjs` is `ClassEquidistribution (rplusDelta hD) t q` for each `q` — which
     `classEquidistribution_of_common_reach` delivers from (i) — plus the **parity split**:
     `jointCount lrDelta` is supported on one parity of `i`, so it is
     `½(jointCount rplusDelta ± Σ_i (−1)^i …)`, and the signed half is FREE from the existing
     two-point machinery (`abs_integral_devFun_mul_le` bounds an ABSOLUTE value, so inserting
     `(−1)^k` changes nothing in `integral_devAvg_sq_le`).
(v) `hlen` is then a COROLLARY, not an analytic leaf: Vandehey's own §6 proof writes `ℓ(n)` as a
    Birkhoff sum of a BOUNDED window/state function (augment the state with the last emitted
    letter, so the seam term is local), which the `wCount`/`wLimit` machinery evaluates.

## 0′. `hK`/`hkK` — **CLOSED** for the `L/R` transducer (2026-09-28 lap 3)

`lr_trigger_bounds` (`VandeheyLRTrigger.lean`) supplies both trigger hypotheses of
`mobiusUniformFreq_of_transducer` for the concrete machine, with `K = 2D + 2 + |v|`, for every
target word `v` that ALTERNATES somewhere (`v[i₀]? ≠ v[i₀+1]?`).  The chain, all axiom-clean:

1. `VandeheyRunBound.numAlt_lrOut_le_two_mul` — Vandehey Lemma 2.2 in run form: one ingested
   digit emits at most `2D` alternations, with NO dependence on the digit.  Proof: the `j`-free
   column identity `(M.b, M.d) = lrProd w ·ᵛ (M'.a, M'.c)` plus the observation that each letter
   ADDS one coordinate to the other, so the coordinate sum bounds the alternation count; a
   vanishing coordinate persists under only one letter, i.e. the rest of `w` is a single run.
   **No case split on vanishing denominators** — Vandehey's Cases 1–3 disappear.
2. `VandeheyAltCount.occIn_le_numAlt_add` — abstract: occurrences of an alternating `v` starting
   in the first emitted block are `≤ numAlt (block) + 2 + |v|`, with no reference to block LENGTH.
3. `VandeheyAltCount.trigger_bounds_of_occIn_le` — `hK` and `hkK` ARE one statement (`kOut` is an
   increment of `occIn`; the `hK` sum telescopes along CF prefixes).

**The translation is CLOSED (lap 3, later).**  `VandeheyLRPattern.lean`:
`map_range'_eq_patWord` (CF digits match ⇒ the stream reads the forced pattern),
`cfDigit_of_map_range'_eq_patBody` (converse), and `card_cf_eq_card_patWord` (a BIJECTION
`n ↦ lrPos w n - 1` between CF occurrences in `[1,N)` of parity `b` and pattern occurrences).
The dictionary itself is `VandeheyLRRuns.lean`: `lrTail_lrPos` (after `n` runs the point is `Tⁿw`
or `(Tⁿw)⁻¹`), `lrExpand_eq_runIdx_parity`, `lrExpand_ne_succ_iff`.

**⚠ STRUCTURAL FINDING (lap 3) — rescale by RUNS, never by LETTERS.**  The Gauss measure has
infinite digit mean, so `lrPos w n / n → ∞` a.e.: the *letter* count per input digit DIVERGES and
the density of run boundaries in the L/R word is `0`.  Any plan that rescales the L/R-letter index
against the input index by a positive constant is WRONG.  What is linear is the RUN count, which
is why Lemma 6.1 is about emitted CF digits.  The bijection above is the right interface precisely
because it lands on CF INDICES, not letter positions.  Upper half now proved:
`VandeheyRunCount.numAlt_lrWord_le` — at most `(2D+1)·n` alternations after `n` input digits
(Lemma 2.2 summed over blocks, one alternation per seam).

**Next, in order.**
(a′) **`hlen`, the remaining analytic leaf**: the run count grows at least LINEARLY,
    `runs(lrWord n)/n → c > 0`.  Route: `lrRun_eq` says `M₀·B_{a₁}⋯B_{aₙ} = lrProd w · M_n` with
    `M_n` in a FINITE set, and the input product's own Stern–Brocot word has exactly `n` runs
    (one per input digit); right-multiplying by a bounded matrix perturbs the path's cone by a
    bounded amount, so the two run counts differ by a bounded FACTOR.  Making "perturbs the cone
    boundedly" precise is the work.  A cheaper sufficient form may be available: the frequency
    argument only needs `liminf runs/n > 0`.
(b′) Then factor the assembly (see (b) below) and assemble.

(a) The run↔CF-digit translation (HANDOFF NEXT 2), superseded above.  An occurrence of a CF word `v` in the image's
    expansion is an occurrence of the single `L/R` word `w_v = X · R^{v₁}L^{v₂}⋯ · Y` with the two
    boundary letters FORCED by alternation (maximal runs at both ends = a one-letter look-around).
    `w_v` alternates, so (a) is exactly what supplies the `i₀` that `lr_trigger_bounds` needs.
(b) Because the assembly's `hout` demands `out` emit the image's CF digits and the `L/R` machine
    emits letters, `mobiusUniformFreq_of_transducer` must be FACTORED: an `OutputWordFreq`
    conclusion (every output word has an `x`-independent Cesàro frequency, `K` allowed to depend
    on `v`) plus a separate CF-digit bridge through (a) and a second `VandeheyRescale` at the
    density of run boundaries.  Note `hK`/`hkK` are FALSE at the `L/R` level for constant `v`
    (`v = LL` occurs ~`j` times in a block), which is precisely why the bridge, not a direct
    instantiation, is the right architecture.

## Queue

0. **THE CRUX (binding, see `DIRECTION.md` CURRENT DIRECTIVE) — Vandehey §5–§6, the OUTPUT
   side, in `VandeheyOutputFreq.lean`.**  Decomposition, as fixed by lap 1 of 2026-09-28:
   - ✅ `gaussMeasure_allWordsEvent`, `exists_boundedWords_sum_gt` (the finite digit-truncated
     escape from the infinite CF alphabet — the elementary stand-in for Airey–Mance tightness).
   - ✅ `wCount_le_of_finset` (pointwise split), `eventually_wCount_le` (the upper-bound engine:
     `wCount ≤ (Sb + ε)·n` eventually, for any bound `Sb` on finite length-`m` subfamily mass).
   - ✅ `eventually_le_wCount` (truncation LOWER bound) and **`tendsto_wCount_div`**: for a
     bounded nonnegative weight on the countably infinite length-`m` genuine words, the
     state-restricted count has Cesàro limit `wLimit ν t a m` — defined as a supremum over
     finite subfamilies, so it mentions NO `x`.  That is the published Lemma 4.3's infinite
     case, with no ergodic theory, no Ryll-Nardzewski, no Vitali-Hahn-Saks.
   - ✅ Trigger layer: `fireAt` / `fireTotal` (the untruncated per-position multiplicity, a
     supremum that is ATTAINED because `K` bounds it — `exists_fireAt_eq_fireTotal`),
     `trigCount` (bucketed by length × state) with `trigCount_eq` identifying it with
     `Σ_i fireAt i J`, `trigLimit`, and `tendsto_trigCount_div` (the truncated count converges
     `x`-independently).  Tail layer: `trigPrefix` / `trigInd` / `tailMass`,
     `fireTotal_sub_fireAt_le` (pointwise: a missed trigger forces the window into
     `trigPrefix`), `trigTotal_le_trigCount_add` (aggregate), `wLimit_trigInd_le`.
   - ⬜ **NEXT: close the assembly** (`tendsto_triggerCount`): a trigger family
     `A ⊆ List ℕ × S` with multiplicity `k`, uniform bound `F ≤ K`, bucketed by word length.
     `F − F_{≤m} ≤ K·1_{U_m}`, `U_m ⊆ ⋃_t {i : tᵢ = t, window_m(i) ∈ P_{t,m}}` where `P_{t,m}`
     is the set of length-`m` words agreeing with a trigger of length `> m`.  The ONE honest
     hypothesis is `τ_m := Σ_t ν t·γ(familySetC P_{t,m}) → 0`, i.e.
     `γ(⋂_m familySetC P_{t,m}) = 0`: the triggers decide a.e.  Note `familySetC P_{t,m}` is
     decreasing in `m`, so `τ_m` converges automatically — the hypothesis is only that the
     limit is `0`, which is Vandehey's Lemma 4.3 condition (2) in honest form.
     Conclusion: `(1/n)Σ_{i<n} F(x,i) → Σ_{(q,t)∈A} k(q,t)·ν t·γ(I_q)`, `x`-independent.
   - ⬜ **Then `MobiusCFNScale` needs a per-matrix `vandehey_matrix_action_of_uniformFreq`.**
     The existing one is global (`∀` matrices); the leaf route needs the single-matrix form so
     the either-or endgame can pin `L = γ(I_v)` from a per-matrix uniform-frequency statement.
     Cheap refactor, do it when the assembly lands.
   - ⬜ Only THEN the supply side: `raneyNorm` as a total function, `RaneyState D` as a
     `Fintype`, and the common-target reach (old HANDOFF NEXT 1–3).

1. **Vandehey crux — the single leaf `MobiusCFNScale`** (`VandeheySmith.lean`):
   `x ↦ p·x` preserves CF-normality for prime `p`.  The Smith shortcut WORKED and is formalized
   (`mobiusCFN_of_leaves`), and the Serret leaf is PROVED (`mobiusCFNGL2_holds`), so
   `vandeheyUniformFreq_of_scale` reduces all of Theorem 1.1 to this one statement.
   - **Now under way: Vandehey §2.**  `VandeheyMat2.lean` (the matrix layer, `act_cfMat`) and
     `VandeheyNormalForm.lean` (`M_D`, `isMD_entry_bounds`, `finite_isMD`) are in.  The next
     item is **Lemma 2.1**, `M·J A_j = A_{d₀} J A_{d₁} ⋯ J A_{d_m}·M'` with `M' ∈ M_D` — a
     Euclidean descent, elementary, spelled out in `HANDOFF.md`.
   - The structural insight of 2026-09-28: **the fibre merges by Serret** (`serret_cfEquiv`),
     so class-relative synchronization is a corollary, not a probe observation.
   - After §2: the abstract **output-frequency transfer principle** (Vandehey §5–§6 in
     transducer-free form) — if a finite-state transducer reads the input digits and the joint
     (state, input window) frequencies converge to `x`-independent limits, then every output
     word frequency converges.  That is pure combinatorics; it needs no CF theory and no
     analysis, and it is what turns `tendsto_jointCount_classStep` into digit frequencies of
     `p·x`.  Then §2 (Raney normal forms, finiteness of the det-`±p` state set) and the fibre
     step (state = class × mergeable fibre) remain.
2. **Joint Lambert, unconditional.**  Discharge `AGP` and `PrimeIntervalSupply` from PNT+
   (`WeakPNT_AP`, PNT).  After that, the quantitative §6 count is a separate target.
3. **C3/MRT `CharTailCancellation`.**  This is the only C3 input with a standard-literature proof:
   Euler product, then `L(1,χ) ≫ q^{-1/2}`, then arg-L winding.
4. **Elliott margin check.**  A Littlewood-strength `ζ'/ζ ≪ log t / log log t` would suffice if
   every consumer in `ElliottZetaTheta.lean` tolerates a `log log log` margin.  Check that.  If
   one doesn't, record "Vinogradov or nothing" in the Maze.
5. **SwingC2 triage.**  Delete or restate `tauMomentPrimesShiftStruct_of_primeDensity`, which
   takes the vacuous `PrimeDensityAP`, and `survivorLeaf_of_struct`.

## Lap notes (newest first)

### 2026-09-28 — OPERATOR OBJECTIVE items 1-3, all three landed

1. **`moshchevitinShkredov_cf_false` PROVED** (`MoshchevitinShkredovRefuted.lean`, wired into
   the root import).  Witness `x = [0;1,2,3,…]` from `exists_irrational_mem_iInter_cfCylinder`
   on the nested words `[1,…,s+1]`; `exists_irrational_cfDigit_succ` is the reusable form.
   Strictly increasing digits ⇒ the first letter of a genuine block pins its unique start
   position ⇒ every block occurs at most once ⇒ every frequency is `O(1/p)`, so the criterion's
   hypothesis is vacuous at `σ = 0` while `γ(I_1) = log₂(4/3) > 0`.  Maze:
   `hall_moshchevitin_shkredov_cf_false`.
2. **`conjC3_of_geom_input_band'`** (`C3MrtBlockDefect.lean`) is the C3 headline with `hURM`
   discharged by `uniformResonantMass_holds`.  `C3MrtURMLowHigh.lean` retired as the redundant
   second route: its sorried narrow high range `|t| < 2δ` had no consumer and is removed; its
   sorry-free lemmas stay.  Maze: `hall_urm_low_high_split`.
3. **`exists_jointFreq_limit` retired.**  Its `Synchronizing` hypothesis is unsatisfiable, and
   that is now a THEOREM, not just a probe: `not_synchronizing_of_injective_quotient` — an
   automaton with a quotient on which every letter acts injectively has no synchronizing word.
   For the det-`±D` transducer the quotient is the row-lattice class in `ℙ¹(ℤ/D)` and each
   `B_a ∈ GL₂(ℤ/D)`.  Axiom-free.  Maze: `hall_vandehey_synchronizing_transducer`.  The live
   transfer principle is `VandeheyCocycle.tendsto_jointCount_of_classEquidistribution`, whose
   hypothesis `ClassEquidistribution` is now the single crux of the Vandehey front.

### 2026-09-28 lap 1 (review) — the output side opened; crux re-aimed

Reviewed the last three laps: all three had gone into the transducer's *input* side (Raney §2,
the pin, Doeblin) while §4.3/§5/§6 — the piece that decides whether the input side is worth
anything — had never been touched.  Course-corrected in `DIRECTION.md` CURRENT DIRECTIVE.

The structural find that makes §5–§6 elementary: our own
`tendsto_jointCount_of_classEquidistribution` returns the joint (window, state) limit in
**factorized** form `ν t · γ(I_q)`.  Vandehey only has `ρ ≪≫ μ̃` (Remark 3.6) and therefore
needs a genuine measure to get countable additivity; with the product form, countable
additivity reduces to countable additivity of `γ` alone, and the infinite CF alphabet is
escaped by a finite digit-truncated family of mass `> 1 − ε`.  That is also exactly the
tightness patch the published §3 owes and never pays.

Landed in the kernel (`VandeheyOutputFreq.lean`, all `#print axioms`-clean):
`gaussMeasure_allWordsEvent`, `exists_boundedWords_sum_gt`, `wCount_le_of_finset`,
`eventually_wCount_le`, plus the guard-rule quartet for the new `Prop` `JointStateFreq`.

