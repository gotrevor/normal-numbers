# PENDING WORK — the queue

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

New math comes first.  Trusted literature inputs (`AGP`, `CharPrimeSumLogQ`,
`ZetaLogDerivExponent`) stay as hypotheses and are not queue items until a new result
needs one discharged (DIRECTION standing rule 3).

*(Both former queue items were cleared on 2026-09-29, lap 1 of the §7 objective.)*

1. ✅ **SwingC2 triage — done.**  `tauMomentPrimesShiftStruct_of_primeDensity`,
   `survivorLeaf_of_struct` and `TauMomentPrimesShiftStruct` are **deleted** (no consumer
   anywhere in the repo).  `PrimeDensityAP` survives as a record of the intended AP input, with
   the 2026-09-25 review's vacuity defect **repaired** by the extra clause `M ≤ Y`; the repair is
   load-bearing and proved so in the kernel by `SwingC2.primeDensityAP_pos` (the repaired
   statement forces a prime to exist in the stated range; the old one did not).  The live open
   obligation on the headline path is unchanged: `shiftedDivisorIncidence_holds`.

2. ✅ **OVERVIEW refresh — done.**  `OVERVIEW.md` + the pandoc-built `OVERVIEW.html` (hand-patched;
   it carries custom CSS, so do NOT regenerate it wholesale from the Markdown).  Vandehey Thm 1.1
   now stated as PROVED, with the §3-free route described and §7 Problem 1 named as the live
   target; joint Lambert corrected to one remaining input (`AGP`).

## Lap notes (newest first)

### 2026-09-29 — lap 1 of the §7 objective: targets frozen, and the endgame is OFF ℤ

`src/NormalNumbers/VandeheyS7.lean` (new, in the root import).

**Frozen (never weakened):** `AffineCFN q r` (`∀ x, IsCFNormal (Int.fract x) → IsCFNormal
(Int.fract (q*x+r))`), `AffineUniformFreq q r` (the crux: every genuine word has an
`x`-INDEPENDENT frequency limit in the image; no value asserted), `IsQuadOverRat`,
`VandeheyS7Problem1`, `vandeheyS7_mul_phi := AffineCFN φ 0`, `vandeheyS7_add_phi := AffineCFN 1 φ`.
An `Audit` section pins all three headline Props by `rfl`, and
`vandeheyS7_mul_phi_of` / `vandeheyS7_add_phi_of` prove in-kernel that the two instances really
are instances of the general Prop (so the general form cannot silently drift off them).

**The lap's advance on the crux.**  The attack map's §3 asserted that Vandehey's either-or
endgame "works verbatim for any `M`", so that the whole problem reduces to frequency EXISTENCE.
That is now a THEOREM, axiom-clean:

    affineCFN_of_uniformFreq : 0 < q → AffineUniformFreq q r → AffineCFN q r

for EVERY real `q > 0` and EVERY real `r` — no integrality, no quadraticity, nothing about ℤ[φ].
Both instances are reduced (`vandeheyS7_mul_phi_of_uniformFreq`, `vandeheyS7_add_phi_of_uniformFreq`).

Two things made it port.  (i) The integer version (`Literature.mobiusCFN_of_uniformFreq`) pins the
unknown limit with `exists_cfNormal_with_cfNormal_image`, a Γ-orbit argument that does not exist
over ℤ[φ]; the replacement pin is the MEASURE-theoretic witness
`exists_feasible_cfNormal_affine` (both `x₀` and `q x₀ + r` CF-normal, from two conull sets
meeting on the feasible window), which never looks at the arithmetic of the coefficients and so is
indifferent to the unit group.  (ii) That witness needs `-q < r < 1`, which `r = φ` violates;
`affineCFN_add_int` / `affineUniformFreq_add_int` show both Props depend on `r` only mod 1, so
`Int.fract` reduces the general `r` to the window.

**Consequence to carry: the ℤ[φ] wall is entirely on the frequency-EXISTENCE side.**  No part of
what remains needs a limit VALUE.  Route A's nodes (window/bounded-distortion lemma, distributional
merging, trigger windows) all feed `AffineUniformFreq` and nothing else.

Guard rule discharged: content locators `affineUniformFreq_one`, `affineCFN_int_translate`;
degenerate case `not_affineCFN_zero` proves the `q = 0` instance FALSE (the junk expansion of `0`
contains no `[1]`, while `γ(I_[1]) > 0`), so `q ≠ 0` in `VandeheyS7Problem1` is load-bearing.

**Lap 2 (same day), DIRECTION item 2 — the obstruction as Lean: DONE.**
`src/NormalNumbers/VandeheyS7Wall.lean`, four theorems, all axiom-clean.

* `finite_intCast_abs_le` — the content locator for Vandehey's finiteness: over ℤ a bound on
  the absolute value bounds the set.  This, and nothing about the dynamics, is the certificate.
* `infinite_zPhi_abs_le_one` — **the certificate has no ℤ[φ] analogue**: `{x ∈ ℤ[φ] : |x| ≤ 1}`
  is INFINITE, witnessed by the powers of `ζ = φ − 1 = φ⁻¹ ∈ (0,1)`.  Dirichlet's unit theorem
  made concrete; `IsZPhi.mul` is where `φ² = φ + 1` enters.
* `infinite_zPhiMatrix_det_one_bounded` — the matrix form: infinitely many determinant-one
  matrices over ℤ[φ] with every entry bounded by 1 (`!![1, ζ^n; 0, 1]`).
* `conj_goldenRatio_integral_forces_diagonal` — **pathwise merging is impossible.**  If `V`, `N`
  are integral and `diag(φ,1) · N = V · diag(φ,1)` then `V 0 1 = V 1 0 = 0`.  So no coupling or
  synchronising-word merging argument exists for `x ↦ φx`, and Vandehey §5's Saloff-Coste–Zúñiga
  citation must be replaced by a DISTRIBUTIONAL statement (Birkhoff–Hopf cone contraction).

Scope stated honestly in the module docstring: this kills the finiteness LEMMA over ℤ[φ], which
is all the Theorem 1.1 proof uses; it does not compute the actual reachable set.

**Lap 3 (same day), DIRECTION items 3–4: the pipeline is FACTORED.**
`src/NormalNumbers/VandeheyS7Clock.lean`, all axiom-clean.

`VandeheyOut.mobiusUniformFreq_of_runClock` — the restatement that made Thm 1.1 assemble — has a
proof that is ONE rescaling and nothing else: no transducer, no output stream, no determinant, no
state set.  So it ports verbatim to a real affine map, and the whole of §7 Problem 1 now reads

    affineCFN_of_runClock : 0 < q → RunClock ℓ rate → SampledUniformCount q r₀ ℓ → AffineCFN q r₀

with both φ instances instantiated (`vandeheyS7_mul_phi_of_runClock`, `..._add_phi_of_runClock`).
The two named hypotheses are the finite-state step, split along its real fault line:

* `RunClock ℓ rate` — monotone clock, positive `x`-independent rate.  Formally MAP-FREE (it
  does not mention `q`, `r₀`), which is the half of the bundle that is not about the image at
  all.  Believed fine: the attack map's 2026-08-24 measurement has `l(n) = c₁n(1+o(1))`
  surviving the loss of Lemma 2.2 because `∫log(1+a)dγ < ∞`; `c₁ ∈ [0.965, 0.989]`.
* `SampledUniformCount q r₀ ℓ` — `x`-independent Cesàro limit for each word's count sampled
  along the clock.  **This is the entire remaining crux**, and the only place the lost ℤ[φ]
  finiteness has to be replaced (trigger windows + distributional merging, Route A nodes 2–3).

Content locator `affineUniformFreq_of_runClock_locator` (identity clock, rate 1) discharges the
guard rule; `not_affineCFN_zero` already rules out vacuity.

**Lap 4 (same day), Route A node 1: the compact-fiber substitute is PROVED.**
`src/NormalNumbers/VandeheyS7Distortion.lean`, all axiom-clean.

The 2026-08-24 correction 2 (drop "compact in PGL₂(ℝ)", keep BOUNDED DISTORTION) is now cashed
in.  `MobState` is a Möbius state in the shape every post-emission Raney state has (`c ≥ 0 < d`,
positive determinant) — over ANY ring, which is the point — with
`distortion s = (c + d)/d`, and

  `MobState.mob_ratio_comparable` : for `0 ≤ u ≤ v ≤ 1`,
     `(v−u)/distortion ≤ (M v − M u)/(M 1 − M 0) ≤ (v−u)·distortion`.

This is precisely the rôle the finite state set played in Vandehey §5–§6.  There one takes a
maximum of per-state constants over a finite set; here ONE constant covers the whole family, and
that two-sided comparability is all his `f_j^±` Riemann squeeze ever consumes.
`uniform_comparable_of_bddDistortion` states the consequence along a whole state sequence.

So the open obligation is narrowed to the HYPOTHESIS `BddDistortion s` — Route A's window lemma,
now a named Prop.  Guard rule: `distortion_id` (content locator; identity has distortion 1 and
the theorem degenerates to equality) and `not_bddAbove_distortion` (distortion is unbounded over
the ambient family, so `BddDistortion` is a real restriction, not a theorem of the setting).

**Lap 5 (same day): distortion is an EXACT COCYCLE, and that is the window lemma's mechanism.**
`src/NormalNumbers/VandeheyS7Cocycle.lean`, all axiom-clean.

`MobState` is now closed under composition (`comp`, the matrix product; the nonnegativity fields
were added for this), and the denominators satisfy

  `den_comp` : `den (s ∘ t) x = den t x * den s (t x)`  — EXACTLY, no constant, no inequality.

Denominators are a cocycle over the action.  Hence, with the two-point distortion
`distOn s u v = den s v / den s u` (and `distortion s = distOn s 0 1`),

  `distOn_comp` : `distOn (s∘t) u v = distOn t u v * distOn s (t u) (t v)`,
  `distOn_le_one_add` : `distOn s u v ≤ 1 + (v−u)·distortion s` (no upper bound on `v` needed),
  `distortion_comp_le` : `distortion (s∘t) ≤ distortion t · (1 + |t([0,1])|·distortion s)`.

**Why this is the mechanism.**  The post-emission state is `A_out⁻¹ · M₀ · A_{a₁}⋯A_{aₙ}`.  The
right factor is a composition of Gauss inverse branches — its distortion is the classical Rényi
constant, which is exactly the probes' measured "`log 4` for every integer control".  The left
factor is the drifting ℤ[φ] part with no finiteness certificate.  `distOn_comp` says the drifting
factor is only ever evaluated ON THE INNER IMAGE, and `distOn_le_one_add` says its contribution
→ 1 as that image shrinks.  That is the structural reason the probes measured ℤ[φ] distortion
SATURATING at ≈ 2.5 instead of drifting, while the conjugate place ran to 10^644 — and it is the
inductive step any window bound must run on.

**Lap 6 (same day): reading is FREE; emitting is the whole problem.**
`src/NormalNumbers/VandeheyS7Branch.lean`, all axiom-clean.  (`MobState.hdet` relaxed from
`0 < det` to `det ≠ 0` — Raney states have `det = ±D`, and the comparability ratio of
`VandeheyS7Distortion` is orientation-blind, so the refactor cost nothing.)

The `φ`-machine is now a Lean object: `gaussBranch a : y ↦ 1/(a+y)` (totalised at `a = 0`),
`phiState = diag(φ,1)`, `runWord` the fold.  Two facts, and they are sharper than the attack map
expected.

1. **Reading an input digit is free.**  Right-composition by `A_a` sends the lower row `(c,d)` to
   `(d, c + a·d)`, so with `a ≥ 1`, `c ≥ 0` it lands in `c ≤ d` FROM ANYWHERE and stays.  Hence
   `distortion_runWord_le_two`: after at least one input digit the distortion is `≤ 2`, from any
   initial state, with NO arithmetic hypothesis and no finiteness.  This is the in-kernel form of
   the probes' "real place flat, no drift", and over ℤ it is Rényi's bounded-distortion property.
2. **Emitting swaps the rows.**  `emit e s` is left-multiplication by `(−e,1;1,0)`, i.e.
   `(a,b;c,d) ↦ (c−e·a, d−e·b; a, b)` (`mob_emit` proves it is `z ↦ 1/z − e`).  So
   `distortion_emit : distortion (emit e s) = (s.a + s.b)/s.b` — the UPPER row's ratio, while
   reading controls the LOWER row's.  Reading pushes the state into the good region; emitting
   throws it back out.  **That exchange is the entire content of the window lemma.**

So the obligation is sharpened from `BddDistortion` (a sequence of abstract states) to
`EmitRowBound` (one explicit arithmetic ratio `(a+b)/b` of two ℤ[φ] numbers, at emission times
only), and `bddDistortion_of_emitRowBound` proves the two are the same statement.  `EmitRowBound`
is exactly what both 2026-08 probes measured saturating at ≈ 2.5.

**Lap 7 (same day): THE BURST PENALTY IS A CONSTANT, not a function of the burst length.**
`src/NormalNumbers/VandeheyS7Burst.lean`, all axiom-clean.  This is the lap that dissolves the
loss of Vandehey's Lemma 2.2.

The obvious estimate loses a factor per emitted digit, so a burst of `k` emissions with no
intervening read would cost `2^k`, and Lemma 2.2 (which bounded bursts) was MEASURED not to port
(`burst ≤ C + log(1+a)/Lévy`, unbounded, tracking `0.843·ln a`).  The dissolution is that a burst
should never be analysed digit by digit at all:

1. **A burst of `k` emissions is ONE pullback.**  It is left-multiplication by `B⁻¹` for
   `B = A_{e₁}⋯A_{e_k}`, whose columns are the continuants `(p_{k−1},q_{k−1})`, `(p_k,q_k)`.
   `distortion_pullback` (EXACT, for arbitrary `P, Q`):

       distortion_after = distortion_before · (β − M 1)/(β − M 0),   β = P/Q .

   The whole burst costs ONE factor: the ratio of the distances from the two image endpoints to
   the convergent `β = p_{k−1}/q_{k−1}`.
2. **That factor is ≤ 2 whatever `k` is.**  The burst emits `e₁…e_k`, so the image lies in the
   cylinder `C = [e₁,…,e_k]`, endpoints `p_k/q_k` and `(p_k+p_{k−1})/(q_k+q_{k−1})`, and `β` is
   outside `C` with

       far  = |β − p_k/q_k|                     = 1/(q_{k−1}q_k),
       near = |β − (p_k+p_{k−1})/(q_k+q_{k−1})| = 1/(q_{k−1}(q_k+q_{k−1})),

   so `far/near = (q_k+q_{k−1})/q_k ≤ 2` since `q_{k−1} ≤ q_k`.  **The burst length does not
   appear.**  `burst_ratio_le` proves the consequence; `one_le_burst_ratio` records that the
   lower side is free, so all the content is on the upper side.
3. `distortion_pullback_le` assembles it: pre-burst distortion `≤ 2` (which reading gives for
   free, lap 6) plus the geometric input gives post-burst distortion `≤ 4`.  A **window bound of
   4 along the whole run.**

**Still owed (the only gap between here and the window lemma):** the continuant bookkeeping —
that the emitted word's matrix is the continuant matrix, `q_{k−1} ≤ q_k`, and the two distance
identities above.  All standard and self-contained.  `ConvergentGap` names exactly that input,
and `burst_ratio_le` is stated so it plugs in as `hfar : v − β ≤ 2*(u − β)`.

**Lap 8 (same day): `ConvergentGap` is PROVED.**
`src/NormalNumbers/VandeheyS7Convergent.lean`, all axiom-clean.

`Conv` is the continuant state `(p',q',p,q)` with the recursion
`(p',q',p,q) ↦ (p, q, p' + a·p, q' + a·q)`, folded over the word; `Conv.Good` is the invariant
(`0 ≤ p'`, `0 ≤ q' ≤ q`, `1 ≤ q`, `Δ² = 1` for `Δ = p q' − p' q`), carried one step at a time
(`Good.step`, the determinant by `linear_combination`).  Then:

* `conv_far_eq` — **the gap identity**: `p/q − p'/q' = ((q+q')/q)·((p+p')/(q+q') − p'/q')`.
  `Δ` CANCELS, so the determinant is needed only as a nonzero, never at its value `±1`.
* `conv_ratio_le_two` — the constant is in `[1, 2]`, and `q' ≤ q` is the whole of it.
* `conv_far_le_two_near` — `far ≤ 2·near`, for EVERY word of positive digits, of EVERY length.
  The burst length appears nowhere.
* `conv_single` — content locator: one digit, `β = 0`, ratio `(e+1)/e ≤ 2`, visible by hand.

So the geometric input of lap 7 is no longer owed, and the window-lemma chain is complete as
mathematics:  reading ⇒ distortion ≤ 2 (lap 6) · burst = one pullback with penalty ≤ 2 (lap 7,
now unconditional by this lap) ⇒ **distortion ≤ 4 along the whole run**.

**Still owed on the window lemma (bookkeeping only, no new mathematics):** wire `Conv.of` to the
machine — that the emitted word's pullback matrix has first column `(p', q')` of `Conv.of` of the
emitted word, and that the image interval really lies in that word's cylinder (the emission
trigger).  Then `distortion_pullback_le` applies verbatim and `BddDistortion`/`EmitRowBound` are
theorems.

**Lap 9 (same day): THE WINDOW LEMMA IS ASSEMBLED.**
`src/NormalNumbers/VandeheyS7Window.lean`, axiom-clean.

`windowBound` : a state of distortion `≤ 2` — which reading gives for free — whose image
endpoints sit in the emitted word's cylinder has **post-burst distortion `≤ 4`**, with the
emitted word's LENGTH appearing nowhere.  Four laps meet in its proof: `distortion_runWord_le_two`
(lap 6), `distortion_pullback` (lap 7, exact), `conv_far_le_two_near` (lap 8).

Supporting: `cylNear`/`cylFar`/`cylBeta`; `conv_near_ne_zero` (the near distance is `Δ/((q+q')q')`
— the ONLY use of the continuant determinant in the whole development, and only as a nonzero);
`TriggerGap` (the emission trigger in the one form the estimate consumes); `triggerGap_endpoints`
(content locator — the cylinder's own endpoints satisfy it, so the hypothesis is not empty).

**The remaining bookkeeping on this node, with no estimate in it:** turn the machine's operational
emission trigger into `TriggerGap`, i.e. show the image interval lies in the emitted word's
cylinder (which is what emission MEANS), and identify the pullback matrix's first column with
`Conv.of`'s `(p', q')` (checked by hand: `A_e = (0 1; 1 e)` and `Conv.of [e] = ⟨0,1,1,e⟩`, and the
recursions agree).  Then `BddDistortion` / `EmitRowBound` are theorems.

**NEXT (lap 10): the SECOND half of `SampledUniformCount`.**  With the window lemma in hand the
remaining crux is the distributional merging — Birkhoff–Hopf cone contraction of the Hilbert
projective metric, NOT coupling (`not_synchronizing`-style pathwise merging is provably impossible
here, `conj_goldenRatio_integral_forces_diagonal`).  `mob_ratio_comparable` is already the right
language: a uniform distortion bound gives uniform two-sided comparability, which is exactly a
Hilbert-metric diameter bound on the cone of image measures, and a bounded-diameter image is what
makes the transfer operator a strict contraction.  First target: state the contraction as a Prop
on `MobState` sequences and prove that `distortion ≤ K` gives a finite Hilbert diameter.

**(superseded) NEXT (lap 9).**  Either (a) finish that wiring — define the emission trigger as a predicate on
`MobState` and prove the cylinder containment by induction on the burst, discharging
`EmitRowBound`; or (b) open the SECOND half of `SampledUniformCount`, the distributional merging
(Birkhoff–Hopf cone contraction on the Hilbert projective metric), which is the remaining crux
once the window lemma lands and which `mob_ratio_comparable` is already the right language for.
(a) is finite and closes a node; (b) is the harder one.  Take (a) first — it converts four laps
of structure into a discharged hypothesis.

**(superseded) NEXT (lap 8).**  Prove `ConvergentGap` for the real thing: define the continuants of the
emitted word, prove `q_{k−1} ≤ q_k` and the two distance identities (`|p/q − p'/q'| = 1/(qq')`
from `det = ±1`), and discharge `ConvergentGap`.  That closes the window lemma
(`BddDistortion` / `EmitRowBound`), leaving `SampledUniformCount`'s SECOND half — the
distributional merging / trigger windows — as the remaining crux.

**(superseded) NEXT (lap 7).**  Attack `EmitRowBound` directly.  The geometry that should give it: emission
fires only when the image interval `M([0,1])` lies inside a cylinder `(1/(e+1), 1/e)`, which pins
`b/d` and `(a+b)/(c+d)` both to that cylinder; combined with the free bound `(c+d)/d ≤ 2` this
gives `(a+b)/b ≤ 2·(e+1)/e ≤ 4` for a SINGLE emission.  The open part is a BURST of consecutive
emissions with no intervening read, where the crude factor compounds — which is exactly the
content of the lost Lemma 2.2 (`burst ≤ C + log(1+a)/Lévy`, unbounded, measured 0.843·ln a).
So the next target is: state the emission trigger as a hypothesis, prove the single-emission
bound, and then find what replaces the burst bound.  Note `∫ log(1+a) dγ < ∞` is still available,
which is why the run clock survives; the question is whether a MULTIPLICATIVE burst penalty can
be averaged the same way.

**(superseded) NEXT (lap 6).**  Close the quantitative loop.  Two sub-nodes, in order:
(i) the Rényi bound for the inner factor — `distortion` of any composition of Gauss inverse
    branches `A_a : y ↦ 1/(a+y)` is ≤ 4, by induction through `distortion_comp_le` (or directly:
    a Gauss branch has `c = 1, d = a`, so `distortion = (1+a)/a ≤ 2`, and the image has length
    `1/(a(a+1)) ≤ 1/2`, so the product telescopes).  This is self-contained and should close.
(ii) the emission rule, which is what makes `|t([0,1])|` small often enough.  Needs the
     φ-transducer as a Lean object; `distortion_comp_le` is the shape its invariant takes.

**(superseded) NEXT (lap 5).**  Build the `φ`-transducer as a Lean object so `BddDistortion` can be attacked:
states as `MobState`s carrying `IsZPhi` entries, the update `M_{n+1} = A_out⁻¹ M_n A_{a_{n+1}}`,
and the emission rule.  Then the window lemma itself, remembering correction 1: Vandehey's
Lemma 2.1 is an INTEGER DESCENT and does not port, so the proof must be new.  The likeliest
route is that emission fires exactly when the image interval falls deep into a cylinder, and
pulling the digits off re-expands the map — i.e. the renormalisation ENFORCES the distortion
window; `mob_ratio_comparable` is already the right language to state that in.

**(superseded) NEXT (lap 4).**  Attack `SampledUniformCount` for `q = φ`.  The first sub-node is Route A's
window lemma stated for the REDUCED post-emission states in terms of BOUNDED DISTORTION (not
compactness in PGL₂(ℝ) — correction 2 of 2026-08-24; the raw state set is unbounded in the
PROVED case too).  That needs the φ-transducer's state as a Lean object, which does not exist
yet: building it (states as Möbius maps over ℤ[φ], update `M_{n+1} = A_out⁻¹ M_n A_{a_{n+1}}`,
distortion as a real functional) is the lap-4 deliverable, with the window lemma as the first
disclosed `sorry` on it.

**(superseded) NEXT (lap 3), DIRECTION items 3–4.**  Factor the Thm 1.1 pipeline so its finite-state step is a
NAMED hypothesis, then state the compact-fiber substitute that discharges it: the bounded-
distortion window lemma for reduced post-emission states (NOT the integer descent — corrected
2026-08-24), and the distributional merging statement.  Every node wires to `AffineUniformFreq`,
which `affineCFN_of_uniformFreq` has already shown is the entire remaining problem.

**(superseded) NEXT (lap 2), DIRECTION item 2 — the obstruction as Lean.**  State and prove, against the
existing Raney transducer, that the reachable ℤ[φ] state set is infinite (unit drift), and the
non-merging fact (`M⁻¹VM` integral for `M = diag(φ,1)` forces `V` diagonal).  Then factor the
Thm 1.1 pipeline so its finite-state step is a NAMED hypothesis that a compact-fiber substitute
can discharge.

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

