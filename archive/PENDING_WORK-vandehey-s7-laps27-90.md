# Archived: Vandehey §7 lap records (laps 27–90) from PENDING_WORK.md

Moved out of `PENDING_WORK.md` on 2026-09-29 when the §7 campaign closed (operator wrap-up item 4).
Nothing is deleted in this repo; the live summary is `docs/VANDEHEY-S7-FALSE-STARTS.md` and
`DIRECTION.md`'s "Completed runs".

## ⭐ VANDEHEY §7 — LAP 88 (review): ROUTE A (UNIVERSALITY), AND THE CRUX IS `BlockForget`

**Binding version = `DIRECTION.md` CURRENT DIRECTIVE.**  Commits `32ae5b1` (S7-BF), `c3babcd`
(S7-EQ).  This SUPERSEDES the lap-77 section below as the attack path (its facts stay true).

### What the review found

* **Fact (ε) — route B's instrument has a ceiling.**  Route B (`OrbitWordBound` + cited
  `GaussACRigidity`) needs `limsup freq ≤ C·γ(I_w)` with `C` uniform in `w`.  Its only surviving
  instrument is a cover of the state-dependent target by a FIXED finite family (S7-WD/WD′/CV/FT).
  1. State-blind is impossible: over the whole width-`≥η` box the targets exhaust `(0,1)` (a state
     `z ↦ v + ε(z−u)` of width `1/2` sends ANY `z` into `I_w`), so such a cover has mass `1`.
  2. Net-indexed is quantitatively dead: the target `s⁻¹(I_w)` is an interval of length `≍γ(I_w)`,
     so resolving it needs `ρ ≲ γ(I_w)`, the box then carries `≍ρ^{-4}` cells, and the unweighted
     cover mass is `≍γ(I_w)^{-3}`.  The ℤ[φ]-separation of the reachable states (`|α|·|α^σ| ≥ 1`)
     says this is intrinsic, not a net artefact.
  So route B's residual is irreducibly the WEIGHTED joint statement `ClassFreqBound` — which needs
  the state's empirical law AND absolute continuity.  Route B is now the ALTERNATIVE, not the front.
* **The repo already owned a second reduction with no cited input.**  `affineCFN_of_uniformFreq`
  (universality ⟹ the headline, via Vandehey's §6 either-or, whose measure witness is
  `exists_feasible_cfNormal_affine`) and `affineUniformFreq_of_runClock : RunClock ℓ rate →
  SampledUniformCount q r₀ ℓ → AffineUniformFreq`.  No `GaussACRigidity`, no constant `C`, no
  absolute continuity — and the attack map called this route the cheaper one (§3 endgame is FREE).
  50 laps of momentum walked past it; lap 88 makes it the front.

### The decomposition to work — `BlockForget`

Landed lap 88 (`VandeheyS7BlockForget`, axiom-clean):

    blockAvg s T w z = (1/T) Σ_{j<T} slotObs w (pairStep^[j] (s, z))

* `abs_slotCount_sub_sum_blockAvg_le` — **the sliding-block identity**: `|slotCount p −
  Σ_{m<p} blockAvg (s_m) T w (Gᵐx)| ≤ T`.  (Each `j`-shift of a length-`p` window costs `j`.)
* `BlockForget w` — `∀ε>0 ∀η>0 ∃T>0, ∀ s s′ of width ≥ η, ∀ z ∈ (0,1),
  |blockAvg s T w z − blockAvg s′ T w z| ≤ ε`.  **The new crux.**  No `x`, no normality, no measure.
* `RefCesaro w` — for the fixed `refState` and each `T`, the Cesàro average of
  `blockAvg refState T w (Gᵐ x)` has an `x`-independent limit.
* `WidthAfford Φ x` — for every `δ` an affordable floor `η` (= S7-SK's `exists_eventually_widthBad_le`
  transported from the clock to the time axis; still resting on `MeanSlack` + `ClockLinear`).
* ⟹ `exists_abs_slotCountFreq_sub_le` (one `L`, independent of `Φ` and `x`, within `4ε`),
  `exists_tendsto_slotCountFreq`, `tendsto_slotCountFreq_eq`, `exists_uniform_slotCountFreq`.

### Order of work (= DIRECTION's mandated moves (b), (c))

1. **DONE lap 88 — the analysis: S7-EQ** (`VandeheyS7IntervalFreq`, axiom-clean).
   `tendsto_blockCount_Ioo : blockCount (Ioo α β) p x / p → γ(Ioo α β)` for CF-normal `x`, by a
   two-sided cylinder squeeze (`meetWords`/`insideWords`, the sharp form of S7-CV, the digit
   truncation paid once).  This is strictly sharper than the lap-62 `VandeheyS7IooFreq` bound.
2. **NEXT — discharge `RefCesaro` from S7-EQ.**  `blockAvg refState T w` is a finite combination of
   events `{z ∈ I_v ∧ G^{|v|} z ∈ J_v}` with `J_v` an INTERVAL: the state after reading `v` is a
   function of `v` (S7-WC `pairIter_fst_congr`), the emission condition depends on one more digit,
   and `mapBlockSet t w 0 = t.mob⁻¹(I_w) ∩ (0,1)` is an interval because `t.mob` is monotone.
   Each such event is an interval inside a cylinder — `G^{|v|}` restricted to `I_v` is a monotone
   bijection onto `(0,1)` — so S7-EQ plus the level-`|v|` reparametrisation evaluates its frequency,
   and the countable union over `v` is truncated by bounded digits exactly as in S7-EQ.
   Sub-steps to name in Lean: (i) `mapBlockSet_eq_Ioo` (the target IS an interval, from
   `cfCylinder_endpoints` + monotonicity of `mob`); (ii) `cylinderPullback_Ioo` (the branch of
   `G^{-j}` on `I_v` maps intervals to intervals); (iii) assemble.
3. **THEN `BlockForget` itself.**  Instruments in hand: `disc` (S7-CN: reading is inert, the
   discrepancy is a Möbius map carried unchanged — so the proof must average, not couple),
   `distortion_runWord_le_two` (the SHAPE contracts), fact (δ)'s box, and S7-SS (stall ⟺ straddle).
   Shape to try first: a state's block average differs from another's only through the EMISSION
   SCHEDULE (S7-SO), and the two schedules differ by a bounded lag (S7-LD), so the two block sums
   are two counts of the same word in two reparametrisations of ONE output stream — the difference
   should telescope into `O(lag)/T`.  That is the first honest attempt, and it is a Lean-able
   statement about `runClock` differences, not a measure-theoretic one.
4. Keep chipping `MeanSlack`/`ClockLinear`: route A needs them for `RunClock`'s rate and for
   `WidthAfford`.

### Not to be re-walked

* `CellMemory`, `ClassFreqBound` as the front (route B's residual; `CellMemory` is a restatement —
  lap 80).  Extending the unweighted cover machinery (S7-WD/WD′/CV/FT).  The window-function frame.
  `GaussACRigidity` (route A does not use it).
* `VandeheyS7FinTarget.lean` is an UNCOMMITTED, unfinished module in the working tree (the level-`M`
  cover-mass lemma only, `sum_gaussMeasure_coverWords_le`).  It belongs to route B's ceiling and its
  headline `slotCount_le_of_finiteTargets` was never written.  Either finish it as the *record* of
  fact (ε) part 1 or delete it; do NOT build on it.


## ⭐ VANDEHEY §7 — LAP 77 (review): FACT (δ), AND THE NEXT TARGET IS `ClassFreqBound`

**Binding version = `DIRECTION.md` CURRENT DIRECTIVE.**  Commits `5a5f0ef` (S7-BX), S7-IN.

### What the review found

* **The width floor was only half the input.**  Laps 58–76 hunted it alone.  Compactness of the
  state set needs `width ≥ η` AND bounded distortion — and the second half is FREE:
  `denRatio := (c+d)/d` obeys `r ↦ 1 + 1/(r+a−1)` on a read (contracting *uniformly in the digit*,
  because the bound does not see `a`) and moves by a factor in `[1/2,2]` on an emission.  So
  `r > 1/2` from step 1 and `r ≤ 6` from step 2 along ANY run.  Unconditional.
* **`width = |det|/(d·(c+d))` exactly**, and `|det|` is conserved by the run.  Hence the box lemma:
  `width ≥ η` ⟹ `d, c+d ≤ √(6|det Φ|/η)` ⟹ all four entries in `[−M, M]` (using `0 ≤ b ≤ d`,
  `0 ≤ a+b ≤ c+d`).  **The predictor's range is precompact** — directive fact (δ).
* **`hΦ` is a triviality** (S7-IN, `exists_mob_eq`): `MapState` has REAL entries and bans only
  `det = 0`, so `z ↦ v + ε(z−u)` interpolates any `u,v ∈ (0,1)`.  Lap 76's "next action #1" (a case
  analysis on `⌊φ·fract x⌋`) was a misreading; it is not needed and would not have worked, since
  `z ↦ φz` does not map `[0,1]` into `[0,1]`.
* **The `∀ Φ` form of `hBA` is needlessly strong.**  `orbitWordBound_of_runBlockAverage_one` asks
  for the block average at ONE `Φ`; discharge that one.

### The decomposition to build next — `ClassFreqBound`

Fix `η, ρ > 0`.  Let `K_η ⊂ ℝ⁴` be the box of fact (δ) and `{B_i}_{i<M}` a partition of it into
cells of diameter `ρ`, with centres `t_i`.  Then for `n` with `width(s_n) ≥ η`:

    s_n ∈ B_i  ⟹  mapBlockSet s_n w j  ⊆  E_i := (t_i-pullback of G^{-j}I_w) inflated by ρ' ,

with `ρ' = O(ρ/η²)` by the S7-PB Lipschitz bound.  Each `E_i` is a FIXED set, so CF-normality of
`x` controls `freq{n : Gⁿx ∈ E_i}` — this is exactly the part fact (α) says predictability kills,
and the compactness is what buys it back.  The residual is

    `ClassFreqBound` :  limsup (1/p) #{n < p : s_n ∈ B_i ∧ Gⁿx ∈ E_i}  ≤  C · freq{s_n ∈ B_i} · γ(E_i)

i.e. the state cell and the current orbit point do not conspire.  **Do NOT drop the state
constraint and sum over `i`**: that costs the factor `M = M(η,ρ)` and gives no fixed `C`.
This is Vandehey's *class equidistribution* with a compact class space in place of a finite one.

Order of work:
1. `stateCell`/`clusterSet` and the inclusion `mapBlockSet s w j ⊆ E_i` for `s` in a `ρ`-cell —
   this is the S7-PB Lipschitz bound re-run with the state as the variable, not the target.
2. `blockAverage_le_of_classFreq`: `BlockAverageBound ⟸ ClassFreqBound + width-frequency`.
3. Then `ClassFreqBound` itself.  The honest sub-question to probe first: is it FALSE for some
   predictable family inside the box?  A kernel refutation there is as valuable as a proof, and it
   would force the arithmetic-of-`Φ` branch of fact (α).

### LAP 78 progress (commits `48c0703`, `84d24cb`, + S7-CL)

* **S7-LG (`VandeheyS7Ledger`)** — the height ledger telescopes.  `∏ b_k ≤ C·∏(a_{k+2}+5)`
  unconditionally (`prod_emitFac_le`), hence `card_bigEmit_le`: big output digits are rare at
  rate `O(1/log T)`.  This is the **burst half** of the width-frequency question.
* **S7-SL (`VandeheyS7Slot`)** — `BlockAverageBound` has no block structure: one emission, one
  test.  `blockAverageBound_iff_slot` restates the crux as a relative frequency among emission
  times.  Free bound `B = 1` (`slotCount_le_runClock`) is what a proof must beat by `γ(I_w)`.
* **S7-CL (`VandeheyS7Class`)** — directive item (c) DONE.  `StateNet` is the net interface,
  `clusterSet` the fixed sets, `mapBlockSet_subset_clusterSet` the containment, and
  `blockAverageBound_of_classFreq` the reduction
  `ClassFreqBound + WidthFreqBound ⟹ BlockAverageBound`, with **no loss of constant** (the
  per-cell denominators sum to the clock, `sum_cellCount_le_runClock`).

### Next attack (directive item (d))

1. **`WidthFreqBound`** — the drift half.  **S7-SA (`VandeheyS7Stall`) closes its structural
   half**: a stall of length `k` forces `width ≤ 36/fib(k+1)²`, absolutely (no `Φ`, no `x`, no
   normality — the two `|det Φ|`s cancel).  Contrapositive `stall_length_lt_of_width`: a state
   of width `≥ η` has been stalling `O(log(1/η))` steps.  So the narrow times are exactly the
   *deep interiors of long stalls*, and `WidthFreqBound` is now the purely combinatorial
   statement that long stalls have small total length-excess — i.e. Vandehey's Lemma 6.1
   (`ℓ(n) = c₁n(1+o(1))`), which the 2026-08-24 probe measured as SURVIVING the loss of
   Lemma 2.2 (burst ≤ C + log(1+a)/Lévy, and `∫ log a dμ < ∞`).
   **S7-AG (`VandeheyS7Age`) finishes the translation**: the finite-range stall identity
   (`runState_add_of_stall'`, the old one assumed a stall FOREVER) plus the stall clock
   `stallAge` give `width (runState Φ x n) ≤ 36/fib(stallAge n + 1)²` pointwise.  So
   "narrow at time `n`" IS "has not emitted for ≳ log(1/η)/log φ steps", and `WidthFreqBound`
   is now a statement about the **emission schedule alone** — no geometry, no state space, no
   cells.  What is left is exactly: the times lying deeper than `K(η)` inside a stall have
   frequency → 0 as η → 0.
   **S7-DB (`VandeheyS7Debt`) collapses that to ONE scalar statement.**  The current stall age is
   a debit on the height ledger: `log fib(stallAge n + 1) + Σ log b_i ≤ ledgerConst + Σ log(a_i+5)`
   (`log_fib_stallAge_le`), i.e. `stallAge n · log φ ≤ slack n` up to a constant.  And summing the
   stall clock is an identity about the schedule:
   `Σ_{n<p} stallAge n = ½ Σ_{stalls} len(len+1)`.  So `Σ_{n<p} stallAge n = O(p)` gives
   `Σ len² = O(p)`, and Chebyshev gives `Σ_{len>K} len = O(p/K) → 0` — which IS `WidthFreqBound`
   by S7-AG.  **Remaining obligation, in full:** the height ledger's running slack has bounded
   Cesàro average, equivalently `(1/p) Σ_{n<p} log d_n = O(1)` — positive recurrence of one
   scalar walk reflected at `√(|det Φ|/6)`.  No geometry, no cells, no state space.
   **S7-SK (`VandeheyS7Slack`) DOES the reduction — and corrects the route.**  S7-DB's stall
   bound is a LOWER bound on the height, so it gives "long stall ⟹ narrow", not the converse,
   and the converse is FALSE (one huge input digit narrows the state with no stall at all).
   The honest reduction goes through the slack directly and is cleaner:
   `slack m := log d_{m+2} − log √(|det Φ|/6) ≥ 0` (`slack_nonneg`, from `d_runState_ge`), and

       `width_ge_of_slack_le` :  slack m ≤ S  ⟹  e^(−2S) ≤ width ,

   with an ABSOLUTE exponent — the two `|det Φ|`s cancel.  Chebyshev on a nonnegative sequence
   (`widthBadCount_le_sum_slack`) then gives `exists_eventually_widthBad_le`:

   > **MeanSlack** (`Σ_{m<q} slack m ≤ A·q` eventually) **+ ClockLinear**
   > (`c·q ≤ runClock(q+2)` eventually) ⟹ for every `ε > 0` there is `η > 0` with
   > `widthBadCount Φ x η q ≤ ε·runClock(q+2)` eventually.

   ✅ **Interface FIXED by S7-FT (`VandeheyS7Front`).**  `WidthFreqOrder` is the hypothesis in
   the order the decomposition needs (ε first, then an affordable width floor η — which is also
   the order the NET is chosen in), and `blockAverageBound_of_front` /
   `blockAverageBound_of_scalar` assemble the whole §7 front:

   > **`ClassFreqBound` (uniformly over nets) + `MeanSlack` + `ClockLinear` ⟹
   > `BlockAverageBound B`.**

   Three hypotheses, and two of them are scalar statements about the emission schedule alone.
   Only `ClassFreqBound` is about the state space at all.

   🔻 **And `ClockLinear` looks like a CONSEQUENCE of `MeanSlack`, not a separate hypothesis.**
   S7-GR (`VandeheyS7Growth`) has the first half: `two_pow_le_fib` (`2^k ≤ fib(2k+1)`) turns
   S7-DB's Fibonacci height bound into a LINEAR comparison,
   `stallAge_le_slack : stallAge n ≤ 1 + 2·slack n / log 2`.  So `MeanSlack` bounds the mean
   stall age: `Σ_{n<q} stallAge(n+2) ≤ 3q + (2/log 2)·Σ slack`.
   ✅ **DONE — S7-RS (`VandeheyS7Reset`).**  `stallAge_sub_self` (the reset time has zero age),
   `card_smallAge_le` (`#{n<q : stallAge n < K} ≤ (runClock q + 1)·K`, via the injection
   `n ↦ (n − stallAge n, stallAge n)` into resets × range K), `card_range_le`
   (`q ≤ K(N_q+1) + (1/K)Σ stallAge`) and `clockLinear_of_meanStallAge`.
   **`ClockLinear` is now a THEOREM given a bounded mean stall age**, and S7-GR turns
   `MeanSlack` into exactly that.  So the §7 front has TWO hypotheses, not three.
   Next Lean step: compose S7-GR + S7-RS into `clockLinear_of_meanSlack` and feed it to
   `blockAverageBound_of_scalar`, dropping `ClockLinear` from its signature.

   So the ENTIRE width leg is now two scalar facts: bounded Cesàro average of `log d_n`
   (positive recurrence of one walk reflected at `√(|det Φ|/6)`) and Vandehey's Lemma 6.1.  S7-LG bounds bursts; what remains is that long
   *non-emitting* runs are rare.  Structural observation to formalize: a non-emitting run of
   length `L` forces the input digits `a_n … a_{n+L−1}` to agree with the CF expansion of the
   single point `s_n⁻¹(1/k)` straddled by the image — so a long run is a long coincidence with a
   *predictable* word.  CF-normality of `x` limits those only for FIXED words, which is where
   fact (δ)'s finiteness has to be reused.
2. **Construct a `StateNet`** from `runState_entries_abs_le` (S7-BX) — a genuinely finite net of
   the box; currently `StateNet` is an interface, not a theorem.
3. **`ClassFreqBound`** itself.  S7-MY (`VandeheyS7Mem`) settles the MECHANISM: if the cell
   membership at time `n` is a function of the last `L` input digits, then "selected AND the
   next digits are `v`" is the occurrence of the single word `u ++ v`, so CF-normality applies
   to the JOINT event with no independence assumption, and quasi-multiplicativity
   (`gaussMeasure_append_le`, lap 50) gives `ClassFreqBound` with the ABSOLUTE constant
   `C = 8 log 2` — independent of `L`, of the selector set, and of the number of cells
   (`memory_joint_le`).  So the one remaining gap is:

   > **`CellMemory`** — up to times of small frequency, which cell of the fact-(δ) net `s_n`
   > lies in is determined by a bounded number of recent input digits.

   Fact (γ) says the *matrix* remembers everything; `CellMemory` asks only that its *position
   in a ρ-net* does not.  Attack: `s_n = (O_n⁻¹ Φ P_{n−L}) · Q_L`; the composition with the
   last-`L` word `Q_L` contracts the distortion (`distortion_runWord_le_two`) but NOT the
   location (S7-MM refutation).  The location is carried by `O_n⁻¹`, i.e. by the emitted word —
   so the real question is whether the recent emitted word is itself recent-input-determined.

   ⚠️ **`CellMemory` in the PATHWISE form is dead, and this is already on record.**
   `papers/vandehey-2017-open-problem-attack-map.md` §3: pathwise merging is *provably*
   impossible for `Φ = diag(φ,1)` (two states coincide iff `Φ⁻¹VΦ` is integral, which forces
   `V` diagonal, i.e. the same input prefix; `2x` merges at step 3, `φ` never in 1200 steps).
   The width alone kills it: `width ≍ d⁻²` and `log d` is a two-sided random walk over the
   WHOLE history (S7-HT), so no bounded window determines the ρ-cell.  The replacement the
   attack map names is **distributional** merging — Birkhoff–Hopf contraction of the Hilbert
   projective metric on the positive cone, which is what `distortion_runWord_le_two` already
   is for the SHAPE.  So the correct next form of the obligation is not "the cell is
   finite-memory" but "the empirical joint law of (cell, future word) factorizes".

   ⭐ **And the attack map says the endgame is FREE** (Vandehey §6): `E_Φ = Φ(CF-normals)` has
   positive Lebesgue measure and CF-normals are co-null, so `E_Φ ∩ E ≠ ∅`, and the either-or
   trick upgrades that to `E_Φ ⊆ E`.  Hence the ENTIRE problem reduces to *"every string
   appears in Φx with a limiting frequency independent of the CF-normal x"* — **no limit
   identification, no `γ(I_w)` on the right-hand side**.  `OrbitWordBound` (the directive's
   objective) is the Pyatetskii–Shapiro route to the same place; the universality route is the
   recorded alternative and is cheaper, but it is OUTSIDE the current directive, so it is
   logged here for the next altitude lap rather than acted on.

### Still open, unchanged

The width floor in FREQUENCY form (`freq{n : width(s_n) < η} → 0 as η → 0`) is still needed to
reach the box at all.  Note what fact (δ) changes about it: the states of width `< η` are exactly
the states about to emit a LARGE digit of the image `y`, so the frequency form is a *tail bound on
`y`'s digits* — strictly weaker than normality of `y`, and the first place to look for a
bootstrap.


## ⭐ VANDEHEY §7 — LAP 76: `StateData` WAS VACUOUS; `PinnedData` REPLACES IT

**Commits `7f36c66` (S7-SA) and `6df6823` (S7-PN).  Read before any use of lap 75's headline.**

### The defect

`stateData_of_orbitWordBound` (kernel, axiom-clean): the crux IMPLIES lap 75's `StateData`.  With
the unit clock, `lowState (Gⁿy/Gⁿx)` is a legitimate `MobState` (width `Gⁿy/Gⁿx`, distortion `1`)
sending `Gⁿx` to `Gⁿy`, so the pinned pullback set contains `Gⁿx` iff `Gⁿy ∈ I_w` and
`BlockAverageBound` unwinds to the conclusion.  Together with lap 75's
`orbitWordBound_of_stateData` this is a closed circle: **S7-SC's repair did not repair anything.**

Rule, sharper than S7-SC's: *pinning a witness to a TYPE pins nothing.*  `MobState` is large enough
to interpolate the single pair of points the coupling ever evaluates.  A hypothesis about a machine
has content only when its data is pinned as a FUNCTION of the input.

### The repair (`VandeheyS7Pin`, S7-PN)

`StatePin x Φ N s v`: `s 0 = Φ`, `N 0 = 0`, `N (n+1) = N n + |v n|`, `v n ≠ []`, digits of `v n`
genuine, `(s n).mob` maps `(0,1)` into `(0,1)`, and the step as MATRICES

    cylState (v n) ∘ s (n+1) = s n ∘ readStateAt x n .

`y` appears nowhere in it.  `StatePin.realize` then PROVES `G^{N n} y = (s n).mob (Gⁿ x)` from
`y = Φ.mob x`, and `StatePin.stateCoupling` gives S7-SC's coupling for free.  The non-gameability
certificate is `StatePin.eq_of_emit` (via `MobState.comp_left_cancel`): `(x, Φ, v)` determines `s`
and `N` outright.  `PinnedData` / `orbitWordBound_of_pinnedData` is the new front.

### Where the front stands after this lap

    vandeheyS7_mul_phi / _add_phi
      ⇐ GaussACRigidity (C/log 2)   -- cited, standing rule 3
      + ImageTight                  -- audited sound (S7-AU)
      + PinnedData q r₀ C           -- S7-PN; only non-bookkeeping part is BlockAverageBound

### Next attack

1. **Build a `StatePin` for `Φ = diag(φ,1)`**, i.e. exhibit `v` (the Raney emission) with the
   reduced-state condition.  `VandeheyLRTransducer` has `lrStep_spec`/`lrRun_eq`/`act_startState_eq`;
   the missing piece is the `MapsTo` field, which is exactly "the state is reduced".  Existence of
   `v` is NOT free — it is the transducer's correctness — but it is finite bookkeeping, not analysis.
2. **Then, and only then, fact (α)**: `BlockAverageBound` for the pinned sets.  Unchanged as the
   wall.  Note the pinned sets now have both their `γ`-mass (S7-PB tower bound) and their
   predictability (S7-PN `eq_of_emit`) certified, so the statement is finally the clean
   "empirical vs expected for a predictable family".
3. Re-audit every remaining `∃`-bundle against the SHARPER rule (type-pinning is not pinning):
   `ImageTight`, `AnchoredPullback`, `StateClock` were audited under the weaker rule only.


## ⭐ VANDEHEY §7 — LAP 74 DECOMPOSITION (review lap; binding version = `DIRECTION.md`)

**This supersedes the "next actions" of `HANDOFF-2026-09-29-lap58-73.md`.**  Everything below the
lap-27 header is still correct history; read this first.

### What the review found

* **Crux-neglect.**  Nine of laps 58–73 attacked the SECOND obligation (`ImageTight` →
  `AnchoredPullback` → `StateClock`).  The crux `OrbitWordBound` got no direct attack in that run.
* **`StateClock`'s uniform width floor is the wrong shape.**  Directive fact (β) says a
  post-emission state can straddle `1/k` at a scale far below any `η`; such a state HAS width
  `< η`.  So the true transducer states admit no uniform floor.  `StateClock` existentially
  quantifies its states, so it is not refuted — but its natural instantiation is dead, and a
  further lap on it in the uniform-`η` form is forbidden by the directive.
* **The width floor is shared** between the two obligations: it is precisely the hypothesis of the
  new pullback bound.  So the honest single problem is "how often is the state narrow?".

### What landed lap 74 — the measure side of the crux is DONE (`VandeheyS7Pull`, axiom-clean)

| name | statement |
|---|---|
| `MobState.expand_le` / `contract_le` | `(width/distortion)·|u−v| ≤ |mob u − mob v| ≤ (width·distortion)·|u−v|` on `[0,1]` |
| `MobState.volume_preimage_le` | **arbitrary** `A`: `|mob⁻¹A ∩ (0,1)| ≤ (distortion/width)·|A|` |
| `MobState.gaussMeasure_preimage_le` | `γ(mob⁻¹A ∩ (0,1)) ≤ (2·distortion/width)·γ(A)`, `A ⊆ (0,1)` measurable |
| `gaussMeasure_preimage_iterate` | `γ(G^{-j}S) = γ(S)` |
| `MobState.gaussMeasure_preimage_tower_le` | **the tower is free**: the bound on `s⁻¹(G^{-j}I_w)` is independent of `j` |
| `blockPullback_sum_le` | a block of length `L` pulls back to total mass `≤ (2K/η)·L·γ(I_w)` |
| `MobState.one_le_volume_preimage_image` | content locator: the `1/width` is not an artefact |

Method note worth keeping: the general-`A` bound comes from `Set.InjOn.invFunOn` +
`LipschitzOnWith.hausdorffMeasure_image_le` + `MeasureTheory.hausdorffMeasure_real (μH[1] = volume)`.
No change-of-variables, no open-set decomposition, no measurability hypothesis on `A`.

Why the BLOCK form and not one output time at a time: while the input point is frozen the
transducer emits `L` forced digits, and those are the first `L` digits of the single point
`z = s(Gⁿx)`.  The event "`w` occurs at offset `j` in the block" is `Gⁿx ∈ s⁻¹(G^{-j}I_w)`, and
`G^{-j}I_w` is a countable union of cylinders — not an interval, which is why the lap-65 interval
bound `sub_le_of_image_le` could not be used.  Gauss invariance makes the whole block cost the
same constant as one step, so the estimate is LINEAR in `L` with density exactly `γ(I_w)`.

### S7-FB / S7-BL (same lap): forced blocks, and the width/length equivalence

`VandeheyS7Forced` + `VandeheyS7Block`, all axiom-clean:

* `MobState.cfDigit_image_eq_basepoint` — a forced block is a chunk of the CF expansion of the
  BASEPOINT `s.mob 0`.  For `s = O_t⁻¹ Φ P_n` that is `O_t⁻¹ Φ (p/q)`, a `GL₂(ℤ)`-image of
  `φ·(rational)`, Serret-equivalent to `φ p/q`.
* `MobState.width_le_of_forced` — forcing `w` costs `width ≤ 2·distortion·γ(I_w)`; equivalently
  (`one_le_pullbackConstant_of_forced`) the lap-74 pullback constant is `≥ 1/γ(I_w)`, so on a
  forced block the pullback bound degenerates to the trivial `≤ 1`.
* `gaussMeasure_cfCylinder_mul_fib_le` — cylinder decay, `γ(I_u)·fib(|u|+1)² ≤ 1/log 2`.
* `MobState.fib_sq_mul_width_le_of_forced` — **the cap**: `fib(L+1)²·width·log 2 ≤ 2·distortion`,
  i.e. `L = O(log(1/width))`.
* `MobState.exists_forcedLength_bound` — for every floor `η>0` and cap `K` there is an `L₀`
  beyond which no such state forces a word.

**The route's two halves are ONE hypothesis**: `width ≥ η ⟺ forced blocks shorter than L₀(η,K)`.
So "the pullback needs a width floor" and "the counting needs bounded bursts" are the same
statement, and the crux's residual is the FREQUENCY of narrow states, plus the distribution of the
basepoints the long bursts spell out.

### Attack order for the next laps

1. **S7-BD (block decomposition).**  State, in Lean, that the output-word count over `p` output
   digits equals `Σₙ #{j < Lₙ : Gⁿx ∈ sₙ⁻¹(G^{-j}I_w)}` for a monotone clock `n ↦ Lₙ` with
   `Σ Lₙ = p`, and derive `OrbitWordBound ⟸ WidthFloorFreq + BlockAverageBound`.  Guard rule:
   `Lₙ = 0` for all `n` (no output) and `w = []` are the degenerate cases; the content locator is
   that `BlockAverageBound` at `Lₙ ≡ 1` is the lap-30 one-step statement.
2. **S7-WF (width frequency).**  `freq{n : width(sₙ) < η} → 0 as η → 0`.  Heuristic to test:
   narrow states occur exactly during a burst, a burst from input digit `a` lasts `≍ log a / λ`
   output digits, so the bad frequency is `≍ Σ_{a ≥ A} freq(a)·log a`.  **CF-normality does NOT
   give uniform integrability of `log a`** — a CF-normal `x` may have `(1/N)Σ log aₙ → ∞`.  So
   either (i) find the extra input that supplies it, or (ii) REFUTE the frequency form too, which
   would be a route-decisive refutation and a genuine advance.  Do (ii) first if (i) stalls: a
   CF-normal `x` with digits `a_{k!} = 2^{k!}` is the candidate witness.
3. **S7-BA (block average).**  The residual, = directive fact (α).  Do not spend a lap here until
   1 and 2 are settled.

---


## ⚠️ VANDEHEY §7 — CORRECTED ATTACK PATH (review lap 27, 2026-09-29)

**This supersedes the "next actions" of `HANDOFF-2026-09-29-2330.md`.**  Read it before touching
the §7 chain.  The binding version is `DIRECTION.md` → CURRENT DIRECTIVE.

### What was wrong

1. **The window function does not exist.**  `VandeheyS7Memory.no_window_function w` (kernel, every
   `w`, every length): `(1,3;0,8)` and `(1,7;0,32)` map `[0,1]` into the digit-`2` and digit-`4`
   cylinders, so after reading ANY word they both emit, and emit `2` and `4`.  Both have
   distortion `1` — the minimum — so the compact bounded-distortion fiber does not evade it.
   Maze: `hall_emit_digit_window_function`.
2. **`spread_runWord_le` is not initial-state independence.**  It bounds the image DIAMETER,
   uniformly in the state.  `runWord s w = s.comp (wordState w)`, so the LOCATION is the state's
   alone.  Input is appended on the RIGHT: recent digits fix the fine position inside the current
   interval, the far past fixes the absolute position, and the emitted digit reads the absolute
   position.
3. **It is a hall already closed.**  `hall_vandehey_synchronizing_transducer` (2026-09-28): no
   word merges two state classes.  A window function is exactly such a merge.  Lap 27's module
   reproves it without the `ZMod D` quotient, so the verdict survives the move off `ℤ`.
4. **The bounded decomposition error is unattainable.**  The exceptional set of
   `cfDigit_agree_depth` has POSITIVE Gauss mass, so a CF-normal input meets it with positive
   frequency: the error is `Θ(p)`, never `O(1)`.  `cfCount_tendsto_of_decomposition` stays in the
   build (it is subsumed, `approxScheme_of_bddError`) but must not be the consumer.

### What is in hand for the corrected path

* `VandeheyS7Approx.sampledUniformCount_of_approxScheme` — the crux from a family-and-error
  scheme `(S v k, ε v k → 0)` chosen before `x`.  No existence hypothesis.
* `MobState.cfDigit_mob_eq_emitDigit` — the emitted digit IS a function of the state.
* `MobState.canEmit_runWord_of_const` — a state inside one cylinder emits that digit forever.
* `VandeheyS7Distortion` — the compact substitute for finiteness
  (`uniform_comparable_of_bddDistortion`); `VandeheyS7Birkhoff` — the `3−2√2` contraction.

### ⭐ THE PRIMARY ROUTE (lap 27): the ergodic reduction

`VandeheyS7Orbit.affineCFN_of_orbitACBound` (axiom-clean) proves `AffineCFN q r₀` from

1. ~~`AffineImageIrrational q r₀`~~ — **DONE, lap 30** (`VandeheyS7Golden.lean`, axiom-clean):
   `affineImageIrrational_goldenRatio` and `affineImageIrrational_add_goldenRatio`.  If the image
   were rational, `z = Int.fract x` satisfies an explicit integer quadratic with leading
   coefficient `r.den²` (`(z+m)² + r(z+m) − r² = (z+m)²(1+φ−φ²) = 0`, resp.
   `z² + (1−2s)z + (s²−s−1) = 0` with `s = r − m`), so `cfDigit_le_of_quadratic` +
   `not_isCFNormal_of_bddDigits` finish.  Only `φ² = φ + 1` is used.
2. `GaussACRigidity C` — CITED.  Discharge plan, all inputs in hand:
   * `MeasurePreserving gaussMap gaussMeasure gaussMeasure` from `gaussMeasure_preimage` +
     `measurable_gaussMap`.
   * **Ergodicity of `gaussMap` for γ** from `Literature.philipp_psi_mixing_holds`: for an
     invariant `E` and a cylinder `I_u`, `γ(I_u ∩ E) = γ(I_u ∩ T^{-m}E) → γ(I_u)γ(E)`; approximate
     `E` by finite unions of cylinders, then take `I_u → E`.  Needs σ(cylinders) ⊇ Borel mod null.
   * Uniqueness of the a.c. invariant probability: mathlib
     `MeasureTheory.MeasurePreserving.rnDeriv_comp_aeEq` makes `dμ/dγ` invariant, ergodicity makes
     it constant.
   * Krylov–Bogolyubov on `[0,1]`: mathlib Prokhorov gives `CompactSpace (ProbabilityMeasure E)`
     for compact `E`; the a.c. bound kills the `1/k` discontinuities so the mapping theorem
     applies to `f ∘ gaussMap`.
   * Last step: `blockCount (cfCylinder v) = blockCount (uIoo cylNear cylFar)` exactly along an
     irrational orbit (`uIoo_subset_cfCylinder`), so weak convergence transfers to cylinders.
2bis. **`GaussACRigidity`: the compactness-free route (lap 28, `GaussKB.lean`).**  Steps (i) and
   (ii) are DONE and axiom-clean: `ergodic_gaussMap : Ergodic gaussMap gaussMeasure`
   (`GaussErgodic.lean`) and `eq_gaussMeasure_of_ac_invariant` (γ is the unique a.c. invariant
   probability).  Step (iii), Krylov–Bogolyubov, is being done WITHOUT Prokhorov/portmanteau:

   * fix one ultrafilter `orbitUF ≤ atTop` and set `limCDF y t := lim_𝒰 empCDF y p t`.  The
     values live in the compact `[0,1]`, so the limit exists (`tendsto_empCDF_limCDF`) — no
     Prokhorov.
   * **`limCDF_sub_le` (PROVED): the AC bound makes `limCDF` `C`-Lipschitz.**  This is the whole
     trick: the limit object is continuous by construction, so no continuity-point caveats and
     no portmanteau theorem are needed.  `limCDF_zero`, `limCDF_one`, `limCDF_mono` also proved.
   * NEXT: `ν := (limCDF y).stieltjes.measure` (Lipschitz ⇒ monotone + continuous, so a
     `StieltjesFunction`); `ν (Ioo a b) = limCDF b − limCDF a`; `ν` is a probability on `[0,1]`.
   * THEN invariance, the one genuinely new step: `T⁻¹(a,b) ∩ (0,1) = ⋃ₖ (1/(k+b), 1/(k+a))` is
     an EXPLICIT countable union of intervals, and its tail beyond `K` sits inside `(0,1/K)`,
     which has mass `≤ C/K` uniformly in `p` by the same AC bound.  So the limit interchange is
     honest and no mapping theorem for a.e.-continuous maps is required.
   * THEN `ν ≪ Leb ≪ γ` on `(0,1)` + invariance + probability ⇒ `ν = γ` by
     `eq_gaussMeasure_of_ac_invariant`; cylinders are intervals up to a countable set along an
     irrational orbit (`uIoo_subset_cfCylinder`), so the cylinder frequencies converge; and since
     EVERY ultrafilter limit is `γ`, the full sequence converges.

3. `OrbitACBound q r₀ C` — **the crux on this route**.  **Lap 29: now word-shaped.**
   `VandeheyS7Cell.orbitACBound_of_orbitCellBound` + `cellCover_inv_log_two` (both axiom-clean)
   reduce it to `OrbitCellBound q r₀ C`: an upper bound on the frequency of each finite word, and of
   "word then large digit", in the image expansion — the shape the transducer layer produces.
   Refuted sub-approaches (do not retry): the nest reformulation is tautological; a bound on the
   number of distinct `K`-window sets gives a cell-dependent constant that explodes; and
   `GaussACRigidity` cannot be weakened from a linear bound to a modulus of continuity (a Hölder CDF
   can be singular).  What is left is exactly S7-C below.  The two instruments S7-C needs are now
   proved: `VandeheyS7Loss.hdist_runWord_le` (exponential merging, uniform in the state) and
   `uniform_comparable_of_bddDistortion`.  Leg 1 is also nearly done:
   `VandeheyS7QuadDigit.not_isCFNormal_of_bddDigits` + `cfDigit_le_of_quadratic` give
   "quadratic irrational ⇒ not CF-normal"; only the explicit quadratic for `Int.fract x` when
   `φ x ∈ ℚ` remains.  One-sided, absolute constant, no
   `x`-independence.  Degenerate verdict `one_le_of_orbitACBound`: `C ≥ 1` always.

### ⭐ LAP 30: what the crux `OrbitCellBound` actually IS (do not re-derive)

Write the state at input time `n` as the Möbius map `s_n = O_n⁻¹ Φ P_n` (`O_n` = the emitted
convergent matrix, `P_n` = the input convergent matrix, `Φ` = the affine map).  Then
`Gᵗz = s_n(Gⁿx)` at matched times, and the crux is exactly

  `limsup (1/N) #{n < N : Gⁿ x ∈ s_n⁻¹(E)} ≤ C γ(E)` for every cell `E`.

Three facts, all established lap 30, fix its difficulty and must steer every further attack.

* **(α) It is a PREDICTABLE-SET problem.**  `A_n := s_n⁻¹(E)` is determined by `x₁…x_n`, and
  CF-normality of `x` is a statement about the tail marginal alone.  Any argument that uses only
  "`A_n` is predictable and `γ(A_n) ≤ D γ(E)`" must fail — that hypothesis is satisfiable by
  sequences for which the conclusion is false (design the tail to land in the predicted interval
  on a positive-density set while keeping the word frequencies Gaussian).  *Not yet a Lean
  refutation; the construction is a named probe (`S7-P1`) below.*
* **(β) The per-state distortion bound genuinely FAILS.**  A post-emission state whose image
  `J = s((0,1))` straddles `1/k` at a scale far below `|E|` has `γ(s⁻¹E) ≈ 1/2` while `γ(E)` is
  arbitrarily small.  Such states are precisely the ones that then emit a HUGE output digit, which
  is what the cell threshold `T` sees.  So the `w = []` tail-cell case of the crux (tightness:
  frequency of image digits `≥ T` is `≤ C/(T log 2)`) is the sub-statement that must control them,
  and the general case is a bootstrap off it, never a bypass.
* **(γ) The state set is literally `PSL₂(ℤ)`.**  For `Φ = diag(φ,1)` with `φ` irrational,
  `Γ ∩ Φ⁻¹ΓΦ = {±I}` (a matrix `[[a,b],[c,d]] ∈ SL₂(ℤ)` with `Φ⁻¹MΦ = [[a, b/φ],[cφ, d]]` integral
  forces `b = c = 0`).  So the state is the point `ΓΦP_n ∈ Γ\SL₂(ℝ)` and no two input words are
  ever identified.  This is the structural source of `no_window_function`, of
  `infinite_zPhi_abs_le_one`, and of the failure of pathwise merging, all at once — and it
  identifies the crux with the translate problem "`Γ g_x(t)` equidistributes ⟹ `Γ Φ g_x(t)` does",
  which is the self-joining wall.  Vandehey's Thm 1.1 is the same statement for `Φ` in the
  *commensurator* `GL₂(ℚ)⁺` (a Hecke correspondence, finite-to-one); `φ ∉ ℚ` is exactly why the
  method stops.

**Named next targets on the crux, in attack order.**

* **S7-T (tightness).**  **Free half PROVED lap 30** (`VandeheyS7Tight.lean`, axiom-clean):
  `largeDigitCount_mul_log_le` — for EVERY irrational `y ∈ (0,1)`,
  `#{i<p : cfDigit y i ≥ T} · log T ≤ log (cfK (digitWord y p))`, from
  `pow_countP_le_prod` + `prod_le_cfK`; hence `tailFreq_le_of_levyBound` gives frequency
  `≤ Λ/log T` under any Lévy bound `log qₚ ≤ Λp`, and `tendsto_freeRate` says that tends to `0`.
  **So tightness — the Krylov–Bogolyubov half of `GaussACRigidity` — costs nothing, and the crux
  never needed it.**  `exists_rate_gap` makes the remaining gap a theorem: for every `C` there is a
  `T` with `C/T < 1/log T`, so no sharpening of `Λ` can reach the crux's `C/(T log 2)`.
  **The open content of S7-T is exactly the passage from `1/log T` to `1/T`.**
  **Lap 31 made that passage a named Lean hypothesis** (`VandeheyS7Dioph.lean`, axiom-clean,
  sorry-free): `GoodDenBound y D` — `#{q ≤ Q : ‖q y‖ ≤ 2/(Tq)} ≤ (D/T) log Q` — together with any
  Lévy bound gives the crux's rate, `tailFreq_le_of_goodDenBound : freq ≤ DΛ/T + ε`.  The
  reduction is unconditional: `largeDigitCount_le_goodDenCount` bounds
  `#{i < p : aᵢ(y) ≥ T}` by `1 + #{q ≤ Qₚ : ‖q y‖ ≤ 2/(Tq)}` with `Qₚ = cfK (digitWord y p)`, via
  `nearInt_convDen_le` (a digit `≥ T` IS a `T`-good approximation, from the new `cfDet`
  determinant identity + `abs_convDen_mul_sub_le : |qₚ y − pₚ| ≤ 2/qₚ₊₁`) and the strictly
  monotone injection `i ↦ qᵢ`.  `heuristic_sum_le` shows the demanded bound is exactly the total
  measure `∑_{q≤Q} 2/(Tq) ≤ (2/T)(1+log Q)` of the target sets, so the Diophantine form is sharp,
  not lossy.
  **Lap 32:** the converse at the convergents — `abs_convDen_mul_sub_ge : 1/(qₚ+qₚ₊₁) ≤ |qₚy−pₚ|`
  plus `round_eq_of_abs_lt` give `le_digit_of_nearInt_le : ‖qₚy‖ ≤ 2/(Tqₚ) → T ≤ 2aₚ₊₁+4`, so
  large digit ⟺ `T`-good convergent.
  **Lap 33 (a real correction, found in the kernel):** the ALL-`q` count overshoots.  Multiples of a
  very good denominator are good (`nearInt_mul_good`), so one digit `aₚ ≥ Tk²` alone contributes
  `k ≈ √(aₚ/T)` denominators (`card_le_goodDenCount_of_large_digit`) against `1` digit.  Since
  `E[√a] < ∞` but `> 0` under Gauss–Kuzmin, the all-`q` count of a normal `y` is `≍ (1/√T) log Q`,
  so `GoodDenBound` as first stated is FALSE and only the **primitive** count can carry the `1/T`
  demand.  `goodDenCountPrim` / `GoodDenBoundPrim` are the corrected objects, and the reduction
  survives verbatim because convergents are primitive (`coprime_cfNum_cfK`, from `cfDet`):
  `largeDigitCount_le_goodDenCountPrim` + `tailFreq_le_of_goodDenBoundPrim`.
  **Lap 34:** `gap_principle` — two distinct primitive `T`-good denominators satisfy `Tq ≤ 4q'`
  (classical, unconditional, from `one_le_abs_cross`), and `goodDenCountPrim_le_log`:
  `goodDenCountPrim y T Q ≤ 1 + log Q / log(T/4)` for `T ≥ 5`.  So primitivity DOES restore
  sparsity — but only to the free rate `1/log T`.  **This localizes the wall precisely:** the
  target sets are the right size (`heuristic_sum_le`), primitivity is the right normalization
  (`card_le_goodDenCount_of_large_digit`), the good denominators are automatically `T/4`-spaced
  (`gap_principle`); the ONLY missing statement is that the `≍ log Q / log T` scales that *could*
  carry a good denominator actually carry one for at most a `log(T/4)/T` fraction of them.  That is
  a statement about WHICH scales — the orbit's equidistribution — with no remaining slack in the
  size or shape of the sets.
  **Lap 35 — the first link between `x`'s expansion and the good set** (`VandeheyS7Transfer.lean`,
  axiom-clean).  `φ` is a UNIT (`φ⁻¹ = φ−1`) and badly approximable, so a good approximation of
  `qφx` transports: `qφx = m+δ ⟹ qx = (mφ−m) + δ(φ−1)`, and `‖mφ‖ ≥ 1/(4m)`
  (`nearInt_goldenRatio_ge`, from lap 30's `abs_sub_mul_goldenRatio_ge`) with `m ≤ 2q` gives
  `nearInt_mul_ge_of_good : ‖qφx‖ ≤ 2/(Tq) → ‖qx‖ ≥ 1/(16q)` for `T ≥ 32`.  **A `T`-good scale for
  the image is a scale at which `x` itself is badly approximated.**  Corollary at `x`'s own
  convergents: `digit_le_of_good_at_convergent : qᵢ(x)` good for `φx` ⟹ `aᵢ(x) ≤ 32`.
  *Limitation, stated honestly:* the good `q` are convergent denominators of `φx`, not of `x`, so
  this constrains only the overlap.  **Lap 36:** the transfer extended.  (i) `nearInt_mul_ge_of_good_add` — the SECOND frozen target
  `x + φ` obeys the same negative correlation, from the same input and with no unit trick
  (`‖q(x+φ)‖` small + `‖qφ‖ ≥ 1/(4q)` ⟹ `‖qx‖ ≥ 1/(8q)` for `T ≥ 16`), plus
  `digit_le_of_good_at_convergent_add` (`aᵢ(x) ≤ 16`).  (ii) `nearInt_numerator_ge_of_good` — the
  numerator of a primitive good approximation is an ANTI-good denominator: `mφx = m²/q + mδ/q` and
  `gcd(m,q)=1` with `q ≥ 2` give `‖mφx‖ ≥ 1/(2q)`.  So good denominators come in pairs `(q,m)`
  whose second coordinate is excluded from the good set, purely from `φ(φ−1)=1`.
  **Lap 37 — the loop is closed** (`VandeheyS7Loop.lean`, axiom-clean).  `goodDenCountPrim_fract`
  (the count does not see `Int.fract`: `nearInt_mul_fract` plus `coprime_shift_iff`, since the
  numerator moves by the integer `q⌊r⌋`) and `goodDenBoundPrim_fract_iff` let the hypothesis be
  stated for the RAW multiplier.  Hence `tailFreq_mul_phi_of_goodDenBound` and
  `tailFreq_add_phi_of_goodDenBound`: for CF-normal `x`, `GoodDenBoundPrim (φx) D` (resp.
  `(x+φ)`) plus a Lévy bound gives the crux's `O(1/T)` tail frequency for the FROZEN targets, with
  irrationality supplied by `VandeheyS7Golden`'s leg 1.  The §7 route now reads end-to-end:
  frozen target ⇐ `GaussACRigidity` + `OrbitCellBound`; `OrbitCellBound`'s tail cell ⇐
  `#{q ≤ Q : ‖qφx‖ ≤ 2/(Tq), gcd = 1} ≤ (D/T) log Q`, a statement about `x`-independent sets.
  **Lap 38 — LEGENDRE, and with it the verdict on the Diophantine route**
  (`VandeheyS7Legendre.lean`, axiom-clean, sorry-free).  `exists_eq_cfK_of_good`: for `T ≥ 24`,
  EVERY primitive `T`-good denominator of an irrational `y ∈ (0,1)` IS a convergent denominator
  of `y`.  The proof is elementary and needs neither the sign alternation of `qₙy − pₙ` (which the
  repo does not have) nor Fibonacci growth.  With `m = round(qy)` and `c p := q·pₚ − m·qₚ ∈ ℤ`:
  `c p = 0` forces `q = qₚ` (both fractions primitive — `hcop` and `coprime_cfNum_cfK'`), so if `q`
  is no convergent denominator then `|c p| ≥ 1` for every `p`, and expanding
  `−c p = q(qₚy − pₚ) − qₚ(qy − m)` against `abs_convDen_mul_sub_le` gives the SELF-PROPAGATING
  bound `1 ≤ 2q/qₚ₊₁ + 2qₚ/(Tq)` (`one_le_cross_bound`): `qₚ ≤ 3q` ⟹ `2qₚ/(Tq) ≤ 1/4` ⟹
  `2q/qₚ₊₁ ≥ 3/4` ⟹ `qₚ₊₁ ≤ 8q/3 ≤ 3q`.  Base `q₀ = 1`; the index `p = 0` (not covered by
  `abs_convDen_mul_sub_le`) is handled directly — `q₁ > 3q` forces `y ≤ 1/q₁ < 1/(3q)`, so
  `round(qy) = 0`, so coprimality gives `q = 1 = q₀`.  Then `qₚ → ∞` (`le_cfK_digitWord`) closes it.
  **What this DECIDES.**  Together with lap 32's `le_digit_of_nearInt_le` (a `T`-good convergent
  forces `T ≤ 2aₚ₊₁ + 4`) the good set is now pinned from BOTH sides:
  `goodDenCountPrim y T Q` counts exactly the convergent denominators `≤ Q` whose next digit is
  `≳ T/2`.  So `GoodDenBoundPrim y D` is not a weakening of the crux's tail cell — it is a
  RESTATEMENT of it, and laps 31–37 bought a reformulation, not a reduction.  **There is no
  remaining slack on the Diophantine side**: sets are the right size (`heuristic_sum_le`),
  primitivity is the right normalization, the spacing is forced (`gap_principle`), and now the
  good set carries no denominators beyond the convergents.  Any further advance must come from
  the transfer (laps 35–36: `nearInt_mul_ge_of_good`, `nearInt_numerator_ge_of_good`) —
  i.e. from the arithmetic of `Φ` relating the convergents of `φx` to those of `x` — never from
  sharpening the Diophantine counting.
  **Lap 39 — the equivalence is now a Lean theorem, and the transfer's ceiling is named.**
  `goodDenCountPrim_le_largeDigitCount` (`VandeheyS7Legendre`, axiom-clean) is the CONVERSE of
  `largeDigitCount_le_goodDenCountPrim`: every primitive `T`-good `q ≤ Q` is `qₚ` with `p ≤ Q`
  (Legendre), and past `p = 3` such a convergent forces `T ≤ 2aₚ + 4`, so
  `goodDenCountPrim y T Q ≤ 3 + #{p < Q+2 : T ≤ 2aₚ(y) + 4}`.  The two counts are now bounded by
  each other in the kernel; `GoodDenBoundPrim` is formally a restatement of the crux's tail cell.
  **Directional finding (the reason not to grind the transfer further).**  The transfer's
  conclusion `‖qx‖ ≥ 1/(16q)` (laps 35–36) is **`T`-INDEPENDENT**: the set it excludes,
  `{u : ‖qu‖ < 1/(16q)}`, has measure `1/8` for every `q`, no matter how large `T` is.  So the
  transfer can only ever remove an `O(1)` proportion of scales, never a `1 − O(log T / T)`
  proportion.  Any bound of the form `(D/T) log Q` must therefore come from a mechanism whose
  strength GROWS with `T` — and the only `T`-growing input available is the goodness hypothesis
  itself (`‖qφx‖ ≤ 2/(Tq)`), used at MANY scales simultaneously, i.e. the equidistribution of `x`
  along the `T/4`-separated good scales.  That is fact (γ) again, reached from the Diophantine
  side.  **So lap 38–39 close the Diophantine detour: it is exactly the crux, not a softening.**
  **Lap 40 — the REFUTATION: `GoodDenBoundPrim` is false without normality**
  (`VandeheyS7Const.lean`, axiom-clean, sorry-free).  `constCF T := (√(T²+4) − T)/2` is the
  fixed point of the Gauss map with `ζ⁻¹ = T + ζ`, i.e. `[0; T, T, T, …]`: `gaussMap_constCF`,
  `cfDigit_constCF` (every digit is `T`), `irrational_constCF` (`T²+4` is never a square for
  `T ≥ 1`).  Since every digit equals `T`, `nearInt_convDen_le` makes EVERY convergent
  denominator a primitive `T`-good denominator (`good_cfK_constCF`), and `cfK_le_prod` gives
  `qₚ ≤ (T+1)ᵖ`, so `goodDenCountPrim_constCF_ge : P − 2 ≤ goodDenCountPrim ζ_T T ((T+1)^P)`.
  Hence `not_goodDenBoundPrim_constCF : D·log(T+1) < T → ¬ GoodDenBoundPrim ζ_T D`.
  **What this settles.**  (i) Lap 34's free rate `log Q / log(T/4)` is ATTAINED, so no amount of
  Diophantine bookkeeping — spacing, primitivity, the transfer — can improve it; the wall located
  at lap 34 is a genuine wall, not an artifact of a lossy step.  (ii) `GoodDenBoundPrim (φx) D`
  is NOT an unconditional Diophantine fact; it holds only for `y` with Gauss–Kuzmin tail
  statistics.  With lap 39's equivalence this means the Diophantine reformulation IS the crux's
  tail cell, exactly, with no slack anywhere.  **The Diophantine detour is closed as a detour:
  laps 31–40 converted the tail cell into an equivalent form and proved that form has no
  independent leverage.**  Any future lap must attack the statistics of the image expansion
  directly (fact (γ), the `Γ\SL₂(ℝ)` translate problem), not the counting.
  **Lap 41 — the bootstrap, resolved** (`VandeheyS7Boot.lean`, axiom-clean, sorry-free).
  `blockCount_cellSet_le_shift`: UNCONDITIONALLY, for every irrational `y ∈ (0,1)`, every word
  `w` and every `T`, `blockCount (cellSet w T) p y ≤ blockCount (cellSet [] T) p y + w.length`.
  The reason is the shift — `Gⁿy ∈ cellSet w T` forces `Gⁿ⁺ᴸy ∈ cellSet [] T` (`cfDigit_add`) and
  `n ↦ n + L` is injective.  So the general cell's frequency is ALWAYS at most the tail cell's,
  with no hypothesis and no geometry; and `cellSet_mono_threshold` gives the other marginal,
  `freq(w,T) ≤ freq(I_w)`, for free.
  **But the bootstrap cannot close.**  The crux demands `freq(w,T) ≤ C·γ(cellSet w T)` and
  `γ(cellSet w T) ≍ γ(I_w)·γ(cellSet [] T)` — a PRODUCT, while the two unconditional bounds give
  only the MINIMUM.  `not_min_le_const_mul` (kernel): for every `C > 0` there are
  `a, b ∈ (0,1]` with `C·ab < min a b` (witness `a = b = 1/(2C)`).  So lap 30's "the tail cell
  controls the general cell" is FALSE as stated: no combination of the tail cell with the
  word-frequency bound produces the general cell.  The crux needs the JOINT law of "word `w`,
  then a large digit" in the image — genuine independence, not two marginals.
  **Cumulative verdict of laps 38–41.**  Every counting-side lane is now closed by a theorem:
  the Diophantine form is equivalent to the tail cell (lap 39), the tail cell is not an
  unconditional fact (lap 40), and the tail cell does not imply the general cell (lap 41).  What
  remains in `OrbitCellBound` is exactly the joint statistics of the image expansion — fact (γ),
  the `Γ\SL₂(ℝ)` translate problem — and nothing else.
  **Lap 42 — the sharp unconditional form** (`sum_blockCount_cellSet_le`, axiom-clean).  The
  shift bound upgrades from max to SUM: for any finite family `F` of distinct words of the same
  length `n`, `∑_{w∈F} blockCount (cellSet w T) p y ≤ blockCount (cellSet [] T) p y + n`, for
  every irrational `y ∈ (0,1)`.  The cells are pairwise disjoint
  (`cfCylinder_disjoint_of_length_eq`) so at most one fires at each time `k`, and they all inject
  into the tail cell under the SINGLE shift `k ↦ n + k`.
  **This is the exact unconditional content of `OrbitCellBound`.**  Since
  `∑_{|w|=n} γ(cellSet w T) = γ(cellSet [] T)` too, both sides of the crux sum to the same tail
  quantity: the crux says PRECISELY that the tail cell's visits are spread across the length-`n`
  words in proportion to `γ(I_w)`.  It is an equidistribution-ACROSS-WORDS statement *given* the
  tail — which is exactly why neither marginal can supply it (lap 41) and why the counting lanes
  are all closed (laps 39–40).  The crux is now stated in its irreducible form.
  **Lap 43 — THE THRESHOLD IS FREE: the crux collapses to its `T = 1` case**
  (`VandeheyS7Reduce.lean`, axiom-clean, sorry-free).  `OrbitWordBound q r₀ C` is the `T = 1`
  statement — `freq(I_w) ≤ C γ(I_w) + ε` for every finite word `w` in the image expansion.
  `orbitCellBound_of_orbitWordBound : 0 ≤ C → AffineImageIrrational q r₀ →
  (LevyBound on the image) → OrbitWordBound q r₀ C → OrbitCellBound q r₀ C`.
  Three steps, all from pieces already proved: (i) `cellSet_subset_union` — along irrationals the
  cell splits as `⋃_{T ≤ a ≤ S} I_{w++[a]} ∪ cellSet w (S+1)`; (ii) the residual is killed by the
  FREE tightness — lap 41's `blockCount_cellSet_le_shift` reduces it to the tail cell and
  `tailFreq_le_of_levyBound` makes it `≤ Λ/log(S+1) → 0` (`tendsto_freeRate`); (iii) the finitely
  many cylinders go to the hypothesis and their masses sum to `≤ γ(cellSet w T)` because they are
  disjoint subsets of it (`sum_gaussMeasure_cfCylinder_le`).
  **This is the payoff of laps 38–42.**  Those laps proved the threshold parameter carries no
  content (the tail is free, the counting is equivalent, the bootstrap fails); lap 43 turns that
  into a reduction.  The §7 route now reads: frozen targets ⇐ `GaussACRigidity` (cited) +
  `OrbitWordBound` + a Lévy bound on the image — a ONE-PARAMETER-FREE statement, "the image
  expansion of a CF-normal `x` does not over-represent any finite word".
  **Lap 44 — the second hypothesis, minimised and named.**  Lap 43's reduction never used the
  quantitative Lévy bound, only tightness of the image's digit distribution, so that is now the
  hypothesis: `ImageTight y := ∀ ε > 0, ∃ T ≥ 2, eventually blockCount (cellSet [] T) p y / p ≤ ε`,
  with `imageTight_of_levyBound` (axiom-clean) showing it is strictly weaker than `LevyBound`.
  `orbitCellBound_of_orbitWordBound` now reads: `0 ≤ C`, `AffineImageIrrational`, `ImageTight` on
  the image, `OrbitWordBound` ⟹ `OrbitCellBound`.  The `Λ` parameter is gone from the chain.
  **Why `ImageTight` is a GENUINE second obligation, not a formality** (reasoned, not yet a Lean
  witness): `OrbitWordBound` is one-sided, and one-sided upper bounds are compatible with digits
  marching to infinity — if `aᵢ(y) = 2^{2^i}` then every individual word occurs at most once, so
  every word frequency tends to `0` and the upper bounds hold vacuously, while
  `log qₚ ≍ 2^p` destroys any Lévy bound and tightness fails outright.  So tightness cannot be
  derived from the one-sided crux; it needs its own argument.
  **Lap 45 — CF-normality DOES give tightness** (`VandeheyS7Tight2.lean`, axiom-clean,
  sorry-free).  `imageTight_of_isCFNormal : Irrational y → y ∈ Ioo 0 1 → IsCFNormal y →
  ImageTight y`.  Two elementary ingredients: `blockCount_cellSet_nil_add_eq` — at each orbit
  time the digit is `≥ T` or equals exactly one `a ∈ [1,T)`, so
  `blockCount (cellSet [] T) p y + ∑_{a<T} blockCount (I_{[a]}) p y = p`; and
  `one_le_sum_gaussMeasure_cfCylinder_singleton` — every `t ∈ (0,1)` lies in `I_{[cfDigit t 0]}`
  and a digit `> n` forces `t ≤ 1/n`, so `Ioo 0 1 ⊆ (⋃_{a≤n} I_{[a]}) ∪ Ioo 0 (2/n)` and hence
  `1 ≤ ∑_{a≤n} γ(I_{[a]}) + (2/n)/log 2`.  No null-set argument: the covering is exact,
  rationals included.  `blockCount_freq_of_isCFNormal` (the converse of
  `isCFNormal_of_orbit_freq`, same `≤|v|` window↔orbit gap) is the bridge.
  **This vindicates lap 44's weakening.**  `LevyBound` would need `∑ log(aᵢ+1) = O(p)`, a uniform
  integrability statement that CF-normality does NOT supply — a sparse sequence of enormous
  digits moves no cell frequency while blowing up `∑ log aᵢ`.  Tightness is exactly the part of
  Lévy that normality gives, so `ImageTight` was the right hypothesis and `LevyBound` would have
  been unprovable.
  **Lap 46 — the chain assembled** (`VandeheyS7Chain.lean`, axiom-clean).
  `vandeheyS7_mul_phi_of_orbitWordBound` / `vandeheyS7_add_phi_of_orbitWordBound`: both frozen
  §7 targets now follow from exactly THREE inputs — the cited `GaussACRigidity (C/log 2)`, the
  crux `OrbitWordBound`, and `ImageTight` on the image.  Compare lap 30: three hypotheses, one
  carrying a threshold `T` and a Lévy constant `Λ`; both parameters are now gone.
  `imageTight_of_image_isCFNormal` records that `ImageTight` is strictly weaker than the
  conclusion, so it is a legitimate intermediate target, not a restatement of it.
  **Recorded obstruction on (a).**  Transferring tightness from `x` to `y = fract(φx)` does NOT
  go through the Diophantine route: `largeDigitCount_le_goodDenCountPrim` + `goodDenCountPrim_le_log`
  give `#{i<p : aᵢ(y) ≥ T} ≤ 4 + log qₚ(y)/log(T/4)`, so dividing by `p` needs `log qₚ(y) = O(p)`
  — a Lévy bound for the IMAGE, which is what tightness was supposed to avoid.  And the two
  expansions genuinely decouple: `|qₙ φ x − φpₙ| ≤ φ/qₙ` has `φpₙ ∉ ℤ`, so `x`'s convergents give
  no rational approximations to `φx`.  Tightness of the image therefore needs the clock (the
  emitted-vs-read matrix comparison `Oℓ ≈ ΦPₙ`), and that is the next real build.
  **Lap 47 — the three shapes of the crux are the same statement** (`VandeheyS7Equiv.lean`,
  axiom-clean).  `orbitWordBound_of_orbitACBound : 0 ≤ C → AffineImageIrrational q r₀ →
  OrbitACBound q r₀ C → OrbitWordBound q r₀ (2 log 2 · C)`.  A cylinder IS an interval along an
  irrational orbit: `cfCylinder_subset_uIcc` puts `I_w` inside `[min,max]` of the rational
  endpoints `cfVal w`, `cfVal (bumpLast w)`, and an irrational orbit point cannot BE an endpoint,
  so `blockCount (I_w) ≤ blockCount (Ioo m M)`; and `sub_le_gaussMeasure_cfCylinder` (new) gives
  `M − m ≤ 2 log 2 · γ(I_w)` from `gaussMeasure_cfCylinder` plus
  `log(1+M) − log(1+m) ≥ (M−m)/(1+M)` and `M ≤ 1`.
  With lap 43 (`orbitCellBound_of_orbitWordBound`) and lap 29
  (`orbitACBound_of_orbitCellBound` + `cellCover_inv_log_two`), the three formulations —
  INTERVALS, WORDS, CELLS — are now mutually derivable up to absolute constants.  **The route has
  exactly one crux and the choice of shape is free**, so future laps may attack whichever form is
  most tractable without changing what is being proved.
  **Next attack (lap 48), in order.**
  (a) Transfer tightness from `x` to `y = fract(φx)`.  Lap 45 gives `ImageTight x` for free from
  `x`'s normality; what is needed is `ImageTight y`.  The clock is the route
  (`Oℓ ≈ ΦPₙ`, `det Φ = φ` fixed, so `log qℓ(y) ≍ log qₙ(x) + O(1)`), and note that the WEAKER
  tightness statement may not need the full clock: a large image digit at emitted time `ℓ` means
  the state's image interval is tiny, which costs input digits.
  (b) `OrbitWordBound` — the crux.
  **Older next-attack note (lap 45), in order.**
  (a) `ImageTight` for `y = fract(φx)` with `x` CF-normal.  The natural route is the CLOCK: the
  emitted convergent matrices satisfy `Oℓ ≈ Φ Pₙ` with `det Φ = φ` fixed, so `log qℓ(y) ≍
  log qₙ(x) + O(1)`; a Lévy bound for `x` plus a linear lower bound on the emission rate `ℓ(n)`
  would give one for `y`.  Prerequisite, and provable on its own: **CF-normal `x` ⟹ `LevyBound x`**
  — normality gives the EXACT frequencies of `{a ≥ T}`, so a dyadic decomposition of
  `Σ log(aᵢ+1) ≤ Σ_k (k+1) log 2 · #{i : aᵢ ∈ [2ᵏ, 2ᵏ⁺¹)}` converges against `2⁻ᵏ` tails.
  (b) `OrbitWordBound` itself — the genuine crux, fact (γ), now the only content-bearing
  hypothesis besides the cited `GaussACRigidity`.
  **Older next-attack note (lap 43).**  Two open obligations remain on the route, and both are now sharply
  stated.  (a) `OrbitWordBound` — the genuine crux, fact (γ).  (b) The Lévy bound on the image,
  which is now a REQUIRED input rather than a convenience: probe whether it follows from
  `OrbitWordBound` itself (a word-frequency upper bound plus `cfK_le_prod` may bound
  `log qₚ` by `Σ log(aᵢ+1)` and hence by a `C`-weighted Gauss average), which would leave
  exactly one open statement in the whole chain.
  **Older next-attack note (lap 42).**  Attack the joint law directly at its smallest nontrivial instance:
  `w` a single digit.  The two-cell statement "digit `a` then a digit `≥ T`" in the image is the
  first place the product vs. minimum gap bites, and the `s_n = Oₙ⁻¹ΦPₙ` state description says
  exactly which input events produce it.  Concretely: formalize the two-step emission relation
  (`MobState.cfDigit_mob_eq_emitDigit` composed with itself) and ask what input word class the
  pair `(a, ≥T)` pulls back to — a NAMED finite-state condition on `x`'s digits would turn the
  joint law into a statement CF-normality of `x` can reach.
  **Older next-attack note (lap 40).**  The `w ≠ []` cells are now the only untried part of
  `OrbitCellBound`, and the lap-30 bootstrap note says the tail cell was supposed to CONTROL
  them.  Since the tail cell is now known to be exactly Gauss–Kuzmin for the image, reverse the
  bootstrap: assume the tail cell (as a named hypothesis `ImageTailLaw`) and ask whether the
  general cell follows — i.e. is `OrbitCellBound` a consequence of its own `w = []` case plus the
  proved geometry (`VandeheyS7Loss.hdist_runWord_le`, `uniform_comparable_of_bddDistortion`)?
  A positive answer would collapse the crux to a single one-parameter statement.
  **Older next-attack note (lap 39):** the only `T`-growing multi-scale object in hand is the pair
  `(q, q')` of consecutive good denominators with `Tq ≤ 4q'` (`gap_principle`) together with
  `nearInt_numerator_ge_of_good` (the numerators `m, m'` are excluded from the good set).  Probe:
  does the pair `(q, m)` with `gcd(m,q)=1`, `‖qφx‖ ≤ 2/(Tq)` and `‖mφx‖ ≥ 1/(2q)` force a
  SECOND excluded scale in the multiplicative window `[q, Tq/4]`, i.e. can the gap principle be
  iterated with `T`-dependent gain?  A negative answer (with a witness) is equally an advance.
  **Older next-attack note (lap 38):** run the unit trick at the STATE
  level — `‖qx‖ ≥ 1/(16q)` says the orbit point `(qx, qφx) mod 1` avoids a fixed neighbourhood of
  the `x`-axis whenever the image emits a large digit; combined with `gap_principle` the good
  scales are `T/4`-separated AND confined to a region of the torus of measure `≍ 1/T`.  That pair
  is the first candidate mechanism for the `1/T` rate that does not route through a soft
  equidistribution statement.
  **Older next-attack note (lap 34):** instantiate at `y = Int.fract (φ x)`, where `E_q = {u : ‖qφu‖ ≤ 2/(Tq)}`
  is **`x`-independent**; the open question is then the single sentence "does CF-normality of `x`
  control the visit counts to `{E_q}`?".  Two concrete probes: (i) the `q` occurring are the
  denominators of `φx`, so ask whether `q ∈ ℕ` can be replaced by `qφ ∈ ℤ[φ]` and the norm form
  used as in S7-H; (ii) look for a REFUTATION of `GoodDenBound` for some CF-normal `x` — it would
  kill the Diophantine route as stated and force the `w ≠ []` cells back in.
* **S7-H — DONE, lap 30** (`VandeheyS7Hecke.lean`, axiom-clean; Maze row
  `hall_hecke_approximation`).  The "approximate `φ` by `F_{k+1}/F_k`, apply the PROVED Thm 1.1,
  diagonalize" route is refuted by its own accounting: `goldenNorm_factor` +
  `one_le_abs_goldenNorm` give `abs_sub_mul_goldenRatio_ge : |p − qφ| ≥ 1/(4q)`, hence
  `pow_lt_den_sq_of_image_approx : |(p/q)x − φx| < |x|/(4cᴺ) → cᴺ < q²` and
  `sq_le_det_of_approx : q² ≤ pq`.  Buying `N` digits of agreement costs a determinant
  exponential in `N`, so Thm 1.1's automaton has `e^{Ω(N)}` states while reading `N` digits.
  **Where the content sits:** for a rational target the norm form vanishes identically — that is
  precisely why Thm 1.1 is provable and this is not.
* **S7-P1 — DONE, lap 30** (`VandeheyS7Predict.lean`, axiom-clean; Maze row
  `hall_predictable_from_marginals`).  Fact (α) is now a kernel refutation.
  `PredictableHitPrinciple` — "a sequence with perfect marginals on cells of width `1/m` lands in
  its own predicted interval of width `δ` at most a `δ + 1/m` fraction of the time" — is FALSE:
  the grid `u n = n/k` is *exactly* uniform on the `k` cells (`cellUniform_grid`, zero error) and
  yet `u n ∈ (u_{n−1}, u_{n−1}+δ)` for every `n ≥ 1` once `1/k < δ` (`hitCount_grid`), so the hit
  frequency is `(k−1)/k`.  At `δ = 1/2, k = 10`: `9/10` observed against `6/10` allowed
  (`not_predictableHitPrinciple`).  **Consequence, and the standing instruction for the crux:** any
  proof of `OrbitCellBound` must use the specific arithmetic of `s_n = O_n⁻¹ Φ P_n` (fact (γ)) —
  never "predictable + small + correct marginals".  With `no_window_function` this closes both
  soft routes: the state cannot be forgotten, and it cannot be ignored.
  *Remaining gap in the witness (cheap, optional):* the refutation is at a finite horizon with
  exact marginals; extending it to an infinite equidistributed sequence is the block-concatenation
  of grids, `O(√N)` discrepancy, and needs no new idea.
  *Next locator worth having:* the same principle IS true for a CONSTANT predictor (cover
  `(c, c+δ)` by `⌈δm⌉+2` cells), which would pin the content on the past-dependence exactly.

### The FALLBACK route: state-indexed decomposition (named next goals, in order)

* **S7-A. The state space.**  A `def` for the post-emission states: `¬ CanEmit` (nothing left to
  emit) plus `distortion ≤ D`.  Content locator + degenerate case, per the guard rule.  Include
  the normalization map `strip : MobState → MobState × List ℕ` (emit while you can) and prove it
  terminates on states whose image is short enough.
* **S7-B. The state process.**  `stateSeq : ℝ → ℕ → MobState`, the post-emission state after
  reading `n` CF digits of the input, with the clock `ℓ x n := ` total emitted length.  Prove
  monotone, and that the emitted stream is the image's CF digit stream (correctness).
* **S7-C. `StateEquidistribution`.**  The empirical measure of `(stateSeq x n)` converges weakly
  to an `x`-independent ν, on a class of cells fine enough to resolve `emitDigit`.  This is the
  ℤ[φ] replacement for `ClassEquidistribution` / `JointStateFreq`.
* **S7-D. Crux from S7-C.**  Cells × input words give the scheme's finite families; feed
  `sampledUniformCount_of_approxScheme`.
* **S7-E. ν itself.**  Birkhoff–Hopf contraction on the compact fiber ⇒ existence and uniqueness.

### The open probe left behind

Is the emitted digit a window function of the input for ONE FIXED `M`?  It is TRUE for
`M = id` (the image is the input) and expected false for `M = φ`; deciding it needs two reachable
post-emission states straddling different endpoints `1/k`.  Not on the critical path — S7-C does
not need it — but it would sharpen the Maze row.

---

Concrete next moves, cheapest and most clear-cut first.  Front context is in `STATUS.md`.  The
lap-by-lap log from before the 2026-09-27 merge is `archive/PENDING_WORK-to-2026-09-27.md`.
Treadmill laps append dated notes **below the queue**, and a review lap folds them back into it.

