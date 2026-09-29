# PENDING WORK — the queue

## Joint Lambert update, 29 September 2026

The synchronized-word theorem is unconditional at proof commit `f6fbf87` on
`proof/joint-lambert-unconditional`, in the sibling checkout `normal-numbers-lambert`.
There are no remaining prime-distribution hypotheses on that theorem.
The old AGP target below is a separate analytic question, not a prerequisite.
The next Lambert target is an all-N occurrence count; its proposed stronger paper bound is
`N exp(-C (log log N)^2 log log log N)`, documented on that branch in
`docs/JOINT-LAMBERT-QUANTITATIVE-NEXT.md`.  It is not yet formalized.


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

## Lap notes

### 2026-09-29 lap 26 — the emitted digit is a function of the STATE alone (`VandeheyS7Emit.lean`)

    cfDigit_mob_eq_emitDigit :  0 < s.b → CanEmit s → y ∈ [0,1] → cfDigit (s.mob y) 0 = emitDigit s

**That is the whole point of the lap.**  The emitted digit does not depend on the unread future
of the input.  Since the state after reading a window is `s₀ · wordState w` (`runWord_eq_comp`)
and merging makes `s₀` invisible (`spread_runWord_le`), the digit is a function of the WINDOW —
which is exactly what `cfCount_tendsto_of_decomposition` (lap 22) takes as its hypothesis.

Supporting, all axiom-clean:

* `mob_mem_uIcc` : a state maps `[0,1]` — the range of every possible continuation — into the
  interval between `s.mob 0` and `s.mob 1`.  The sign of `det` decides the orientation and
  `uIcc` absorbs it, so NO hypothesis on `det` is needed.  (The two exact identities
  `mob y − mob 0 = y·D/(d(cy+d))` and `mob 1 − mob y = (1−y)·D/((c+d)(cy+d))` carry it.)
* `cfDigit_zero_antitone` / `cfDigit_zero_eq_of_between` : `⌊1/·⌋` is antitone, so a digit that
  agrees at the endpoints is constant across the interval.
* `CanEmit s := cfDigit (s.mob 0) 0 = cfDigit (s.mob 1) 0`, with `emitDigit` the common value.

`0 < s.b` is load-bearing and not cosmetic: `phiState` has `b = 0`, where `mob 0 = 0` and the
digit is the junk value.  It is the same side condition the repo's `emit` already carries.

Degenerate case `not_canEmit_of_ne`: when the endpoints disagree, no digit is determined and the
machine must read more input — which is precisely the `boundaryBad` situation of
`VandeheyS7Boundary`.  **That is why that set had to be measured**, and the two modules now meet.

**Next attack (lap 27): the window function `F` itself.**  Define `F w := emitDigit (wordState w)`
(or `emitDigit (s₀.comp (wordState w))` and then quotient out `s₀` by merging).  The statement to
prove: for a.e. input and all large windows, the image digit at the corresponding position equals
`F` of the window.  The `CanEmit` hypothesis is discharged off `boundaryBad` by
`cfDigit_agree_depth`; the `s₀`-independence is `spread_runWord_le`.  Both are in hand, so this
is a matter of lining up the indices — the clock `ℓ` is what relates input position to image
position, and it is `VandeheyS7Clock`'s FIRST named hypothesis, believed fine and measured.

### 2026-09-29 lap 25 — the window lemma is UNCONDITIONAL along the run

**A route correction first, recorded so it is not retried.**  Lap 24's stated next step — get the
general `TriggerGap` by composing with the initial state on the LEFT — is WRONG.  `s₀(cylFar w)`
need not lie between near and far, so left-composition does not preserve the trigger.  The
correct general statement is the operational one.

* `abs_sub_beta_mem` : distance to `β` is monotone across the cylinder.  `conv_far_eq` gives
  `far − β = k(near − β)` with `1 ≤ k ≤ 2`, so the two have the SAME sign — `β` lies outside
  `[near, far]` (it is the parent cylinder's other endpoint, with `near` the separating mediant)
  and `near` is the closer.  Hence every `x` between them has `|near−β| ≤ |x−β| ≤ |far−β|`.
* `triggerGap_of_mem_cyl` : both image endpoints in `w`'s cylinder — exactly when the machine
  emits `w` — gives `TriggerGap`.  This is the general case, not the extremal one.
* `windowBound_runWord` : **post-burst distortion ≤ 4 along the machine's run, from ANY initial
  state, with no trigger hypothesis and no distortion hypothesis.**  Reading gives
  `distortion ≤ 2` for free (`distortion_runWord_le_two`) and emission gives the trigger.  Only
  the nondegeneracy side conditions (`hQ`, `hden0`, `hden1`) remain, and those are
  non-vanishing-denominator conditions, not estimates.

All axiom-clean.  The window lemma was "done as mathematics" per the 2026-09-29 handoff; it is
now done as a theorem about the machine.

**Next attack (lap 26): obligation 1 of lap 22 — define `F`.**  Nothing structural is in the way
any more.  The pieces: `runWord_eq_comp` (state = initial · word), `windowBound_runWord` (bounded
distortion along the run), `cfDigit_agree_depth` + `budget_le` (a window of input determines a
proportional number of image digits).  What to build: a definition of the emitted-digit function
`F : List ℕ → ℕ` from the machine's state, and the statement that the image digit at position `j`
equals `F` of the input window.  Start by writing down the machine as an explicit corecursion
(state + emission) rather than leaving it implicit in `runWord`/`emit`; the emission side
condition of `emit` (`e·a ≤ c`, `e·b ≤ d`) is what picks `e`, so `F` should be defined as the
largest such `e`, and then `mob_emit` says it does the right thing.

### 2026-09-29 lap 24 — `TriggerGap` is achieved, unconditionally, on the word matrix

`triggerGap_wordState : TriggerGap (wordState w) w` for any nonempty word with genuine digits —
no side conditions at all.  Axiom-clean.  This removes `windowBound`'s trigger hypothesis in the
extremal case, via two endpoint identities that `wordState_eq_conv` (lap 23) makes immediate:

    (wordState w).mob 0 = b/d       = p/q         = cylFar w
    (wordState w).mob 1 = (a+b)/(c+d) = (p+p')/(q+q') = cylNear w

**They come out SWAPPED** relative to `triggerGap_endpoints`' phrasing: the word matrix reads `0`
to the FAR endpoint and `1` to the near one.  Hence `triggerGap_endpoints_swap`.  `TriggerGap` is
symmetric in what it demands (both images between near and far), so the same argument serves —
but the swap is worth recording, since assuming the original orientation would silently produce a
false endpoint identity.

Scope, stated honestly: this is the EXTREMAL case, `s = wordState w`, not the general machine
state.  The machine's accumulated state is `s₀ · wordState w` (lap 13's `runWord_eq_comp`), and
what this pins is the endpoint of the range the general statement must cover.

**Next attack (lap 25): `TriggerGap` for `s₀ · wordState w`.**  The general statement is that
composing with the initial state on the LEFT keeps both images between near and far.  That should
follow from monotonicity of `s₀.mob` on `(0,∞)` — the same fact that gave `mob_ratio_le` /
`mob_ratio_ge` in lap 12 — since `s₀` maps the interval `[cylFar, cylNear]` into an interval with
the same ordering.  If it goes through, `windowBound` becomes unconditional along the whole run,
and obligation 1 of lap 22 (defining `F`) is unblocked.

### 2026-09-29 lap 23 — the word matrix IS the continuant matrix (transposed)

The handoff's queued bookkeeping is done, and it landed on lap 13's `wordState`:

    wordState_eq_conv :  wordState w  =  (p', p ; q', q)   for  Conv.of w = ⟨p', q', p, q⟩

(all digits `≥ 1`), axiom-clean.  Supporting: `idState_comp`, `wordState_append` (appending a
digit multiplies on the right).

**The transpose is the content, not a convention slip.**  The word matrix is built by PREPENDING
branches — which is what the machine does as it reads input — while `Conv` is built by APPENDING
digits, which is what the continuant recursion does.  Those two are transpose-conjugate.  Both
recursions were checked against each other: appending sends `(a,b;c,d) ↦ (b, a+e·b ; d, c+e·d)`
on the word matrix and `(p',q',p,q) ↦ (p, q, p'+e·p, q'+e·q)` on `Conv`, which agree under the
transpose, and the base cases agree (`idState = (1,0;0,1)`, `Conv.of [] = ⟨1,0,0,1⟩`).

**Consequence worth recording:** lap 13's Fibonacci growth of the word matrix's ROWS is literally
the classical growth of the convergent denominators `q_n`.  Two separately-derived facts are now
known to be one fact, and `windowBound`'s `Conv`-language hypotheses (`(of w).p'`, `(of w).q'`)
can be discharged from `wordState` facts and vice versa.

**Next attack (lap 24): `TriggerGap` from the machine.**  `windowBound` takes `TriggerGap s w` as
a hypothesis and `triggerGap_endpoints` proves it when `s.mob 0 = cylNear w` and
`s.mob 1 = cylFar w`.  With `wordState_eq_conv` in hand those two endpoint identities are now
statements about `wordState`, so prove them there.  That turns `windowBound` from conditional
into unconditional along the machine's run, which is the last structural gap before `F` can be
defined (obligation 1 of lap 22).

### 2026-09-29 lap 22 — the Cesàro engine, and the remaining obligation isolated to ONE hypothesis

`VandeheyS7Assemble.lean`, both theorems axiom-clean.

* `cfFreq_finset_sum` : a FINITE family of input words has a joint occurrence frequency, namely
  `∑ γ(I_u)`.  Finite additivity on top of CF-normality — the engine that turns "the image digit
  is a window function of the input" into an image frequency.
* `cfCount_tendsto_of_decomposition` : if the image's count of `v` agrees with the total count of
  a finite family `S` of input words **up to a bounded error**, then
  `cfCount v z p / p → ∑_{u∈S} γ(I_u)`.  The limit depends only on `S`, hence only on the window
  function and `v` — **NOT on `x`.  That is precisely the `x`-independence `SampledUniformCount`
  asks for.**

The bounded-error form is the right one: edge effects of a fixed-length window are `O(1)` in `p`,
not `o(p)` in disguise, so nothing is being smuggled.

**Where the route now stands.**  Everything analytic is proved; the whole remaining gap is the
single hypothesis `hdecomp` — identifying `S` from `cfDigit_agree_depth`.  Two sub-obligations:

1. **The window function.**  Show the image digit at position `j` is a fixed function of a
   fixed-length window of the input digits.  All the ingredients exist
   (`cfDigit_agree_depth` + `budget_le` + the two measure bounds); what is missing is the
   *definition* of `F` and the statement that the machine's emission is what `runWord` computes
   (the handoff's "remaining bookkeeping on the window lemma": `TriggerGap`, and identifying the
   pullback matrix's first column with `Conv.of`'s `(p', q')`).
2. **Finiteness of `S`.**  `S` is finite only after the digit cutoff `K`; uncapped it is
   countably infinite and the limit/sum exchange needs the repo's existing summability inputs
   (`CFAeKhinchin.summable_logMul_vol_cfCylinder`, `summable_sqLog_gaussMeasure_cfCylinder`).

**Next attack (lap 23): obligation 1, starting with the emission bookkeeping.**  It is the older
of the two and was already queued in the 2026-09-29 handoff.  Concretely: turn the φ-machine's
operational emission trigger into `TriggerGap`, and prove `A_e = (0 1; 1 e)` matches
`Conv.of [e] = ⟨0,1,1,e⟩` (hand-checked already; the recursions agree).  That makes
`BddDistortion` / `EmitRowBound` theorems rather than hypotheses, and it is what lets `F` be
defined at all.

### 2026-09-29 lap 21 — THE ROUTE IS NOT BUDGET-LIMITED (`VandeheyS7Budget.lean`)

The question this lap had to settle: `cfDigit_agree_depth` needs `δ_L · scale u m` small, where
merging gives `δ_L ~ φ^{-2L}` and the cutoff costs `S^m`.  Can `m` be taken PROPORTIONAL to `L`?

**Yes, with an explicit constant, and the constant is positive for every finite cutoff `K`.**

* `goldenRatio_pow_le_fib` : `φ^k ≤ fib (k+2)`, a two-step induction off `φ² = φ + 1` — the same
  recursion as `fib`, which is why it is exact rather than an estimate.
* `fib_prod_ge` : `φ^{2k} ≤ fib(k+2)·fib(k+3)`, i.e. `δ_{k+3} ≤ φ^{-2k}`.
* `budget_le` : `S^m · δ_L ≤ exp(m log S − 2k log φ)` for `L = k+3`.
* `budget_tendsto_zero` : for any `c < 2 log φ / log S`, the product along `m = ⌊ck⌋` decays
  geometrically.
* `not_budget_of_large` (degenerate case): past that threshold the exponent is positive and the
  bound says nothing, so `2 log φ / log S` is sharp.

All axiom-clean.  **Why this matters for the route, not just the bookkeeping:** raising `K` to
shrink the exceptional mass raises `S = 4(K+1)²e^{2η}` and so shrinks `c` — but only
logarithmically, and never to zero.  So the two limits can be taken in the order `K` first, then
`L → ∞`, and there is no circularity.  A positive proportion of the image digits is determined
by a bounded window of input digits.  That was the last thing that could have killed Route A on
arithmetic grounds.

**Next attack (lap 22): assembly into `SampledUniformCount`.**  Every analytic input now exists.
What remains is bookkeeping of a kind the repo already does elsewhere: the determined image
digits give block counts that depend only on the input window, so their Cesàro averages converge
by the input's CF-normality (frequency EXISTENCE only — no value, per
`affineCFN_of_uniformFreq`).  Concretely: state the "window-determined block count" Prop, prove
it from `cfDigit_agree_depth` + `budget_le` + the two measure bounds, and then reduce
`SampledUniformCount` to it.  Expect this to be several laps; it is assembly, not new
mathematics, and the guard rule applies to each new Prop.

### 2026-09-29 lap 20 — the scale cutoff is closed, reusing the repo's Khinchin machinery

The lap-19 gap (`gaussMeasure_exceptional_le` is at a FIXED scale, but `cfDigit_agree_depth`
needs `ε = δ · scale u i`) is now closed.  The instrument was already in the repo:
`CFLogTail.logTailFn K` (log of the digit when it exceeds `K`, else `0`) with the Markov bound
`gaussMeasure_logBadZone_raw_le`, whose `n`'s cancel.  Three new theorems, all axiom-clean:

* `log_digit_succ_le` : `log(a+1) ≤ log(K+1) + log 2 + logTailFn K x`, pointwise.  True in both
  regimes — for `a ≤ K` the tail term is `0`, for `a > K` it is `log a` and `log(a+1) ≤ log(2a)`.
* `log_scale_le` : summing along the orbit,
  `log (scale u n) ≤ 2n(log(K+1) + log 2) + 2·logBirkhoffSum K n u`.
  (`cfDigit u j = cfDigit (gaussMap^[j] u) 0` is `rfl`, so the Birkhoff sum matches on the nose.)
* `scale_le_exp` / `gaussMeasure_scale_bad_le` : off the log-tail bad zone `scale u n ≤ S^n` with
  `S = 4(K+1)²e^{2η}`, and that bad zone has mass `≤ (∫ logTailFn K dγ)/η` UNIFORMLY in `n`.
  `integral_logTailFn_tendsto_zero` sends it to `0` as `K → ∞`.

**Confirmed: one integral underwrites both named hypotheses.**  `∫ log(1+a) dγ < ∞` is what
`VandeheyS7Clock` cites for the clock rate AND what pays for the scale cutoff here.  That is a
structural fact about the route, not a coincidence — record it before it gets re-derived.

The transfer chain is now complete except for assembly:

    spread_runWord_le → abs_sub_runWord_le → cfDigit_agree_depth
      exceptional set:  gaussMeasure_exceptional_le  (fixed scale)
      scale cutoff:     gaussMeasure_scale_bad_le    (removes the u-dependence)

**Next attack (lap 21): assemble, and state the残 gap honestly.**  Combine the two measure
bounds into a single "for a.e. `u`, for all large `n`, the first `m(n)` digits of the image are
determined by the last `n` input digits" statement, choosing `m(n)` so that
`δ_n · S^{m(n)} → 0` — merging's `δ_n = 1/(fib(n-1)fib(n))` is exponentially small with rate
`φ²`, so `m(n) = c·n` works for `c < 2 log φ / log S`.  THEN the remaining step to
`SampledUniformCount` is the Cesàro/ergodic bookkeeping: digit-block frequencies along the clock.
Do the `m(n)` arithmetic first — it is pure inequality work and it pins the constant `c`, which
is the quantity that decides whether the route closes.

### 2026-09-29 lap 19 — the exceptional set has small Gauss mass

`gaussMeasure_exceptional_le` (axiom-clean): at a fixed scale `ε ∈ (0,1]`,

    gaussMeasure (⋃_{i<m} (gaussMap^[i])⁻¹ (boundaryBad ε))  ≤  m · 6√ε / log 2 .

Linear in the depth `m` and in `√ε`.  Merging supplies `ε` exponentially small in the word
length, so this is summable — the Borel–Cantelli input.

Reuse, not rebuild: `gaussMeasure_preimage_iterate` was already in `CFPin.lean` (invariance, so
each level contributes the SAME mass — no Jacobian), and `gaussMeasure_le_volume` was already in
`CFDigitLaw.lean` (density ≤ 1/log 2).  New here: `boundaryBad_eq_iUnion` (reindexed as an
explicit countable union of intervals) and `measurableSet_boundaryBad`.

**The one honest gap, deliberately separated.**  This statement is for a FIXED `ε`, but
`cfDigit_agree_depth` needs `ε = δ · scale u i`, which depends on `u`.  The missing step is a
CUTOFF: on the set `{u : scale u m ≤ S}` the fixed-scale bound applies with `ε = δS`, and the
complement `{u : scale u m > S}` must be shown small.  Since `log (scale u m) = 2∑_{i<m}
log(cfDigit u i + 1)`, that is exactly a large-deviation statement for the Khinchin integral
`∫ log(1+a) dγ < ∞` — the same integral `VandeheyS7Clock` cites for the clock rate.

**Next attack (lap 20):** state `ScaleCutoff` as a named Prop (guard rule: content locator +
degenerate case) — `∀ η > 0, ∃ S, ∀ m, gaussMeasure {u | scale u m > S^m} < η` or the Cesàro form
— and prove the pieces that do not need the ergodic theorem: `log (scale u m) = 2∑ log(aᵢ+1)`
(`Finset.prod_range` + `Real.log_prod`), monotonicity, and the reduction of `SampledUniformCount`
to `ScaleCutoff` + what is already proved.  Check `CFDigitLaw.lean` / `CFBlockFreq.lean` first:
the repo may already have the Birkhoff average of `log(1+a)` from the Khinchin work
(`KHINCHIN.md`).

### 2026-09-29 lap 18 — DEPTH-`m` DIGIT AGREEMENT IS PROVED

`cfDigit_agree_depth` (axiom-clean): if `|u − v| < δ` and at every level `i < m` the point
`gaussMap^[i] u` lies in `(0,1)` and avoids `boundaryBad (δ · scale u i)`, then
`cfDigit v i = cfDigit u i` for all `i < m`.  Here `scale u i = ∏_{j<i} (cfDigit u j + 1)²` is
the accumulated one-step cost from lap 17.

Two things made it clean:

* **The shift identity is `rfl`.**  `cfDigit x i = cfDigit (gaussMap^[i] x) 0` holds definitionally
  because `cfDigit x n = ⌊(gaussMap^[n] x)⁻¹⌋₊`.  So the induction carries ONLY the metric
  invariant `|gaussMap^[i] u − gaussMap^[i] v| < δ · scale u i`, not any digit bookkeeping.
* **Strictness on both sides.**  `cylinder_of_not_boundaryBad` (refactored out of lap 16's proof)
  gives `1/(n+1) < v < 1/n` STRICTLY, and the strict upper bound is exactly what keeps
  `gaussMap v > 0` so the induction can take another step.

So the merging → digits transfer is complete at every depth.  The chain is now:

    spread_runWord_le → abs_sub_runWord_le → cfDigit_agree_depth
                                           ↘ volume_boundaryBad_le (per level)

**Next attack (lap 19): the measure of the pullback union.**  The only remaining gap in the
transfer is that the exceptional set is `⋃_{i<m} (gaussMap^[i])⁻¹ (boundaryBad (δ · scale u i))`,
and its measure must be shown small.  Two facts do it: `gaussMeasure` is `gaussMap`-INVARIANT (so
each pullback has the same measure as the set itself, no Jacobian to track), and
`volume_boundaryBad_le` bounds each at `6√(δ · scale u i)`.  What must be controlled is
`∑_{i<m} √(scale u i)` against `√δ` — and `scale` is exponential in `∑ log(aᵢ+1)`, which is
`O(m)` a.s. by the SAME Khinchin integral `∫ log(1+a) dγ < ∞` that `VandeheyS7Clock` cites for
the clock rate.  Note that coincidence: one integral underwrites both named hypotheses.
First step: find/prove `gaussMeasure` invariance in the repo (`CFInvariance.lean` is the likely
home) and state the pullback bound.

### 2026-09-29 lap 17 — one Gauss step costs exactly `(n+1)²`

`gaussMap_eq_sub` and `abs_gaussMap_sub_le`, both axiom-clean.  Inside a depth-one cylinder the
integer part of `x⁻¹` is the SAME integer for both points, so it cancels and

    gaussMap u − gaussMap v = u⁻¹ − v⁻¹ = (v − u)/(u v),   hence
    |gaussMap u − gaussMap v| ≤ (n+1)² |u − v|

with `n` the shared digit.  Exact, not an estimate: the only inequality is `u, v > 1/(n+1)`.

So a depth-`m` agreement costs `∏_{i<m} (aᵢ+1)^{-2}` in `δ`.  Merging supplies
`δ_n = 1/(fib(n-1)fib(n))`, which is exponentially small — the right order to pay this, since
`∑ log(aᵢ+1)` is `O(n)` almost surely (finite Khinchin mean, the same integral
`∫ log(1+a) dγ < ∞` that `VandeheyS7Clock`'s docstring cites for the clock rate).

**Next attack (lap 18): the depth-`m` induction.**  Iterate `abs_gaussMap_sub_le` with the shift
identity `cfDigit w (k+1) = cfDigit (gaussMap w) k` (proved in `CFAffineFamily.lean`).  The clean
statement to aim for:

    ∀ i < m, gaussMap^[i] u ∉ boundaryBad (δ · ∏_{j<i} (cfDigit u j + 1)²)
      →  ∀ i < m, cfDigit v i = cfDigit u i

i.e. the exceptional set is a FINITE union of depth-one bad sets pulled back along `gaussMap`,
each of measure `O(√(δ ∏ …))`.  Bounding that union is where the Khinchin integral enters; do the
induction first and leave the measure of the pullback union as the named node after it.

### 2026-09-29 lap 16 — digit agreement off the boundary set (lap 15 is now load-bearing)

`cfDigit_zero_eq_of_not_boundaryBad` : if `u ∈ (0,1)` is not within `δ` of ANY endpoint `1/k`,
and `|u − v| < δ`, then `cfDigit v 0 = cfDigit u 0`.  Axiom-clean.  With
`volume_boundaryBad_le` the exceptional `u` have measure `≤ 6√δ`, so the first CF digit is
locally constant at scale `δ` off a set of measure `O(√δ)`.

That closes the merging → digits transfer at depth one:

    abs_sub_runWord_le  (|u − v| ≤ δ_n, no state)
      +  cfDigit_zero_eq_of_not_boundaryBad  (digits agree off boundaryBad)
      +  volume_boundaryBad_le  (that set has measure ≤ 6√δ_n)

Supporting lemmas, all elementary and reusable: `cfDigit_zero` (`= ⌊x⁻¹⌋₊`), `floor_inv_spec`
(`1/(n+1) < u ≤ 1/n` for `n = ⌊1/u⌋₊ ≥ 1`), `cfDigit_zero_eq_of_mem` (converse).

**Next attack (lap 17): depth `m`.**  `cfDigit v i = cfDigit u i` for all `i < m`.  The honest
route is induction on `i` through `gaussMap`: if `u, v` share digit `0` and both lie in the same
depth-one cylinder, then `|gaussMap u − gaussMap v| ≤ |u − v| / (u v) ≤ (n+1)² |u − v|`, so the
scale degrades by the SQUARE of the digit at each step.  That is why the depth-`m` bad set needs
`δ` exponentially small in `m` — and merging supplies exactly that (`δ_n = 1/(fib(n-1)fib(n))`).
Formalise the one-step expansion bound first; it is a two-line `gaussMap` computation given
`Int.fract` on the relevant interval.

### 2026-09-29 lap 15 — the trigger window is quantitative: `volume (boundaryBad δ) ≤ 6√δ`

`VandeheyS7Boundary.lean`.  Merging gives two output points within `δ`; a CF digit is `⌊1/x⌋`,
so the digits agree UNLESS a point is within `δ` of a depth-one cylinder endpoint `1/k`.  That
bad set is `boundaryBad δ`, and `volume_boundaryBad_le` bounds it by `6√δ`.  Axiom-clean.

**The rate is `√δ`, not `δ`, and that was the thing to get right.**  The endpoints `1/k` are
infinitely many and accumulate at `0`, so "`2δ` per endpoint" DIVERGES — an obvious-looking route
that does not work.  The split is by scale: discard `(0, 2√δ)` wholesale (measure `2√δ`), and
above that scale only the `k ≤ 1/√δ` endpoints are reachable, contributing `2δ(1/√δ + 1) ≤ 4√δ`.

Consequence worth recording: **no digit cutoff is needed.**  The accumulation at `0` was the
reason to fear one, and paying `√δ` instead of `δ` buys it off.  Since merging supplies
`δ = 1/(fib(n-1)fib(n))`, exponentially small, `√δ` is still exponentially small and the loss is
free.  A cutoff would have had to be carried through the entire Cesàro argument.

**Next attack (lap 16): depth `m`.**  Same statement for `cfCylinder w` with `|w| = m`: the bad
set is the `δ`-neighbourhood of the depth-`m` endpoints.  The depth-`m` cylinder containing a
point of digit-sum-scale `Q` has length `~1/Q²`, so the same scale split should give
`O(√δ)` again with an `m`-dependent constant; the clean route is probably induction on `m` using
`gaussMap`'s expansion `1/x²` rather than re-running the covering.  Then: digits agree off
`boundaryBad`, and `SampledUniformCount` is Cesàro bookkeeping on a full-measure set.

### 2026-09-29 lap 14 — the projective-to-absolute bridge

Merging is proved in the Hilbert metric, but CF digits are read off an ABSOLUTE position
(`digit u = ⌊1/u⌋`), so the bound has to be converted.  It converts exactly:

    abs_sub_le_of_hdist_le :  hdist u v ≤ ε  →  |u − v| ≤ max u v · (exp ε − 1)

and since the machine's output point is in `(0,1)` the `max` is harmless.  `abs_sub_runWord_le`
is the merging bound in that form, still with no initial state on the right.  Axiom-clean.
Content locator `abs_sub_le_of_hdist_le_zero`: at `ε = 0` it collapses to `u = v`, so all the
content is in the exponential factor.

**Next attack (lap 15): digit determination.**  With `|u − v| ≤ δ_n → 0`, two output points have
the same first `m` CF digits as soon as both lie strictly inside the same depth-`m` cylinder.
Prove the one-digit case first — `u, v ∈ (1/(k+1), 1/k) → both have first digit k` — then the
depth-`m` version by iterating, and identify the exceptional set (points within `δ_n` of a
cylinder endpoint) whose Gauss measure `→ 0`.  That exceptional set IS the `ρ(∂U) = 0` trigger
window of DIRECTION item 3, and once its measure is shown to vanish, `SampledUniformCount` is a
Cesàro bookkeeping exercise over a set of inputs of full measure.

### 2026-09-29 lap 13 — MERGING IS DONE: loss of memory, uniform over states (`VandeheyS7Word.lean`)

`spread_runWord_le` : for every initial state `s`, every even word length `n ≥ 3`, and all
`x, y > 0`,

    hdist ((runWord s w).mob x) ((runWord s w).mob y) ≤ 1 / (fib(n-1) · fib(n)) .

The state does not appear on the right.  The infinite `ℤ[φ]` state set is invisible at this
range, which is exactly the merging the finite-chain citation was for.  Axiom-clean.

How it goes, in three steps and no dynamics:

* `wordState w = A_{a₁}⋯A_{aₙ}` and `runWord s w = s.comp (wordState w)` (`runWord_eq_comp`).
* **Fibonacci growth of both rows** (`fib_le_rowMin`).  Prepending `A_a` sends
  `(a b; c d) ↦ (c, d; a + Ac, b + Ad)`, so `rowMin₁(A_a W) = rowMin₂(W)` and
  `rowMin₂(A_a W) ≥ rowMin₁(W) + rowMin₂(W)` — a Fibonacci recursion read straight off the matrix
  product.  No continuants, no Gauss measure, no CF theory.
* **`det = (-1)^n`** (`det_wordState`), so `ad/bc = 1 + 1/(bc)` and
  `log(ad/bc) ≤ ad/bc − 1 = 1/(bc) ≤ 1/(fib(n-1)fib(n))` (`spread_wordState_le`).  Then
  `hdist_comp_le` (lap 12) removes the initial state.

Note the Birkhoff coefficient (lap 11) is NOT used on this route; it is the quantitative
refinement, kept because it gives a per-two-digit rate.

**Next attack (lap 14): wire merging into `SampledUniformCount`.**  With the window lemma
(`windowBound`) and merging both in hand, `VandeheyS7Clock.lean`'s `SampledUniformCount q r ℓ` is
the remaining crux node.  The step to find: `spread_runWord_le` bounds the spread of the machine's
OUTPUT POINT; turn that into a bound on the discrepancy of the sampled digit counts (the trigger
windows with `ρ(∂U) = 0` from DIRECTION item 3).  Read `VandeheyS7Clock.lean`'s docstring first
and identify precisely which quantity the spread bound has to control.

### 2026-09-29 lap 12 — nonexpansiveness, and calculus was not needed

The expected lap-12 step was mean-value bookkeeping on `birkhoff_derivative_le`.  It is not
needed.  That every nonnegative Möbius map is NONEXPANSIVE for the Hilbert metric is a polynomial
identity: for `0 < u ≤ v` and nonnegative `A,B,C,D`,

    v(Au+B)(Cv+D) − u(Av+B)(Cu+D) = (v−u)(ACuv + BC(u+v) + BD) ≥ 0
    v(Av+B)(Cu+D) − u(Au+B)(Cv+D) = (v−u)(ACuv + AD(u+v) + BD) ≥ 0

i.e. `u/v ≤ f(v)/f(u) ≤ v/u` (`mob_ratio_le`, `mob_ratio_ge`), hence `mob_nonexpansive` — with NO
hypothesis on the determinant, so it holds for every `MobState` in either orientation.  All
axiom-clean.

The payoff is `hdist_comp_le`: `hdist ((s.comp t).mob x) ((s.comp t).mob y) ≤ hdist (t.mob x)
(t.mob y)`.  The initial state `s` can only SHRINK what the input word `t` produces, so a
diameter bound for the word alone bounds the spread from every initial state at once.  That is
the loss of memory, and it is exactly what the infinite `ℤ[φ]` state set made unobtainable by the
finite-chain route.

**Next attack (lap 13): the word diameter goes to zero.**  Combine `hdist_comp_le` with
`hdist_image_le` applied to the word state `W = A_{a₁}···A_{a_n}`: the image diameter is
`log (ad/bc)`, and `det W = ±1` gives `ad/bc = 1 ± 1/(bc)` with `bc` a product of consecutive
continuants, so the diameter is `≤ 1/(bc) → 0`.  Note this route needs NO contraction factor at
all — `gaussPair_birkhoffCoeff_le` (lap 11) becomes the quantitative refinement rather than the
load-bearing step.  Formalise `runWord`'s entries as continuants (the `Conv` fold in
`VandeheyS7Convergent.lean` is the right instrument; `cfP`/`cfK` are NOT, see the handoff gotcha)
and prove `q_n → ∞`.

### 2026-09-29 lap 11 — merging: the contraction factor is UNIFORM (`VandeheyS7Merge.lean`)

Next-action #1 from the handoff is done, and it gave more than expected.  Two Gauss branches
compose to `A_a A_b = (1, B; A, 1+AB)` (`gaussPair`), strictly positive in all four entries with
determinant exactly `1` — so the Birkhoff diameter is finite after two digits, from any state.
The surprise: with `ad = 1+t`, `bc = t`, the coefficient collapses to `(√(1+t) − √t)^2`
(`birkhoffCoeff_one_add`), which is DECREASING in `t`.  Large digits contract more; the worst
case is the smallest product `t = AB = 1`, i.e. `a = b = 1`.  Hence

    gaussPair_birkhoffCoeff_le :  birkhoffCoeff (A_a A_b) ≤ 3 − 2√2 ≈ 0.1716

for EVERY pair of digits — no digit bound, no positive-frequency argument, no large deviations.
All axiom-clean.

**Next attack (lap 12):** the mean-value bookkeeping.  `birkhoff_derivative_le` bounds the
derivative in the log coordinate; combine it with `gaussPair_birkhoffCoeff_le` to get
`hdist (s.mob x) (s.mob y) ≤ (3−2√2) · hdist x y` for `s = gaussPair a b`, then iterate along the
input word to get `hdist → 0` geometrically.  That is the loss of memory, and it feeds
`SampledUniformCount`.

newest first)

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

**Lap 10 (same day): the Birkhoff–Hopf coefficient, and its analytic core PROVED.**
`src/NormalNumbers/VandeheyS7Birkhoff.lean`, axiom-clean.

The second half of `SampledUniformCount` is MERGING.  Vandehey cites Saloff-Coste–Zúñiga for a
finite chain; that is unavailable twice over here (infinite state set, and pathwise merging is
PROVABLY IMPOSSIBLE — `conj_goldenRatio_integral_forces_diagonal`).  So the replacement is
distributional: Birkhoff–Hopf contraction of the Hilbert projective metric.  Landed:

* `hdist`, `mob_mem_Icc`, `hdist_image_le` — a state with POSITIVE entries maps `(0,∞)` into
  `[b/d, a/c]`, so the image has Hilbert diameter `≤ log(ad/(bc))`.  Finite exactly when all four
  entries are positive: **positivity, not finiteness, is the right hypothesis over ℤ[φ]**.
* `birkhoffCoeff a b c d = (√(ad) − √(bc))/(√(ad) + √(bc))` — this is `tanh(Δ/4)` in these terms.
  `birkhoffCoeff_lt_one` (a genuine contraction factor as soon as `bc > 0`),
  `birkhoffCoeff_nonneg`, plus both guard-rule cases: `birkhoffCoeff_of_eq` (singular ⇒ 0,
  constant map) and `birkhoffCoeff_bc_zero` (triangular ⇒ 1, NO contraction — positivity of all
  four entries is load-bearing).
* **`birkhoff_denom_bound`** — the whole analytic content, in one inequality:
  `ac x² + (ad+bc) x + bd ≥ x(√(ad)+√(bc))²`, by AM–GM on `ac x² + bd ≥ 2x√(ac·bd)` with
  `(ac)(bd) = (ad)(bc)` identifying the geometric mean.
* `birkhoff_derivative_le` — assembles it: `x(ad−bc)/((cx+d)(ax+b)) ≤ birkhoffCoeff`, i.e. the
  action is `birkhoffCoeff`-Lipschitz in the log coordinate, modulo mean-value bookkeeping.

**What is left on this node:** the mean-value step (derivative bound ⇒ Lipschitz bound in the log
coordinate) — no further inequality and no dynamics — and then the loss-of-memory statement for a
composition, which needs `bc > 0` along the run, i.e. the states to be strictly positive rather
than merely nonnegative.  **That positivity is the next real question**, and it is a statement
about the φ-machine, not about the metric.

**NEXT (lap 11).**  Strict positivity of the run states: show `b, c > 0` after enough input
digits (`gaussBranch` has a zero in the corner, so a single step is not enough — two steps
should be: `A_a A_b = (1, b; a, ab+1)`, all positive for `a,b ≥ 1`).  That, with
`birkhoff_derivative_le`, gives a uniform contraction factor `< 1` per two input digits, which is
the loss of memory that replaces Vandehey's finite-chain merging.

**(superseded) NEXT (lap 10): the SECOND half of `SampledUniformCount`.**  With the window lemma in hand the
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

