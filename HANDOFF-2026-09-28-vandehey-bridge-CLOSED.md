# HANDOFF — Vandehey 2017 Theorem 1.1: **the bridge is closed, §3 is unconditional**

**Branch** `wip/vandehey-matrix-action` · **HEAD** `759a7ad` · `lake build` 🟢 **9291 jobs** ·
working tree clean · nothing pushed.

**Scoped objective (`LEAN_DONE_WHEN`)**: `sorry`-free
`src/NormalNumbers/LiteratureVandehey.lean`, i.e. prove `vandeheyUniformFreq_holds`
(no weakening/renaming of the `def` or theorem).  `DIRECTION.md` CURRENT DIRECTIVE governs and
was **re-set this lap** (review lap C): items (A)–(E) of THE BRIDGE were mandated; **all five
landed**.  Transducer combinatorics were explicitly forbidden until the bridge closed — that
condition is now discharged, so (F) is open.

## Headline of this lap

`VandeheyTwo.classEquidistribution_classStep` and `VandeheyTwo.tendsto_jointCount_classStep`
(`src/NormalNumbers/VandeheyClassEquidist.lean`) are **sorry-free**, trust triple
`[propext, Classical.choice, Quot.sound]`:

> For prime `D`, along **every** CF-normal `x` and from **every** initial class, the frequency of
> positions where the digit window spells `q` *and* the class cocycle sits at `t` converges to
> `γ(I_q) / |ℙ¹(ℤ/D)|`.

That is exactly the content Vandehey's §3 buys from the Moshchevitin–Shkredov theorem which
Airey–Mance refuted on non-compact spaces.  It is now **unconditional and machine-checked**: no
hot-spot criterion, no tightness hypothesis, no ergodic theorem, no Ryll-Nardzewski.

## The review pass (why the direction changed)

Last lap proved the analytic crux `VandeheyState.stateHorizonIntegral_pin` — and then stopped.
The pin was **inert**: nothing in the repo consumed it, and the handoff's "next" list started with
bookkeeping.  Inventory showed the route-decisive uncertainty was not the instantiation but
whether the pin could *mesh* with the cylinder disintegration at all, and whether a **mean** bound
could reach `ClassEquidistribution` (it cannot — its `windowBound` averages sit inside an absolute
value, so a variance bound is required).  Directive re-set accordingly; `STATUS.md` refreshed.

## What was proved, in order (all in `src/`, all sorry-free)

`src/NormalNumbers/VandeheyStateMixing.lean` (new, wired):
* `abs_setIntegral_tailDensity_sub_le`, `continuousOn_setIntegral_tailDensity` — `τ ↦ ∫_B h_τ` is
  `2|B|`-Lipschitz on `[0,1]` for any `B ⊆ (0,1)`.
* **`abs_gaussMeasure_cylinder_inter_sub_le`** — THE brick.  From *any* uniform pin
  `|∫_B h_τ − c| ≤ E` on `τ ∈ [0,1]`: `|γ(I_v ∩ T^{−|v|}B) − c·γ(I_v)| ≤ E·γ(I_v)` for every
  genuine `v`, **at gap zero**.
* `abs_gaussMeasure_familySetC_inter_sub_le`, **`abs_gaussMeasure_biUnion_cylinder_inter_sub_le`**
  (future set may depend on the past cylinder), `abs_gaussMeasure_cylinder_horizon_sub_le`, and
  `VandeheyState.abs_gaussMeasure_{cylinder,familySetC,biUnion}_state_sub_le`.

`src/NormalNumbers/VandeheyTwoPoint.lean` (new, wired):
* Plumbing (word ↔ set dictionary): `cfWord_getD`, `mem_cfCylinder_iff_cfWord`,
  `mem_familySetC_iff_cfWord`, `cfDigit_iterate`, `cfWord_iterate`, `cfWindow_iterate`,
  `cfWord_length/_take/_drop`, `runState_cfWord_split`, `mem_horizonSet_cfCylinder_iff`.
* `winEvent`, `jointEvent`, `devFun`, `measurable_devFun`, `abs_devFun_le`,
  **`jointDev_eq_devFun`** (agree at every irrational point of `(0,1)`).
* `pastWin`, `pastJoint`, `winEvent_ae_eq`, `jointEvent_ae_eq`,
  **`inter_jointEvent_ae_eq`** (the load-bearing identification), `winEvent_shift_ae_eq`,
  `inter_winEvent_ae_eq`, `integral_devFun_mul`.
* **`abs_integral_devFun_mul_le`** — the two-point correlation: four joint masses, and with
  `L = c` the four leading terms cancel **identically**.
* `gapExp`, **`abs_integral_devFun_mul_le_gap`** (unified, every pair),
  **`sum_gap_majorant_le`** (row sum bounded independently of `K`).
* **`integral_devAvg_sq_le`** — the variance bound `∫ devAvg² dγ ≤ varConst/K`.
* **`devAvg_eq_localAvg`**, **`sum_gaussMeasure_localAvg_sq_le`** (disjoint-cylinder comparison),
  `sum_gaussMeasure_cylinder_le_one`, `sum_gaussMeasure_abs_le_sqrt` (Cauchy–Schwarz),
  `varConst`, **`sum_gaussMeasure_windowBound_le`** (`≤ |S|·√(varConst/K)`).

`src/NormalNumbers/VandeheyClassEquidist.lean` (new, wired):
* `card_bad_shift_le`, **`sum_windowBound_le_split`** (the orbit split),
  `tendsto_weighted_window_freq`,
  **`classEquidistribution_of_pin`** (generic in the automaton),
  **`classEquidistribution_classStep`**, **`tendsto_jointCount_classStep`**.

No pre-existing file's proofs were modified.

## Findings worth not re-deriving

1. **The adjacency obstruction never binds for the transfer operator.**  Three earlier laps
   wrestled with it.  `CFGammaMixing.setIntegral_inter_preimage` is an EXACT identity
   (`∫_{I_v∩T^{−m}B}h_s = (∫_B h_{tChain s v})·(∫_{I_v}h_s)`, `tChain s v ∈ [0,1]`), so a pin that
   is uniform in the tail parameter is *already* the conditional statement given the whole past —
   gap zero, no loss of rate.  Composing with the mixture `γ = ∫₀¹(h_s·Leb)dλ(s)` costs nothing
   because the bound is pointwise in `s`.
2. **Uniformity in the initial state buys the past-dependent future.**  Since the pin holds for
   every `e`, the future set attached to `I_v` may be read from `runState δ d v`.  No partition of
   a past family by its exit state is needed.
3. **A mean bound cannot reach `ClassEquidistribution`; the variance can.**  `windowBound` is a
   sup of absolute values, so the route is: two-point correlations → `∫devAvg² = O(1/K)` →
   Cauchy–Schwarz → orbit transfer.
4. **The ε-order is forced**: `ε ↦ K` (variance), then `K ↦ Z` (digit bound must beat
   `(1+|L|)(K+|q|)τ(Z)`, and `m = K+|q|` grows with `K`).  `n`'s threshold may depend on `x`;
   `K` may not — which is why `ClassEquidistribution` puts `∃K` outside `∀x`.
5. **Lean/mathlib gotchas** (some re-confirmed from the reference corpus): `𝒫` is notation for
   `Set.powerset`, unusable as an identifier (`𝒮`, `𝒱` are fine); `pow_le_pow_left₀`;
   `abs_add_le`; `Filter.eventuallyEq_set`; `integral_indicator_const` (not `_one`, which is
   stated with `indicator 1` not `indicator (fun _ => 1)`); set-valued `=ᵐ` needs `(… : Set ℝ)`
   ascriptions or `Inter (ℝ → Prop)` fails; `Real.mul_self_sqrt` (not `← Real.sqrt_mul_self`,
   which rewrites every occurrence of the radicand); `integrable_finsetSum` / `integral_finsetSum`
   / `Set.mem_ofPred_eq` (renames); there are TWO `boundedWords` (`CFSchedule`, `VandeheyAut`) and
   TWO `mem_boundedWords` — qualify them.

## NEXT (in order) — see `PENDING_WORK.md` top section for detail

1. **The fiber.**  The transducer state space is `M_D` (det-`±D` normal forms), not the class
   space.  The class is *the* obstruction to synchronization
   (`PROBE-2026-09-27-transducer-not-synchronizing.md`), and within a class states DO merge
   (`probes/cf_transducer_class.py`).  Define the class projection `M_D → ℙ¹(ℤ/D)` and prove
   **class-relative synchronization**: for `ℓ` large the transducer state at `i` is a function of
   (class at `i`, last `ℓ` digits) outside a set of positions of frequency `→ 0`.  Then every joint
   (window, transducer-state) count is a finite sum of joint (window, class) counts, which
   `tendsto_jointCount_classStep` evaluates.
2. **Vandehey §2 (Raney transducer)**: finiteness of det-`±D` normal forms, the factorization
   `M·A_n = (output CF matrices)·(normal form)`, identity (9).
3. **§5–§6 (trigger counting)**: occurrences of a word `r` in the output are triggered by finitely
   many (state, input window) pairs; `ℓ(n) = c₁n(1+o(1))`, `#occ_r(n) = c_r n(1+o(1))`, so the
   frequency → `c_r/c₁`, independent of `x`.  Then `VandeheyUniformFreq` closes and
   `vandehey_matrix_action_of_uniformFreq` finishes Theorem 1.1.
4. Composite `D`: `ClassSpace D = Option (ZMod D)` models `ℙ¹(ℤ/D)` only for prime `D`.
   `classEquidistribution_of_pin` is already automaton-generic, so this is
   hypothesis-verification, not redesign.
5. Repoint the `Maze.lean` row citing Vandehey 1.1 off `.cited` once
   `vandehey_matrix_action_holds` is genuinely sorry-free.

**Possible shortcut, worth evaluating before grinding §2.**  By Smith normal form every nonsingular
integer Möbius map is a composition of `GL₂(ℤ)` maps and `x ↦ nx`, `x ↦ x/n`.  The `GL₂(ℤ)` part is
elementary (Serret: `GL₂(ℤ)`-equivalent numbers have CF expansions sharing a tail, and digit
frequencies only see the tail), so the whole theorem reduces to `x ↦ Dx` for prime `D` — exactly
the case the class automaton is built for.  This could cut §2's bookkeeping substantially.

## Designated-open, do not touch

`VandeheyAut.exists_jointFreq_limit` (`VandeheyAutomaton.lean:622`) — its `Synchronizing`
hypothesis is **unsatisfiable** for the transducer Theorem 1.1 needs
(`PROBE-2026-09-27-transducer-not-synchronizing.md`).  Leave it.
The one open `sorry` in the scoped target is `vandeheyUniformFreq_holds`
(`LiteratureVandehey.lean:299`); all other `src/` sorries are off-campaign and out of scope.
