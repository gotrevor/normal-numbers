# PENDING WORK — B5′ campaign

> **CURRENT STATE (2026-08-23 reflection lap, `dac27b5`).** Everything below the
> "── ARCHIVE ──" divider is the W3/W4/W5-input history, kept for the proven-lemma
> record but SUPERSEDED. Live state:
>
> - ✅ W1–W4 done. ✅ **W5 core done**: B–Y Lemma 13 (`TBrick.exists_refinement`),
>   THE SCHEDULE (`CFSchedule`), limit point `xstar` (irrational, in every
>   scheduled cylinder), **CF normality of `xstar`** (`xstar_cf_freq_tendsto`).
>   All axiom-clean. src/ sorry-free, 8742 jobs green.
> - 🔨 **Frontier = d-ary side** (`DaryCorrect.lean`): base-`d` simple normality
>   of `xstar` for every `d ≥ 2`. Staged: `xstar_dary_step`/`xstar_dary_window`
>   (per-stage good block, ≥ `kmin` new digits), `badBlocks↔HasDiscLt` bridge,
>   `two_pow_le_cfK`.
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
