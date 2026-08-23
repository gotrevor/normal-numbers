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

- NEXT concrete step (the remaining crux — the CF side + combine):
  (i) **CF discrepancy side**: aggregate `chebyshev_blockCount_brick` across
      CF words into a single bad-zone bound `≤ (small in n)·γ(I_w)`, via
      `CFDiscLt` / `CFWordBridge` (blockCount ↔ countOccurrences).  Subtlety:
      the CF alphabet is infinite — must use the `CFDiscLt` deviation-form
      aggregation (finite weighted sum) not a per-word union.  This is the
      one genuinely-open sub-piece left in the balance.
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
