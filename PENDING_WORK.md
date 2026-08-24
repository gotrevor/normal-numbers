# PENDING WORK — B6 campaign (affine images) + B5′ (COMPLETE, below)

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
   `chain_orbit_equidist`. Items 2–5 of `HANDOFF-2026-08-27-2359.md` (limit point,
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
