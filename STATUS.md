# STATUS — normal-numbers 📊

**B5′ COMPLETE + axiom-clean (10 headlines); B6 campaign OPEN — Vandehey §7 affine images, additive, one crux `sorry` left.** · **Build**: 🟢 green (8757 jobs) · **Updated**: review lap · 2026-08-24 · `7f46d25`

## Where it stands

**B5′ is DONE; B6 is the active frontier — route PIVOTED (hdom refuted).** The
whole B5′ expedition (ten headline theorems — Track A base-b normality + Track B
Tier 1 Becher–Yuhjtman + Tier 2 Khinchin) is proved and `#print axioms`-clean
(trust triple only). The LIVE work is the **additive B6 campaign** (Vandehey,
Compositio 2017, §7): a real `x` with BOTH `x` and its affine image `ψ(x)=q·x+r`
CF-normal, for `q>0`. It reduces (`isCFNormal_of_irrational_orbit_freq`) to ONE
crux — `exists_interleaved_affine_witness` (`CFScheduleA.lean:1559`), the **sole
open `sorry` in `src/`**: an interleaved (diagonal) schedule building `x` as a
limit of nested intervals whose x-stages and ψ-stages alternate. The
route-decisive uncertainty was SETTLED this cycle: the natural **dominance**
hypothesis (`|block| = o(word)`) is UNATTAINABLE — steering resolves each stream
to the other's metric scale at cost `Θ(word)`, so blocks are `Θ(word)` and growth
is geometric. The hdom-free **uniform-prefix-goodness** route is mandatory, and
its crux crack — `exists_uniformly_freq_good_block_steer` (a steer block whose
EVERY prefix is `δ·k + o(k)`-good) — is PROVED + axiom-clean. What remains is the
**hdom-free chain-limit assembly**: a copy-extended `chain_cf_digit_freq_tendsto`
whose mid-block bound uses the block's own prefix bound (not the refuted `hdom`),
then the ψ-round rebuild + two-stream recursion.

- **Track A** (base-b normality): Wall, the ln 2 reduction (conditional on the
  correct equidistribution hypothesis), Stoneham — axiom-clean.
- **Tier 1 = Becher–Yuhjtman** (IMRN 2019): `exists_absolutely_normal_cf_normal`
  — an explicit real absolutely normal ∧ CF-normal. Apparently the first
  formalization in any prover. Axiom-clean.
- **Tier 2 = expedition headline**: `exists_absolutely_normal_cf_normal_khinchin`
  — additionally Khinchin-typical. Axiom-clean.
- **B6 = affine images (active)**: `exists_cfNormal_and_affine_cfNormal` — target
  proved MODULO the crux `sorry`; depends on `sorryAx` until the schedule closes.

## What's happened (newest first)

- 2026-08-24 (review lap): **B6 route pivot RATIFIED — hdom refuted, hdom-free
  limit is the last crux.** Inventory (real `#print axioms`): build green 8757,
  both B5′ headlines trust-triple, sole `src/` `sorry` = the B6 crux
  `exists_interleaved_affine_witness`. Confirmed the grind laps since the last
  review CORRECTLY diverged from the prior directive: they refuted `hdom`
  (`ec0875d` — steer blocks are `Θ(word)`, dominance impossible) and PROVED the
  replacement crux crack `exists_uniformly_freq_good_block_steer` (`f2b4b33`,
  axiom-clean) + the full uniformly-good-block toolkit (`quadScales*`, multiscale
  measure, interpolation arith) + `chainTail_dev_split_var`. The CURRENT DIRECTIVE
  was STALE (still mandated `chain_orbit_equidist` WITH dominance); rewrote it to
  the **hdom-free `chain_cf_digit_freq_tendsto` variant** (step-4 assembly),
  FORBADE more block/measure atoms, named the route-decisive case (mid-block bound
  closing via `addslack₂` + `o(word)` boundary slack dividing out). No charter
  trigger fired.

- 2026-08-24 (review lap): **B6 course-correction — PIVOT TO THE CRUX.**
  Inventory: build green 8756, B5′ headlines re-verified trust-triple, sole
  `src/` `sorry` = the B6 crux `exists_interleaved_affine_witness`. Diagnosed
  crux-neglect: 11 straight grind laps (11–21) each proved a geometric ATOM
  (axiom-clean, green) but the crux stayed untouched and the recursion/telescoping
  was deferred "next lap" ~7×. Declared the atom toolkit COMPLETE; reset the
  CURRENT DIRECTIVE to build the frequency telescoping hardest-first via an
  abstract generic-chain lemma `chain_orbit_equidist`, naming the route-decisive
  case (dominance vs growing fillers + alternation). No charter trigger fired.

- 2026-08-24 (reflection lap → COMPLETION): **Tier 2 CLOSED — the whole
  expedition is done, axiom-clean.** Steps 1–3 all landed this lap. (1) Rewired
  `CFSchedule.lean` to the summable-**family** refinement (fixed cutoffs
  `khinchinK j`, no level-tied `K_t→∞`). (2) Built the log-tail telescoping in
  `CFCorrect.lean` (`logTailMass` + monotonicity, `uSched_logTail_le`,
  `tailSched_logTail_le`, `xstar_logTail_prefix_bound`, `logTailMass_cfPrefix`)
  and assembled the crux `xstar_log_tail_uniform`, hence `xstar_khinchinTypical`
  (axiom-clean). (3) Route D′: relocated the frozen `khinchinK₀`/`KhinchinTypical`
  defs byte-identical to a new upstream `KhinchinDefs.lean`, dropped Khinchin's
  `import Headline`, and closed the Tier-2 headline
  `⟨xstar, xstar_isAbsolutelyNormal, xstar_isCFNormal, xstar_khinchinTypical⟩`.
  All 10 headlines re-`#print axioms`-verified trust-triple. Also (earlier in the
  lap): ratified route C′ and de-staled the CURRENT DIRECTIVE (it still named the
  superseded Chebyshev/variance plan). ROUTE VERDICT: CONTINUE → reached the
  destination.
- 2026-08-24 (grind run, route C′): **FAMILY machinery COMPLETE + axiom-clean.**
  `volume_logBadZone_le_vol` (Lebesgue bridge), three-zone combine
  (`exists_good_avoiding_bad_khinchin` + `_family`), `exists_refinement_uniform_khinchin_family`
  (log-tail payload at every `j<tK`), `CFLogTail.lean` layering (khinchinK₀-free
  upstream). Found+fixed the level-tied-cutoff design bug via the summable family
  (geometric budget `≤1/7`). CFSchedule still carries the SUPERSEDED single-zone
  threading (true, green, unused) — next lap rewires it to the family form.
- 2026-08-24 (review lap): **Tier-2 route SETTLED, schedule fence relaxed, moment
  seed proved.** Broke the 3-lap "operator-gated" stall (fc801ba/17dc2c9/7d6740f
  were pure route-analysis ending in a false "need operator" stop). Confirmed the
  only route is the additive W6 log-concentration bad zone; relaxed the
  `DIRECTION.md` "don't touch the schedule" fence to additive-only with a
  Tier-1-axiom invariant. Proved `summable_gaussKuzmin_logsq` (moment condition
  `E[(log a₁)²]<∞`, axiom-clean) — the analytic seed of the tail bound.
  Re-verified Tier 1 axiom-clean (trust triple), build green (8735 jobs).
- 2026-08-24 (grind laps): **Tier 1 LOCKED** (`b3bc2c4`,
  `exists_absolutely_normal_cf_normal`, axiom-clean) + Tier-2 assembly seeded:
  `gaussMeasure_Ioo`/`gaussMeasure_digit_cylinder` (Gauss–Kuzmin single-digit
  law), `Khinchin.lean` (geometric-mean⟺log-average reduction `khinchinTypical_iff_log_tendsto`,
  `khinchinK₀_pos`), `prod_le_cfK`+`wSched_log_sum_le` (total log-mass bound),
  `xstar_log_digit_avg_truncated_tendsto` (finite-truncation slice).
- 2026-08-24 (review lap): **Pillai crux `windowCount_eq_sum_phaseCount` PROVED**
  (axiom-clean) — the `Q`-scale↔`N`-scale phase-count identity, via a
  `Finset.card_nbij'` bijection `i ↔ i/r`; dodged last lap's `r*(i/r)` vs
  `(i/r)*r` omega-atom trap by anchoring on `Nat.div_add_mod` + one explicit
  `Nat.mul_comm`. Re-verified headlines axiom-clean (trust triple), build green
  (8743 jobs). Directive refreshed (it still named the closed `m`-growth
  estimate as THE crux) → FINISH Pillai, now double-limit-first. No trigger fired.
- 2026-08-24 (grind laps): **d-ary side CLOSED** — `xstar_dary_freq_tendsto`
  (base-`d` simple normality every base, axiom-clean); the `m`-growth interior
  crux (`tendsto_gain_div_mSched_sub`) + Pillai combinatorial core
  (`phaseWindowFreq_tendsto`, `card_straddling_phases`, window/slice
  correspondence, `card_matchingValues`).
- 2026-08-23 (reflection lap): re-verified 10 headlines axiom-clean (trust
  triple), build green (8742 jobs), src/ sorry-free. Found DIRECTION/STATUS/
  PENDING_WORK badly STALE — they still named the Lemma-13 assembly the
  "untouched crux", but Lemma 13 + schedule + `xstar` + CF normality all landed
  since. Refreshed all three; reframed the destination into Tier 1 (B–Y
  abs-normal + CF-normal, source-backed) vs Tier 2 (Khinchin, campaign-original
  stretch); set directive to LOCK Tier 1 via the d-ary `m`-growth estimate.
  ROUTE VERDICT: CONTINUE (no trigger fired; strong forward motion).
- 2026-08-23: **CF NORMALITY OF `xstar` PROVED** (`CFCorrect.lean`,
  `xstar_cf_freq_tendsto`) + **d-ary digit extraction / payload accessors**
  (`DaryDigits`/`DaryCorrect`): digit windows are literally the base-d digits;
  each active stage gives a good block. All axiom-clean.
- 2026-08-23: **THE SCHEDULE + Lemma 13 + limit point** — `CFSchedule.lean`
  (uniform Lemma 13, brick sequence, invariants, dominance), `xstar`
  irrational in every scheduled cylinder (`CFLimit` applied). Axiom-clean.
- 2026-08-23: **B–Y Lemma 13 PROVED** (`TBrick.lean`, both `t'=t` and `t→t+1`)
  — the measure-balance selection lemma (good mass ½|I_w| beats CF + Σ d-ary bad
  zones) made UNCONDITIONAL; seed brick + refinement toolkit (`TBrickRefine`).
- 2026-08-23 (review lap): diagnosed input-gathering fixation, redirected to the
  Lemma-13 measure-balance assembly (now proved).

## Outstanding

### Short-term (mirror PENDING_WORK top — B6 hdom-free assembly)
1. ✅ **DONE** — hdom-free chain limit: `chainTail_dev_prefix_var`,
   `chain_cf_digit_freq_tendsto_uniform`, `chain_orbit_equidist_uniform`
   (`CFChainFreq`, axiom-clean). Needs `hblock`/`hslack` from the schedule.
2. **ψ-round `_uniform` (NOW hardest-first)** — rebuild `exists_freq_good_extend_affine_steer`
   to emit uniformly-good blocks (call `exists_uniformly_freq_good_block_steer`;
   pick `n₁,s`, `m_s` per the measure budget + resolution length). Route-decisive:
   per-round feasibility (budget vs resolution) + `hslack` from geometric growth.
3. **`SchedStateA`/`schedStepA`/`schedA`/limit** — two-stream recursion → two
   uniformly-good chains → `chain_orbit_equidist_uniform` both streams → the crux.

### Long-term
- B6 general family / Tier-2 image-Khinchin stretch (detaches freely; after the
  single-map crux closes).

### To completion
- B5′ (Track A + Tier 1 + Tier 2): **DONE**, all axiom-clean.
- B6 single-map (`exists_cfNormal_and_affine_cfNormal`): crux `sorry` open →
  close via the 3 items above.

## Axiom ledger (fidelity spine — all from real `#print axioms`, 2026-08-24 review lap)

| headline theorem | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `exists_absolutely_normal_cf_normal` (**Tier 1 = Becher–Yuhjtman**) | uncond | trust triple | 🟢 DONE (re-verified this lap) |
| `exists_absolutely_normal_cf_normal_khinchin` (**Tier 2 headline**) | uncond | trust triple | 🟢 DONE (re-verified this lap) |
| `exists_cfNormal_and_affine_cfNormal` (**B6 affine image**, active) | uncond (q>0) | `[propext, sorryAx, Classical.choice, Quot.sound]` | 🔨 crux `sorry` (`exists_interleaved_affine_witness`); NOT a math axiom — disclosed decomposition, being discharged |
| `isNormal_iff_equidistributed_orbit` (Wall) | uncond | trust triple | 🟢 DONE |
| `isNormal_log_two_of_equidistributed` | cond (orbit equidist.) | trust triple | 🟢 DONE (hypothesis is the open conjecture, correctly a hypothesis) |
| `isNormal_two_stoneham23` (Stoneham) | uncond | trust triple | 🟢 DONE |
| `xstar_cf_freq_tendsto` (CF normality of x\*) | uncond | trust triple | 🟢 DONE |
| `xstar_dary_freq_tendsto` (d-ary simple normality, every base) | uncond | trust triple | 🟢 DONE |
| `pillai` (simple-to-all-powers ⇒ full normality) | uncond | trust triple | 🟢 DONE |
| `gaussMeasure_digit_cylinder` (Gauss–Kuzmin single-digit law) | uncond | trust triple | 🟢 DONE |
| `summable_gaussKuzmin_logsq` (Tier-2 moment seed) | uncond | trust triple | 🟢 DONE |

Math-axiom count (🟢+🟡+🟠, excluding trust base + native_decide artifacts):
**0** proven-but-cited axioms across all 10 B5′ headlines (every one 🟢, trust
triple only). The B6 target carries `sorryAx` — a **disclosed decomposition
`sorry`**, NOT a cited math axiom — being actively discharged (the interleaved
schedule). No 🟡/🟠 debt, no 🔴. Trust triple = propext, Classical.choice,
Quot.sound throughout.

## Pointers
DIRECTION.md (CURRENT DIRECTIVE) · ROADMAP.md · KHINCHIN.md (B5′ plan W1–W6) ·
JUDGE.md · papers/literature-review.md · newest HANDOFF (`ls HANDOFF-*.md | sort | tail -1`) ·
PENDING_WORK.md · papers/becher-yuhjtman-2019-*.md
