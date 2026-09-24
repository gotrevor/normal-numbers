# STATUS — normal-numbers 📊

**ACTIVE (branch `wip/twopoint-avg`): the C1 casting-out swing.  `ConjC1` now follows from
Delange's theorem plus the single node `PairDecorr` — the cited Kátai/BSZ hypothesis is GONE.**
· **Build**: 🟢 green (9283 jobs) · **Updated**: lap 25 · 2026-09-24 · HEAD after `dfaa5c7`
· On `master`/Pair A: Theorem C′ (`isNormal_subsetLambert_of_sqrtFreshMassZero`) PROVED and
  trust-triple, 2026-09-23.

## Where it stands (ACTIVE: C1 / twopoint campaign, branch `wip/twopoint-avg`)

`KICKOFF-2026-09-24-twopoint-bet.md` bets on the averaged weighted two-point leaf of C1.  Laps
1–10 proved the **Kátai/BSZ inequality itself** in kernel (`katai_master`, `katai_mean_sq`) — it is
a theorem here, not a citation.  Laps 11–12 rewired C1 onto the growing-`w` arithmetic leaf
`twoPointGramSum b t (w N) N = o(N·L(w N)²)`.  Laps 13–23 priced four attacks on that leaf against
the *trivial* bound and refuted three of them as estimation strategies.

**Lap 24 (review lap) corrected the laps-13–23 framing.**  The cutoff `w` is existentially
quantified, so the leaf only has to hold at ONE cutoff per `N`; diagonalising
(`exists_slow_cutoff`), fixed-pair `o(N)` decorrelation already closes it.  So the whole
uniform-in-`(p,q,w)` saving programme of laps 15–23 is **sufficient but far from necessary**, and
the wrap-2 claim "per-pair decorrelation does not imply the leaf" is **false** — the implication is
now a theorem (`twoPointPairGramSmall_of_fixedPair`).  Cashing it:
**`conjC1_of_delange_pairDecorr` : Delange + `PairDecorr` ⟹ `ConjC1`**, with NO cited Kátai
hypothesis — strictly sharper than `conjC1_of_delange_katai` (`SwingC1Weyl.lean`).

Where that leaves the bet: `PairDecorr b t` for a fixed pair `p ≠ q` is
`E_m e(t(θ_{pm} − θ_{qm})) → 0`, which by `pairDecorr_iff_twoPointWeighted` **is** a
natural-density weighted two-point Elliott correlation.  That is a **named open problem** (Tao
2016 gives it in *logarithmic* average only).  The leaf is therefore no harder than Elliott-2pt at
natural density, and — by `tendsto_maxRecipSum_div_sq` — strictly weaker than it, with no known
route in between.

## What's happened (C1 / twopoint campaign, newest first)

- **2026-09-24 (lap 25) — THE KÁTAI-FREE CHAIN, END TO END.**  `TwoPointKataiFree.lean`:
  `conjC1_of_delange_decouple`, `…_largeDecay`, `…_shiftCorr`, **`conjC1_of_delange_multiElliott`**.
  Every headline of the swing loses its cited `KataiOrthogonality`.  **`ConjC1` now rests on exactly
  two inputs**: `DelangeMean` (🟡 proven) and `MultiElliott` (🔴 open, and *equivalent* to the leaf).
  Two escape hatches closed: `WeightDecouple` is the whole crux, not an easier piece; and the
  elementary small/large-prime split cannot be tuned (leaf (D)'s tension re-derived).
- **2026-09-24 (lap 24, review lap) — THE DIAGONAL CORRECTION.**  `TwoPointGramDiagonal.lean`:
  `exists_slow_cutoff` (diagonalisation, no uniformity in `w` needed),
  `twoPointPairGramSmall_of_fixedPair`, `truncSum_div_tendsto_of_twoPointWeighted`, and three
  Kátai-free reductions of C1 — `conjC1_of_delange_pairwiseTwoPoint`,
  `conjC1_of_delange_twoPointElliott_weightDecouple`, `conjC1_of_delange_pairDecorr`.  All
  trust-triple.  Direction REVISED: stop chasing a uniform per-pair saving; the target is the
  fixed-pair statement, and the honest read is that this route is Elliott-equivalent in practice.
- **2026-09-24 (laps 11–23)** — `katai_mean_sq` (the Kátai step as a theorem), the leaf unfolded
  to arithmetic (`kataiPairGram_eq`), and four routes priced: trivial estimates insufficient by an
  unbounded factor; `ℓ¹` averaging no gain; `ℓ²`/fourth moment needs an exact `≥ N²/8` evaluation;
  rotation pairing rigid for constant `z`, live for a pointwise gap.
- **2026-09-24 (laps 1–10)** — the Kátai/BSZ inequality assembled end-to-end in kernel
  (`TwoPointKataiAssemble.lean`); the repo's cited `KataiOrthogonalityAvg` shown to OVERSTATE the
  literature; the fixed-`w` quantifier worry refuted as an *argument* (`TwoPointWorry.lean`) and
  then shown not to be where a proof comes from (probe: the arithmetic table is not asynchronous).

## Axiom ledger — C1 / twopoint campaign (real `#print axioms`, 2026-09-24, 9282 jobs)

| headline | paper claim | `#print axioms` | math axioms |
|---|---|---|---|
| `conjC1_of_delange_pairDecorr` | C1 is conjectural (Fable C1) | `[propext, Classical.choice, Quot.sound]` | **0** — hypotheses only: `DelangeMean` (🟡 proven, Selberg–Delange, project-scale) and `PairDecorr` (🔴 open: natural-density two-point Elliott for `ζ^ω`) |
| `conjC1_of_delange_twoPointGram` | as above | trust triple | 0 — `DelangeMean` 🟡 + the growing-`w` leaf 🔴 |
| `conjC1_of_delange_multiElliott` | C1 is conjectural | trust triple | 0 — `DelangeMean` 🟡 + `MultiElliott` 🔴 (open, *equivalent* to the leaf).  **The sharpest form: two inputs, nothing else cited.** |
| `katai_mean_sq` | Kátai 1986 / BSZ 2013 | trust triple | **0 — DISCHARGED** (was the cited `KataiOrthogonality`) |
| `twoPointWeightedAvg_all` (`TwoPointBet.lean`) | the bet's ratified target | `sorryAx` | open `sorry`, disclosed; 🔴 reduces to fixed-pair Elliott |

🔴 here is honest: C1 is a *conjecture* in Fable, so a route resting on an open two-point Elliott
statement is not a straying unconditional theorem — it is the conjecture's true depth, now
measured.  The 🟡 `DelangeMean` is the live debt worth chipping (Selberg–Delange for `ζ^ω`).

## Where it stands (multicutoff campaign — DONE, `master`/Pair A)

Laps 0–7 of `KICKOFF-2026-09-22-multicutoff-lean.md` are landed and the headline
`isNormal_subsetLambert_of_sqrtFreshMassZero` is **fully assembled and compiling**: the root chain,
Lemma B, the graded joint state, hypothesis-free Theorem A (`KMT.window_bound_schedule`), the
explicit Astra §8 schedule, and the squeeze `kmt_along_graded` + `tailOK_graded`.  `tailOK_graded`
— the tail crux of the last two laps — is **PROVED**.  What remains is **nothing**: the last three leaves
(`termE5_tendsto`, `schedule_admissible`, `termE4c_tendsto`) closed on 2026-09-23, and
`#print axioms isNormal_subsetLambert_of_sqrtFreshMassZero` is the bare trust triple.  `src/`
holds only the two pre-existing off-campaign `sorry`s.

**The route finding that got us here** (laps G5c-e…i, both kept): Theorem A's contracting site
`j₀` has index `≤ log₄|h|`, a constant for fixed `h` uniform in `N`
(`PrimeModelSiteIndexBound.exists_site_re_nonpos_le`).  So leg E5 collects its contraction at the
**near-top** cutoff `y_{cIdx}`, not at the bottom cutoff, and the root chain from there to `N` is
`O(log u_N)` halvings rather than `≍ L₃N`.  That is what lets `J_N` be tied to the full mass
`S_P(N)` as Astra §8 has it, and it reduced the tail to the one-step chain `S_P(N,2N) ≤ ε_N`.

## What's happened (multicutoff campaign, newest first)

- **2026-09-23 (laps G5c-k/l/m) — THEOREM C′ PROVED.**  `termE5_tendsto` (Astra 8.6),
  `schedule_admissible` (all eleven clauses) and `termE4c_tendsto` all landed sorry-free, and the
  headline is trust-triple clean.  ROUTE FINDING in the middle one: the cut depth `LG` must be
  read off the bottom **site** cutoff `y_{J−1}`, not off `yBotG` — the two dyadic-cut clauses pin
  `2^L` from both sides and `yBotG` is unboundedly far below `y_{J−1}` on the mass branch of
  `JG`'s `min`, where `hcutlo` then fails.  `LG` redefined; `LG_spec`, `cut_le_next`,
  `twoJ1_lt_yBotG`, `yG_le_self`, `log_ge_sq` are the new helpers.
- **2026-09-23 (review lap)** — direction KEPT, priority narrowed to the three remaining leaves,
  E5 first (`DIRECTION.md` → CURRENT DIRECTIVE refreshed); ground truth re-derived at 9161 jobs.
- **2026-09-22/23 (laps G5c-a…j)** — the schedule and Theorem C′.  Landed: `yBotG_tendsto`,
  `termE4b_tendsto`, `termE4a_tendsto`, `JG_tendsto`, `tail_graded`, the site-index bound (new
  file, route finding), the route correction (`JG` retied to `S_P(N)`, E5 at `y_{cIdx}`,
  `freshMassTwo_graded` + `tailOK_graded` PROVED), `recipSumIoc_yG_le` (the short root chain),
  `termE1_tendsto`.  Statement changes: the three graded-chain `∃ j₀` conclusions gained the
  conjunct `(j₀ : ℕ) ≤ Nat.log 4 h.natAbs` — a pure strengthening of this campaign's own
  statements; the ungraded chain and `PrimeModelBrunLower.lean` untouched.
- **2026-09-22 (laps G1–G5b, the regrade)** — graded local weight, graded box tail, graded joint
  state, graded E4, Theorem A on the graded state, Theorem A in schedule form.  This executed the
  2026-09-22 ROUTE CORRECTION: the constant class count `dpK k` is arithmetically dead
  (`log R ≥ 128k log y_0` ⇒ transfer term `≍ ρ_N·L₄N`; and the ungraded E4a diverges like
  `J e^{20}`), so the class count and the Markov range must be graded by band.
- **2026-09-22 (laps 0–6)** — root chain + `SqrtFreshMassZero`; block-Bonferroni sieve, product-
  model defect, support level, graded CRT counts, graded retained box; Theorem A with all five
  legs.  Nothing in the paper refuted; one paper *gap* closed (Astra §8 tacitly uses `j₀` fixed).

## Outstanding (multicutoff campaign)

### Short-term (mirrors PENDING_WORK top)
1. `Statement.lean`-style audit surface for `SqrtFreshMassZero` / `DivergentRecip` /
   `IsNormal 4 (subsetLambert P 4)` — the only piece of the campaign's own hygiene not yet done.
2. The abstract Astra §10 consumer `F_N = ∑_j 4^{−j} S_P(y_j, 2N) → 0` — strictly weaker
   hypothesis, same schedule; only the E1 leg needs re-running.

### Long-term
Off-campaign and designated open: `PrimeLambertOscillation.phaseOscillation`,
`MahlerDriftOne.exists_prime_nonresidue`.

### To completion
Theorem C′ is done.  The campaign's remaining work is the audit surface and the §10 consumer.

## Axiom ledger — multicutoff campaign (real `#print axioms`, 2026-09-23, 9161 jobs)

| headline theorem | paper claim | `#print axioms` shows | verdict |
|---|---|---|---|
| `SqrtFresh.recipSumIoc_le_rootChain` | Astra (11.3), exact finite root chain — UNCOND | trust triple | 🟢 clean |
| `SqrtFresh.sqrtFreshMassZero_of_freshMassZero` | Astra §11.4 | trust triple | 🟢 clean |
| `SqrtFresh.sqrtFreshMassZero_of_relDensityZero` | Astra §11.4 | trust triple | 🟢 clean |
| `BlockSieve.graded_brun_lower` | Lemma B, arithmetic form (Fable §3 / Astra §4) | trust triple | 🟢 clean |
| `KMT.window_bound_schedule` | **Theorem A** in schedule form, no model/sieve hypothesis | trust triple | 🟢 clean |
| `SiteIndexBound.exists_site_re_nonpos_le` | closes the Astra §8 gap (`j₀ ≤ log₄\|h\|`) | trust triple | 🟢 clean |
| `FamilyGraded.tailOK_graded` | the `TailOK` half of Theorem C′ | trust triple | 🟢 clean |
| `FamilyGraded.termE1_tendsto` / `termE4a_` / `termE4b_` | (8.2)/(8.3)/(8.4) | trust triple | 🟢 clean |
| `FamilyGraded.termE5_tendsto` / `schedule_admissible` / `termE4c_tendsto` | (8.6), §8 admissibility, (8.7) | trust triple | 🟢 clean |
| `FamilyGraded.kmt_along_graded` | the `KMT_along` half of Theorem C′ | trust triple | 🟢 clean |
| `FamilyGraded.isNormal_subsetLambert_of_sqrtFreshMassZero` | **Theorem C′** (Fable §9 / Astra §11) — UNCOND | trust triple | 🟢 **clean — PROVED** |

Math-axiom count for the campaign: **0** (no `axiom` declarations anywhere; the trust base is
`propext, Classical.choice, Quot.sound` throughout, and every headline reaches it with no
`sorryAx`).  There is no debt left in this campaign.

## Pointers (multicutoff)
`KICKOFF-2026-09-22-multicutoff-lean.md` · `papers/ROUND2-multicutoff-fable.md` ·
`papers/ROUND2-multicutoff-astra.md` · `HANDOFF-2026-09-23-theoremC-COMPLETE.md` ·
`PENDING_WORK.md` · `DIRECTION.md` (CURRENT DIRECTIVE)

---

# (below: the G4 disjunctivity campaign — CLOSED; kept as the durable overview of that work)


## 🗺️ The maze map — read before proposing a route

`src/NormalNumbers/Maze.lean` is the register of routes **walked and closed**: 116 halls, 10
of them machine-checked (`alias` onto the refutation theorem, so renaming it breaks the
build).  Verdict vocabulary and its tells live in the `Verdict` inductive; the three evidence
tiers in `Tier`.  ⚠️ Only `Tier.kernel` rows carry the kernel's authority.

Two passes: match your route against the eight shapes first (most halls close for a
structural reason visible *before* any work), then grep `register` for your object.  Design
notes: `DESIGN-2026-09-20-t3c-verdict.md`, `DESIGN-2026-09-20-walsh-weyl-bridge.md`.
The frontier beside the register: `Walsh.lean` (base two) and `WalshBase.lean` (every base)
carry the digit-character criterion, both directions, as the dual of `equidistributed_of_weyl`.

> **Sparse-prime normality PROVED unconditionally (2026-09-22, Fable session).**  The frozen
> `KMT_quant₂ C₁ C₂` (`C₁ k = exp 4k`, `C₂ k = exp(exp(k+7))`) is a theorem,
> `PrimeModelKMT.KMT_quant₂_primeModel`, assembled from the prime model (lower Brun sieve →
> radical joint law → phase contraction at the least nontrivial site), and
> `exists_sparse_normal_unconditional : ∃ S, DivergentRecip S ∧ IsNormal 4 (subsetLambert S 4)`
> is axiom-clean (`[propext, Classical.choice, Quot.sound]`, main `e222677`).  Says nothing about
> `G₄` or any classical constant.  Spec + audit: `papers/prime-model-assembly-2026-09-22.md`.
> **Family theorem also PROVED**: `PrimeModelFamily.isNormal_subsetLambert_of_sparse` — every
> prime set with `π_P(x) log log x ≤ π(x)` eventually and divergent Σ1/p has a normal base-4
> Lambert constant, axiom-clean, schedule built from the actual accumulated mass.  The paper
> records the growth regime where relative-density-zero alone fails on this route (L¹ tail
> criterion vs correlation majorant coupling, `π_P ~ π/L₄`; conditional obstruction, not a
> constructed counterexample).  Paper M1/M2 misprints corrected after Astra's audit 2026-09-22.
> **Sharper family theorem PROVED** (same day): `PrimeModelFamilySharp.isNormal_subsetLambert_of_sparseIter`
> — hypothesis weakened to `π_P(x)·(log log log x)^5 ≤ π(x)` eventually, by consuming the
> polynomial-constant `window_bound_regime` directly instead of the frozen `KMT_quant₂` shape;
> the tail is then paid for by the crude total mass `∑_{p≤2N} 1/p ≤ 12 L₂N + 21`, no density
> input.  Paper Part III.  Frontier of this schedule family: exponent `> 4` on `L₃` (`> 2` with
> `ε = J^{-4}`); `π_P ≈ π/L₄` still fails.  **Exponent 3 also PROVED** the same day:
> `PrimeModelFamilyIter.isNormal_subsetLambert_of_sparseIter3` (`π_P·(log log log x)^3 ≤ π`),
> schedule `J₁ = ⌊L₃N⌋₊`, `ε = J₁^{-4}`, `J = min(J₁, ⌊S_P(y)/8⌋₊)`; paper Part IV.  Frontier of
> this schedule family: any exponent `> 2` on `L₃` — **PROVED as a theorem**
> (`isNormal_subsetLambert_of_sparseIterPow`, real `β > 2`, paper Part V); below that only the
> transfer error `E1` is left.
> **Superseded the same evening** (Astra's phase-weighted E1, refereed): the window length never
> needed to multiply the fresh mass.  `PrimeModelKMTFixedH.window_bound_regime_h` (fixed `h`,
> coefficient `4π|h|/3`) and `PrimeModelFamilyL4.isNormal_subsetLambert_of_sparseL4o`:
> **`(π_P(x)/π(x))·log log log log x → 0` and divergent Σ1/p ⇒ normal** (paper Part VI).  Covers
> every `π/(L₃)^β`, `β > 0`, and `π/(L₄)^γ`, `γ > 1`.  Barrier: density `≍ 1/L₄`, with an explicit
> density-zero divergent set on which the fresh-mass criterion fails (Part VI).
> **Abstract consumer PROVED**: `PrimeModelFamilyConsumer.isNormal_subsetLambert_of_freshMassZero` —
> divergent Σ1/p plus `recipSumIoc P (yI N) (2N) → 0` ⇒ normal, **no density hypothesis**; reaches
> sets of limsup relative density 1 (prime-bursts example, Part VI).

> **DEEP REFLECTION lap — 2026-09-16.**  Build 🟢 **9085 jobs**, re-verified.  `src/` = the two
> pre-expedition forbidden-drift `sorry`s; **zero `axiom`s**; **math-axiom count 0** — there is no
> axiom ledger to chip on this project, so the reflection's job is *route*, not debt.
> **ROUTE VERDICT: CONTINUE** — no registered trigger fired.  The named risk is **scope creep**,
> not a false summit: B0–B3 attacked the machine, B4/B5 were growth-class bookkeeping, and a
> working machine always has one more parameter to widen.  So the directive now carries a
> **pre-registered FINISH LINE**: the `a`-side is campaign B's TERMINAL objective.
> **Decisive probe, compiled this lap** (`scratch/ProbeA.lean`): the §4C good-prime contraction
> **survives** the scaled frequency `a_p·q` — `phaseA_eq_sum_local` shows the local phase at `p`
> is the ordinary one at scaled coefficients, and `sum_sq_distZ_coeffA_ge_gen` shows the seed
> `freqSeed bb K` is *unchanged*, the entire cost being one additive `⌈log_bb Ca⌉` on the layer
> budget (`coeffAL` is linear in `q`, and `sum_sq_distZ_freqDepthB_ge` has no box hypothesis at
> all).  So the `a`-side is a two-module port, not a wall.  Architecture call:
> `omegaOnA 1_S s m = omegaOn (s.filter S) m`, so the prime-subset campaign **is** the `a`-side at
> `a = 1_S` — generalize `G4SubsetC*` **in place**, no fifth §4D stack.
> Ledger re-run from real `#print axioms` this lap, every headline row confirmed trust-triple
> clean; no drift found and no correction needed.  See `REFLECTION-2026-09-16-campaignB.md`.

> **Campaign B is CLOSED (2026-09-16, overnight laps).**  The master additive weight is proved
> for **unbounded** coefficients and, simultaneously, on a **divergent prime subset**:
> `isDisjunctive_weight_logLogPow` (`c_p ≤ A₀(1+log₂log₂ p)^s`, any `A₀, s`),
> `isDisjunctive_subsetWeight_logLogPow` and `isDisjunctive_residueClass_weight_logLogPow`,
> all trust-triple clean, with an unwound audit surface in `G4WeightStatement`.  Build 🟢 9084
> jobs; `src/` = the two pre-expedition forbidden-drift `sorry`s, **zero `axiom`s**.  The
> remaining boundary (`c_p ≍ log p`) is a *proved* obstruction of this schedule family, not an
> open lemma: see `DESIGN-2026-09-16-prime-subset.md`.

> **Review lap B-review-1 (2026-09-16).**  **Campaign A is CLOSED.**  All three of its headlines
> are unconditional and trust-triple clean: `isDisjunctive_residueClass` (∑_{p≡a(q)} 1/(bᵖ−1)),
> `isDisjunctive_Omega` (∑ₙ Ω(n)/bⁿ = ∑_{q prime power} 1/(b^q−1)) and
> **`isDisjunctive_weight c C hC`** — *every* bounded coefficient vector, `b ≥ 3`.  The previous
> directive's `e`-schedule ladder landed in full, and so did its item 4.  Directive re-set
> (`DIRECTION.md` → CURRENT DIRECTIVE) to **campaign B: the master additive weight**
> `w(n) = ∑_{p∣n}(a_p + c_p(v_p(n)−1))` with **`c` unbounded**.  Two probe results this lap:
> (a) `TWeight.ovC` is consumed at exactly one site (`summable_corrB`) and *only* for
> summability, so the transport interface is **not** the obstacle — relaxing `ov_le` to a per-`d`
> bound is free; (b) **base 2 stays a machine-checked dead end** — `G4RowMassOptimal`'s
> `two_pow_le_sum_abs` proves every line-sum-annihilating integer array has row-ℓ¹ mass `≥ 2^K`,
> so `rowL1 2 K ≥ 1` for the whole design family, not just our parameters.  The whole
> `C`-dependence of the closed proof sits in exactly two places (`hjunk_holdsCE`'s
> `100000·C·k₄³ ≤ 2^{k₄}` and `hfarC_holdsE` via `w_c ≤ (max C 1)·Ω`); both must become tail
> conditions on `∑_p c_p/p²`.  Build 🟢 9067 jobs; `src/` = the two pre-expedition
> forbidden-drift `sorry`s, **zero `axiom`s**.

> **Review lap A-review-1 (2026-09-16).**  Campaign A (prime-subset Lambert series, operator
> override 2026-09-15 23:58) is the live objective; the R/S deformation campaign is banked.
> In kernel already: Mertens-in-AP (`G4MertensAP`), the subset weight and its closed form
> `∑_n ω_S(n)/bⁿ = ∑_{p∈S} 1/(b^p−1)` (`G4SubsetWeight`), the **entire analytic route A–D made
> weight-generic** (`G4TransportW`, `G4FrameW`, `G4RemainderW`, `G4SubsetJunk`), and the
> conditional headline `isDisjunctive_subsetLambert_of_witness`.  The ONE remaining obligation is
> the `e`-parametrized *schedule witness*: `G4SchedBE` has 12 of the 14 parameter facts and 4 of
> the 6 budget terms; `term_b_leE`/`term_c_leE` → `hbudget_holdsE` → the `e`-assembly with the
> `S`-filtered small primes is the crux ladder to `isDisjunctive_residueClass`.  Directive reset
> to that ladder (`DIRECTION.md` → CURRENT DIRECTIVE).  Build 🟢 9051 jobs; `src/` has exactly the
> two pre-expedition forbidden-drift `sorry`s and **zero `axiom`s**.

> **Review lap 166 (2026-09-15).**  DESIGN §0's **third** untested escape — *giving up the
> single-`n` joint sample* — is closed at the schedule in the new `G4GroupedVerdict.lean`, and
> the design's prose estimate for it is **corrected**.  That estimate (`w ≳ 2 log H / log dmin`,
> "a vanishing fraction of `H`", so `H/w` free blocks) dropped the family factor `|𝓕|`, which at
> the schedule is `(2 dmax+1)^{2E} = dmin^{4E}`.  Putting it back: `grouped_size_cond` gives the
> true threshold `w ≥ 8E + 5`, `grouped_block_count_le` turns it into **`8 K G ≤ K² + 1`** (at
> most `(K²+1)/(8K) ≈ K/8 = 20000` blocks at `i = 0`), and `grouped_balanced_union_le` delivers
> the grouped verdict at the same rate `dmin^{−w/2} ≤ dmin^{−(4E+2)}`.  So the joint sample is
> not sacred, but it may only be cut into `≈ K/8` blocks, each a `1/K` fraction of the atoms;
> confinement is untouched.  Lap 165's stuck-bail is **refused** — it mistook "R's checklist is
> done" for "no work is open".  New objective **S** in `DIRECTION.md` → CURRENT DIRECTIVE.
> Build 🟢 9041 jobs; all new declarations `[propext, Classical.choice, Quot.sound]`.

> **Laps 146–160 (2026-09-15).**  Objective R's error budget **(E) is proved**, not documented:
> `Budget.RoughRowVarianceLower` — the one hypothesis the deformation verdict rested on — now
> follows from explicit arithmetic on a CRT progression (`G4RowVariance.roughRowVarianceLower_arith`
> / `_dyadic` / `_mertens`), and `scales_satisfiable` shows its hypotheses are meetable for every
> `K`, `k`, `Q`.  The chain *arithmetic of ω → variance lower bound → capture budget → cancelled
> layers → upper density ≤ dmin^(−H/2)* is machine-checked end to end (`two_layers_of_dyadic`,
> `cancelled_union_le`).  R's other two open items are theorems too
> (`union_le_of_determining`, `grouped_union_le'`), and the refutation of
> "row-balanced ⇒ ignores a coordinate" is a uniform family at every `K ≥ 3`
> (`threshold_exact`).  Build 🟢 9040 jobs; every new declaration axiom-clean.
> No claim about the normality of `G₄`.

> **Lap 127 (2026-09-15).**  The base-`2^k` directive's **step 3 is refuted** (E-T13 fired) —
> see `ROUTE-ESCALATION-2026-09-15-base2k-step3.md`.  Steps 1–2 and the whole residue counting
> layer are proved and kept (`G4EntropyResidue`, `G4EntropySubLaw`, `G4EntropyResRead`).
> The successor is elementary and its heart is in kernel:
> `NormalNumbers.BlockRigidity.Sys.eq_uniform` + `NormalNumbers/PowerBaseCount.lean` give the
> route to `IsNormal b y → IsNormal (b^K) y`, hence `IsNormal 4 fullRealW`, with no measure
> theory, no Wall and no Fourier.  Build 🟢 9030 jobs.  See
> `HANDOFF-2026-09-15-entropy-lap127.md`.

## Attended update, 2026-09-13: Stoneham base-6 disjunctivity proved

Every finite base-6 word occurs arbitrarily late in `stoneham23`:
`stoneham_base6_interval_recurrence` and `isDisjunctive_six_stoneham23`, in
`StonehamBoundary.lean`.  The fixed-boundary congruence route is complete at
`f1f9749`; frozen statements unchanged, host build and transitive dependency
checks passed.  Fable/low finished in lap 1; the bounded campaign is stopped.
No literature novelty claim, no normality claim in base 6, and no ln-2 result.

The parallel theta investigation produced an exact low-precision seed
permutation and a counterexample to inferring short-block cancellation from
such information; `experiments/theta_seed_precision.py` is its exact probe.
ROADMAP also corrects the old open label for `sum 1/(9^k 2^(2^k))` using
Vandehey's later normality theorem.  No second normality campaign was launched.

The September 8 and 13 snapshots below are historical; the live campaign is G4.

**A machine-checked conjecture graph around normality/disjunctivity, plus a
sorry-free proof wing (Becher–Yuhjtman, image-Khinchin, the adder tower, the
Mahler multiplier chapter) — and the G4 disjunctivity theorem, proved and
kernel-verified 2026-09-14; the live campaign is now its base-`b` generalization.**
· **Build**: 🟢 green (9085 jobs) ·
**Updated**: **DEEP REFLECTION lap** · 2026-09-16 · `wip/g5-prime-subset` @ `36c02ca`+

## 🏁 2026-09-15 (entropy **lap 126**): **`IsNormal 2 fullRealW` — THE EXPEDITION'S ENDPOINT, PROVED AND AXIOM-CLEAN**

**Build** 🟢 9024 jobs.  `src/` carries exactly **two** `sorry`s, both pre-expedition and off-path
(`PrimeLambertOscillation.phaseOscillation`, `MahlerDriftOne.exists_drift_one_background`); the
entropy expedition's part of `src/` is **sorry-free**.

> **`G4.Sched.isNormal_fullRealW : IsNormal 2 fullRealW`** — `[propext, Classical.choice, Quot.sound]`.

`fullRealW = realOfDigits 2 (fullDigW (primeLambertAtBase 4))`: the real whose `j`-th **binary**
digit is `G₄`'s `fullPosW j`-th binary digit.  `fullPosW` is `StrictMono` (`fullPosW_strictMono`)
and takes **no real argument at all** — the machine-checkable form of "schedule only".  The
unwound audit statement is `isNormal_two_of_schedule_read` (`G4EntropyWStatement`):

> `∃ p, StrictMono p ∧ (∀ j, digitOf 2 fullRealW j = digitOf 2 (Int.fract G₄) (p j)) ∧ IsNormal 2 fullRealW`

with `digitOf_fullRealW` as the faithfulness step (`fullRealW`'s **own** expansion is the read,
not merely a number assembled from those digits).  Corollaries: `isDisjunctive_fullRealW`,
`irrational_fullRealW`.

**What closed it.**  Lap 122's steps 1–3 landed in laps 123–125 (`G4EntropyWPrefix`, the sandwich
and `abs_prefix_ratio_sub_le_cap`, `head_frac_tiny` on the new `P₀` lower bound).  This lap's
step 4:

* **`kk_mul_KK_le_fTW`** — `head_frac_tiny` at `a = 1`: *one read window is a `1/KK` fraction of
  the history before it*.  This one fact pays for the ungated head, the partial window and the
  `a = 0` stub, none of which then needs a certificate.
* **The threshold `a` vs `⌊√(KK j)⌋`** — a *fixed* split cannot work (at `a = 1` the certified
  branch's leftover `2·kk/s` is `O(1)`), so the branches are balanced at `2/√K` each.
* `mediant_abs_le` (deviations of history and increment simply add), `incr_bounds`,
  `mid_assemble_gated`/`_trivial`, 🎯 **`abs_ratio_mid_le`**, `tendsto_midErrW`,
  `tendsto_fgrpW_atTop`, `tendsto_winCount_fullDigW`, `isNormalSequence_fullDigW`,
  `properDigits_fullDigW`.

`exists_matchesAt_fullDigW` needed no separate non-vacuity witness after all: once the frequency
limit holds at every `n`, the limit `2^{−|v|} > 0` forces `winCount v n > 0` directly.

## 🧭 2026-09-15 (entropy **review lap 126, opening**): the mid-band estimate is COMPLETE; only the squeeze and the endpoint remain

**Build** 🟢 9021 jobs · `src/` carries exactly **two** `sorry`s, both pre-expedition and off-path ·
`tendsto_fullWRead_freq`, `fullPosW_strictMono`, `abs_prefix_ratio_sub_le_cap`, `head_frac_tiny`,
`fullW_prefix_winCount_bounds`, `aLe_fnthW`, `aLe_le_headW` all print the trust triple.

Lap 122's mandated steps 1–3 all landed in laps 123–125:

* **`G4EntropyWPrefix`** — the prefix read count (`startsLe`, `aLe`, the order-isomorphism
  `image (fnthW i) (range (aLe i c)) = startsLe i c`, `fullGoodWPre`,
  `fullW_prefix_winCount_bounds`).
* **The sandwich, THE CRUX** — `pairsLe i c` bracketed by two honest truncations
  `bandWtr i X₁ ×ˢ univ ⊆ pairsLe i c ⊆ bandWtr i X₂ ×ˢ univ` with `X₂/X₁ = 1 + O(1/K)`, then
  **`abs_prefix_ratio_sub_le_cap`**: the mid-band word frequency at *every* cutoff above the gate,
  with **no upper hypothesis** — the top-`O(1/K)` failure the route trigger E-T11 anticipated was
  absorbed by capping both flanks at the tile top (`cutBot`/`cutTop`, `card_flank_ratio_cap`).
* **`head_frac_tiny`** — the ungated head, on the new **lower** bound for `P₀`
  (`G4GridP0Lower.P₀_growth`, from counting `Q`-separated *pairs* of same-layer atoms;
  the `Mprod` and primorial routes are refuted by a log count and must not be retried).

> **What is left is exactly one thing**: the monotone **squeeze** — the mediant lemma, the
> band-`i` increment at an arbitrary read index `n` (gated branch via
> `aLe_fnthW` + `abs_prefix_ratio_sub_le_cap`, ungated branch via `aLe_le_headW` + `head_frac_tiny`),
> the limit at `i = fgrpW n`, and then `IsNormalSequence 2 (fullDigW …)` → **`IsNormal 2 fullRealW`**.

## 🧭 2026-09-15 (entropy **review lap 122**): the ladder's four steps are DONE; the last obligation is MID-BAND PREFIX CONTROL

**Build** 🟢 9012 jobs · `src/` carries exactly **two** `sorry`s, both pre-expedition and
off-path (`PrimeLambertOscillation.phaseOscillation`, `MahlerDriftOne.exists_drift_one_background`);
the expedition's part of `src/` is **sorry-free** · `tendsto_fullWRead_freq`,
`fullPosW_strictMono`, `entropy_E1_march`, `entropy_E1_tile` all print the trust triple.

Lap 119's mandated four steps all landed: `entropy_E1_march` (the `(K,j)` cone, laps to `3ab6487`),
`entropy_E1_tile` (E1 at **every** outer scale of the tile), `card_bandTtr_ge`, and the read —
rebuilt in laps 120–121 on the **wide band** `bandW i = ` level-`i` sample in
`[wFloor i, wTop i]`, `wTop i = Xlo (KK (i+1))`.  Widening (rather than lowering the floor) is what
drowns band `i+1`'s uncertifiable head in band `i`'s full read.  Endpoint so far:

> **`Sched.tendsto_fullWRead_freq`** — every finite binary word `v` has frequency `2^{−|v|}` in
> `G₄`'s digits read along `fullPosW`, **at the band cutoffs `fTW (i+1)`**; `fullPosW` is
> `StrictMono` and schedule-only.

**The single remaining obligation, and why it is not a corollary.**  `IsNormalSequence 2`
quantifies over *all* `n`.  The read consumes band `i`'s distinct window starts in increasing
order, so a read index cuts the band at a **position** threshold `c`; a start is
`2·kIdx(gridAt i) n α` with `d_α·kIdx ≤ n < d_α·(kIdx+1)`, so `2·kIdx(n,α) ≤ c` means `n ≲ c·d_α/2`
— an **atom-dependent** scale cut, not a truncated sample, so `abs_posAvg_bandWLaw_le` does not
apply verbatim.  The fix, and this lap's course correction:

> `gridOf.mul_d_le_mul_d` (`K·d_β ≤ (K+1)·d_α`) and `kIdx_cross` bracket the consumed pair set
> between two honest truncations, `bandWtr i X₁ ×ˢ univ ⊆ pairsLe i c ⊆ bandWtr i X₂ ×ˢ univ`
> with `X₂/X₁ ≤ (K+1)/K·(1+2/c)`.  The sandwich costs a **relative `O(1/K)`** against a capture
> error already `O(K^{−1/4})`.

Four ordered items follow in `PENDING_WORK.md`: the prefix read count (mechanical), the sandwich
(the crux), `head_frac_tiny` for cutoffs below the gate, and the monotone squeeze to
`IsNormal 2 fullRealW`.

## 🧭 2026-09-14 (entropy **review lap 119**): the scale gap is an ARTIFACT — the two-dimensional ladder

**Build** 🟢 9004 jobs · one named `sorry` in `src/` on the active decomposition
(`Sched.entropy_E1_march`), plus the one carried leaf `Sched.card_bandTtr_ge` · every new
sorry-free endpoint `[propext, Classical.choice, Quot.sound]`.

What blocked `IsNormal 2 fullReal` was the **head of each band**: position cutoffs below the
certificate floor `Xlo (KK i)`, which `G4EntropyScaleGap` showed no rung of the ladder covers
(`Xhi K k₄ + 1 < Xlo (K+4)`, a tower separation).  This lap's source audit of every `m`/`m₁`
-sensitive hypothesis in `entropy_E0`'s cone found that **the gap is an artifact of pinning `m`
to `K`**, not a property of the entropy method:

> `m₁` is the small-prime cutoff exponent (`R = 2^{2^{m₁}}`), and the cone constrains it **only
> from below** — except for two ceilings with astronomical slack.  Raising `m₁` by one at fixed
> `K` (keeping `m₂ = 8K²`, so `dyadic_factor_le` is literally unchanged) **squares `Y`**, hence
> `Xlom K (j+1) = Y_{j+1}^{50} = Y_j^{100} = Xm K j`: the certified windows `[Y^{50}, Y^{100}]`
> **tile contiguously**.

`G4EntropyMTower.lean` (new) carries the arithmetic spine, all of it proved:

```
mm₁ K j = m₁ K + j,  mm K j = m K + j,  Rm/Ym/Xm/Xlom/Mcm       the marched scales
Xlom_succ              Xlom K (j+1) = Xm K j          THE TILING IDENTITY
jstar K = m (K+4) − m K − 1
Xm_jstar               Xm K (jstar K) = Xlo (K+4)     the march reaches the next rung EXACTLY
Mcm_le_two_pow_m₂      Mc ≤ 2^{m₂} on the whole march   (binding: 6K² + 31K + 81 ≤ 8K²)
four_mul_le_four_pow_N_m   the `hfar` ℕ inequality on the whole march
exists_tile            every X' ∈ [Xlo K, Xlo (K+4)] lies in one certified window
entropy_E1_march_zero  the j = 0 instance IS `entropy_E1_down`  (definitions line up)
entropy_E1_tile        E1 at EVERY outer scale in [Xlo K, Xlo (K+4)] — the gap closed
```

`entropy_E1_tile` is gated on the single named leaf **`entropy_E1_march`** (the E1 chain at the
marched parameters), whose port is the same "verbatim copy + substitution" shape
`G4EntropyE0Down`/`G4EntropyE1Down` already ran twice for `X'`.  Why A0's NO does **not** apply:
A0 raised `X` with `Y, R, Mc` fixed, so `log Mx / log Y` grew past its ceiling `Y^{2^{3K/4}}`;
the march raises all of them together, keeping `X = Y^{100}` and that ratio pinned at `≤ 101`.

Consequence for the wall: `certified_granule_exceeds_previous_scale` and
`ScheduleWitness.X_lt_Xlo_step` stay true — they are statements about the **one-dimensional**
ladder — but they no longer bound what this mechanism can prove.

## 🧭 2026-09-14 (entropy laps 93–117): `Q ∣ P₀`, and a **schedule-only** strictly increasing read

**Build** 🟢 8995 jobs · sorry-free · every endpoint `[propext, Classical.choice, Quot.sound]`.

> **`Sched.tendsto_fullRead_freq`** — for every finite binary word `v`,
> `winCount (fullDig G₄) v (fT (i+1)) / fT (i+1) → 2^{−|v|}`, with
> **`Sched.fullPos_strictMono`**; `fullPos` is defined from the **base-four schedule alone**.

The lap-51 objective's *x-freeness* and `E-T8`'s *strict monotonicity* at once.  Packaged as
`fullReal`, `isDisjunctive_fullReal`, `irrational_fullReal`.

**The enabling discovery** (`G4EntropyWindows`, lap 95): `shiftG_eq` makes two different atoms'
shifts congruent mod `Q` at the same layer, and `freezeQ` contains their distance — so
**`Q ∣ P₀`**, every orbit index of every atom at every sample time is congruent mod `Q`, and
`Q = (U+K+N+2)!` dwarfs `m_K`.  Hence **`windows_eq_or_disjoint`**: any two sampled windows
coincide or are disjoint.  The read can then take the *whole* sample's windows in a band.

Supporting: `bandT` (an `n`-only band threshold, so the restriction is a pure sample-time
restriction), `H₂_bandTLaw_ge`/`abs_posAvg_bandTLaw_le` (the restricted *joint* law stays
certified), the multiplicity bridge (`shared_idx_apart` … `overhang_frac_le`: reading the
position set rather than the `(n,α)` pairs costs an `8/|Atom|` fraction), and
`read_freq_error_bound` (the assembly done over opaque reals, after three attempts died on
`whnf` timeouts over the closed terms).

Still not normality: the limit over *all* prefix lengths cannot be assembled by concatenating
per-scale certificates, which is what `certified_granule_exceeds_previous_scale` rules out (a
size comparison — see its ⚠️ scope note; it is not a proof that prefix frequencies diverge).

## 🧭 2026-09-14 (entropy laps 61–90): the granularity **wall**, and the band read that saturates it

**Build** 🟢 8993 jobs · every new module sorry-free · every endpoint
`[propext, Classical.choice, Quot.sound]`.

### The wall — normality is closed on this mechanism, with a theorem

`NormalNumbers.G4.Sched.certified_granule_exceeds_previous_scale`
(`G4EntropyMixture.lean`, built on `G4EntropyGranule.granule_exceeds_previous_scale`):

> Any sub-collection of scale `i+1`'s sample times whose derived capture bound is **not vacuous**
> already reads more digits than scale `i` produced in total:
> `|Atom_i|·|P_{K_i}|·m_i < |S|·m_{i+1}`.

So no prefix bound can be **assembled** from a concatenation of per-scale certificates: the
first certified granule of scale `i+1` outweighs everything scale `i` produced.  ⚠️ This is a
**size comparison**, not a proof that prefix frequencies diverge (attended review 2026-09-14);
"closed on this mechanism" = closed for deduction from the fixed sampled data alone, not for
every arithmetic extension.  The cause is `X(K) = 2^{100·2^{m(K)}}` with `m(K) ≥ K³`, so this
subsumes lap 54's `chunks_insufficient` and is immune to every refinement of the chunking
(including the per-atom certification `card_good_ge` of lap 61, which shrinks the granule to a
single atom).

Supporting: `FinLaw.H₂_mix_le` (mixing costs one bit) and
`H₂_empirical_window_restrict_ge` (restricting the **sample times** costs `(δ+1)/σ`, the dual of
`H₂_restrictCoords_ge`).

### The band read — the strongest object the wall leaves standing

`G4EntropyBandSeq.lean`, `G4EntropyBandPrefix.lean`:

* `bandPos : ℕ → ℕ`, **`bandPos_strictMono`** — a genuine strictly increasing sequence of digit
  positions (`isSampled_bandPos`: all of them sampled, hence density zero).
* **`tendsto_bandRead_freq`** — for every finite binary word `v`,
  `winCount (bandDig G₄) v (bT (i+1)) / bT (i+1) → 2^{−|v|}`.
* `tendsto_midRead_freq`, `abs_midRead_freq_sub_le(′)`, `tendsto_midRead_freq_of_depth` — the
  same limit at every cutoff beyond an initial, relatively vanishing portion of each band.
* `bandReal`, `isDisjunctive_bandReal`, `irrational_bandReal`.

Ingredients: `exists_good_atom`/`tendsto_goodAtom_occursCount` (**one** atom per scale carries
every word at its correct density — the average over `(K²+1)^K` atoms is not needed),
`window_gap_same_atom` (one atom's windows are pairwise disjoint, with a full window's margin),
`band_gap` (the scales can be read in ordered bands), `abs_posAvg_bandLaw_le` (the band
restriction keeps the certification).

⚠️ **Not a density-one statement.**  The bad initial portion of band `i` dwarfs every cutoff
below it, so the bad set has lower density `0` and upper density `1`.  That is the wall seen
from the cutoff side, and is exactly why this is not normality.  Nothing here is a claim about
the normality of `G₄`.

## 🧭 2026-09-14 (entropy laps 52–55): the lap-51 objective is **PROVED**, and its named successor E-T8 is **refuted as a route**

**The headline** (`src/NormalNumbers/G4EntropyBlockWord.lean`, all
`[propext, Classical.choice, Quot.sound]`):

* `samplePos : ℕ → ℕ` — defined from the base-four schedule alone; no real appears in its body.
* `samplePos_spec` — every value is a genuine sampled position `2·kIdx(n,α) + p`, `n ∈ P_i`,
  `p < m_i`.
* **`isNormalSequence_digits_along_samplePos`** —
  `IsNormalSequence 2 (fun j => digitOf 2 (Int.fract G₄) (samplePos j))`.
* `isNormal_realOfDigits_samplePos`, `isDisjunctive_sampleReal`, `irrational_sampleReal`.

Route: rung 1 `G4EntropyOcc` (window counting), rung 2 `G4EntropyBlockWord`
(`cyc_bounds`, `tendsto_cyc_div_blen`: the scale-`i` block's cyclic window frequency → `2^{−|v|}`,
out of `tendsto_occursCountP_primeLambertFour`), rung 3 `G4EntropyConcat` (a normal real from any
family of finite blocks with converging window frequencies — **no growth hypothesis**).

**This is not a claim about the normality of `G₄`.**  The number is built *from* `G₄`'s digits
along a density-zero position sequence and is not `G₄`; `G₄`'s own normality stays closed on this
mechanism (lap 37).

**E-T8** (upgrade `samplePos` to strictly increasing — a genuine subsequence) is **refuted as a
route**, in `src/NormalNumbers/G4EntropySubsample.lean`:
`FinLaw.H₂_restrictCoords_ge` and `abs_posAvg_restrict_sub_le` show a sub-collection of relative
size `ρ` costs `√(1/ρ)`, certifiable only while `ρ ≫ δ/m`; `card_Atom_growth` and
**`chunks_insufficient`** (`kk i/(50√(KK i)) < |Atom_{i+1}|/|Atom_i|`) show a scale never admits
as many certifiable chunks as the block-length growth demands.  The barrier is
dimension-independent (window truncation is `lowTuple`'s dual), so chunking the sample times
instead of the atoms does not escape it.  It refutes the route, not the existence of such a
sequence.

## 🧭 2026-09-14 (entropy review lap 51): the frequency ladder is COMPLETE and BOUNDED; new objective = an explicit NORMAL NUMBER from `G₄`'s sampled digits

**Where it stands.**  The lap-37 objective — the joint (`t`-wise) sampled-word frequency theorem —
was met and then pushed to its boundary.  Laps 38–45 built it; lap 47
(`tendsto_occursCountJointFree_primeLambertFour`) freed the positions to *every* vector in
`[0, m_K−ℓ+1)^t` with no alignment, at `≤ 2t√(1600 log2 · ℓt/√K)`; lap 48
(`no_pointwise_bound_from_deficit`) proved the averaging is **necessary** — a law with a deficit of
one bit per window still has a probability-zero pattern at a fixed position vector, so no `o(1)`
pointwise bound can follow from the deficit premise.  Laps 49–50 opened a second, non-frequency
line: per-block joint **richness** (`joint_richness_primeLambertFour` — for at least half the
blocks the `t` sampled windows take `≥ 2^{t·m_K − 200t√K}` distinct joint values, shortfall rate
`800/√K → 0`).  Build 🟢 8979 jobs; every headline prints the trust triple.

**What this review changed.**  Every endpoint of laps 31–50 is a statistic *at scale `i`, with
`i → ∞`* — a sequence of finite statements, never one infinite object.  The repo already owns both
pieces that close that gap: `Bridge.isNormal_realOfDigits` and the `countOccurrences` concatenation
calculus (`CFChainFreq.countOccurrences_append_addslack₂` — additive seam, no shortness
requirement), while `tendsto_occursCountP_primeLambertFour` supplies exactly the block frequency a
concatenation argument consumes.  So the new objective is the expedition's **first infinite
object**: an `x`-independent map `samplePos : ℕ → ℕ`, built from the schedule alone, with
`IsNormalSequence 2 (fun j => digitOf 2 (Int.fract G₄) (samplePos j))` — hence a normal real read
off `G₄`'s binary digits along an arithmetic schedule.  Strictly stronger than every `i → ∞`
statement (those are its input) and stated in the vocabulary `isDisjunctive_two`/`IsNormal` use.
**It is not a claim about the normality of `G₄`**, which stays closed on this mechanism (lap 37).

## 🧭 2026-09-14 (entropy DEEP REFLECTION lap 37): normality on this mechanism is CLOSED — and MEASURED

**Where it stands.**  Brief §8 is satisfied and the expedition's negative is now *quantitative*.
`entropy_E0`/`entropy_E1` are unconditional, axiom-clean theorems about the implemented base-four
schedule; `T_E`/`T_S`/`T_mix` are refuted with witnesses meeting their exact premises; §5's positive
answer is proved and rendered on real digits (`tendsto_occursCountT_primeLambertFour`, over the very
`OccursAt 2 · v ·` predicate `isDisjunctive_two` uses); and laps 34–36 added the matching spectral
lower bound (the `√K` deficit is a property of the object) and the all-positions capacity bound.

**Binary normality of `G₄` is closed on this mechanism, by theorem.**  `qForces_normal_iff_density_one`
requires a read set of density **one**; `G4EntropyScales.sum_weight_le` gives **every** admissible
family of grids over **every** set of scales a read set of density `≤ 1/8`.  The gap is not a
constant: `key_size`'s own proof yields `Q·D₀ ≥ K·B^{2K}` against `H_K·m_K ≤ (2(K²+1))^K·K`, so the
sampled density is `≤ ½(3/K⁴)^K`, while `entropy_cover_bound` pins the window at exactly `m_K = K/4`
(it needs both `m ≤ K/4` and `η⁴ ≤ 2^{−K}`).  Reading density `≥ 1/2` would take a window `≈ K^{4K}`
times longer.  The structural cause is one `GridParams` field — `hQdvd : ∀ m ≤ U, m ∣ Q`, so
`Q ≥ lcm(1,…,U)` with `U ≥ B^K`.  Three escapes (varying the frozen residue, shifting the real
`x ↦ 2^σ x`, using more scales) are each closed by something already proved; see
`REFLECTION-2026-09-14-entropy.md` §1 so they are not re-derived.

**The new objective** (`DIRECTION.md` CURRENT DIRECTIVE, reflection lap 37): the **joint (`t`-wise)
sampled-word frequency theorem** — `entropy_E1` bounds the law of the *whole vector*, and every
result so far has projected it to one coordinate.  Used jointly it says the sampled windows of `G₄`
are asymptotically **independent** and uniform: for all words `w₁,…,w_t` of length `ℓ`, the frequency
of *"`G₄`'s block at `2·kIdx(n,α_s)+p_s` spells `w_s` simultaneously"* tends to `2^{−tℓ}`.

## 🧭 2026-09-14 (entropy review lap 23): §6 CLOSED as a characterization; §5's negative CORRECTED

**Where it stands.**  The entropy expedition's brief-§8 outcome is met and then some.  `entropy_E0`
and `entropy_E1` are unconditional, axiom-clean theorems about the *implemented* base-four
schedule.  Brief §6's transfers `T_E`, `T_S`, `T_mix` are **refuted** with witnesses meeting their
exact premises (laps 8–9), and its positive branch is now **closed as a characterization**
(laps 16–22): a quantized or digit-local sampler forces normality **iff** it reads a density-one
set of digit positions — and this schedule reads at most `1/4` of every prefix at any budgeted
quantization level, because the freezing modulus `Q_K·D₀_K` dwarfs the alphabet.  A single
*unquantized* orbit value would suffice (lap 19); the sample determines none (lap 21).

**The finding of this review lap.**  Lap 15 recorded §5 as answered *negatively* — "entropy rate
`→ 1` controls no sampled frequency at any word length".  What `entropy_rate_not_control_bit`
actually proves is that it controls no frequency **at a fixed offset inside the window** (uniform
on the leading-bit-zero half has rate `(m−1)/m` and kills the leading bit).  Normality counts a
word's occurrences **averaged over the offsets**, and on lap 15's own witness that averaged
1-frequency is `(m−1)/(2m) → 1/2`.  Entropy *does* control the averaged frequency.  §5's real
answer is therefore **positive and unproved**, and it is the new objective: turn `entropy_E1` into
a genuine frequency theorem about `G₄`'s binary digits at the sampled positions
(`DIRECTION.md` CURRENT DIRECTIVE, review lap 23).

## 🔬 2026-09-14 (entropy expedition, laps 1–7): the SAMPLE-ENTROPY theorems E0 and E1

The live campaign is the attended **entropy expedition** (`BRIEF-entropy-expedition-2026-09-14.md`,
`DIRECTION.md` override + entropy CURRENT DIRECTIVE), branch `wip/g4-entropy`.  Fix `x = G₄` and
read its *binary* digits through the implemented base-four schedule.  Ten new `G4Entropy*`
modules, all `sorry`-free, no new axioms, no pre-expedition file edited:

```
Sched.entropy_E0 : K = 4k₄ → 33856 ≤ K → (1/5)·k₄·(K²+1)^K < (jointLaw …).H₂
Sched.entropy_E1 : K = 4k₄ → 160000 ≤ K → k₄·(K²+1)^K − 50·√K·(K²+1)^K < (jointLaw …).H₂
```

`jointLaw` is the law of the **whole vector** `Z^x_K = (⌊2^{m_K}{4^{k_{K,α}(n)}x}⌋)_{α}` under
*one* uniform `n ∈ P_K`; `m_K = K/4`, `H_K = (K²+1)^K`.  E1 is the brief's quantitative target
with `C = 50`, and dividing by `m_K H_K` gives `H₂/(m_K H_K) ≥ 1 − 200/√K → 1`, the qualitative
E0.  Both print the trust triple.  The mechanism: an *entropy* deficit replaces the covering
deficit of an omitted word (E0 has no omitted word), and the four schedule allowances were
re-closed exponentially small (`hbig_small`, `hfar_small`, `jackson_term_small`,
`smallPrime_term_tiny`, new Jackson degree `DjE = (16K²2^{m_K})²`).

**Lap 8 settled the bridge: `T_E` is FALSE** (`NormalNumbers.G4.Sched.not_T_E`, axiom-clean).
The sample is digit-local and reads a set of digit positions of density `≤ 1/4`, so the witness
`maskedReal G₄` (G₄'s digits at the sampled positions, `0` elsewhere) satisfies `entropy_E0`
and `entropy_E1` verbatim yet is not normal.  `E0` also became a genuine limit for `G₄`
(`E0_primeLambertFour`).  The frontier is now brief §6's positive branch: which arithmetic
input reads a *positive-density* set of positions.

**This is not normality and does not claim it.**  It is an unconditional statement about the
quantized arithmetic sample.  The bridge to ordinary digit frequencies is brief §6's transfer
`T_E`, and settling it is the whole objective of the next laps — see the entropy CURRENT
DIRECTIVE.  Review lap 8's finding: the sample is **digit-local** (`ZSample_eq_blockVal`), so
`T_E` forces the sampled position set `S = ⋃_K S_K` to have lower density ≥ 1/2, while
`kIdx_spec`'s `d_α ∣ kIdx` confines `S_K` to multiples of `2d_α` with `d_α ≥ 1 + Q_K·D₀_K`
and `Q_K = (U+K+N+2)!`.  That points hard at `T_E` being **false**, with an explicit witness.

## 2026-09-14 (review lap 16): the headline's corollaries — IRRATIONALITY — and base two RETIRED

`IsDisjunctive.irrational` (`DisjunctiveCorollaries.lean`): a rational `a/q` has
`q·orbit b x n ∈ ℤ`, so its orbit misses `[1/(2|q|), 1/|q|)`.  Hence, axiom-clean and
unconditional, **`G4.irrational_primeSum : 3 ≤ b → Irrational (∑' p : Nat.Primes, 1/(bᵖ−1))`**
— an independent, machine-checked proof of the `b ≥ 3` half of the prime-Lambert
irrationality family (Tao–Teräväinen arXiv 2512.01739 Thm 1.3 is the base-two case), by a
different route, and strictly stronger for those bases.  Also `IsDisjunctive.exists_ge` (every
interval is hit *arbitrarily late* — cut it into `N+1` pieces, the hitting times are distinct)
and hence `every_word_occurs_base_late`: every finite base-`b` word occurs infinitely often.

**Base two is RETIRED, not deferred.**  Lap 13 refuted the parameter choice (`rowL1 2 K = 1`);
this lap refutes the design family: killing a layer costs one tensor coordinate, and any
nonzero integer array with vanishing line sums in `K` directions has `L¹ ≥ 2^K`, so
`rowL1 ≥ 2^K b^{−K}/(b−1) ≥ 1` at `b = 2` for *every* such design — the cost of killing a
layer exactly cancels its gain.  And no re-tuning of `Y` escapes: the medium range needs
`Y ≲ √X` while a non-cancelling far range needs `Y ≥ X^{1−o(1)}`.  The only repair is signed
cancellation for `p > Y` — the deep two-point correlation input the brief forbids inheriting.
New campaign (G5): make the arithmetic input an interface, instances `ω` and `Ω`.

## 🏁 2026-09-14 (lap 14): G4B PROVED — `IsDisjunctive b (primeLambertAtBase b)` for every `b ≥ 3`

`NormalNumbers.G4.isDisjunctive_base` (`G4SchedBAssembly.lean`): for every integer `b ≥ 3`,
`∑_n ω(n)/bⁿ = ∑_p 1/(bᵖ−1)` (`isDisjunctive_primeSum`) is disjunctive in base `b`; every
finite base-`b` word occurs (`every_word_occurs_base`); and `∑ ω(n)/(cᵏ)ⁿ` is disjunctive in
base `c` for `cᵏ ≥ 3` (`isDisjunctive_root`).  `#print axioms = [propext, Classical.choice,
Quot.sound]`, no `sorry`, no `native_decide`.  The base-four theorem is re-derived as the
instance `isDisjunctive_four'`.  The whole §4 layer is base-general (`gridFrame bb`, the
named masses `rowL1 b K = (2/b)^K/(b−1)`, `rowL2`, `farBound`, the seed
`freqSeed b K = b^{−4}(2/b²)^K`), and the §5 schedule `SchedB` runs in `(b, K)` under
`3 ≤ b`, `2b² ≤ K`, `K ≥ 100`, with `hbig`/`hfar` settled at the worst case `b = 3`.
Base two stays refuted on this route (`rowL1 2 K = 1`).  Handoff:
`HANDOFF-2026-09-14-g4-lap14.md`.

## 2026-09-14 (review lap 13): G4 base-four INDEPENDENTLY VERIFIED; campaign advances to base `b ≥ 3`

Re-ran the whole audit from scratch: `lake build` 8930 jobs green; `isDisjunctive_four`,
`isDisjunctive_two`, `G4DisjunctiveFour_holds`, `G4DisjunctiveTwo_holds`,
`every_binary_word_occurs`, `primeSumAtBase_four`, `summable_omegaR_div_pow` each print
`[propext, Classical.choice, Quot.sound]`; `grep` finds **no `axiom` declaration anywhere in
`src/`**; and the endpoint's *definitions* (`IsDisjunctive`, `orbit`, `omegaR`,
`primeLambertAtBase`, `primeSumAtBase`, `OccursAt`) were re-read line-by-line against the
brief's frozen statement and are faithful.  Since the kernel guarantees the proof given the
definitions, and the definitions match the brief, **the base-four result stands**.

New campaign **G4B** (brief §7.1): `IsDisjunctive b (primeLambertAtBase b)` for every `b ≥ 3`.
Decisive symbolic probe run before any code — the five `ScheduleWitness` inequalities
re-derived in `b`.  `hB` gets easier (deficit `K log2·b^{−ℓ}/(4ℓ log b)`, vs `K·4^{−ℓ}/(8ℓ)`
at `b = 4`); `θ₀(b) = b^{−4}(2/b²)^K` gets larger; but `hbig`'s very-large-prime term is
`(log Mx/log Y)·(2/b)^K/(b−1)`, which at **`b = 2` is identically `1`** — so `hbig` is FALSE
at base two for every `η, ε, K, X`.  That is a genuine refutation of the base-two route (not
a stalled proof) and it explains the brief's own `b ≥ 3`.  Details: `DIRECTION.md` CURRENT
DIRECTIVE, `PENDING_WORK.md` §G4B.

## 🏁 2026-09-14: G4 disjunctivity PROVED (base four and base two), axiom-clean

`NormalNumbers.G4.isDisjunctive_four : IsDisjunctive 4 primeLambertFour` and
`isDisjunctive_two : IsDisjunctive 2 primeLambertFour` (`G4ScheduleAssembly.lean`), for the
constant `primeLambertFour = ∑' n, ω(n)/4ⁿ = ∑_p 1/(4ᵖ−1)` (`primeSumAtBase_four`).
Corollaries `every_binary_word_occurs`, `every_quaternary_word_occurs`.  Every one prints
`[propext, Classical.choice, Quot.sound]`; no `sorry`, no `native_decide`, no local axiom in
the dependency cone.  The whole brief §4–§5 candidate argument is machine-checked.  Handoff:
`HANDOFF-2026-09-14-g4-lap12.md`.


## Where it stands

**Live (2026-09-16, DEEP REFLECTION lap).**  The G4 disjunctivity machine's theorem now reads:
for `b ≥ 3` and a weight `w(n) = ∑_{p∣n}(a_p + c_p(v_p(n)−1))` with `c` in the polylog class
`c_p ≤ A₀(1+log₂log₂p)^s`, optionally restricted to any prime set with a Mertens rate,
`∑_n w(n)/bⁿ` is disjunctive — proved for `a ∈ {1, 1_S}`, unconditional, trust-triple clean,
with an unwound audit surface (`G4WeightStatement`).  **The one remaining axis is a general
bounded `a`**, and it is campaign B's *terminal* objective: a pre-registered finish line now sits
in `DIRECTION.md`, because a machine that works always has one more parameter to widen and the
marginal content of a widening lap goes to zero.  This lap's probe settled the `a`-side's
feasibility in the affirmative — §4C's good-prime contraction survives the scaled frequency
`a_p·q` with the frequency-separation seed **unchanged**, the whole cost being one additive
`⌈log_bb Ca⌉` on the layer budget.  Two upgrades that sound natural are *machine-checked dead
ends of this mechanism and are not targets*: base 2 (`one_le_rowMass_two` — every design in the
family has row mass `≥ 1`, while §4D needs `< 1`) and normality rather than disjunctivity
(`qForces_normal_iff_density_one`).

**The attended campaign is CLOSED.**  `G₄ = ∑_p 1/(4ᵖ−1) = ∑_n ω(n)/4ⁿ` is disjunctive in
base four and in base two (`G4.isDisjunctive_four`, `isDisjunctive_two`), and the whole brief
§4–§5 argument generalises: `G4.isDisjunctive_base : 3 ≤ b → IsDisjunctive b
(primeLambertAtBase b)` for every integer `b ≥ 3` (brief §7 follow-on item 1).  Every one of
those prints `[propext, Classical.choice, Quot.sound]`; `src/` contains **no `axiom`
declaration at all**, and no G4/G4B file carries a `sorry`.  As of review lap 16 the digit
theorem also yields its number-theoretic corollaries: `irrational_primeSum` (`∑_p 1/(bᵖ−1)`
is irrational for `b ≥ 3`) and `every_word_occurs_base_late` (every word, arbitrarily late).

**Live campaign: the attended ENTROPY EXPEDITION** (branch `wip/g4-entropy`; it supersedes
G5 for this run).  Brief §2–§6 are **all closed** as of lap 36: `Sched.entropy_E0` /
`Sched.entropy_E1` are unconditional, axiom-clean theorems about the joint quantized sample of
G₄; the §6 transfers `T_E`/`T_S`/`T_mix` are **refuted** with witnesses meeting their exact
premises, and the positive branch is closed as a *characterization* — a quantized/digit-local
sampler forces normality **iff** it reads a density-one set of positions, which no admissible
family over any set of scales does (`sum_weight_le`).  §5's positive answer is proved and
rendered on real digits.  **Normality of `G₄` is therefore closed on this mechanism, by theorem
and quantitatively** (lap 37: density `≤ ½(3/K⁴)^K` against a required window `≈ K^{4K}·m_K`).
The live objective is now the **joint (`t`-wise)** sampled-word frequency theorem — the first
statement that consumes `entropy_E1`'s joint hypothesis as a joint hypothesis.

**Base two (the number `∑_p 1/(2ᵖ−1)` itself) is refuted on this route and retired** — see the
lap-16 entry above and `DIRECTION.md`.  It remains a theorem of Tao–Teräväinen, not of this
repo; `PrimeLambertOscillation.phaseOscillation` is the honestly-disclosed hole of the old
base-two attempt and is not a prerequisite for anything proved here.

**Live campaign G5** (`DIRECTION.md` CURRENT DIRECTIVE, *past* the attended brief's finish
line — first thing to re-authorise when Trevor returns): replace the arithmetic input `ω` by
a named interface and prove the theorem for a class of additive weights, with two instances —
`ω` (re-deriving `isDisjunctive_base`) and `Ω`, giving the new constant
`∑_{q = pᵃ} 1/(b^q − 1)`.  The decisive case is C2 (`G4LocalContraction.norm_localSum_le`),
whose local model is `ω`'s indicator `1_{p∣m}` and must become the valuation `v_p(m)`.

**The Mahler-multiplier chapter** (previous campaign, complete): `M(g,k) < g^(k+1)` answers
Berend–Boshernitzan's stated open question, `sup_g M(g,k)/g^(k+1) = 1` is sharp, and at
`k = 1`, prime base, the sandwich is `p²/12 ≤ M(p,1) ≤ p²/4 + O(p)`.  `src/` carries exactly
TWO `sorry`s, both off every unconditional headline and both deep-analytic:
`exists_prime_nonresidue` (`MahlerDriftOne.lean`; a prime `q ∈ (p/3,p/2)` with `(p|q) = −1` —
a character sum over primes in an interval shorter than the reciprocity modulus, i.e.
Burgess/Karatsuba-strength) and `phaseOscillation` (`PrimeLambertOscillation.lean`).

## What's happened (newest first)

- **2026-09-16 (DEEP REFLECTION lap — campaign B closed, `a`-side probed)** — **ROUTE VERDICT:
  CONTINUE**; no registered trigger fired (B-review-1's 🚦 growth-class trigger did not fire —
  `Tame` + `isDisjunctive_weight_logLogPow` landed).  Ground truth re-derived: `lake build` 🟢
  **9085 jobs**, every campaign-B headline re-`#print axioms`-ed to the trust triple, **zero
  `axiom`s** and **math-axiom count 0**, `src/` = the two pre-expedition forbidden-drift `sorry`s.
  **Governance finding**: the risk on this project is not a false summit but **scope creep** —
  B0–B3 attacked the machine, B4/B5 were growth-class bookkeeping and an audit surface, and an
  open-ended generalization ladder emits headlines indefinitely at falling marginal content.  Fix:
  a **pre-registered FINISH LINE** in `DIRECTION.md` making the `a`-side campaign B's terminal
  objective.  **Mathematical finding (the decisive probe, compiled)**: the `a`-side crux *holds* —
  `coeffAL` is linear in the frequency and `sum_sq_distZ_freqDepthB_ge` carries **no box
  hypothesis**, so scaling the local phase by `a_p` leaves the seed `freqSeed bb K` untouched and
  costs only `N ≥ 1 + ⌈log_bb(2^K·Ca·D)⌉`; and `norm_sampleAvg_prod_ee_le` already takes a
  per-prime `LocalPhase` family and per-prime seed, so no new probabilistic layer is needed.
  Architecture call: the prime-subset campaign **is** the `a`-side at `a = 1_S`
  (`omegaOnA 1_S s m = omegaOn (s.filter S) m`), so generalize `G4SubsetC*` *in place* — no fifth
  §4D stack.  (`REFLECTION-2026-09-16-campaignB.md`, `DIRECTION.md` → CURRENT DIRECTIVE.)

- **2026-09-14 (entropy DEEP REFLECTION lap 37)** — **ROUTE VERDICT: CONTINUE** (no registered
  trigger fired; E-T3/E-T4/E-T5 all checked against the laplog and git history).  Inventory from
  ground truth: `lake build` 🟢 **8970 jobs**, every headline re-`#print axioms`-ed to the trust
  triple, no local `axiom` in `src/`, two off-campaign `sorry`s.  **Governance defect found and
  fixed**: the lap-23 objective was met at lap 31 and laps 32–36 then ran five laps with no live
  objective — new trigger **E-T7** forbids a lap that meets the 🎯 from picking its own next
  target.  **Mathematical finding**: normality of `G₄` on this mechanism is closed *and measured*
  — density `≤ ½(3/K⁴)^K` from `key_size`'s own slack, window pinned at `m_K = K/4` by
  `entropy_cover_bound`, gap `≈ K^{4K}`; the structural cause is `GridParams.hQdvd`
  (`Q ≥ lcm(1,…,U)`, `U ≥ B^K`).  Three escapes re-costed and each closed by an existing theorem.
  New objective set: the **joint (`t`-wise) sampled-word frequency theorem**, in three rungs
  (`REFLECTION-2026-09-14-entropy.md`, `DIRECTION.md`).
- **2026-09-14 (entropy laps 34–36)** — the `√K` wall proved **two-sided**
  (`log_det_normalized_two_sided`: `1/300000 ≤ log det(1+T_{K²}^{⊗K})/((K²)^K√K) ≤ log2/√K + 12`),
  so the `ℓ = o(√K)` word-length ceiling is a property of the object, not of the estimate; and the
  capacity bound extended from one aligned tiling to **all window positions**
  (`abs_posAvg_sub_le`, loss-free via `H₂_lowTuple_ge` + `posEquiv`).
- **2026-09-14 (entropy laps 24–33)** — §5 answered positively and rendered on digits:
  `tendsto_occursCountT_primeLambertFour` (every binary word at frequency `2^{−|w|}` among the
  aligned blocks of `G₄`'s sampled windows), `tendsto_blockFreq_of_E0` (the scheme, not `G₄`,
  supplies the implication), the disjoint tiling with zero slack, and the deficit traced to
  `log det(1+T^{⊗K})`.
- **2026-09-14 (entropy review lap 8)** — inventory: build 🟢 8948 jobs, `entropy_E0`,
  `entropy_E1`, `isDisjunctive_four/two/base`, `primeSumAtBase_eq_primeLambertAtBase` all on the
  trust triple; `src/` holds exactly two `sorry`s, both off-campaign and disclosed.  No
  repetition across laps 1–7 (each closed a different brief section), but **crux-neglect did
  apply**: §6 `T_E` was untouched while §4 closed.  Direction REVISED — §5 (S) deprioritized,
  `T_E` promoted to THE objective, with a concrete decomposition (digit-locality lemma →
  sampled-position density → masked witness) written into the entropy CURRENT DIRECTIVE.
- **2026-09-14 (DEEP REFLECTION LAP, after G4 lap 9b)** — **ROUTE VERDICT: CONTINUE;
  brief §4 CLOSED; two recorded §5 parameter values REFUTED.**  Inventory: `lake build`
  green (8888 jobs), zero `sorry`s and zero axioms anywhere in the G4 wing, every G4
  headline on the trust triple, and **all five named §4 inputs now proved about the one
  concrete `gridFrame`**.  Trigger check: G-T1 stays retired, G-T2 and G-T4 did not fire,
  **G-T3 is now live and did NOT fire** — this lap re-derived every `ScheduleWitness`
  inequality from the Lean definitions and they close.  Two corrections to lap 9b's recorded
  paper check, each of which would have sent grind laps at a FALSE inequality:
  (a) `lam = 1` makes `smallPrimeBound`'s third error term `exp(+Θ(TL))`, so `hbudget` is
  unsatisfiable — `lam` must exceed `2e`; `lam = 13/2`, `lam' = e`, `Mc = ⌈10⁴·T·L⌉` works
  (`C > e^{lam}/log(lam/2e)`, minimised `≈ 3690` at `lam ≈ 6.4`).  (b) `N ≈ 10K log K` makes
  `hfar` false — `farC = log((X+Dm)/|P|) + log(log(X+Dm)+1)` has a `log log X = L` term that
  lap 9b dropped, so the retained depth must be the brief's `J = ⌈3 log₂ L⌉`.  New structural
  finding: the §5 schedule squeezes `K` from **both** sides —
  `0.58 log log L ≲ K ≲ log L/(2 log log L)` — the lower edge coming from D's medium range
  (`0.52·8^{−K/2}√(log Mc)` vs `εη`, with `log Mc ≥ log L` forced by C's `R = X^{1/(20Mc)}`).
  With `K` frozen that term diverges, which is precisely the mechanism behind the brief's
  "do not freeze `K`" prohibition.  Mandated next move: **`hB`**, the `X`-free witness
  inequality, with the derived sufficient hypothesis `K ≥ 33856·ℓ²·16^ℓ`.  Trigger G-T5
  registered (re-cost `K = ⌊log log L⌋` if a §5 inequality resists 6 laps).  Also corrected a
  stale STATUS claim: `src/` has TWO disclosed `sorry`s, not one (`phaseOscillation` in the
  old irrationality file was uncounted).

- **2026-09-14 (FRESH-MIND REVIEW LAP #2, after G4 lap 5)** — **Direction KEPT,
  mandated move CHANGED: stop producing inputs, close a named `Prop`.**  Inventory:
  zero `sorry`s and zero axioms in the whole G4 wing, every headline on the trust
  triple — and zero of `PropA`…`PropJackson` discharged after five laps.  Trigger
  **G-T1 retired as satisfied** (C3 is proved: `G4CRTInput.crt_input` plus the
  assembly `G4TransferMoment.norm_sampleAvg_prod_ee_le`; lap 3 eliminated the
  Shiu-type exponential moment entirely by a degree-`M` polynomial bound, so the
  route carries no external sieve dependency).  G-T2/G-T3 have not fired.  New
  trigger **G-T4** covers the abstract-frame ↔ concrete-object seam: a bookkeeping
  mismatch is fixed by one deliberate `G4Wiring` commit; a *mathematical* mismatch
  is an escalation, never a `Prop` edit.  Mandated: `G4Frame.lean` with
  `gridFrame` and the theorems `gridFrame_propA`, `gridFrame_propC`; then **D**,
  Jackson, B assembly, §5 schedule, in that order.

- **2026-09-14 (FRESH-MIND REVIEW LAP, G4 lap 3)** — **Course-correction: the crux
  moved from B to C, and C's arithmetic seed is proved.**  Laps 1–2 put all their
  effort into §4B; a crux-neglect check showed §4C — the half the brief itself says
  is unproved ("the growing-array moment and exponential-moment bounds still need
  proofs"; "the transfer from the independent residue model to the actual progression
  is not automatic independence") — had received zero laps.  This lap attacked it.
  Proved, unconditionally and `#print axioms`-clean: `minWeight_kronPow`, the
  **minimum distance of a product code** (`M` of minimum weight `d` ⟹ `M^{⊗K}` of
  minimum weight `d^K`); `minWeight_diff` (`D_s` has minimum weight 2, via telescoping
  row sums plus injectivity from `det T_s = s+1`); hence `minWeight_tensorDiff`
  (`‖supp(Aᵀq)‖₀ ≥ 2^K`); the column-mass bound `‖Aᵀq‖∞ ≤ 2^K‖q‖∞`; the layer choice
  `freqDepth K w = K+1+⌈log₄|w|⌉` with its window
  `4^{−(K+2)} ≤ |w|4^{−j} ≤ 4^{−(K+1)}`, its retention `j > K`, and its uniform
  admissibility `j_α ≤ K+1+⌈log₄(2^K D)⌉` over the whole Fourier box; and the §4C
  seed **`∑_α dist(w_α4^{−j_α},ℤ)² ≥ 4^{−4}8^{−K}`**.  The two powers are structurally
  distinct — `16^{−K}` is the squared window scale, `2^K` the code distance — so
  weakening the support bound to `2` would destroy the `8^{−K}` that §5 needs against
  `rK`.  Also checked on paper (not yet in Lean) that the §5 schedule is self-consistent
  on all four of the brief's essential comparisons, so the parameter budget is not the
  risk; C3 is.  `DIRECTION.md` CURRENT DIRECTIVE rewritten to G4 with triggers G-T1…G-T3.

- **2026-09-08 (DEEP REFLECTION LAP)** — **The certificate space is mapped; the
  run+jump chain is the route.**  Built an exact combinatorial model of the lower
  side (backgrounds `D`, junction `D → D'` costing `D'(p−D)`, vertex condition
  `−D_prev/D_next ∈ ⟨p⟩ (mod D)`; `M(p,1) =` max-bottleneck closed walk) and
  **checked it against the census**: equal at `p = 13,19,23,29,31`, off by one at
  `7,11,17` (`experiments/mahler_bg_cycle_model.py`).  Three refutations, each
  with a proof and a measurement: (i) orbit-free cycles are impossible — at the
  maximum `D_j` the divisibility forces `λ_j = 1`, the monodromy is parabolic, the
  solution space one-dimensional, so consecutive coprimality pins `D_i = O(1)` and
  the cost to `O(p)`; the `E = 0` column is empty for every prime `7 … 89`; the
  previous lap's `5/27` 3-cycle lead is dead (it exceeds the `3−2√2` cap the same
  argument gives, and its vertex condition fails directly).  (ii) The closed-form
  single-background frame `D = (p+j)/c` caps at **`p²/12` exactly** (`j = 1` is
  degenerate for every `c`, so `cj ≥ 6`) — family II is that frame's optimum.
  (iii) The multi-offset frame caps at `1/5` and has **no** uniform floor.
  **The finding**: the `E ≤ 1` optima all have one shape — the run of consecutive
  integers `p−b … b` plus the jump `b → p−b` — every vertex free except the
  bottom, giving `M(p,1) ≥ b(p−b−1)` whenever `−1 ∈ ⟨p⟩ (mod b)`, `3 ≤ b < p/2`.
  **2512 `(p,b)` pairs checked, zero mismatches**; ratio `≥ 0.1983` for every prime
  `11 … 20000`, median `0.2499`.  `b ∣ p+1` makes the condition free, so
  `b = (p+1)/3` gives `2/9` and `b = (p+1)/4` gives `3/16` — unconditional, and
  together they cover every prime `p ≢ 1 (mod 12)`.

- **2026-09-08 (REVIEW LAP)** — **The factor `3` is a drift, and it is not
  intrinsic.**  Derived and machine-checked the closed form of the one-junction
  certificate: `M ≈ min(p(p−D)/b, p(b−1)D/(b|g|))` with drift
  `g = −b·c₂⁻¹ − p (mod bD)`; drift `1` ⟺ `−1 ∈ ⟨p⟩ (mod D)` (family I's
  hypothesis, now *equivalent* to optimality rather than an artifact of
  `D = (p+3)/2`); a junction scaled by `k` divides `M` by `k` and needs
  `−k ∈ ⟨p⟩ (mod D)` (family II, `k = 3`).  **Refuted**: any closed-form
  background `D = (p+j)/2` caps at `1/3`, since `g ≡ −p (mod b)` is odd for
  `b = 2` and `j = 1` is degenerate.  **Measured** (`mahler_onejunction_scan.py`,
  literal `NumCert.Good` check): with a per-prime `D`, `M/⌊p/2⌋² ≥ 0.881` at
  every prime `17 … 127`.  Next: `MahlerBackgroundCert.lean` (family I with free
  `D, c₀, b`), then the arithmetic crux "∃ `D ∈ (p/3,p/2)` with `−1 ∈ ⟨p⟩`".

- **2026-09-08 (grind laps 2–3, post-reflection)** — **THE RUN+JUMP CHAIN THEOREM.**
  `MahlerRunJump.lean` (the certificate: `Θ(p)` backgrounds `b, b+1, …, p−b`, valid
  for every `M < b(p−b−1)`, via one generic two-denominator edge lemma) and
  `MahlerRunJumpWalk.lean` (the data from `p^f ≡ −1 (mod b)` and `T = 2φ((p−b)!)`,
  the two closed walks, the theorem).  **`mahler_lower_bound_runjump`: for every
  prime `p`, every `3 ≤ b < p/2` with `−1 ∈ ⟨p⟩ (mod b)`, `M(p,1) > b(p−b−1) − 1`.**
  Corollaries: `3 ∣ p+1` ⟹ `M(p,1) > 2(p+1)(p−2)/9 − 1`; `4 ∣ p+1` ⟹
  `M(p,1) > (p+1)(3p−5)/16 − 1`; so **`3/16 · p²` for every prime `p ≢ 1 (mod 12)`**
  (`p ≥ 11`).  Against the exact census the bound is EXACT at `(p,b) = (13,5)`,
  `(23,10)`, `(31,14)` (`M = 35, 120, 224`), and never exceeds `M(p,1)` at any
  admissible pair `p ≤ 31`.  All trust triple, no `sorry`.
  **T3 endpoint (stated per the directive)**: the UNCONDITIONAL constant is `3/16`
  for `p ≢ 1 (mod 12)` and `1/12` (family II) for `p ≡ 1 (mod 12)`; the clean
  CONDITIONAL `1/4` is `mahler_lower_bound_runjump_near_half` (`p = 2b + j`,
  `−1 ∈ ⟨p⟩ (mod b)` ⟹ `M(p,1) > (p−j)(p+j−2)/4 − 1`), whose hypothesis is
  measured to hold with `j ≤ 33` at every prime `p < 2000`
  (`experiments/mahler_runjump_admissible.py`).  Removing the hypothesis is an
  Artin-type short-interval statement, not grind work.

- **2026-09-08 (grind lap 2)** — **The uniform prime lower bound.**
  `MahlerNumCert.lean` (generic numerator-certificate layer over
  `AdderEscapeCert`), `MahlerFamilyI.lean` (one junction over `1/D`,
  `D = (p+3)/2`: `M(p,1) > ⌊p/2⌋² − 2` when `p^k ≡ −1 (mod D)`; instances
  `M(41,1) ≥ 399`, `M(199,1) ≥ 9799`), `MahlerFamilyII.lean` (second junction =
  the first scaled by `3`: `M(p,1) > (⌊p/2⌋² − 2)/3` for **every** prime `p ≥ 17`,
  via Euler `e = 3φ(D)`).  All trust triple, no `sorry`.

- **2026-09-08 (REVIEW LAP)** — **The prime lower side reformulated as a long
  addition; the first uniform law proved.**  `MahlerBurstDigit.lean` (new,
  trust triple): the `k = 1` background certificate in **adder form** — carry
  `bgCarry` and emitted digit `bgDigit` for "constant background `b` plus burst
  `N`", with `bgResidue_div_eq_bgDigit` identifying the window digit at distance
  `d = i+1` with the digit emitted at position `i`, and
  `mahler_lower_bound_bg_adder` restating the bound with one condition per digit
  position (and no `hstab` — the carry dies when the burst runs out).  On top of
  it, the **first uniform-in-`p` brick**: `bgDigit_zero_ne`, for odd `g ≥ 5` and
  any burst with `B ≡ −4 (mod g)`, position `0` misses the target `g−1` for
  *every* `m < ⌊g/2⌋²` — because the digit sum is `2(u−r) (mod g)` and
  `2(u−r) ≡ −1` forces `u − r ≡ Q`.  `B ≡ −4 (mod p)` is the law satisfied by
  the extremal burst at every prime `7 … 59` (exact digit-DFS).  Route settled
  by data: the burst family holds `M/⌊p/2⌋² ≥ 0.43` up to `p = 59`, so it *is*
  uniformly quadratic — the gap is a formula, not existence.  Closed-form bursts
  `B = p^K(p−c) − 4` REFUTED (only `Θ(p)`).  Engine validated end-to-end by
  `mahler_lower_bound_base29` (`M(29,1) ≥ 140`, `decide +kernel`).
- **2026-09-08 (autonomous, lap 6)** — **The escape engine is a theorem.**
  `AdderEscapeCert.lean`: a decidable automaton certificate (tail intervals,
  per-channel carries, block-free channel digits) plus a witness pair of closed
  walks gives an irrational `α` with the block never occurring in `m·α`,
  `1 ≤ m ≤ M` (`escape_mahler_lower_bound`, trust triple).  Next brick: the
  `(7,2)` instance `M(7,2) ≥ 176`, and exact `k = 1` values at `11, 17`.
- **2026-09-08 (autonomous, laps 3–5)** — **Prime lower side: five new
  certificates, the burst law, and period-2 backgrounds.**
  `MahlerPrimeLowerBound.lean`: `M(17,1) ≥ 63`, `M(31,1) ≥ 224` (exact),
  `M(59,1) ≥ 840 = ⌊59/2⌋² − 1` (beyond the census).  All census bursts are
  `B = p^j κ − 4S_j` with `κ ≡ −8/3 (mod p)`; the family is NOT uniformly
  quadratic (ratio decays past `p ≈ 60`).  `MahlerLowerBoundPeriod2.lean`:
  the `p = 19` extremal shadows `1/(Q+1)`, a period-2 background; formalized
  as a base-`g²` certificate through the Pillai digit bridge, giving
  `M(19,1) ≥ 80` (exact).  General prime lower bound still open
  (`PENDING_WORK.md` §top).
- **2026-09-08 (autonomous, lap 2)** — **The universal constant is `1`, in Lean.**
  `MahlerLowerBoundSmooth.lean`: `mahler_lower_bound_smooth` (`t ∣ g^j`, `t < g`
  ⟹ `M(g,k) ≥ t(gᵏ−1)`; the divisor bound is `j = 1`), instances
  `M(630,1) ≥ 393125` (`0.9905·630²`) and `M(26250,1) ≥ 688878756`
  (`0.99973·26250²`), and `mahler_constant_one_sharp`: for every `k ≥ 1`,
  `ε > 0`, `L`, some base `g ≥ L` has `M(g,k) ≥ (1−ε)g^(k+1)` (Dirichlet on
  `log 3/log 2`, `g = 2^a3^b L`, `t = min(2^a,3^b)²L`).  With
  `mahler_multiplier_lt` this closes the "sharp universal constant" wing:
  `sup_g M(g,k)/g^(k+1) = 1`, not attained.  Formalizes the host's
  `docs/mahler-universal-constant-is-one-2026-09-07.md` (its lower side).
- **2026-09-08 (autonomous)** — **The `(7,2)` extremal orbit dissected; escape
  engine started.**  The instrument's SCC for block `00` is three cycles
  (`1/4`, `4/5`, and `0.(541251512)₇`); their mixing escapes all `m ≤ 175`
  exactly (numeric, 3000 digits), and the period-9 point IS the exact witness
  (`176` is the first `m` that hits).  Its shadow denominators `5,5,5,28,4,4,35,5,5`
  are the drop mechanism verbatim, with `MahlerFarey`'s jump estimate tight.
  No burst family reaches it (sign structure of carries), so the exact lower
  side at `k ≥ 2` needs the automaton: `AdderEscape.lean` lands the true-carry
  recursion and the digit formula for `m·x` (trust triple).  Plan in
  `PENDING_WORK.md` §top.
- **2026-09-07 (autonomous)** — **`g^(k+1)/4` refuted for `k ≥ 2`; first `k = 2`
  prime lower bounds.**  Exact `M(7,2) = 176 = 0.51·7³` (new; with `M(3,2) = 8`,
  `M(5,2) = 48`: ratios `.30 .38 .51`, climbing) — the `k = 1` constant `1/4` does
  not persist, and the shadow-denominator DROP found in `MahlerQuarter.lean` is
  where the extra multipliers live.  `MahlerPrimeLowerBoundBlock.lean`
  (`mahler_lower_bound_bg_block`, trust triple): `M(5,2) ≥ 44`, `M(7,2) ≥ 103`
  in the kernel.  The background+burst family caps at `102` at `(7,2)`: the
  `k = 2` extremal orbit (run blocks `00`/`66`) is a new shape to find.
- **2026-09-07 (autonomous)** — **`M(g,1) ≤ (g² + 6g + 1)/4` for odd primes: the
  multi-scale bound lands at the census constant `1/4`** (`MahlerQuarter.lean`,
  `Mahler.mahler_multiplier_quarter`, trust triple).  The denominator-jump engine
  of `MahlerFarey.lean` iterated: the canonical shadow's denominator strictly
  increases every stage once `d·μ·g·(Q−d) ≤ (μ−d)(μ−2d)·Q`, which at
  `μ = (g+1)(g+5)/4` has discriminant `−4μ²`.  Retires `g(g+1)/2` for `g ≥ 5`.
  ⚠️ Found while formalizing: for `k ≥ 2` the shadow denominator can drop by a
  factor `g`, so `g^(k+1)/4` at `k ≥ 2` is NOT claimed (`PENDING_WORK.md` top).
- **2026-09-02 (autonomous)** — **`M(g,k) < g^(k+1)`: Berend–Boshernitzan's open
  question (Acta Arith. 66, p. 320) answered YES** (`MahlerMultiplierStrict.lean`,
  `Mahler.mahler_multiplier_lt`, ledger `Literature.berendBoshernitzan_strict_holds`,
  trust triple).  The B–B paper was read in full (host findings, archived): the
  `t(gᵏ − 1)` lower bound and `B = 125` are their Thm 3.1 / Ex 3.1 — re-attributed.
- **2026-09-02 (autonomous)** — **Mahler run branch settled at `gᵏ`; prime-base
  conjecture refuted** (`MahlerRunBranch.lean`).  For prime `g`, if `0ᵏ` or `(g−1)ᵏ`
  occurs i.o. in `α` then some `m ≤ gᵏ` has any `k`-block i.o. in `m·α`
  (`mahler_multiplier_of_zero_runs` / `_pred_runs`, trust triple) — the Liouville
  witnesses' branch is pinned to `[gᵏ − 1, gᵏ]`.  Exact adder-machine computation
  (`experiments/mahler_exact_M.py`) gives `M(g,1)` for `g ≤ 29`: for odd primes it
  tracks `((g−1)/2)²`, so `M(g,k) = Θ(g^(k+1))` for primes too and the room is on the
  LOWER side, in the run-free branch (Farey-hopping orbits).  `PENDING_WORK.md` top.
- **2026-09-02 (review lap)** — **Mahler lower bound sharpened from `gᵏ − 1` to
  `t·(gᵏ − 1)`** (`MahlerLowerBoundGeneral.lean`).  Own construction:
  `α = B·liouvilleNumber g` turns the multiplier problem into a digit problem
  about the multiples of one integer; `B = c` for `g = t·c` stretches the budget
  by `t`.  Even bases: `M(g,k) ≥ (g/2)(gᵏ−1)`.  Numerically sharp for this `α`.
  The chapter's open question moves to **prime bases, upper side**.
- **2026-09-01** — **CFScheduleA schedule route encoded as `Prop` nodes; `src/`
  sorry-free** (section below): `VarianceBlockCountPsiPushed` refuted in-kernel
  (`varianceBlockCountPsiPushed_false`), `SchedABlockLinear` open/choice-opaque,
  every dependent conditional.  Same lap: tower floors (C2 cardinality-optimal,
  `c5_sharp`, B–B `M(3,1)=2` lower half), N3 `e` factorial-kick machine, N2
  Stoneham base-6 readout.  Every pre-existing axiom set unchanged (census).
- **2026-09-01** — Mahler chapter made two-sided: upper bound sharpened
  `(g+3)gᵏ → g^(k+1)` (universal covering lemma + shadow-rational escape, closing
  the `g = 2` gap), lower bound `gᵏ − 1` proved from `liouvilleNumber g`.
  Furstenberg 1967 dense-orbit theorem wired via re-homed ×p×q rigidity.
- **2026-09-01** — C10 tower claim proved via a *reduction finding* (the family
  splits; the dossier's 540 396-state certificate is not needed).  Tower brief
  C1–C10 closed.  `PiSqBBP` Aristotle faithfulness cross-check passed.
- **2026-08-31** — ledger hotspot edges; π²-BBP proved.
- **2026-08-30** — `adder_sixfold_disjunction` proved (novel candidate theorem);
  tower phase A; literature ledger first pass (`Literature.lean`).
- **2026-08-26** — `IsNormal.isDisjunctive` (unconditional API gap) closed; Track
  D3 `quadratic_irrationals_disjunctive_of_hypothesisM`; Comparator harness and
  the Phase-3 publishing-prep pass completed locally.
- **2026-08-25** — image-Khinchin headline complete (`ae_tail_average_tendsto`
  proved via the L²-variance/finite-truncation route); B6 affine family exceeded.

## CFScheduleA schedule route encoded as Prop nodes (2026-09-01)

- **`src/` is sorry-free.**  The two disclosed `sorry`s of the abandoned interleaved-
  schedule route (`CFScheduleA.lean`) are re-encoded as named conjecture-graph nodes
  (`def … : Prop`, statements verbatim), with every dependent taking the node as an
  explicit hypothesis (Trevor's decision, 2026-09-01):
  - `VarianceBlockCountPsiPushed` — **RED / refuted.**  Kernel-checked negation
    `varianceBlockCountPsiPushed_false` (`CFScheduleARefuted.lean`, trust triple): the
    bound fails already for `ψ = id`, `v = [1]`, `wx' = [2,…,2]` — a cylinder-restricted
    second moment centred at the global mean is `Θ(n²)`.  Dependents
    `psi_pushed_chebyshev_brick` → `gaussMeasure_aggregate_psi_pushed_le` →
    `exists_scale_cfCylinder_psi_avoid_zbad_poly` are vacuous and say so.
  - `SchedABlockLinear` — **OPEN.**  Choice-opaque (`schedA` is a `Classical.choose`
    recursion whose spec carries no block upper bound), argued false for this construction
    in `OBSTRUCTION-2026-08-24-block-measure-budget.md`.  Dependents `schedA_block_geom` →
    `schedA_hfreq_x`/`_z` → `exists_interleaved_affine_witness`.
- Every other constant's axiom set is unchanged (before/after `collectAxioms` census over
  all NormalNumbers modules); all headlines below keep exactly the trust triple.
- **Tower deductions kernel-checked** (`AdderTowerDeductions.lean`, same day): the
  single-multiplier floor `exists_irrational_mul_omits_digit` (base `b ≥ 3`, any digit,
  any `m ≠ 0`: some irrational `X` has `m·X` omitting the digit entirely — Cantor-set
  encoding of `Set ℕ` through `realOfDigits`), hence **C2 is cardinality-optimal**
  (`no_single_multiplier_all_digits`), **B–B `M(3,1) = 2` lower half**
  (`Literature.berendBoshernitzan_M31_lower_holds`; with C1 both halves are in-kernel)
  and `M(g,1) ≥ 2` for all `g ≥ 3`; and **C5 sharpened** (`c5_sharp`: the `X + 4Y`
  channel is unnecessary — a two-line corollary of C1).  All trust triple.
- **N3 `e` factorial-kick machine landed** (`EFactorialKick.lean`, same day): in every
  base `b`, a run of `k` zeros / top digits of `e` at position `n` with
  `bᵏ > eSplit b n + 1` pins the rational surrogate `fract (bⁿ·A(M)/M!)` to an explicit
  window of width `< 1/(M+1) + b⁻ᵏ` (`eSurrogate_window_of_zeroRun`/`_of_maxRun`,
  unconditional); the CITED node `EIrrationalityExponentTwo` caps runs at `(1+ε)n`
  (`eRun_le_of_exponentTwo`); numerator rigidity `A(M) ≡ A(M mod p)` (`eNum_zmod`).
  Trust triple throughout.
- **N2 base-6 Stoneham readout PROVED** (`StonehamBase6.lean`, same day):
  `stoneham_base6_readout` — the base-6 orbit of `α₂,₃` at position `n` is
  `(3^a mod 2^c)/2^c` up to a `2^{−Θ(3^{j*+1})}` error (`a = n−(j*+1)`, `c = 3^(j*+1)−n`),
  so the base-6 digits of `α₂,₃` are a transcript of `3^a mod 2^c`.  Trust triple.

## Outstanding

### Short-term (mirrors PENDING_WORK top)
**Campaign B FINAL — the `a`-side, the campaign's TERMINAL objective** (set 2026-09-16 DEEP
REFLECTION lap, `DIRECTION.md` → CURRENT DIRECTIVE).  `w_{a,c}(n) = ∑_{p∣n}(a_p + c_p(v_p(n)−1))`
for a general **bounded** `a` (`a_p ≤ Ca`), active set `S = {p : 1 ≤ a_p}` with a Mertens rate.
1. Promote `scratch/ProbeA.lean` into `src/NormalNumbers/G4PhaseA.lean` (`omegaOnA`,
   `totalPhaseA`, `localPhase_const_mul`, `phaseA_eq_sum_local`, `vecMul_const_mul`,
   `coeffAL_const_mul`, `sum_sq_distZ_coeffA_ge_gen`) + `norm_sampleAvg_ee_phaseA_le` through
   `norm_sampleAvg_prod_ee_le` with the per-prime seed
   `fun p => if GoodPrime ρ p ∧ 1 ≤ a p then θ₀ else 0`.
2. `SvalA` / `torusChar_SvalA` / `norm_sampleAvg_torusChar_SvalA_le` (`Sval` with `omegaOn`
   replaced by `omegaOnA`).
3. The schedule's layer budget `N ≥ 1 + clog bb (2^K * (Ca * D))`.  🚦 if some schedule quantity
   is capped from above by `N` in a way `⌈log_bb Ca⌉` breaks (watch the moment cap
   `Mc ≤ 2^{m₂}`), that is a proved obstruction — write it into the DESIGN file.
4. Assembly at `S = {p : 1 ≤ a_p}` by generalizing `G4SubsetC*` **in place**, then the audit
   theorem in `G4WeightStatement`.
Then 🏁 **STOP** — the campaign is complete; do not re-parametrize again.  Permitted stretch
only: the general **additive function** `f(p^v) ≤ a_p + c_p(v−1)`, `f(p) = a_p`, `f` monotone in
`v`, which should ride the existing far-field *domination* with no new §4D work.

Historical (objective S, review lap 166 — banked, closed):
1. ✅ lap 166 — DESIGN §0's third escape (grouped sampling) closed at the schedule
   (`G4GroupedVerdict.lean`); ✅ laps 167–168 — the seam (`Sched.budget_confines`) and the
   non-vacuity of `InsideCapture` (`Capture.structural_satisfiable`).

Historical (entropy expedition):

Campaign **entropy expedition** — 🏁 **OBJECTIVE MET (lap 126)**: `IsNormal 2 fullRealW` is
proved and axiom-clean, so `DIRECTION.md`'s lap-126 CURRENT DIRECTIVE and the ACTIVE operator
override's stop condition ("stop when the endpoint is proved axiom-clean") are both discharged.
Per route trigger **E-T7**, the lap that meets the objective does **not** pick its own successor;
the next altitude lap sets one.  Candidates it should weigh (recorded, not chosen):
* **`IsNormal 4 fullRealW`, and `IsNormal (2^k)`** — the natural strengthening of the *same*
  object.  Requires the read's word frequencies **restricted to positions in a fixed residue
  class mod `k`**.  The entropy machinery does support this: the block-entropy deficit over a
  sub-class of positions is bounded by the *total* deficit `ℓ·δ`, so Pinsker costs only a factor
  `√k`.  What is new is tracking the parity of `fTW i + a·kk i + q` across window boundaries.
  (Going through Wall + Maxfield instead is a genuinely harder classical theorem — do not assume
  it is the cheap route.)
* Anything about `G₄` itself remains **forbidden** by the ACTIVE override.

DONE in lap 126 (kept for provenance):
1. **`G4EntropyWMediant.lean`** — the schedule-free mediant lemma in `ℝ`.  ✅
2. **`G4EntropyWSqueeze.lean`** — the read ratio at an arbitrary `n`.  ✅
3. **The limit and the endpoint.**  ✅  `G4EntropyWStatement.lean` is the audit surface.

DONE in laps 123–125 (kept for provenance):
1. **`G4EntropyWPrefix.lean`** — the prefix read count: `startsLe i c`, the order-isomorphism
   `image (fnthW i) (range (aLe i c)) = startsLe i c`, `fullGoodWPre`, and the prefix analogues of
   `fullW_band_winCount_bounds` / `fullW_winCount_bounds`.  ✅
2. **The sandwich — THE CRUX.**  `pairsLe i c := (bandWPairs i).filter (2·kIdx · ≤ c)`;
   `bandWtr i X₁ ×ˢ univ ⊆ pairsLe i c ⊆ bandWtr i X₂ ×ˢ univ` with `X₂/X₁ ≤ (K+1)/K·(1+2/c)`
   (`kIdx_cross`, `gridOf.mul_d_le_mul_d`); the cardinality ratio from `card_apSample_ge_half` /
   `card_apSample_le`; the truncated overhang (`card_multi_atom_le_real_at`, already generic).  ✅
   (`abs_prefix_ratio_sub_le`, then `abs_prefix_ratio_sub_le_cap` with no upper hypothesis)
3. **`head_frac_tiny`** — cutoffs below the gate `4·wFloor i + 4·P₀`.  ✅ (on `G4GridP0Lower.P₀_growth`)
4. The monotone squeeze and the endpoint — **the only item still open**; see the lap-126 list above.

Superseded short-term list (lap 37's three rungs — all MET, kept for provenance):
1. **`G4EntropyOcc.lean`** — the counting bridge, **and the decisive probe**: `occCount s v n`
   (`#{p < n : s spells v at p}`), the bridge to `countOccurrences v ((List.range n).map s)` with
   seam `≤ |v|−1`, and interval-split additivity.  If the `tails.countP` shape resists, trigger
   **E-T9**: restate rungs 2–3 in list-of-blocks form.
2. **`G4EntropyBlockWord.lean`** — render scale `i` as one block: the `(n, α, p)` enumeration of
   the sample, length `|P_i|·|Atom_i|·m_i`, and `occCount → 2^{−|v|}` out of
   `tendsto_occursCountP_primeLambertFour` (the `(m−ℓ+1)/m` and seam corrections vanish, `m_i → ∞`).
3. **`G4EntropyNormalReal.lean`** — the assembly: the `(scale, repetition)` recursion with
   `r_m·|y_m| ≥ (m+1)(T_{m−1}+|y_{m+1}|)`, `samplePos`, `IsNormalSequence 2`, `ProperDigits`, and
   `isNormal_realOfDigits`.  Repetition defeats the prefix problem; `|y_{m+1}| ≫ ∑_{j≤m}|y_j|` is
   unavoidable because `|P_i|` explodes with `i`.
4. Upgrade after the headline (trigger **E-T8**), not before: a strictly increasing `samplePos` —
   a genuine *subsequence* of `G₄`'s digits — via restricting the empirical law to `S ⊆ P_K` of
   relative size `ρ` at deficit cost `Δ/ρ` (affordable for `ρ ≫ K^{−1/2}`).
5. Bounded secondary, only on an E-T3 stall: **measure the wall** — `Sched.density_le_pow`
   (`≤ ½(3/K⁴)^K`) and `Sched.window_needed_ge` (density `≥ 1/2` needs `mm ≥ K^{4K}·m_K`).

Campaign **G5** (dormant for this run), in order:
1. **The decisive probe in Lean**: generalise C2 (`G4LocalContraction.norm_localSum_le`) from
   an indicator model to a valuation model — default class `v_p = 0` (mass `≥ 1/2`), active
   classes `v_p = 1` (mass `(1/p)(1−1/p)`, phase `xᵢ`), junk `v_p ≥ 2` of mass `≤ k/p²`.
   Paper check: `∑_p k/p² = O(T) = L^{0.02+o(1)}` against a gain `L^{1−o(1)}` — closes.
2. The weight interface itself (`w(n) ≤ log₂ n`, `w(dm) = w(d)+w(m) −` defect), then
   `G4Transport`, `G4Remainder`/`G4FarTail`/`G4MediumPrimes`, then `G4SmallPrimeVector`.
3. The `Ω` series identity `∑_n Ω(n)/bⁿ = ∑_{q prime power} 1/(b^q − 1)`.
4. Second target if the port stalls twice: **effective** disjunctivity — the schedule is
   explicit and the samples are `n < X`, so a first-occurrence bound `N(b, ℓ)` is already
   inside the proof; extracting it means `homit : ∀ m` ⇝ `∀ m ≤ M₀` through `G4Wiring`.
5. Legacy (not this campaign): cited-only ledger nodes (`philipp_psi_mixing`,
   `vandehey_matrix_action`); `k ≥ 2` Mahler lower side via the escape engine.

### Long-term
The conjecture graph toward the sink `IsNormal 2 (Real.log 2)`: the ln-two
ladder (`LnTwoFreq`, `ConditionalDisjunctive`), the run tower
(`LnTwoExpSep`/`LnTwoPolySep`), the shared Diophantine-wall interface.

### To completion
No axiom debt to discharge — the math-axiom count is **0** and has been since the G4 wing landed,
so "completion" here is not a shrinking ledger.  As of the 2026-09-16 deep reflection it has a
concrete meaning: **campaign B's `a`-side, and then stop.**  The two `CFScheduleA` residues are
`Prop` nodes as of 2026-09-01; the two `src/` `sorry`s are pre-expedition, off-path and not
prerequisites for anything proved here.

## Axiom ledger

**Re-run at the DEEP REFLECTION lap** (2026-09-16, build 🟢 9085 jobs, HEAD `36c02ca`).  Real
`#print axioms` output, all exactly `[propext, Classical.choice, Quot.sound]`; every row below
was re-checked against the compiler this lap, not inherited:

| headline theorem | paper claim | `#print axioms` shows | verdict |
|---|---|---|---|
| `G4.isDisjunctive_base (hb : 3 ≤ b)` | `∑_p 1/(bᵖ−1)` is disjunctive in base `b ≥ 3` — UNCONDITIONAL | trust triple | 🟢 clean; 0 math axioms |
| `G4.isDisjunctive_residueClass (ha : IsUnit a)` | `∑ₙ ω_S(n)/bⁿ`, `S = {p ≡ a (q)}`, disjunctive, `b ≥ 3` — UNCONDITIONAL | trust triple | 🟢 clean; Mertens-in-AP is a *theorem* here (`G4MertensAP`), not an axiom |
| `G4.isDisjunctive_residueClass_primeSum` | the same constant as `∑_{p≡a(q)} 1/(bᵖ−1)` | trust triple | 🟢 clean |
| `G4.isDisjunctive_subsetLambert (hmert)` | any prime set `S` with a Mertens rate | trust triple | 🟢 clean; `MertensRate S c C` is an explicit hypothesis, not an axiom |
| `G4.SchedB.isDisjunctive_Omega (hb : 3 ≤ b)` | `∑ₙ Ω(n)/bⁿ` disjunctive, `b ≥ 3` — UNCONDITIONAL | trust triple | 🟢 clean |
| `G4.SchedB.isDisjunctive_Omega_primePowerSum` | the same constant as `∑_{q prime power} 1/(b^q−1)` | trust triple | 🟢 clean |
| `G4.SchedB.isDisjunctive_weight c C hC (hb)` | every bounded coefficient weight `w_c = ω + excess c`, `b ≥ 3` — UNCONDITIONAL | trust triple | 🟢 clean |
| `G4.SchedB.isDisjunctive_weight_logLogPow c hc (hb)` | **unbounded** coefficients: every `c_p ≤ A₀(1+log₂log₂ p)^s`, `b ≥ 3` — UNCONDITIONAL | trust triple | 🟢 clean (2026-09-16) |
| `G4.SchedB.isDisjunctive_subsetWeight_logLogPow` | the **merge**: a prime set `S` with a Mertens rate *and* an unbounded polylog `c` | trust triple | 🟢 clean (2026-09-16) |
| `G4.isDisjunctive_residueClass_weight_logLogPow (ha)` | the merge at `S = {p ≡ a (q)}`, `a` a unit | trust triple | 🟢 clean (2026-09-16) |
| `G4.audit_isDisjunctive_*_logLogPow` (`G4WeightStatement`) | the same three with every abbreviation unwound — the audit surface | trust triple | 🟢 clean (2026-09-16) |
| `G4.Sched.isNormal_fullRealW` | `IsNormal 2 fullRealW` — UNCONDITIONAL | trust triple | 🟢 clean (banked) |

**Math-axiom count (🟢+🟡+🟠): 0.**  No `axiom` declaration anywhere in `src/`, no
`native_decide` artifact in any headline cone.  `src/`'s two open `sorry`s
(`MahlerDriftOne.exists_prime_nonresidue`, `PrimeLambertOscillation.phaseOscillation`) are
pre-expedition, off-path, forbidden drift, and appear in **no** row above.  There is **no 🔴**:
every row is an unconditional statement.  Campaign B's target is a strictly stronger theorem,
not a debt.

**Re-run at review lap 166** (2026-09-15, build 🟢 9041 jobs), all exactly
`[propext, Classical.choice, Quot.sound]`: `isNormal_fullRealW`,
`isNormal_two_of_schedule_read`, `PowerBase.isNormal_pow`, `RowVariance.two_layers_of_dyadic`,
`RowVariance.cancelled_union_le`, `RowVariance.roughRowVarianceLower_mertens`,
`RowVariance.threshold_exact`, `RowVariance.union_le_of_determining`,
`RowVariance.grouped_union_le'`, `Sched.balanced_union_le`, and lap 166's
`Sched.grouped_size_cond` / `grouped_block_size` / `grouped_block_count_le` /
`grouped_balanced_union_le`.  **Math-axiom count (🟢+🟡+🟠): 0** in the G4 / entropy /
deformation wing — no `axiom` declaration anywhere in `src/`, no `native_decide` artifact in
these cones.  The repo's two open `sorry`s are `MahlerDriftOne.exists_prime_nonresidue` (a prime
in `(p/3, p/2)` with prescribed Legendre symbol — 🟠 generational: Linnik strength, nowhere near
mathlib) and `PrimeLambertOscillation.phaseOscillation` (the target of an open irrationality
problem; `irrational_primeLambert` is *explicitly* labelled sorry-gated, not a theorem).
Neither appears in any headline cone below.

Real `#print axioms` output, re-run at entropy **lap 126** (HEAD `6abd3f0`,
build 🟢 9024 jobs).  **Re-verified this lap**: `isNormal_fullRealW`,
`isNormal_two_of_schedule_read`, `digitOf_fullRealW`, `isDisjunctive_fullRealW`,
`irrational_fullRealW`, `isNormalSequence_fullDigW`, `tendsto_winCount_fullDigW`,
`abs_ratio_mid_le`, `tendsto_fullWRead_freq`, `fullPosW_strictMono`,
`abs_prefix_ratio_sub_le_cap`, `head_frac_tiny` — all exactly
`[propext, Classical.choice, Quot.sound]`.
`entropy_E1_tile`'s lap-119 `sorryAx` is **gone**: its leaf `entropy_E1_march` is now a theorem.
**Math-axiom count in the entropy wing: 0** — every headline
below prints exactly the trust triple `[propext, Classical.choice, Quot.sound]`, with no
`native_decide` artifact and no local `axiom` anywhere in `src/`.  The two open `sorry`s in the
repo (`MahlerDriftOne.exists_prime_nonresidue`, `PrimeLambertOscillation.phaseOscillation`)
belong to other campaigns and are on this expedition's forbidden-drift list; they do not
appear in any cone below.  Every UNCONDITIONAL headline: trust triple only; the single exception is
flagged.  G4 rows come first.  Nothing in the G4 wing has a `sorry` or an axiom — its debt is
carried honestly as the named unproved `Prop`s `SeparatingFrameExists` / the
`ScheduleWitness` hypothesis, which is exactly what makes `isDisjunctive_four_of_witness`
conditional.  **Brief §4 is closed**: all five of `PropA`, `PropB`, `PropC`, `PropD`,
`PropJackson` are now *theorems* about the concrete `gridFrame`, two of them modulo named
real inequalities that live in the witness.

| headline theorem | paper claim | `#print axioms` shows | verdict |
|---|---|---|---|
| `G4.Sched.entropy_E0` | **sample entropy `H₂(Z^{G₄}_K) > (1/5)m_K H_K`** for every admissible `K ≥ 33856` — UNCONDITIONAL, about the quantized sample only (brief §4 E0) | trust triple | 🟢 clean (entropy lap 6) — NOT a normality claim |
| `G4.Sched.entropy_E1` | **`H₂ ≥ m_K H_K − 50√K·H_K`** for `K ≥ 160000` — UNCONDITIONAL (brief §4 E1, `C = 50`) | trust triple | 🟢 clean (entropy lap 7) — implies E0's ratio `≥ 1 − 200/√K` |
| `G4.Sched.not_T_E` | **brief §6's transfer `T_E` is FALSE** — `maskedReal G₄` has the same joint law at every scale and is not normal (uncond.) | trust triple | 🟢 clean (entropy lap 8) |
| `G4Entropy.forces_normal_iff_density_one` | **a digit-local hypothesis forces normality iff its read set has density one** (uncond.) | trust triple | 🟢 clean (laps 16–18) |
| `G4Entropy.qForces_normal_iff_density_one` | same for an arbitrary family of times + quantization levels `⌊2^{mᵢ}{2^{rᵢ}x}⌋` (uncond.) | trust triple | 🟢 clean (lap 20) |
| `G4.Sched.not_qForces_normal_at_pow` | **no quantized sampler on this schedule forces normality**, at any level up to `B^K ≥ K^{3K}` (uncond.) | trust triple | 🟢 clean (lap 22) |
| `G4Entropy.entropy_rate_not_control_bit` | entropy rate `→ 1` does not pin a **fixed-offset** bit (uncond.) | trust triple | 🟢 clean (lap 15) — ⚠️ read lap 23's correction: it says nothing about the **offset-averaged** frequency, which entropy *does* control and which is now the objective |
| `G4.Sched.tendsto_occursCountT_primeLambertFour` | **every finite binary word `v` occurs at frequency `2^{−|v|}`** among the aligned `|v|`-blocks of `G₄`'s sampled windows, over `OccursAt 2 · v ·` (uncond.) | trust triple | 🟢 clean (lap 31) — §5's positive answer, on real digits; **not** a normality claim (sampled positions have density zero) |
| `G4.Sched.tendsto_occursCountP_primeLambertFour` | **every finite binary word at frequency `2^{−|v|}` among ALL positions `(n,α,p)` of the sampled windows** (uncond.) | trust triple | 🟢 clean (lap 36 abstract / rendered) — the INPUT to the live normal-number objective |
| `G4.Sched.tendsto_occursCountJointFree_primeLambertFour` | **`t` sampled windows decorrelate**: every pattern `(w₁,…,w_t)` at frequency `2^{−tℓ}`, over all position vectors in `[0,m_K−ℓ+1)^t`, no alignment (uncond.) | trust triple | 🟢 clean (lap 47) — the strongest frequency statement this arithmetic supports |
| `G4Entropy.no_pointwise_bound_from_deficit` | the averaging in the line above is **necessary**: a one-bit-per-window deficit still admits a probability-zero pattern at a fixed position vector (uncond.) | trust triple | 🟢 clean (lap 48) — the boundary, a refutation |
| `G4.Sched.joint_richness_primeLambertFour` | for at least half the blocks the `t` sampled windows of `G₄` take `≥ 2^{t·m_K − 200t√K}` distinct joint values; shortfall rate `800/√K → 0` (uncond.) | trust triple | 🟢 clean (laps 49–50) — per-block, no averaging over positions |
| `G4Entropy.abs_posAvg_sub_le` | the same capacity bound over **all** `m−ℓ+1` window positions, not one aligned tiling: `≤ 2√(log2·ℓδ/(m−ℓ+1))` (uncond., abstract `FinLaw`) | trust triple | 🟢 clean (lap 36), rendered at the schedule in lap 36's `G4EntropyPosition` |
| `G4.log_det_normalized_two_sided` | `1/300000 ≤ log det(1+T_{K²}^{⊗K})/((K²)^K√K) ≤ log2/√K + 12` for `K ≥ 5` (uncond.) | trust triple | 🟢 clean (lap 34) — the `√K` deficit is **structural**, so `ℓ = o(√K)` is a property of the object |
| `G4.Sched.not_T_E_of_density_lt_one` | `T_E` refuted again from density `< 1` alone, at a single `c` (uncond.) | trust triple | 🟢 clean (lap 18) |
| `G4Entropy.tendsto_density_compl_zero` | a satisfiable digit-local hypothesis forces normality only if its read set has density **one** (uncond.) | trust triple | 🟢 clean (lap 18) — the barrier at full strength |
| `G4.Sched.entropy_E1_march` | **E1 on the marched `(K, j)` ladder** — the deficit bound at every marched outer scale (uncond.) | trust triple | 🟢 clean (2026-09-15) — retires the scale gap: `entropy_E1_tile` is now unconditional |
| `G4.Sched.entropy_E1_tile` | **E1 at EVERY outer scale in `[Xlo K, Xlo (K+4)]`** — the certified windows tile with no hole (uncond.) | trust triple | 🟢 clean (2026-09-15) — was `sorryAx`-gated at lap 119 |
| `G4.Sched.tendsto_fullWRead_freq` / `fullPosW_strictMono` | **every finite binary word has frequency `2^{−|v|}` in `G₄`'s digits read along the strictly increasing, schedule-only `fullPosW`, at the band cutoffs `fTW (i+1)`** (uncond.) | trust triple | 🟢 clean (lap 121) — the frequency half of the live objective; **not** a normality claim yet (all `n` still open: MID-BAND PREFIX CONTROL) |
| 🏁 **`G4.Sched.isNormal_fullRealW`** / **`isNormal_two_of_schedule_read`** | **`IsNormal 2 fullRealW`** — a strictly increasing, schedule-only read of `G₄`'s binary digits is the binary expansion of a number normal in base two (uncond.) | trust triple | 🟢 clean (lap 126) — **the entropy expedition's endpoint**; says nothing about the normality of `G₄` itself |
| `G4.Sched.digitOf_fullRealW` | `fullRealW`'s **own** base-two expansion is that read (uncond.) | trust triple | 🟢 clean (lap 126) — the faithfulness step of the headline |
| `G4.Sched.isDisjunctive_fullRealW` / `irrational_fullRealW` | `fullRealW` is disjunctive in base two, hence irrational (uncond.) | trust triple | 🟢 clean (lap 126) |
| `G4.Sched.abs_ratio_mid_le` | **mid-band control at an ARBITRARY read index**: the read ratio at any `n` is within `midErrW` of its value at the band cutoff (uncond.) | trust triple | 🟢 clean (lap 126) — the last structural obligation |
| `G4.Sched.abs_prefix_ratio_sub_le_cap` | **mid-band prefix control**: at every position cutoff `c` above the gate, the prefix read's word frequency is within `2√(808 log2·ℓ/√K) + 128/K` of `2^{−ℓ}` (uncond.) | trust triple | 🟢 clean (lap 125) — the crux of the last obligation; no upper hypothesis on `c` |
| `G4.Sched.head_frac_tiny` | **the ungated head is negligible**: `headW(i+1)·kk(i+1)·KK(i+1) ≤ fTW(i+1)`, i.e. band `i+1`'s pre-gate read is a `1/K` fraction of the history (uncond.) | trust triple | 🟢 clean (lap 125) — rests on the new `P₀` lower bound `G4GridP0Lower.P₀_growth` |
| `G4.isDisjunctive_base` | **`3 ≤ b → IsDisjunctive b (∑_n ω(n)/bⁿ)`** — UNCONDITIONAL, the campaign endpoint generalised (brief §7.1) | trust triple | 🟢 clean — no `sorry`, no `native_decide`, no local axiom in the cone |
| `G4.isDisjunctive_four` / `isDisjunctive_two` | **G₄ disjunctive in base 4 and base 2** — UNCONDITIONAL, the attended frozen endpoint | trust triple | 🟢 clean |
| `G4.isDisjunctive_primeSum` / `every_word_occurs_base` / `isDisjunctive_root` | prime-sum form, every finite word, root bases (uncond.) | trust triple | 🟢 clean |
| `G4.irrational_primeSum` | **`3 ≤ b → Irrational (∑' p, 1/(bᵖ−1))`** (uncond.) — the `b ≥ 3` half of the Tao–Teräväinen family, independent route | trust triple | 🟢 clean (lap 16) |
| `G4.every_word_occurs_base_late` / `every_binary_word_occurs_late` | every word occurs *arbitrarily late*, hence infinitely often (uncond.) | trust triple | 🟢 clean (lap 16) |
| `IsDisjunctive.irrational` / `IsDisjunctive.exists_ge` | disjunctive ⇒ irrational; every interval hit arbitrarily late (uncond., any base) | trust triple | 🟢 clean (lap 16) |
| `G4.isDisjunctive_four_of_witness` | G4 disjunctive base 4 — **CONDITIONAL** on a `ScheduleWitness` for every omitted cylinder (= brief §5) | trust triple | 🟢 clean; the hypothesis IS the residual candidate content — never report as the endpoint |
| `G4.separatingFrameExists_of_witness` | §5 witness ⇒ `SeparatingFrameExists` (uncond.) | trust triple | 🟢 clean — the audit surface: one frame, all five props |
| `G4.isDisjunctive_four_of_frames` / `…_two_of_frames` | base 4 / base 2 — CONDITIONAL on `SeparatingFrameExists` | trust triple | 🟢 clean, conditional |
| `G4.Frame.finite_contradiction` | §4E finite separating test from A–D + Jackson (uncond.) | trust triple | 🟢 clean |
| `G4.gridFrame_propA` | **§4A** exact affine Lambert transport on the concrete grid (uncond.) | trust triple | 🟢 clean — input CLOSED |
| `G4.gridFrame_propC` | **§4C** uniform joint small-prime Fourier control, whole box (uncond.) | trust triple | 🟢 clean — input CLOSED, closed-form `smallPrimeBound` |
| `G4.Frame.propJackson` | **§4E** product-Fejér smoothing, `κ = 1/(res√(D+1))`, `Λ = (2D+1)^r`, EVERY frame (uncond.) | trust triple | 🟢 clean — input CLOSED, no side conditions |
| `G4.gridFrame_propD_of_bounds` | **§4D** three ranges + far tail ⇒ `PropD` (uncond., given `hbig`, `hfar`) | trust triple | 🟢 clean — input CLOSED modulo two §5 inequalities |
| `G4.gridFrame_propB_of_bound` | **§4B** zonotope tube volume ⇒ `PropB` (uncond., given `hB`) | trust triple | 🟢 clean — input CLOSED modulo one §5 inequality |
| `G4.bigAvg_le'` / `G4.farAvg_le` | §4D medium (`Y`-split, signed L²) and far-tail closed forms (uncond.) | trust triple | 🟢 clean — the brief's §4D tripwire honoured |
| `G4.log_det_one_add_tensorGram_le'` | §4B spectral `log det(1+T_{K²}^{⊗K}) ≤ r(log2+23√K)` (uncond.) | trust triple | 🟢 clean |
| `G4.schedule_budget` | §5 C4: `C·K^{2K+1}8^K < c·L` eventually (uncond.) | trust triple | 🟢 clean |
| `PrimeLambert.primeSumAtBase_four` | `∑_p 1/(4ᵖ−1) = ∑_n ω(n)/4ⁿ` (uncond.) | trust triple | 🟢 clean — the endpoint's identity |
| `PrimeLambert.isDisjunctive_two_of_four` | base-four ⇒ base-two dictionary (uncond.) | trust triple | 🟢 clean |
| `exists_absolutely_normal_cf_normal` | Becher–Yuhjtman 2019 Thm 1 (uncond.) | trust triple | 🟢 clean |
| `exists_absolutely_normal_cf_normal_khinchin` | image-Khinchin (uncond.) | trust triple | 🟢 clean |
| `isNormal_log_two_of_equidistributed` | conditional ln-two | trust triple | 🟢 clean (hypothesis is a named `Prop`, not an axiom) |
| `Mahler.mahler_multiplier` | Mahler 1973 Thm M, sharpened | trust triple | 🟢 clean |
| `Mahler.mahler_lower_bound` / `…_even` | our own lower bounds | trust triple | 🟢 clean |
| `Mahler.mahler_multiplier_quarter` | our own `M(p,1) ≤ (p²+6p+1)/4`, odd prime | trust triple | 🟢 clean |
| `Mahler.mahler_lower_bound_smooth` / `mahler_constant_one_sharp` | our own `sup_g M(g,k)/g^(k+1) = 1` | trust triple | 🟢 clean |
| `Mahler.mahler_lower_bound_bg_adder` / `bgDigit_zero_ne` | our own adder-form certificate + the uniform `B ≡ −4 (mod p)` law | trust triple | 🟢 clean |
| `Adder.FamilyI.mahler_lower_bound_family_I` / `…_prime_family_I` | our own `M(p,1) > ⌊p/2⌋²−2` when `−1 ∈ ⟨p⟩ mod (p+3)/2` | trust triple | 🟢 clean |
| `Adder.FamilyII.mahler_lower_bound_family_II` / `…_prime_family_II` | our own uniform `M(p,1) > (⌊p/2⌋²−2)/3`, every prime `p ≥ 17` | trust triple | 🟢 clean |
| `Adder.Background.Two.mahler_lower_bound_two_cycle` / `…_prime_seven_mod_twelve` | our own `M(p,1) > p(p−1)/6 − 1`, every prime `p ≡ 7 (mod 12)` | trust triple | 🟢 clean |
| `Adder.Background.mahler_lower_bound_drift_one` | our own `M(p,1) ≥ D(p−1)/2 − 1` per drift-one background | trust triple | 🟢 clean |
| `Adder.RunJump.mahler_lower_bound_runjump` / `…_three` / `…_four` | our own run+jump chain: `M(p,1) > b(p−b−1)−1` for `−1 ∈ ⟨p⟩ (mod b)`; `2/9` and `3/16` for `3 ∣ p+1`, `4 ∣ p+1` | trust triple | 🟢 clean |
| `Adder.Farey.mahler_lower_bound_farey` | our own two-background Farey certificate, `⌊p/2⌋²−2` | trust triple | 🟢 clean |
| `Adder.Background.mahler_lower_bound_prime_drift_one` | our own `M(p,1) > ≈p²/6`, **conditional** | trust triple **+ `sorryAx`** | 🔴→ correctly conditional: its one hypothesis `exists_prime_nonresidue` (prime `q ∈ (p/3,p/2)` with `(p\|q) = −1`) is Linnik-strength, disclosed, and reaches NO unconditional theorem |
| `Mahler.mahler_lower_bound_base29` | our own `M(29,1) ≥ 140` | trust triple (`decide +kernel`, no `native_decide`) | 🟢 clean |
| `Mahler.mahler_multiplier_of_zero_runs` / `…_pred_runs` | run branch at `gᵏ` (prime `g`) | trust triple | 🟢 clean |
| `Mahler.mahler_multiplier_lt` / `Literature.berendBoshernitzan_strict_holds` | `M(g,k) < g^(k+1)` (B–B open question) | trust triple | 🟢 clean |
| `Literature.mahler_theoremM_holds` | Mahler 1973, all `g` | trust triple | 🟢 clean |
| `Literature.berendBoshernitzan_bound_holds` | B–B 1994 `2g^(k+1)`, all `g ≥ 2` | trust triple | 🟢 clean |
| `Literature.furstenberg_dense_orbit_holds` | Furstenberg 1967 | trust triple | 🟢 clean |
| `varianceBlockCountPsiPushed_false` | refutation of the schedule brick (own) | trust triple | 🟢 clean |
| `Adder.exists_irrational_mul_omits_digit` / `Adder.c5_sharp` | tower floors (own) | trust triple | 🟢 clean |
| `stoneham_base6_readout` | N2 base-6 Stoneham readout (own) | trust triple | 🟢 clean |
| `Literature.berendBoshernitzan_M31_lower_holds` | B–B `M(3,1)=2`, lower half | trust triple | 🟢 clean |
| `Adder.adder_sixfold_disjunction` | novel candidate | trust triple | 🟢 clean (kernel-tier cert) |
| `Adder.c10_disjunction_universal` | tower C10 | trust triple | 🟢 clean |
| `IsNormal.isDisjunctive` | unconditional API gap | trust triple | 🟢 clean |
| `quadratic_irrationals_disjunctive_of_hypothesisM` | Track D3, conditional | trust triple | 🟢 clean |

Math-axiom count (🟢+🟡+🟠): **0**.  🔴: none.  `src/` carries exactly TWO disclosed
`sorry`s (a stale earlier count said one): `exists_prime_nonresidue`
(`MahlerDriftOne.lean`, Linnik-strength, reached only by the CONDITIONAL
`mahler_lower_bound_prime_drift_one`) and `phaseOscillation`
(`PrimeLambertOscillation.lean`, the OLD irrationality endpoint, which the G4 kickoff
explicitly excludes as a prerequisite and which no G4 declaration imports).  Every
unconditional headline above is `sorryAx`-free, and **no G4 file has a `sorry`**.  The two
former `CFScheduleA` schedule residues are named `def … : Prop` nodes, which no headline
depends on.

**Honest reading of the G4 row set**: the ledger is axiom-clean, but that certifies the
*proofs*, not the endpoint.  G4 is not done: `isDisjunctive_four_of_witness` rests on the
`ScheduleWitness` hypothesis, which is brief §5 and is unproved.  What changed at this lap
is that the hypothesis is now a finite list of **explicit real inequalities in explicit
parameters** rather than any unproved mathematics — and those inequalities were re-derived
from the Lean definitions this lap and do close.

## Pointers

`DIRECTION.md` (**binding directive** — G4 §5, triggers G-T2…G-T5) ·
`KICKOFF-2026-09-14-g4-disjunctivity.md` + the brief at
`~/personal/claude/knowledge/core/projects/normal-numbers-g4-disjunctivity-fable-handoff-2026-09-14.md` ·
newest baton: `ls HANDOFF-2026-09-14-g4-lap*.md | sort -t p -k2 -n | tail -1` ·
`PENDING_WORK.md` §Reflection 2026-09-14 (the §5 re-derivation, the two refuted parameter
values, the two-sided `K` window) · `CHECK-g4-route-deviations.md` (host's independent route
checks) · `ROADMAP.md` · `papers/literature-review.md` §G4 chapter ·
`BRIEF-literature-statements.md` (the novelty tripwire ledger)

---

## Historical campaign ledger (superseded state snapshots)

Everything below is retained as proof-campaign history. In particular, its claims
that image-Khinchin or `ae_tail_average_tendsto` are open are no longer active.

**Track D update (2026-08-26):** the unconditional API gap
`IsNormal.isDisjunctive` is proved, axiom-clean, fully built, and committed as
`b755fd5`.  D3 is also ✅: `QuadraticDisjunctive.lean` freezes Axiom M_b as the
named Prop `QuadraticHypothesisM`, proves the independent missing-word
Hausdorff-dimension bound from an endpoint-safe finite cover, and proves the
exact theorem `quadratic_irrationals_disjunctive_of_hypothesisM`.  For every
`b ≥ 2`, `QuadraticHypothesisM b` alone implies that every quadratic
irrational is `b`-disjunctive.  Guarded axioms for the dimension theorem and
exact wrapper are the standard trust triple, and the full build is green at
8766 jobs.  A fresh review-lap statement probe also checked definitionally that
`QuadraticHypothesisM` is exactly the closed/forward-invariant/dimension-`< 1`
avoidance hypothesis and contains no encoded disjunctivity conclusion.  The
older B5′/B6 status below is retained as historical campaign state.

**B5′ COMPLETE + axiom-clean (10 headlines); B6 affine-images DONE + EXCEEDED (single-map + FULL affine family, any real `r`, `q>0`, all trust-triple). ONE open obligation left in the whole repo: `ae_tail_average_tendsto` — the log-tail SLLN feeding the image-Khinchin headline (witness CF-normal + all affine images CF-normal + Khinchin-typical).** · **Build**: 🟢 green (8760 jobs) · **Updated**: review lap #3 · 2026-08-25 · `53e454c`+

## Where it stands

**B5′ + all of B6-affine are DONE and axiom-clean; the sole live frontier is the
image-Khinchin stretch, reduced to ONE strong-law crux.** The B5′ expedition (ten
headline theorems), the B6 single-map `exists_cfNormal_and_affine_cfNormal`, and the
B6 Tier-2 **full affine family** `exists_cfNormal_and_affine_family_cfNormal'` (any
real `r`, `q>0` — the faithful Vandehey §7 statement) are all proved and
`#print axioms`-clean (trust triple only). B6 was closed via the MEASURE route
(existence is a.e.-trivial; the false schedule crux is dead code, marked REFUTED).
**The one remaining open obligation across `src/` is `ae_tail_average_tendsto K`
(`CFAeKhinchin.lean:343`)**: `∀ᵐ x ∂γ, logBirkhoffSum K n x / n → ∫ logTailFn K dγ`.
Only `K=0` is consumed (g-direct route) — it closes `ae_khinchinTypical` (currently
`+sorryAx`) which grafts into the affine family to yield the image-Khinchin headline.
This is the genuine research core: a **strong law (a.e. Birkhoff convergence) for the
UNBOUNDED log-digit function** under the Gauss measure — no ergodic theorem in
mathlib, so it goes through an L²→a.e. variance argument mirroring the PROVEN
`ae_orbit_freq`. Route (DIRECTION.md CURRENT DIRECTIVE, Approach B / finite
truncation): (1) `integral_blockCount_cross` two-cylinder 2nd-moment identity
[LANDED, axiom-clean], (2) `abs_cov_two_cyl_pair_le` general-`(i,j)` two-cylinder
covariance bound [LANDED, axiom-clean], (3) `variance_truncated_le` uniform-in-M
variance, (4) MCT limit → `variance_logBirkhoffSum_le`, (5) Chebyshev+Borel–Cantelli+
monotone squeeze (transcribe `ae_orbit_freq`), (6) graft → image-Khinchin headline.

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

- **2026-09-08 (grind lap 2)** — **The uniform prime lower bound.**
  `MahlerNumCert.lean` (generic numerator-certificate layer over
  `AdderEscapeCert`), `MahlerFamilyI.lean` (one junction over `1/D`,
  `D = (p+3)/2`: `M(p,1) > ⌊p/2⌋² − 2` when `p^k ≡ −1 (mod D)`; instances
  `M(41,1) ≥ 399`, `M(199,1) ≥ 9799`), `MahlerFamilyII.lean` (second junction =
  the first scaled by `3`: `M(p,1) > (⌊p/2⌋² − 2)/3` for **every** prime `p ≥ 17`,
  via Euler `e = 3φ(D)`).  All trust triple, no `sorry`.

- 2026-08-25 (review lap #3): **B6-affine DONE + EXCEEDED; direction re-pointed at the
  ONE open crux (image-Khinchin's log-tail SLLN); decorrelation core landed.** Inventory
  by real `#print axioms` (HEAD `53e454c`, build 🟢 8760): B5′ (10 headlines), B6 single-map,
  AND B6 Tier-2 full family `exists_cfNormal_and_affine_family_cfNormal'` (any `r`, `q>0`)
  all trust-triple — the measure route is not just done but exceeded (general family + full
  `r`). Confirmed recent laps genuinely narrowed the crux (measure pivot → single-map → full
  family → image-Khinchin assembly → g-direct reduction to ONE tail-average sorry). Prior
  directive (measure route) fully discharged ⇒ rewrote CURRENT DIRECTIVE to PROVE
  `ae_tail_average_tendsto` via the L² variance route, KEY INSIGHT = finite-truncation
  (Approach B) reduces the second moment to Finset algebra + one MCT limit (sidesteps nested
  `integral_tsum`). Hardest-first this lap: LANDED the two decisive decorrelation bricks
  `integral_blockCount_cross` (cross 2nd-moment identity) + `abs_cov_two_cyl_pair_le`
  (general-`(i,j)` two-cylinder covariance) — both axiom-clean, green. No charter trigger fired.

- 2026-08-25 (review lap #2b): **ROUTE PIVOT — schedule crux is FALSE, B6 goes to the
  measure route.** While driving step 1c of the "prove the variance crux" plan, the
  pushforward structure yielded a rigorous counterexample to `variance_blockCount_psi_pushed`
  (`v=[1]`, `ψ(cfCyl wx')⊆cfCyl[2,…,2]` ⇒ pushed count `≡0` at scales `n≤|wx'|` ⇒
  `LHS=n²γv²γ(wx') > RHS` once `n>88/γv≈212`). The crux is FALSE — a deep cylinder is a tiny
  interval, so `blockCount n(ψ·)` is near-constant over it for `n≲|wx'|` at a value ≠ `nγv` ⇒
  2nd moment `Θ(n²)`. So `psi_pushed_chebyshev_brick`/`_poly` establish nothing; both schedule
  z-routes are dead. Took the 2026-08-24-pre-registered "escape #3": pivoted B6 to the MEASURE
  argument (existence is a.e.-trivial). New crux = `ae_isCFNormal` (a.e. CF-normality via
  L²→a.e. Borel–Cantelli from the PROVED `variance_blockCount_le`, no ergodic theorem), then
  ψ⁻¹-preserves-null ⇒ two co-null sets meet ⇒ witness. Wrote OBSTRUCTION + ROUTE-ESCALATION
  docs, rewrote CURRENT DIRECTIVE, marked the false crux REFUTED in-source (kept, not deleted).
  Charter trigger FIRED and handled by pivot, not stop.

- 2026-08-25 (review lap #2): **Whole clean z-side reduced to ONE analytic crux;
  direction re-pointed at it.** Inventory by real `#print axioms`: build green 8757,
  both B5′ headlines trust-triple = DONE, B6 still `+sorryAx` (now via the DEAD
  two-stream `schedA_block_linear`, `:5630`). Confirmed the last ~10 laps were
  genuine crux-narrowing, not leaf-fixation: ψ(xA) irrationality PROVED, the
  Chebyshev/Markov budget + transfer engine built axiom-clean, the conditional-at-`wz`
  route walled by a density-vs-coverage obstruction (`5816044`) then corrected, and
  the clean local-density architecture found — collapsing the entire single-stream
  z-selector (`psi_pushed_chebyshev_brick`→`_poly`) onto ONE disclosed sorry
  `variance_blockCount_psi_pushed` (`:4254`). Found the prior directive STALE (its
  step 1 done, steps 2–3 collapsed); rewrote DIRECTION to mandate PROVING the crux,
  hardest-first, decomposed into (1) restricted ψ-pushed 2nd-moment identity
  (routine), (2) ψ-conjugated interval-base mixing via change-of-variables bounded
  density ratio, (3) geometric-sum assembly. Base-mass factor `γ(cfCyl wx')`
  MANDATORY (its loss walled every prior route). No charter trigger fired.

- 2026-08-25 (review lap): **B6 L4 crux PROVED; direction re-pointed at the z-side
  (ψ(xA) irrationality first).** Inventory by real `#print axioms`: build green
  8757, both B5′ headlines trust-triple = DONE, B6 still `+sorryAx` via the DEAD
  two-stream `schedA_block_linear` (`:4823`, sole `src/` sorry). Found the CURRENT
  DIRECTIVE stale: its mandated crux `schedL4_block_linear` is PROVED (`030d8fb`)
  and its step-4 "z-side = REUSE" is REFUTED (`b178653`). Validated the grind
  ON-PATH (last ~10 laps proved the block-linear crux, landed the x-side, built the
  Z-I engine — genuine crux work). Rewrote DIRECTION to mandate z-side
  re-integration, hardest-first = force ψ(xA) irrational via a per-stage
  diagonalization filler digit over an enumeration of `ψ⁻¹(ℚ)`, keeping the
  freq-good block on the FULL hull (target-shrink RULED OUT: breaks the `¼γwx≤γtar`
  balance). No charter trigger fired.

- 2026-08-24 (review lap): **B6 L4 crux collapsed to the cfK-cap graft; bridge +
  layer 1 PROVED.** Inventory by real `#print axioms`: build green 8757, both B5′
  headlines trust-triple, sole `src/` sorry = the DEAD two-stream
  `schedA_block_linear`. Validated the L4 pivot SOUND and the grind ON-PATH (the
  last ~5 laps located + proved the block-linear support layer and started the
  recursion — genuine crux work, not leaf-fixation). Found the CURRENT DIRECTIVE
  stale in specifics (mandated L4 measure bricks all since DONE) and re-pointed it
  at the real crux `schedL4_block_linear`, whose ONE open sub-obstruction is the
  **cfK cap** (`cfK u ≤ e^{κ|u|}` ⇒ `Nfib` affine in `|wx|`). Confirmed it is a
  positive-measure selection (NOT the refuted hard digit-cap) with its whole
  measure/selection stack already proved, then de-risked it: proved the bridge
  `cfK_le_of_notMem_cfKbadExtSet` + the layer-1 variant
  `exists_multiscale_freq_good_block_steer_len_cfK` (exposes `cfK u ≤ e^{κ|u|}`),
  build green, additive. Rewrote DIRECTION to mandate the graft (layer 2 → 3 →
  `schedL4_block_linear`). No charter trigger fired.

- 2026-08-24 (review lap): **B6 PIVOT RATIFIED — two-stream route DEAD, RESUME
  single-stream L4; broke a FALSE STOP.** Inventory by real `#print axioms`: build
  green 8757, both B5′ headlines trust-triple, sole `src/` sorry = the B6 crux
  `schedA_block_linear` (`:2537`). The prior grind laps hit a genuine obstruction
  (two-stream forces super-exponential blocks, `OBSTRUCTION-2026-08-24`) and
  correctly proposed the single-stream pivot, but then declared the crux
  "operator-gated" and stopped — a false stop (no operator on an autonomous run).
  Discovered the single-stream "L4" route is the ORIGINAL module design
  (`CFScheduleA.lean:24–31`) whose L3 foundation `volume_preimage_affineMap`
  (`CFAffine:94`) is already proved; the two-stream layer was a later drift into
  the wall. Rewrote DIRECTION.md CURRENT DIRECTIVE to resume L4 (brick 1 = the
  ψ-pullback Gauss distortion bound `gaussMeasure(ψ⁻¹ S) ≤ (2/q)·gaussMeasure S`,
  ingredients confirmed present), decomposed the full L4 path in PENDING_WORK, and
  forbade grinding the dead two-stream lemmas / any further box-stuck. Item-2
  (integer-shift, all real `r`) + both signposts remain DONE. No charter trigger
  fired (L4 additive, no forbidden import).

- 2026-08-24 (review lap): **B6 route pivot (hdom refuted).** Inventory (real
  `#print axioms`): build green 8757,
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

### Short-term (mirror PENDING_WORK top — image-Khinchin's tail-average SLLN, in `CFAeKhinchin.lean`)
- ✅ **LANDED this lap (bricks 1–2, axiom-clean):** `integral_blockCount_cross` (cross
  2nd-moment identity), `abs_cov_two_cyl_pair_le` (general two-cylinder covariance bound).
1. **`variance_truncated_le K M n`** — uniform-in-M variance of `S_n^M = Σ_{a<M} u_a·blockCount[K+1+a] n`:
   `|∫(S_n^M)² − (n·μ_M)²| ≤ n·(C₃+80C₁C₂)`. Split `Σ_{i,j}` diagonal (i=j: `n·Var(f_M)≤nC₃`,
   distinct cylinders disjoint) vs off-diag (fold brick 2 via `sum_range_dist_le`+`geom_trunc_sum_le`).
2. **`variance_logBirkhoffSum_le K n`** — MCT limit M→∞ on step 1 (`S_n^M ↑ logBirkhoffSum K n` a.e.
   from `logTailTerm_tsum_ae_eq` at each `Tⁱx`; `∫(S_n^M)²↑∫(logBirkhoffSum)²`, `μ_M→μ`).
3. **`chebyshev_logBirkhoffSum` + `ae_tail_average_tendsto`** — transcribe `chebyshev_blockCount` +
   `ae_orbit_freq` (`CFAeNormal.lean:81`); monotone gap-squeeze available (`logTailFn K ≥ 0`).
4. **Graft** `ae_khinchinTypical`'s co-null set into `exists_cfNormal_and_affine_family_cfNormal'`
   ⇒ image-Khinchin headline; re-`#print axioms` clean.

### Long-term
- After image-Khinchin: the campaign's headline set is complete. Possible further stretches
  (affine images of Khinchin-typical, etc.) detach freely but are not required.

### To completion
- B5′ (Track A + Tier 1 + Tier 2): **DONE**, all axiom-clean.
- B6 single-map + full affine family: **DONE**, all axiom-clean.
- image-Khinchin headline: gated on `ae_tail_average_tendsto` (4 items above); bricks 1–2 landed.

## Axiom ledger (fidelity spine — all from real `#print axioms`, 2026-08-25 review lap #3, HEAD `53e454c`+)

| headline theorem | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `exists_absolutely_normal_cf_normal` (**Tier 1 = Becher–Yuhjtman**) | uncond | trust triple | 🟢 DONE (re-verified this lap) |
| `exists_absolutely_normal_cf_normal_khinchin` (**Tier 2 headline**) | uncond | trust triple | 🟢 DONE (re-verified this lap) |
| `exists_cfNormal_and_affine_cfNormal` (**B6 affine image**) | uncond (q>0) | trust triple | 🟢 **DONE** (2026-08-25, measure route). Crux `ae_orbit_freq`→`ae_isCFNormal`→`exists_feasible_cfNormal_affine` (`CFAeNormal.lean`, sorry-free) wired into the headline; the false-crux schedule chain is dead code, kept marked REFUTED. |
| `exists_cfNormal_and_affine_family_cfNormal'` (**B6 Tier-2 full family**) | uncond (any `r`, q>0) | trust triple | 🟢 **DONE** (2026-08-25). Faithful Vandehey §7 Tier-2 statement; `volume_notCFNormal_univ` crux (non-CF-normal null on all ℝ). |
| `ae_khinchinTypical` / image-Khinchin headline | uncond | `+ sorryAx` | 🟡 OPEN — gated on `ae_tail_average_tendsto` (log-tail SLLN). Decorrelation bricks 1–2 landed axiom-clean this lap; variance→a.e. chain remaining. |
| `isNormal_iff_equidistributed_orbit` (Wall) | uncond | trust triple | 🟢 DONE |
| `isNormal_log_two_of_equidistributed` | cond (orbit equidist.) | trust triple | 🟢 DONE (hypothesis is the open conjecture, correctly a hypothesis) |
| `isNormal_two_stoneham23` (Stoneham) | uncond | trust triple | 🟢 DONE |
| `xstar_cf_freq_tendsto` (CF normality of x\*) | uncond | trust triple | 🟢 DONE |
| `xstar_dary_freq_tendsto` (d-ary simple normality, every base) | uncond | trust triple | 🟢 DONE |
| `pillai` (simple-to-all-powers ⇒ full normality) | uncond | trust triple | 🟢 DONE |
| `gaussMeasure_digit_cylinder` (Gauss–Kuzmin single-digit law) | uncond | trust triple | 🟢 DONE |
| `summable_gaussKuzmin_logsq` (Tier-2 moment seed) | uncond | trust triple | 🟢 DONE |

Math-axiom count (🟢+🟡+🟠, excluding trust base + native_decide artifacts):
**0** proven-but-cited axioms across all 10 B5′ headlines AND both B6 affine headlines
(single-map + full family) — every one 🟢, trust triple only. The only `+sorryAx` is
`ae_khinchinTypical` (image-Khinchin stretch), a **disclosed decomposition `sorry`**
(`ae_tail_average_tendsto`), NOT a cited math axiom — being actively discharged (the L²
variance route; decorrelation bricks landed this lap). No 🟡/🟠 debt on the proven
headlines, no 🔴. Trust triple = propext, Classical.choice, Quot.sound throughout.

## Pointers
DIRECTION.md (CURRENT DIRECTIVE) · ROADMAP.md · KHINCHIN.md (B5′ plan W1–W6) ·
JUDGE.md · papers/literature-review.md · newest HANDOFF (`ls HANDOFF-*.md | sort | tail -1`) ·
PENDING_WORK.md · papers/becher-yuhjtman-2019-*.md
