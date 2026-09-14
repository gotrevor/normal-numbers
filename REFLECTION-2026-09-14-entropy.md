# Reflection — 2026-09-14 (entropy expedition, deep reflection lap 37)

*Altitude lap, Opus/xhigh.  HEAD `1fe35d7`, branch `wip/g4-entropy`, `lake build` 🟢 **8970 jobs**,
working tree clean.  Every headline re-`#print axioms`-ed this lap from source (not from a handoff):
trust triple only, no local `axiom` anywhere in `src/`.  `src/` holds exactly two `sorry`s, both
pre-existing and off-campaign (`MahlerDriftOne.exists_prime_nonresidue`,
`PrimeLambertOscillation.phaseOscillation`).*

---

## 0. ROUTE VERDICT — **CONTINUE**, with the directive replaced

No registered trigger has fired.

| trigger (DIRECTION, review lap 23) | status |
|---|---|
| **E-T3** two laps stalled on one assertion ⇒ decompose | did **not** fire — laps 24–36 each closed a *named whole theorem* (`tendsto_occursCountT_primeLambertFour` L31, `log_det_one_add_tensorGram_ge` L34, `abs_posAvg_sub_le` L36) |
| **E-T4** generalized subadditivity unmeetable by the `ℓ`-block coordinates | did **not** fire — `tileCoord_injective` + `sum_block_deficit_tile_le` met it with **zero slack** (lap 29) |
| **E-T5** assembly needs a smaller deficit than `entropy_E1` delivers | did **not** fire — the assembly closed at `δ_K = 50√K`, and lap 34 proved that deficit is *structural* (`log_det_normalized_two_sided`), so the `ℓ = o(√K)` ceiling is a property of the object, not of the estimate |

False-summit tells, checked explicitly:
* **(a) recurring "the crux is almost cracked" with nothing closing** — absent.  Thirteen consecutive
  laps each landed a sorry-free, axiom-clean theorem.
* **(b) declining finishability across reflections** — the *normality* estimate did decline, but by
  **proof**, not by fatigue: `not_T_E` (lap 8) → `tendsto_density_compl_zero` (lap 18) →
  `qForces_normal_iff_density_one` (lap 20) → `sum_weight_le` (lap 22).  A refutation is not a stall.

**So this is not ESCALATE.**  What *has* gone wrong is narrower and real: **the CURRENT DIRECTIVE's
🎯 objective was met at lap 31, and laps 32–36 ran for five laps with no live objective**, choosing
their own (good) targets.  The laps 24–33 wrap says so in as many words — "the run's remaining scope
is a judgement call for an altitude lap, which owns `DIRECTION.md`" — and no altitude lap made it.
That judgement is this lap's first deliverable.

---

## 1. Is the DESTINATION still right?

**The expedition's own destination (brief §8) is reached.**  Restated and checked against the brief,
not against a handoff:

| brief §8 requirement | state |
|---|---|
| "an unconditional G4 sample-entropy/frequency theorem" | `entropy_E0`, `entropy_E1` (uncond., axiom-clean) + `tendsto_occursCountT_primeLambertFour` (word frequency `→ 2^{−ℓ}` at the sampled aligned positions of `G₄`, stated over `OccursAt 2 · v ·` — the very predicate `isDisjunctive_two` uses) |
| "a resolved primary transfer question — a proof, or a counterexample satisfying its exact premise" | `not_T_E` with `maskedReal G₄`, which satisfies `entropy_E0`/`entropy_E1` **verbatim** and is not normal.  `not_T_S`, `not_T_mix` likewise |
| "an unresolved bridge must remain visibly unresolved" | honoured: nothing in the repo claims normality of `G₄` |

**The larger destination — binary normality of `G₄` — is now closed on this route, by theorem, and
the closure is quantitative.**  This is the honest headline and it must not be softened:

1. `qForces_normal_iff_density_one` + `tendsto_density_compl_zero`: a satisfiable hypothesis about a
   *quantized* sample forces normality **iff** the digit positions it reads have density **one**.
2. `Sched.card_isSampled_le_real`: this schedule reads density `≤ 1/4`; `G4EntropyScales.sum_weight_le`:
   **every** admissible family of grids, over **every** set of scales, reads `≤ 1/8` together.
3. And the size of the gap is not a constant.  `key_size`'s own proof gives
   `Q·D₀ ≥ K·B^{2K}` against `H_K·m_K ≤ (2(K²+1))^K·K`, so the sampled density at scale `i` is
   `≤ ½·(2(K²+1)/B²)^K ≤ ½·(3/K⁴)^K` — exponentially small in `K log K`, not `2^{−(i+2)}`.
   Meanwhile `entropy_cover_bound` pins the window at `m ≤ K/4` **and** `η⁴ ≤ 2^{−K}` (i.e.
   `m ≥ K/4`): the machinery supports exactly `m_K = K/4`.  To read density `≥ 1/2` the window
   would have to be `≳ d_min/H_K ≈ K·K^{4K}` — **a factor `≈ K^{4K}` longer than the entropy proof
   admits.**

   The structural reason is visible in one field of `GridParams`: `hQdvd : ∀ m, 0 < m → m ≤ U → m ∣ Q`.
   The freezing modulus must be divisible by every integer up to `U ≥ B^K`, so `Q ≥ lcm(1,…,U)`,
   while the sample reads only `H_K·m_K` positions per period `2Q·K·U`.  *That* is the wall, and it
   is a property of the frozen-residue mechanism, not of any estimate inside it.

**Three escapes were considered and each is closed by something already proved** (recorded so the
next lap does not re-derive them):

* *Vary the frozen residue.*  The CRT condition is `b₀ ≡ t_α (mod d_α²)`; one may legitimately take
  `b₀ ≡ t_α + d_α σ_α (mod d_α²)`, giving `kIdx ≡ σ_α (mod d_α)` and a family of size `∏_α d_α =
  √Mprod`.  But the `n`-progression has modulus `P₀ ≥ Mprod = ∏_α d_α²`, so the position gaps are
  `2P₀/d_α` while the family only shifts by `< 2d_α`: short by `√Mprod`.  This is exactly what
  `sum_weight_le` already encodes.
* *Shift the real (`x ↦ 2^σ x`), i.e. move the window to `2·kIdx + σ`.*  This is the one axis
  genuinely **outside** the digit-locality barrier — the family `{E0 for 2^σ x : σ < Σ_K}` is local
  to `⋃_σ(S+σ) = ℕ`, and the lap-8 mask witness dies on it.  It fails on the arithmetic instead:
  `A_K{2^σ u} = 2^σ A_K u`, so the transported point is `2^σ F_K(n) + (1−2^σ)(θ−γ)` and the Fourier
  budget would have to hold to degree `2^σ·D_j` with `σ` up to `2P₀/d_α`.  Equivalently: `σ`-shifted
  windows are a longer window of length `σ + m`, which is the `LevelBudget` question, closed by
  `not_qForces_normal_of_levels`.
* *More scales.*  `sum_weight_le` sums the per-scale weights over **all** `(K,N)` and gets `1/8`.

**Recalibrated destination.**  Not normality of `G₄` on this mechanism — that is refuted as a
*method*, which is itself a result.  The realistic, valuable endpoint now is: **the strongest true
statement about `G₄`'s binary digits that this arithmetic actually supports**, stated in the
language normality is stated in.  That is what §2 names.

---

## 2. Are we attacking the highest-value thing?  (the new objective)

Read from altitude, the ledger says: every *negative* is proved and sharp; the *positive* side has
one rung built (single word, aligned positions, `t = 1`) and two rungs visibly available.  The
highest-value open statement — new mathematics about `∑_p 1/(4^p−1)`, unproved, load-bearing, and
reachable with the machinery already in the repo — is:

> **The sampled windows of `G₄` are asymptotically INDEPENDENT and uniform.**
> For every `t`, every partition of the atoms into `t`-blocks, and all words `w₁,…,w_t` of length
> `ℓ`, the frequency over `(n, block, positions)` of *"`G₄`'s block at `2·kIdx(n,α_s)+p_s` spells
> `w_s`, simultaneously for all `s ≤ t`"* tends to `2^{−tℓ}`.

Why this and not something else:

* **It is strictly stronger** than everything proved so far: `t = 1` aligned is lap 31, `t = 1` all
  positions is lap 36's abstract bound not yet rendered, and `t ≥ 2` is a genuine *correlation*
  statement — the sampled windows decorrelate.  Disjunctivity gives one word at a time; this gives
  arbitrary prescribed patterns at `t` prescribed sampled positions simultaneously.
* **It is what entropy is actually for.**  `entropy_E1` bounds the joint law of the *whole vector*;
  every result so far has projected it to one coordinate and thrown the joint content away.  This is
  the first statement that consumes the joint hypothesis as a joint hypothesis.
* **It is feasible with the existing toolchain, and the feasibility is checked, not assumed.**
  `FinLaw.H₂_le_sum_H₂_map` (Gibbs, joint injectivity) applies verbatim to a coordinate family
  indexed by *blocks* instead of atoms; partitioning `A` into `⌊|A|/t⌋` blocks of size `t` gives
  average deficit `≤ tδ` per block; the per-block pattern coordinate is the product of the `t`
  per-window tiling coordinates and is injective because each factor is; and
  `abs_avg_block_prob_tile_opt`'s second half (deficit sum ⇒ averaged TV bound, via the
  Hellinger-route Pinsker step) is already abstract in the deficit.
* **It is not blocked by any barrier** — it is a statement about the sampled positions, which is
  where the truth lives; it makes no normality claim and cannot be mistaken for one.

**Hardest-first, honestly applied.**  Nothing open is route-decisive any more — the route question
was *settled*, not deferred.  With no decisive-risk item left, "hardest" reduces to "most
mathematics per lap", and the joint theorem is that.  The genuinely uncertain step inside it, and
therefore the one to probe first, is **whether the per-block pattern coordinate keeps the deficit
additive** (E-T4's analogue at `t ≥ 2`): if `∑_blocks (tℓ − H₂(pattern coord)) ≤ t·Δ` fails, the
whole statement degrades to a `t`-dependent rate and must be re-stated, not patched.

**Secondary, bounded target** (take it if the main chain stalls twice, per E-T3): **measure the
wall**.  `Sched.density_le_pow`: the sampled density at scale `i` is `≤ ½(3/K⁴)^K`, and
`Sched.window_needed_ge`: any level function reading density `≥ 1/2` needs `mm i ≥ K^{4K}·m_K`.
Both are strengthenings of `key_size` by its own proof's slack, and they turn "astronomically
sparse" into a number.  That is the honest final form of the campaign's negative.

---

## 3. What a sharp outsider would say we're missing

1. **The joint law has been used only through its marginals.**  Three modules project `jointLaw` to
   one coordinate.  Nobody has asked what `H₂ ≥ m_K H_K − 50√K H_K` says about *pairs*.  It says they
   are nearly independent, and that is free.  (This is §2's objective; it is the single largest piece
   of mathematics left lying on the floor.)
2. **The negative results are stated qualitatively where they are provably quantitative.**  "Density
   `≤ 1/4`" is true but is `≤ ½(3/K⁴)^K`; "astronomically sparser" is true but is a factor `K^{4K}`.
   A negative result's value is its constant.
3. **`PENDING_WORK.md` is 493 KB / 7132 lines.**  No grind lap can read it, so grind laps navigate by
   HANDOFF momentum — which is precisely the failure mode that let laps 32–36 run objective-less.
   The ACTIVE section at the top is the only part that functions.  Keep writing *there* and let the
   rest be archive; do not extend the bottom.
4. **`papers/literature-review.md` had no entropy chapter** until this lap.  Added below (§5) so the
   next reflection inherits a source-grounded read rather than this file's own optimism.

---

## 4. Faithfulness at altitude

Re-read against the brief, not against a summary:

* `entropy_E0` / `entropy_E1` quantify over `gridOf K (N K)` at `k₄`-bit windows with `K = 4k₄` —
  the brief's `m_K = K/4`, **not** `Sched.m K`.  ✅ the §2 tripwire is honoured.
* `entropy_E1`'s subject is `jointLaw … (primeLambertAtBase 4)`, the law of the **whole vector**
  under **one** uniform `n ∈ P_K`.  ✅ not independent per-atom draws (the brief's other tripwire).
* `tendsto_occursCountT_primeLambertFour` is stated over `OccursAt 2 (primeLambertAtBase 4) v
  (2·kIdx(gridAt i) n c.1 + c.2·v.length)` — real digits of the real constant, at base-four orbit
  position `k` rendered as binary shift `2k`.  ✅ the factor 2 the brief warns about is present.
* `not_T_E`'s witness `maskedReal G₄` is checked to satisfy `E0` *and* `entropy_E1` verbatim, i.e.
  **the exact premise**, which is what the brief demands of a counterexample.  ✅
* No headline claims normality; `IsNormal` appears only inside refuted `Prop`s and the
  characterization.  ✅

**Transcription drift found: none.**

---

## 5. KEEP / STOP / NEXT

**KEEP**
* One named theorem per lap, rendered on real digits (`OccursAt`/`digitOf`), never left abstract.
* Committing a compiling skeleton with named `sorry` leaves early in the lap.
* Harvesting Lean gotchas into the session wrap — laps 24–36 produced two dozen verified ones.

**STOP**
* Running without a live objective.  When a directive's 🎯 is met, the lap that meets it says so in
  its handoff **and stops picking its own next target**; the next altitude lap sets one.
* Re-proving barrier variants.  The barrier is complete, sharp, and closed on three axes.
* Appending to the bottom of `PENDING_WORK.md`.

**THE SINGLE HIGHEST-VALUE NEXT TARGET** — the joint (`t`-wise) sampled-word frequency theorem for
`G₄`, in three rungs:

1. **Render lap 36 at the schedule** (`G4EntropyPosition.lean`): `posFreq`,
   `abs_posFreq_sub_le_of_deficit`, the `E0`/`entropy_E1` instances, `blkAt`→general-`p` digit
   rendering, endpoint `tendsto_occursCountP_primeLambertFour` — every finite binary word occurs with
   frequency `2^{−|w|}` among **all** positions of `G₄`'s sampled windows.  This is `t = 1` of the
   target and the currently dangling thread (lap 36 proved the bound and never connected it to `G₄`).
2. **The abstract `t`-wise capacity bound** (`G4EntropyJoint.lean`): block the atoms into `t`-blocks,
   the per-block pattern coordinate, joint injectivity, `∑_blocks (tℓ − H₂) ≤ tΔ`, and the averaged
   `2√(log 2·tℓ·tδ/…)` bound.
3. **The schedule instance and the digit rendering** of rung 2 — `tendsto_occursCountJoint_…`.

**Why this ordering**: rung 1 is reused verbatim by rung 3's rendering (the general-`p` `blkAt` lemma
is needed by both), and rung 2's uncertain step is probed as early as possible.
