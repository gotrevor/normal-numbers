# HANDOFF — entropy expedition, lap 1 (2026-09-14, Opus grind)

Branch `wip/g4-entropy`.  Spec: `BRIEF-entropy-expedition-2026-09-14.md`, staging in
`KICKOFF-2026-09-14-entropy-expedition.md`, DIRECTION override at the top of `DIRECTION.md`.

## 1. What was proved / refuted / narrowed

All three new modules are **sorry-free** and carry no new axioms.

### `src/NormalNumbers/G4EntropyInfo.lean` — brief §2 (entropy convention) + §4 (info set)

- `FinLaw Ω` : a probability vector on a `Fintype`.  `H₂ = (∑ negMulLog p)/log 2`; the
  zero-mass convention is mathlib's `negMulLog 0 = 0`, not a hand-rolled one.
- **`FinLaw.prob_infoSet_ge` — THE INFORMATION-SET LEMMA.**  `H₂ L ≤ (1−δ)M`, `0<δ<1`, `0<M`
  ⟹ the set `{ω : 2^{−(1−δ/2)M} ≤ p ω}` carries mass `≥ δ/(2−δ)`.
- `FinLaw.card_infoSet_le` : that set has `≤ 2^{(1−δ/2)M}` elements.
  Together these are exactly the brief's §4 display, and they are the first load-bearing piece.
- `FinLaw.mul_prob_compl_infoSet_le` : the Markov step, `θ·Pr[outside] ≤ H₂`.  Proved through
  the *pointwise* inequality `θq ≤ negMulLog q / log 2` for `0 ≤ q ≤ 2^{−θ}`, which is true at
  `q = 0` by inspection — so `−log 0` is never formed and no `ℝ≥0∞` detour is needed.
- `FinLaw.H₂_le_logb`, `H₂_le_logb_card` : maximum entropy, via `negMulLog s ≤ 1 − s`.
- `empirical S hS f` : the law of `f i` for `i` uniform in a nonempty finite sample — the
  pushforward of ONE uniform choice.  `H₂_empirical_le : H₂ ≤ log₂|S|`.

### `src/NormalNumbers/G4EntropySample.lean` — brief §2 (freeze the sample)

- `kIdx G n α = (n − t_α)/d_α`, and **`kIdx_spec`**: on `P = apSample X G.P₀ G.b₀`,
  `n = t_α + d_α·kIdx G n α` **and** `d_α ∣ kIdx G n α`, from `GridParams.exists_mult_mul`.
  Natural subtraction/division appear only inside that proved domain.
- `uSample G x n α = fract(4^{kIdx} x)`, `ZSample G m x n α = ⌊2^m u⌋₊`, `ZSample_lt`,
  `apSample_nonempty` (`b₀ < X` suffices).
- `blockVal y j m = ∑_{i<m} digitOf 2 y (j+i)·2^{m−1−i}`, with two elementary floor identities
  proved for every `0 ≤ y`: `floor_two_pow_succ`, `floor_two_pow_add`.
- **`ZSample_eq_blockVal` — THE DICTIONARY.**  `ZSample G m x n α = blockVal (fract x) (2·k) m`:
  `Z` is exactly the `m`-bit binary window at zero-based position `2k`.  The factor two is the
  base-four ↔ base-two shift; losing it changes the sampling law.
- `blockVal_eq_of_occursAt` : ties `blockVal` back to `OccursAt`/`digitOf`, the language of
  `IsDisjunctive`/`IsNormal`.
- `ZVec` (into `G.Atom → Fin (2^m)`), `jointLaw` = `empirical` over `P_K` — the pushforward of
  one uniform `n`, never per-atom independence.  Both halves of the sanity bound:
  `H₂_jointLaw_le_mul : H₂ ≤ m·|Atom|` and `H₂_jointLaw_le_card : H₂ ≤ log₂|P_K|`.

### `src/NormalNumbers/G4EntropyCapture.lean` — brief §3C (start on (C))

- **`abs_sampleAvg_sub_integral_le`** : the two-sided transfer `|sampleAvg f − ∫f| ≤ 2κ + Λδ₃`.
  The existing `separating_test_bound` proof already established this but discarded one side at
  its last step; here it is extracted as the reusable statement.  `G4SeparatingTest.lean` is
  untouched; `separating_test_bound_of_transfer` recovers the old conclusion as an instance.
- The **bounded-Lipschitz bump** `bump E ρ y = 1 − min 1 (infDist y E / ρ)` on any pseudo-metric
  space: `bump_nonneg`, `bump_le_one`, `bump_eq_one_of_mem`, `bump_eq_zero_of_not_mem`
  (off `thickening ρ E`), **`bump_sub_le`** (`bump y − bump z ≤ dist y z / ρ`), `continuous_bump`,
  `integrable_bump`, `integral_bump_le` (`∫ bump ≤ μ(thickening ρ E)`).
- **`capture_inequality` — (C) in abstract form.**  For `Good ⊆ P` with `F n ∈ E` on `Good`:
  `|Good|/|P| ≤ μ(thickening ρ E) + a/ρ + 2κ + Λq`, `a ≥ avg_n dist(F n, S n)`.
  It is an unconditional comparison of two expectations — nothing is conditioned on membership
  in `Good`, which is precisely what licenses a data-dependent choice of `ℬ` later.

## 2. Which bottleneck moved

The brief's §3C asked for a bounded-Lipschitz/arbitrary-compact-set version of the separating
test with the old one recovered as an instance.  That is done, and it turned out to need **no
new estimate at all** — the old proof was already two-sided, and the only new mathematics is the
bump's Lipschitz drop.  So the cost of (C) is now entirely in the three *inputs*:

  (i) `μ(thickening ρ E_K(ℬ))` — brief §3B, the joint-box cover bound (G);
 (ii) `a_K = avg dist(F_K(n), S_K(n))` — must be recovered from the actual remainder bounds
      (`G4Remainder`, `G4FarTail`), NOT from the old fixed 1/8 allowances;
(iii) `κ_K, Λ_K, q_K` — `G4Jackson` + the Fourier decay, at the proposed degree
      `D_K = (16K²2^{m_K})²`.

No quantifier changed and no new assumption was introduced: `capture_inequality` takes the
transfer as a hypothesis, and `abs_sampleAvg_sub_integral_le` discharges it from exactly the
hypotheses `G4Wiring` already supplies for the disjunctivity endpoint.

## 3. Next bounded test (lap 2)

1. **Instantiate `capture_inequality` on the torus** with `Ω = (ℝ/ℤ)^{r_K}`, `F = F_K`,
   `S = S_K`, feeding `abs_sampleAvg_sub_integral_le` from the `G4Wiring` character family.
   The bounded test is `bump (E_K ℬ) ρ_K`; the only genuinely new obligation is that `G4Jackson`
   approximates *this* test (it is `1/ρ`-Lipschitz and `[0,1]`-valued) to within `κ_K`.
   That is brief §3C's "extract the bounded-Lipschitz version of the Jackson bound".
2. **Then §3B (G)**: the cover of `E_K(ℬ)` by `|ℬ|` transported boxes, reusing `G4TubeVolume`,
   `G4GridTube`, `G4Ellipsoid`, `G4Tensor` — with `|ℬ|` (the number of *joint* boxes) replacing
   the current `Bs.card ^ H` product-cover factor.  Do not replace `ℬ` by the product of its
   coordinate projections; that erases the entropy saving.
3. §3A (exact transported sample, expose the identity inside `coe_sum_dilatedTailB` /
   `propA_of_progression` without changing the old endpoint) is needed before (C) can be
   instantiated for `x = G4`; it is independent of 1 and 2 and can be done in parallel.

## Build state

`lake build` green, 8941 jobs.  `src/` gains three sorry-free modules; no existing declaration
was modified.  `G4ScheduleAssembly.isDisjunctive_four` / `isDisjunctive_two` untouched.

---

# Lap 2 + lap 3 addendum

**Lap 2** (`e0fa0d5`): `G4EntropyJackson.lean` — Fejér smoothing for an arbitrary continuous,
`[0,1]`-valued, `dAv`-Lipschitz test (`jackson_of_dAvLipschitz`, `jackson_of_clipTest`), with
`κ = 1/(ρ√(D+1))` and `Λ = (2D+1)^r` **independent of the set `E`**; `Frame.propJackson`
recovered as `propJackson_of_general`.  `G4EntropyFrame.lean` — `capture_inequality_torus` and
`Frame.capture_le`: (C) on the torus in the average metric, every input from existing machinery.

**Lap 3**: `G4EntropyCover.lean` — **(G)**.  `jointBox`/`boxUnion`/`imageOfSet`,
`tube_subset_pieces_joint`, and `volume_tube_le_joint`:

  `vol(tube (E 𝓑) res) ≤ ∑_{G, |G| ≥ (1−ε)r} |𝓑| · η^{|G|} · vol([A_G,I_G]·cube)`.

The cover factor is `|𝓑|` — the number of **joint** boxes — where the old product cover paid
`(#Bs)^H`.  `volume_tube_le_of_joint` recovers the old statement as the instance `𝓑 = Bs^H`
(via `tube_mono`), so nothing the product cover proved is lost.  The mechanism is unchanged:
Markov in `dAv` picks the good coordinate set, the determinant/ellipsoid bound handles the
piece cube; only the indexing of the cover changed.

So (C) and (G) are both proved, with exactly the shape the information-set lemma consumes:
`N` joint boxes cost `N` in the cover and carry mass `≥ δ/(2−δ)` when `N ≤ 2^{(1−δ/2)mH}`.

**Next (lap 4): §3A, the exact transported sample** — the last structural gap.  `capture_le`
needs `Ffull n ∈ E 𝓑` for the particular atom vector `u^{G4}_{K,α}(n)`, not just membership in
the orbit-closure image that `gridFrame_propA` provides.
