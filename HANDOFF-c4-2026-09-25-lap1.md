# HANDOFF C4 — 2026-09-25 lap 1

Worktree `~/src/nn-c4`, branch `wip/c4-infinite`.  Target `src/NormalNumbers/AbelianWindowSets.lean`.

## Directive conflict (read first)
Repo-root `DIRECTION.md`'s CURRENT DIRECTIVE is dated 2026-09-23 and points at
`PrimeModelFamilyGraded.lean` (Theorem C′).  `KICKOFF-2026-09-24-c4.md` is newer, was ratified on
this branch (`cafe6e1`), and is the operator's named objective for this run, so this lap worked C4.
An altitude lap should refresh `DIRECTION.md`; I did not edit it.

## This lap's advance
**Necessity is DONE.**  `abelianAt_one_of_abelianAt` is sorry-free, `#print axioms` = the three
standard ones.  New supporting API in `AbelianWindowSets.lean`:
- `symParityMean_tendsto_zero_of_abelianAt` / `abelianAt_of_symParityMean` — the two halves of
  `isAbelianNormalTwo_iff_symParityMean` specialised to ONE window length `L` (the mathlib-side
  statement quantified over all `L`, useless against a single-`L` hypothesis).
- `digitSign`, `abs_shift_sum_sub`: `|∑_{n<N} (-1)^{s(n+i)} − ∑_{n<N} (-1)^{s n}| ≤ 2i`, by
  induction on `i` off `sum_range_succ` / `sum_range_succ'`.
- `abs_symParityMean_one_sub`: `|symParityMean s L 1 N − L·parityMean s {0} N| ≤ 2L²/N`.
Chain: abelian at `L` ⇒ first symmetrized correlation → 0 ⇒ (boundary estimate) digit-sign mean
→ 0 ⇒ abelian at 1.

**`S = ∅` branch of `c4_realizable` is DONE** (`not_isAbelianAt_zero_fun`: the all-zeros sequence
has `onesFreq _ L 0 N ≡ 1 ≠ 1/2^L`).

**Crux isolated** as the single remaining `sorry`: `c4_realizable_of_mem_one`.

## The crux, in usable coordinates
For a sequence whose parity correlations `c T = lim parityMean s T N` exist:
`IsAbelianAt s L ↔ ∀ 1 ≤ j ≤ L, F j L = 0` with `F j L = ∑_{T ⊆ [0,L), |T| = j} c T`.
Shift-invariance ⇒ `c` depends on the shape of `T` only.

*Mechanism.*  `F 1 L = L·c{0}` (this is precisely the necessity theorem).  If only pair
correlations were nonzero, `ρ d = c{0,d}` gives `F 2 L = ∑_{d=1}^{L-1} (L−d)·ρ d`, whose SECOND
DIFFERENCE is `F2(L+1) − 2F2(L) + F2(L−1) = ρ L`.  So `F 2` can be an ARBITRARY sequence with
`F2(0) = F2(1) = 0` — exactly matching the admissibility hypothesis `S = ∅ ∨ 1 ∈ S`.  Pick
`F2(L) = 0` for `L ∈ S`, tiny `≠ 0` otherwise, read off `ρ = Δ²F2`.  This is why C4 should be
true, and it is the intended engine.

*Sub-approach REFUTED this lap.*  There is no stationary `±1` process with pair correlations only:
the length-`n` Fourier expansion `2^{-n}(1 + ∑_{a<b} ρ(b−a) x_a x_b)` goes negative once
`n·∑_d |ρ d| > 1`, and stationarity forces `n → ∞`.  So `F j` for `j ≥ 4` cannot be killed
correlation-by-correlation; they must be killed as symmetrized SUMS.

*Next attack (block-i.i.d. at many scales).*  I.i.d. blocks of length `m` with a uniform random
offset kills every `c T` whose trace on some block has odd size (the within-block law
`2^{-m}(1 + ∑ ρ_{ab} x_a x_b)` is legitimate for finite `m` as soon as `∑|ρ| ≤ 1`), leaving
`ρ̃ d = ρ d·(m−d)/m` supported on `d < m`, and `c T ≠ 0` only when `T` splits into dominoes lying
inside blocks — so `F j` for `j ≥ 4` is `O(ρ²)` and computable in closed form.  Single-scale
defect: `ρ̃` finitely supported ⇒ `F 2` eventually affine ⇒ only rigid `S`.  Infinite `S` therefore
needs a product/concatenation over infinitely many scales `m_1 ≪ m_2 ≪ …`, each stage fixing the
lengths it owns and perturbing decided lengths by a summable amount.  Next lap: compute `F 4` for
the single-scale block process exactly and see whether a second free parameter (a within-block
4-point term) can zero it simultaneously with `F 2`; that settles whether one scale can serve a
finite `S` at all.

## Lap 2 addendum (same session)
**Route found and probed: PERIODIC witnesses.**  `probes/c4_periodic_words.py` (stdlib, with a
de Bruijn known-answer check) enumerates all cyclic binary words of length `D` and reports
`G(v) = {L ≥ 1 : abelian at L}`.  Because a period-`D` sequence has only `D` distinct windows,
`G(v) ⊆ [1, D−1]` automatically — a periodic sequence fails abelian at every large `L` for free.
Results: `D = 16` realizes `∅, {1}, {1,2}, {1,3}, {1,4}, {1,2,3}, {1,3,4}, {1,2,3,4}`; the one
admissible subset of `[1,4]` it misses, `{1,2,4}`, IS realized at `D = 64` (hill-climb, word
recorded in the probe run).  **Every admissible finite set probed is realizable, and no
obstruction to `{1,2,4}` appears in the correlation coordinates** (`L=2` gives `ρ1 = 0`, `L=4`
gives `ρ3 = −2ρ2`, and `L=3` fails as soon as `ρ2 ≠ 0`).  Confidence C4 is TRUE: high for finite
`S`, moderate for infinite `S`.

**Lean landed this lap** (all green, `AbelianWindowSets.lean`):
- `ind`, `sum_ind_eq_card`, `ind_shift_mul`, `sum_ind_period`,
  `tendsto_ind_freq` — a general lemma: the empirical frequency of a `D`-periodic decidable
  predicate converges to its exact period average, with the explicit `2D/N` rate.
- `onesCount_periodic`, `tendsto_onesFreq_periodic`,
  **`isAbelianAt_periodic_iff`** — for a `D`-periodic `s`, `IsAbelianAt s L` is EXACTLY the finite
  arithmetic condition `#{r < D : onesCount s L r = j} / D = C(L,j) / 2^L` for all `j ≤ L`.
  This turns the analytic headline into finite combinatorics on cyclic words and is reused by
  both the finite-`S` and the infinite-`S` routes.

**Next attack.**  (a) Finite `S`: give a *construction* (not a search) of a cyclic word of length
`D` realizing a prescribed admissible `S ⊆ [1,k]`; the de Bruijn word of order `k` realizes
`{1,…,k}` (every `k`-word once ⇒ every `L`-word exactly `2^{k−L}` times), so the question is how
to delete prescribed lengths — likely by a product/XOR of a de Bruijn word with a length-`m`
pattern. (b) Infinite `S` needs aperiodicity: concatenate `w_k^{R_k}` with `R_k` growing fast,
where `w_k` is exact at all `L ≤ k`; boundary error is `O(1/R_k)` so every `L`-frequency
converges.  `isAbelianAt_periodic_iff` is the stage-`k` input to that.

## Lap 3 addendum
**Generator family identified: the AP-defect processes.**  `probes/c4_ap_defect_family.py`
(known-answer checked).  `P_{m}`: digits i.i.d. uniform except on one arithmetic progression of
difference `m` (uniform random offset `θ ∈ [0,m)`), which carries a prescribed stationary pattern
process `Q` with a random phase.  Then `c T = 0` unless all of `T` is congruent mod `m`, and
`c T = (1/m)·c_Q(T/m)` when it is.  Consequences:

* `F_j^{(m)}(L) = (1/m) ∑_{r<m} F_j^Q(n_r(L))`, `n_r(L) = #{i<L : i ≡ r mod m}`.  So `P_m` is
  abelian at EVERY `L ≤ m` for free, whatever `Q` is.
* **Renormalisation.**  If `m ∣ L` then every `n_r = L/m`, so `F_j^{(m)}(L) = F_j^Q(L/m)`:
  `P_m` is abelian at `L` iff `Q` is abelian at `L/m`.  `G(P_m) ∩ mℕ = m · G(Q)`.  This is the
  self-similar handle that should generate INFINITE `S`.
* Mixtures `∑ α_m P_m` (α ≥ 0) are shift-invariant and `F_j` is linear in α, so the design
  problem is a nonnegative linear program.

**Sub-approach constrained (recorded, not fatal).**  With the *alternating* inner pattern
`Q = 0101…`, `F_2^{(m)}(L) < 0` for EVERY `L > m` (verified for `m ≤ 5`, `L ≤ 12`).  Since mixture
weights are nonnegative, a mixture of alternating AP-defects is abelian exactly on `[1, min{m :
α_m > 0}]` — only initial segments.  Fix: the inner pattern is a free parameter; a mean-zero
pattern with POSITIVE short autocorrelation (e.g. `000111`, `A(1) = 1/3`) gives `F_2 > 0` just
above `m`.  Both signs are therefore available and the LP is not sign-degenerate.

**Lean landed this lap** (green): `altSeq n = n % 2`, `onesCount_altSeq_ne_zero`,
`not_isAbelianAt_altSeq`, `isAbelianAt_altSeq_one`, and **`c4_realizable_singleton_one`** — the
first nontrivial instance of the crux, `S = {1}`, proved end-to-end through
`isAbelianAt_periodic_iff`.  (The `L ≥ 2` failure uses `j = 0`: a window of length `≥ 2` of
`0101…` always contains a one, so the weight-`0` frequency is `0 ≠ 2^{-L}`.)

**Next attack.**  Formalize the AP-defect at scale `m` as a *sequence* operation:
`interleave m Q t` = a normal sequence `t` overwritten on the AP `m ∣ n` by `Q`.  The
renormalisation `G(interleave m Q t) ∩ mℕ = m · G(Q)` is the lemma to aim at; with `m = 2` it
already gives infinitely many new `S` by recursion, which is the infinite-`S` crux.
