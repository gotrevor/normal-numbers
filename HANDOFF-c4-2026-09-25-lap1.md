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
