# HANDOFF — entropy lap 39 (measure the wall), 2026-09-14, Opus

**Branch** `wip/g4-entropy`.  `lake build` 🟢 **8974 jobs**.  New module sorry-free and
`#print axioms`-clean (trust triple).  No pre-expedition file edited.

## 0. The lap in one line

The directive's **bounded secondary — "measure the wall"** — is done, and the wall is *larger*
than the reflection estimated: the sampled density per scale is `≤ ⅛(2/K⁶)^K`, not `½(3/K⁴)^K`.

## 1. What was proved — `G4EntropyWall.lean`

`cube_le_gridB` (`K³ ≤ B`) is not tight: the schedule's own `N K = 100K²` makes
`B = K²(K+N)+1` **quartic**.

```
quartic_le_gridB              100·K⁴ ≤ gridB K (N K)
density_le_pow                8·(B²)^K·#{scale-i sampled positions < L} ≤ (K²+1)^K·L   (ℕ)
density_le_pow_real           #{…} ≤ ⅛·(2/K⁶)^K·L                                      (ℝ)
levelBudget_of_le_superpow    (∀ i, mm i ≤ K^{4K}·m_K) → LevelBudget mm
window_needed_ge              L/4 < #{sampled < L}  ⟹  ∃ i, K^{4K}·m_K < mm i
not_qForces_normal_at_superpow
```

Read against `qForces_normal_iff_density_one`, which needs density **one**: one scale of the
implemented schedule reads a `⅛(2/K⁶)^K` fraction of the digits, and *any* level function must
read `K^{4K}` times the implemented window `m_K = K/4` per sampled time before the counting
argument can even fail — failing it being necessary, not sufficient.  This strictly supersedes
`not_qForces_normal_at_pow`, which spent only `B^K ≥ K^{3K}`.

## 2. Which bottleneck moved

Nothing is open in the directive's ACTIVE scope any more: rungs 1–3 (laps 37–38) closed the 🎯
objective, and this lap closed the bounded secondary.  Per **E-T7** this lap does not pick its
own next target; the next altitude lap sets one.

## 3. Lean notes harvested this lap

- `Nat.pow_pos` takes ONE explicit argument: `Nat.pow_pos (Nat.pow_pos hBpos) : 0 < (B^2)^K`.
- `push_neg` is deprecated in this toolchain; `simp only [not_exists, not_lt] at h` is the
  drop-in for `¬ ∃ i, a < f i`.
- `field_simp` on `(1/8)·(2^K/Q)·L = (2^K·L)/(8·Q)` closes it alone; a trailing `ring` then
  errors with "No goals".
- To divide a product inequality by a positive factor, build `Pr * lhs ≤ Pr * rhs` with
  `nlinarith` from the two scaled hypotheses and finish with `le_of_mul_le_mul_left _ hPR`;
  `nlinarith` will not do the division itself.
