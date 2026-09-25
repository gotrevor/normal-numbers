# HANDOFF c3-mrt 2026-09-25 lap56 — obligation A, brick 1: the CRT layer along a progression

**New file** `src/NormalNumbers/C3MrtProgForms.lean` (chain tip:
`lake build NormalNumbers.C3MrtProgForms`, 8987 jobs).  Sorry-free, 7 declarations, trust triple.
`lake build` green (9257).

## The structural point that makes obligation A cheap

`ProgressionLogRung K` (lap 55, obligation A) needs the `K`-fold chain re-run with `n` restricted
to `n ≡ n₀ (mod M)`.  I expected a five-file transcription.  It is much less, because:

> the entire `K`-fold chain runs on ONE fact about its index set — that the joint progression
> `{n : ∀ i, d i ∣ n+i+1}` is a single residue class mod `L`.  Intersecting with `n ≡ n₀ (mod M)`
> gives a single residue class mod `L' = lcm(M, lcm d)`: **same shape, larger modulus**.  And
> nothing downstream needs `L'` to be the LEAST common multiple:
> * `multi_forms_det` (lap 39) only asks `d_i ∣ L'`, so the forms `(L'/d_i)X + (a+i+1)/d_i` stay
>   nondegenerate — determinant `L'(j−i)/(d_i d_j) ≠ 0`;
> * every mass estimate *improves* when the modulus grows (`1/L' ≤ 1/L`), and the exchange bound
>   `∏ d_i ≤ K^{K²}·lcm(d) ≤ K^{K²}·L'` survives verbatim.
>
> So the extra progression is **free for the estimates** and costs only the reindexing.

## What landed

* `progLcm M d = lcm(M, Finset.univ.lcm d)`, `progLcm_pos`, `dvd_progLcm`, `mod_dvd_progLcm`.
* `joint_class_prog` — the intersected CRT statement
  `(n ≡ n₀ [MOD M] ∧ ∀ i, d i ∣ n+i+1) ↔ n ≡ n₀ [MOD progLcm M d]` (uses `Nat.mod_lcm`).
* `joint_base_prog` — the base point `a = n₀ % L'` is `< L'` and satisfies both constraints.
* `nondegenerateForms_prog` — `nondegenerateForms_of_tuple` at an arbitrary common multiple.
* `inner_sum_prog_forms` — the reindexed inner sum, in exactly the shape
  `initial_segment_bound_of_kElliott` consumes, with `L'` for `L`.
* `inner_sum_prog_empty` — the tuples with no joint solution.

## NEXT — obligation A, brick 2

The mass layer.  `joint_multi_harmonic_mass` (`C3MrtMultiMass`) and `kfold_lcm_mass_le`
(`C3MrtMultiTupleMass`) need restating over the class mod `progLcm M d`.  Both go through
`class_harmonic_mass` (`C3MrtTwoShift`), which is already stated for an arbitrary modulus — so the
change is: feed it `progLcm M d` instead of `Finset.univ.lcm d`, and note
`∏_s d_s ≤ K^{K²}·lcm(d) ≤ K^{K²}·progLcm M d` (`prod_le_lcm_mul_pow` then `Nat.le_of_dvd` on
`lcm d ∣ progLcm M d`).  The `(m+1)/d_0` head term is unchanged.
After that: `multi_truncation_telescope` (unchanged — it quantifies `F`, `S`, `α`, `β` internally,
and the progression only shrinks `S`), then `multi_full_sum_bound`, `inner_multi_bound`,
`multi_bound_of_rung`, `multi_correlation_of_uniform_rung`.

**Watch for**: the truncation identity `sum_pow_omega_multi_eq` expands `∏ z_i^{ω(n+i+1)}` into a
sum over tuples `d` of inner sums over the *joint progressions*; restricting `n` to a class mod `M`
commutes with that expansion trivially (it is a restriction of the outer index set), so the
telescope's `S ⊆ range M` hypothesis just becomes `S ⊆ {n ∈ range M | n ≡ n₀ mod M}`.  No new
estimate is needed — confirm this when brick 2 lands.
