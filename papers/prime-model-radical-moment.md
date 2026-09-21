# The arithmetic moment budget (discharged)

`src/NormalNumbers/PrimeModelRadicalMoment.lean`, namespace
`NormalNumbers.PrimeModel.Radical`.  No `sorry`, no `axiom`;
`#print axioms` = `[propext, Classical.choice, Quot.sound]`.

`radical_box_tail` (PrimeModelRadicalTail) carried the moment budget
`∑ i, ((p i)^α − 1)/(p i) ≤ A` as a hypothesis.  It is now proved for the
intended parameters.

* `theta_le` : `θ(N) = ∑_{p ≤ N} log p ≤ N log 4`, read off from mathlib's
  `primorial_le_four_pow`.
* `mertens_crude` : `∑_{p ≤ N} (log p)/p ≤ 4 log N` for `N ≥ 2`.  Dyadic strong
  induction `N ↦ M = ⌊N/2⌋`: on the top block `(M, N]` every prime has
  `1/p ≤ 2/N`, so the block is at most `(2/N)·θ(N) ≤ 2 log 4 = 4 log 2`, and
  `2M ≤ N` gives `4 log M + 4 log 2 ≤ 4 log N`.  Base cases `N = 2, 3`.
* `exp_sub_one_le_two_mul` : `exp t − 1 ≤ 2t` on `[0, 1/2]`, via
  `1 − t ≤ exp(−t)`.
* `radical_moment_budget` : for injective `p : ι → ℕ` with every `p i` prime
  and `p i ≤ y`, `0 < y`, `log y ≥ 2`, and `α = 1/(2 log y)`, the budget sum is
  `≤ 20`.  (The proof actually yields `≤ 4`: `p^α − 1 ≤ 2α log p` since
  `α log p ≤ 1/2`, then `2α · 4 log y = 4`.)
* `radical_box_tail_exp20` : `radical_box_tail` at that `α` with the budget
  discharged — mass outside `B(T)` is `≤ k · exp 20 / T^(1/(2 log y))`, with no
  moment hypothesis left.

## Note on the Mertens input

The kickoff suggested `PrimeNumberTheoremAnd.IEANTN.Mertens.sum_log_prime_div_eq_log`
(`|∑_{p ≤ y} log p/p − log y| ≤ log 4 + 4`).  That package is **not** a
dependency of this project (it is absent from `lake-manifest.json`, and its
`Mertens.olean` is not built), so the crude bound `≤ 4 log N` is proved here
from mathlib alone.  It is looser than `log y + log 4 + 4` but ample: the
budget lands at `4`, far under `20`.  This also corrects the older tail note,
which quoted a `2 log y` prime bound as if it were supplied.

## Remaining obligations (unchanged by this lap)

General CRT counting; two-sided sieve discrepancy `δ` (fundamental lemma);
phase decay; final constants.  This is a selected-prime shortcut layer, **not**
G4 normality.  SECONDARY is **done**: `jointModel R k q (r,s) = weight k q s / |R|`,
`jointModel_nonneg`, `jointModel_mass_one`, `jointModel_tail` (the joint tail
outside `R × B(T)` equals the state-only tail — the uniform residue factor
integrates out), and `radical_joint_phase_transfer`, which composes
`probability_complement_phase` on `R × states` with `radical_box_tail_exp20`
to give `≤ 2 k exp 20 / T^α + 2 δ` from a retained **joint** `L¹` discrepancy
`δ`.  The actual law `ν` is an arbitrary normalized nonnegative law: its
residue marginal is *not* assumed uniform, and `f` may depend on `r` (so the
small-prime phase factor may).
