# HANDOFF 2026-11-03/04: perfect-power Lambert constants are RICH (DONE)

Branch `wip/rich-power-lambert`, worktree `~/src/nn-rich`.  Kickoff:
`KICKOFF-2026-11-03-rich-power-lambert.md`.

## Result

`NormalNumbers.ArithmeticDisjunctivity.isRich_powerLambert` (frozen statement, byte-identical)
is proved, so `powerLambert_rich_not_normal` is unconditional: for `b, r ≥ 2`,
`Σ_{n≥1} 1/(b^{n^r} − 1)` is rich (every base-`b` word has positive lower frequency) and not normal.

    #print axioms isRich_powerLambert
      [propext, Classical.choice, Quot.sound]
    #print axioms powerLambert_rich_not_normal
      [propext, Classical.choice, Quot.sound]

`src/NormalNumbers/PowerLambertRich.lean` is sorry-free and is now imported from the root
(together with `PowerLambertRichCount` and `PowerLambertRichOrbit`); full `lake build` is green
(10955 jobs, barrier audit passes).

## Proof route (simpler than the kickoff's)

Files: `PowerLambertRichCount.lean` (arithmetic), `PowerLambertRichOrbit.lean` (orbit split),
`PowerLambertRich.lean` (assembly).

* No rational head: `S = coefficientValue (powerDivisorCount r) b`.  `orbit_powerLambert_eq`:
  `orbit n = {periodicTail Q n + aperiodicTail Q n}`; `periodicTail_add_mul` is exact periodicity.
* `Q = (D!)^r`.  The kickoff's `p`-adic incompatibility step (b) is unnecessary:
  `card_filter_dvd_add_mul_le` bounds `#{k<K : M ∣ m₀ + kQ} ≤ K m₀/M + 1` since
  `gcd(M,Q) ∣ m₀`.  Summing (`sum_aperiodicPowerCount_le`, `sum_aperiodicTail_le`):
  `Σ_{k<K} R(n₁+kQ) ≤ C(2K/(D+1) + √(KQ+1))`, `C = Σ_j (n₁+1+j)/b^{j+1}`.
  `r ≥ 2` enters only via `d^r ≥ d²` (the `√` boundary term and `Σ 1/d² ≤ 2/(D+1)`).
* Witness: disjunctivity on the middle third of the `w`-cylinder (no guard digits).
* `fract_add_mem_Ico_of_close`, Markov `card_le_two_mul_card_filter_lt`,
  `exists_progression_occursAt_powerLambert`, `eventually_le_card_filter_of_progression`
  (lower density `≥ 1/(4Q)`).

## Environment notes

* The pre-commit hook runs a full `lake build` with 6 CPUs; on this box that intermittently hits
  `Too many open files` (host virtiofs limit), not a code error.  `taskset -c 0-2 lake build`
  succeeds.
* `pgrep -f "lake build"` matches the claude process itself (its argv contains the phrase);
  use `pgrep -x lake`.

## Next (optional, not the gate)

`PowerLambertFrequencies.lean` (conjecture node `PowerLambertFrequenciesExist`) is the stretch
target the kickoff allows once the headline lands.  The same decomposition (periodic part exact,
non-periodic part `O(1/D)` in mean) is the natural route: frequencies of the `Q_D`-periodic model
converge as `D → ∞`, and the averaged bound here controls the difference in `B¹`.
