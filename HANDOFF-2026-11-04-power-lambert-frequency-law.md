# HANDOFF 2026-11-04: the word-frequency law of the perfect-power Lambert constants is computable (DONE)

Branch `wip/power-lambert-frequencies`, worktree `~/src/nn-freq`.  Kickoff:
`KICKOFF-2026-11-04-power-lambert-frequency-law.md`.  Gate
`sorry-free:src/NormalNumbers/PowerLambertFrequencyLaw.lean`: met.

## Result

Both frozen theorems of `src/NormalNumbers/PowerLambertFrequencyLaw.lean` are proved (statement
lines unchanged; only the two `sorry`s replaced):

    #print axioms powerLambertFreq_eq_lim
      [propext, Classical.choice, Quot.sound]
    #print axioms powerLambert_frequency_law
      [propext, Classical.choice, Quot.sound]

* `powerLambertFreq_eq_lim`: for `b, r ≥ 2` and every base-`b` word `w`, the limiting frequency
  `powerLambertFreq b r w` equals `lim_D periodicModelFreq b r ((D!)^r) w`.  Each term is a finite
  count over one period of the exactly periodic model `n ↦ {periodicTail b r Q n}`.
* `powerLambert_frequency_law`: `Σ 1/(b^{n^r} − 1)` is rich, every word frequency exists, and it is
  not normal.  The proof is the triple of `isRich_powerLambert`, `powerLambertFrequenciesExist` and
  `not_isNormal_powerLambert`.

New lemma (same file, same axioms): `eventually_abs_wordFreq_sub_periodicModelFreq_le`.  For every
`ε > 0` there is `D₀` such that every `D ≥ D₀` has `|freq_N(w) − G_D(w)| ≤ ε` eventually in `N`.
Its proof is the proof of `exists_eventually_abs_wordFreq_sub_le` with the chosen
`D = ⌈32/(εη)⌉₊` replaced by an arbitrary `D ≥` that value.  The only `D`-dependence is
`2/(D+1) ≤ εη/16` and `hQD`, both monotone.  The limit then follows from `le_of_tendsto` and
`Metric.tendsto_atTop`.  The existing lemma is untouched.  Root `src/NormalNumbers.lean` now
imports the file.

## Sanity table (numerics only, not in Lean)

These are the first `10^6` digits of `Σ_{n≥1} 1/(10^{n²} − 1)`, computed exactly by carry
propagation of `Σ c(m) 10^{-m}` with `c(m) = #{n ≥ 1 : n² ∣ m}`, truncated at `10^6 + 200`.  The
script is `/tmp/nnsanity/digits.py` and was not kept.

| digit | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
|---|---|---|---|---|---|---|---|---|---|---|
| freq | .000558 | .606123 | .277578 | .047053 | .049252 | .002524 | .011626 | .000152 | .004552 | .000582 |

* The squarefree share of `[1, 10^6]` (`c(m) = 1`) is `.607926`, against `6/π² = .607927`.
* The digit-`1` frequency `.606123` sits `.0018` below it.  A digit differs from `c(m) mod 10`
  (by a carry, or because `c(m) ≥ 10`) at `.4054%` of positions, which bounds the gap.

The data claims nothing beyond this.

## Checkpoint

* Single-module `lake build NormalNumbers.PowerLambertFrequencyLaw` is green, and the full root
  build `taskset -c 0-2 lake build NormalNumbers` is green (10962 jobs, barrier audit passes).
* Not pushed (the host pushes).
* Possible continuation (not in scope): a closed form or explicit rational values of
  `lim_D G_D(w)`.  For example, the digit-`1` frequency should be the density of squarefree
  `m` with no carry in, about `6/π²` minus the carry share.  This is open and not stated.

## Final checkpoint (2026-11-04, treadmill stop)

* Branch `wip/power-lambert-frequencies`; proof commit `dd43c33c` on top of kickoff `0a775c11` /
  `5cb3fa16`.  Working tree clean apart from this section.  `box done --green` was run, and the
  host re-verifies the build.
* Scoped gate met.  The remaining `sorry`s in `src/` are outside this scope and designated-open.
* Exact next step (optional, new scope): state the digit-`1` frequency of
  `Σ 1/(10^{n²} − 1)` as a `def … : Prop` node, either closed-form or in terms of the
  squarefree density and the carry share, then try to prove it.
