# HANDOFF c3-mrt 2026-09-25 lap52 — `rung_multi_uniform` + `rung_multi_correlation`

**The `K`-fold assembly's last gap is closed.**  `src/NormalNumbers/C3MrtMultiRung.lean`,
both targets green, both new declarations `[propext, Classical.choice, Quot.sound]`.

* `rung_multi_uniform` — the `K`-point `rung_two_uniform`.  `exists_common_threshold` applied
  twice (common base `A`, then common starting exponent `I`) over
  `Fintype.piFinset (fun _ : Fin K => range (Y+1)) ×ˢ range (Y^K + 1)`; admissibility of that
  index set is `d i ≤ Y` plus `a < lcm d ≤ Y^K` (`univLcm_le_pow`).  Degenerate tuples take the
  dummy witness `2` / `0`; their conclusion branch is vacuous.  The per-tuple input is
  `rung_multi_of_named_inputs` at `nondegenerateForms_of_tuple`.  Note the `hsolv` hypothesis of
  `multi_correlation_of_uniform_rung`'s `hrungU` is redundant — `hadvd` gives it with `n₀ = a` —
  so it is simply ignored here.
* `rung_multi_correlation` — one-line composition with `multi_correlation_of_uniform_rung`.

## Where the ledger now stands

The `D ≥ 3` route rests on exactly two named inputs: `KPointLogElliott K` (Tao–Teräväinen's
product log-Elliott, laps 35–39) and `TwistedPrimeSumSavingAllLevels` (the VK input).  Every
other ingredient is a proved theorem of this repo.

## NEXT

Wire `rung_multi_correlation` to `weylLambertTwist_of_kfold_bound` (`C3MrtBudget`).  The budget
lap already checked `K^{K²}` fits inside `exp(c(K+1)³)`; what the wiring needs is the
`depthAvg`-shaped restatement of the correlation bound, i.e. converting the `ε`-for-every-`ε`
form of `rung_multi_correlation` into the explicit `η N ≤ A(log N)^{-a}` rate that
`budget_absorb` consumes.  That conversion is where the decay class pinned in lap 40 bites:
`rung_multi_correlation` as stated gives `o(log N)` with NO rate, so the wiring will need
`KPointLogElliott` in a quantitative form.  **That is the next crux**, and it is the same gap
lap 40 characterised: `η N ≤ exp(−C(log log log N)⁴)`.
