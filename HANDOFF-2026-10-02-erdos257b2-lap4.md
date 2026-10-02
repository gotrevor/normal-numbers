# HANDOFF — Erdős #257 base 2 (prime subsets), lap 4 (2026-10-02)

Branch `proof/erdos257-base2`, HEAD = this file's commit (after f3298bbe). Tree clean, build green.
Scope: `sorry-free:src/NormalNumbers/Erdos257Base2.lean` (axioms = trust base).

## Done this lap
- N7 PROVED (`G4Base2Sched.lean`): `SchedB.scheduleWitnessSC2` (b=3 parameter layer `HypE 3 K e`,
  base-2 hM/hB/hbig/hfar/hbudget) and `exists_scheduleWitnessSC_two_of_supplyEff`.
- Finding: the ineffective supply (`∃ e₀`) cannot feed the schedule (moment cap
  e ≤ 2^{8K²}/(10⁵T)); replaced by `SchedB.VeryLargeCovSupplyEff` (threshold A·(P₀(c₀+1)2^t)^A ≤ 2^e).
- `binPair_cov_core` (explicit good-L hyps), `goodL_of_ge`, `binPair_cov_eff` (G4Base2GoodL.lean).
- `veryLargeCovSupplyEff_of_TT` PROVED.  Erdos257Base2.lean has no local sorry.

## Open (headline `#print axioms` still shows sorryAx through these)
1. `exists_bins` (G4Base2Supply) — greedy bins of mass ≤ 2θ.
2. `abs_one_sub_binDelta_le` (G4Base2Supply).
3. `sum_inv_vlPrimes_le` (G4Base2Supply) — Mertens upper on (Y, Y^102].
4. `avg_binErr_le` (G4Base2Supply) — semiprime count + CRT.
5. N5 `binInd_ap_mean` (G4Base2TTHyp) — inclusion–exclusion + rough-number count.

## Gotcha
In big contexts with `set Y := YE K e` / `m₁ 3 K`, `positivity`/`nlinarith`/`linarith` hit whnf
timeouts; use explicit lemmas and `linarith only [...]`, or abstract (`obtain ⟨M1, hM1⟩ : ∃ M1, m₁ 3 K = M1`).
