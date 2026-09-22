# KICKOFF 2026-09-22 — Pair A multicutoff: formalise the graded-cutoff normality theorem

Branch `wip/g5-prime-subset`.  Engine Opus/low.  Authorised by Trevor 2026-09-22 ("time to write
this up into lean").  **New files only** under `src/NormalNumbers/`, namespace
`NormalNumbers.PrimeModel.*`; never edit `PrimeModelBrunLower.lean` (the nested sieve stays for the
old theorems), never edit any existing statement, never touch `papers/`, `agent-mail/`, Pair B files.

## The spec (paper tier, pair-refereed; read these first)

- `papers/ROUND2-multicutoff-fable.md`: §1 setting, §2 **Theorem A** (graded window bound, no
  `Regime`), §3 **Lemma B** (graded block-Bonferroni lower sieve), §6 **Theorem C** ledger,
  §7 Lean ledger (which existing declaration each new one generalises), §9 **Theorem C′** (the
  headline below) and the root-chain lemma.
- `papers/ROUND2-multicutoff-astra.md`: §4 the sieve with explicit constants, §5 atoms/remainder,
  §8 an alternative schedule, §10 abstract consumer `F_N = ∑_j 4^{−j} S_P(y_j, 2N) → 0`, §11 the
  square-root fresh-mass criterion (11.1)-(11.7).
- `probes/block_sieve.py` (uv; passes): hand-checked controls for Lemma B's identities, the
  telescoping minorant, the coefficient rule, and two exact CRT instances.  Use its numbers as
  test cases for `decide`-able sanity lemmas if useful.

## Headline (statement shape ratified; adapt binders/implicit `P` to the file conventions)

```lean
/-- Square-root fresh reciprocal mass of the prime set `P` vanishes. -/
def SqrtFreshMassZero : Prop :=
  Tendsto (fun N : ℕ => recipSumIoc P (Nat.sqrt N) N) atTop (𝓝 0)

theorem isNormal_subsetLambert_of_sqrtFreshMassZero
    (hS : SqrtFreshMassZero P) (hP : DivergentRecip P) : IsNormal 4 (subsetLambert P 4)

/-- Root chain (Astra 11.3 / Fable §9). -/
theorem recipSumIoc_le_rootChain {ρ : ℝ} (hρ : 0 ≤ ρ) {Z y M : ℕ} (hy : 2 ≤ y) (hZ : Z ≤ y)
    (hM : y < M) (hr : ∀ q, Z ≤ q → recipSumIoc P (Nat.sqrt q) q ≤ ρ) :
    recipSumIoc P y M ≤ ρ * ⌈Real.log (Real.log M / Real.log y) / Real.log 2⌉₊

theorem sqrtFreshMassZero_of_freshMassZero (hF : FreshMassZero P) : SqrtFreshMassZero P
theorem sqrtFreshMassZero_of_relDensityZero
    (h : Tendsto (fun t : ℕ => (piP P t : ℝ) / (t.primesBelow.card : ℝ)) atTop (𝓝 0)) :
    SqrtFreshMassZero P
```

The consumer closes through the existing `isNormal_subsetLambert_of_KMT_along` (`G4WiringSparse`)
exactly as `PrimeModelFamilyConsumer.lean` does: produce `KMT_along P J` and `TailOK P J` for the
schedule of Fable §6/§9 (or Astra §8/§11 - pick one and say which in the handoff).

## Laps, smallest first (each a green node; commit a compiling skeleton with named sorries FIRST)

0. `PrimeModelSqrtFresh.lean`: `SqrtFreshMassZero`, `recipSumIoc_le_rootChain` (induction on the
   chain `M_{l+1} = Nat.sqrt M_l`; intervals `(a,b]` telescope; `Nat.sqrt` only decreases so
   `M_K ≤ M^{2^{−K}} ≤ y`), `sqrtFreshMassZero_of_freshMassZero` (`yI N ≤ Nat.sqrt N` once
   `epsI N ≤ 1/2`, then `recipSumIoc_mono_right`), `sqrtFreshMassZero_of_relDensityZero`
   (`recipSumIoc_le_of_dominated'` with `y = Nat.sqrt N`: bound `δ (9 + 12 log 2)`).  Elementary;
   no sieve.  This lap alone is a publishable node.
1. `PrimeModelBlockSieve.lean` (pure combinatorics, no arithmetic): Bonferroni pair
   `∑_{i≤r} (−1)^i C(b,i) = (−1)^r C(b−1,r)` (`r` even, `b ≥ 1`; `= 1` for `b = 0`), `U ≥ I ≥ 0`,
   `U − D ≤ I` with `D = C(b, r+1)`; telescoping `∏_l U_l − ∑_l D_l ∏_{m≠l} U_m ≤ ∏_l I_l`;
   coefficient rule `λ(E) ∈ {−1,0,1}` with disjoint supports (Fable §3, probe check 2).
2. Product-model defect (same file or `PrimeModelBlockSieveModel.lean`): `E[L] ≥ (1 − η) ∏ V`,
   `η ≤ 0.3 ∑_j e^{−u_j}`.  Needs `1 − x ≥ e^{−2x}` on `[0, 1/2]`, `e_{r+1} ≤ λ^{r+1}/(r+1)!`,
   block mass `≤ 8d` via existing `block_le_eight` (last block clipped at `2k` so `v ≥ 2`).
   Constants `e < 4`, `log 2 ≥ 1/2`, `0.215`, `1.25` are in Fable §3 / Astra §4.
3. Support level `log R = ∑_j (128 d_j + 4u_j + 14) log y_j` (Astra §4 / Fable §3).
4. Per-prime class counts: `SieveCond`/`SiftedCond` with classes `Fin (d p)`, `d : ℕ → ℕ`,
   `2 d p ≤ p`; `radical_sieve_count` with `∏_{p∈E} d p` (same CRT proof); `localWeight (d p)`;
   `state_model_density`; remainder `≤ R²` in the shape of `brun_remainder_le_square`.
5. Per-shift box: `retainedBox` with `T : Fin k → ℝ`, card `≤ ∏ ⌊T_j⌋₊`; tail at shift `j` over
   primes `≤ y_j` (`radical_box_tail_exp20` shape, needs `log y_j ≥ 2`).
6. **Theorem A** (Fable §2): graded `windowMeanLe`, per-site E1 reusing `sum_omegaGt_shift_le`,
   graded model expectation with `A_{d p}`, `A_j = 0` for `j < j₀`,
   `E5 = e^k exp(−S_P(2k, y_{j₀}))`, `Q = primorial (2k)`.
7. **Theorem C′** (`PrimeModelFamilyGraded.lean`, mirroring `PrimeModelFamilyConsumer.lean`):
   the schedule, `ρ_N := sup_{q ≥ Z_N} r_P(q)`, `u_N`, `J_N`, `KMT_along` + `TailOK`
   (`tail_fresh` shape), then the headline.

## Existing anchors (all `src/NormalNumbers/`)

`PrimeModelKMTFixedH.lean` (`window_bound_regime_h`, `windowMean_sub_windowMeanLe_le_h`),
`PrimeModelFamilyConsumer.lean` (`FreshMassZero`, `isNormal_subsetLambert_of_freshMassZero`,
`tail_fresh`, `recipSumIoc_mono_right`), `PrimeModelFamilyIterMass.lean` (`yI`, `JI`),
`PrimeModelDensityMass.lean` (`piP`, `recipSumIoc_le_of_dominated'`), `G4WiringSparse.lean`
(`recipSumIoc`, `DivergentRecip`, `KMT_along`, `TailOK`, `isNormal_subsetLambert_of_KMT_along`),
`G4SubsetWeight.lean` (`subsetLambert`), `PrimeModelPrimeDimension.lean` (`block_le_eight`,
`primeRecipSum_le`), `PrimeModelBrunCount.lean` (`brun_sifted_count_lower`,
`brun_remainder_le_square`), `PrimeModelRadicalCRT.lean` (`SieveCond`, `SiftedCond`,
`radical_sieve_count`), `PrimeModelRadical.lean` (`localWeight`, `weight`, `primeRecip`),
`PrimeModelRadicalState.lean` (`hitShift`, `actualState`, `retainedBox_card_le`,
`state_model_density`), `PrimeModelRadicalMoment.lean` (`radical_box_tail_exp20`),
`PrimeModelLowerTransfer.lean` (`finite_phase_of_lower_atoms`), `PrimeModelPhaseFactor.lean`
(`sum_omegaGt_shift_le`), `G4WiringCRT.lean` (`ePhase`, `norm_ePhase_sub`, constant `4π`).

## Rules

- A lap succeeds by advancing the crux; a refutation of a paper step is an advance - record it in
  the HANDOFF with the exact inequality that fails, and stop that leg.  Never report a sorry
  count; decomposing one sorry into named leaves is progress.
- `decide +kernel` / `native_decide` / deprecation warnings are fine.  Commit every green build.
- If a leaf costs more than ~40 minutes, commit what compiles with a named sorry and move on.
- `#print axioms` on each headline once sorry-free; `box done --green` only when lap 7's
  headline is sorry-free and axiom-clean.  Write `HANDOFF-2026-09-22-multicutoff-lean.md` at
  every stopping point (which laps landed, what refuted, what next).
- Do not change branches.  Other files in the tree may be dirty (a concurrent prose session);
  commit only your own files.
