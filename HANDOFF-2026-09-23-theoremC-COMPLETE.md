# HANDOFF 2026-09-23 — **Theorem C′ is PROVED** (multicutoff campaign complete)

Branch `wip/g5-prime-subset`, HEAD `3523f8d`.  Working tree clean, `lake build` 🟢 **9161 jobs**.
Ran `KICKOFF-2026-09-22-multicutoff-lean.md` under the 2026-09-22 17:12 EDT attended override,
on the graded route of `DIRECTION.md` → CURRENT DIRECTIVE.  Continues
`HANDOFF-2026-09-23-graded-theoremC-leaves.md` (which listed three open leaves).

## The headline

```lean
theorem isNormal_subsetLambert_of_sqrtFreshMassZero
    (hS : SqrtFreshMassZero P) (hP : DivergentRecip P) : IsNormal 4 (subsetLambert P 4)
```
`#print axioms` = `[propext, Classical.choice, Quot.sound]`.  Laps 0–7 of the kickoff are all
landed.  `src/` holds exactly the two pre-existing off-campaign `sorry`s
(`PrimeLambertOscillation.phaseOscillation`, `MahlerDriftOne.exists_prime_nonresidue`).

## Landed this run (each its own green commit)

| commit | what |
|---|---|
| `91dcb89` | review lap: `DIRECTION.md` CURRENT DIRECTIVE refreshed, `STATUS.md` re-derived |
| `a11a5b9` | **`termE5_tendsto`** — Astra (8.6), the phase contraction at the near-top cutoff |
| `db4b4a1` | **`schedule_admissible`** — all eleven clauses; `LG` re-pinned (route finding) |
| `3523f8d` | **`termE4c_tendsto`** — the CRT remainder; **Theorem C′ complete** |

### E5 (`termE5_tendsto`)

With `c = cIdx P h N ≤ log₄|h|` (the bounded contracting-site index of lap G5c-e):
`∑_{p∈P, 2J<p≤y_c} 1/p = S_P(y_c) − S_P(2J) = (S_P(N) − S_P(y_c,N)) − S_P(2J) ≥ 8J − 1 − (12 L₂(2J)+21)`,
off `JG_le_mass`, the short root chain `recipSumIoc_yG_le` and Mertens.  So
`E5 ≤ e^{2J}e^{−8J+22+12 log 2J} = e^{22}(2J)^{12}/(e^6)^J → 0`.
New prerequisites: `twoJ1_lt_yBotG` (`2 J₁N < yBot N`, via `yN_core`'s `log N − 1 ≤ y_N` and
`L₂N + 1 < exp(L₂N) = log N`) and `yG_le_self`.

### ROUTE FINDING — the cut depth `LG` had to be redefined

The two dyadic-cut clauses pin `L` from **both** sides:
`hcut2` (`2 ≤ y_b^{2^{−L}}` for every band) ⟺ `2^L ≤ log₂ y_{J−1}`;
`hcutlo` at the bottom band (`y_{J−1}^{2^{−L}} ≤ 2J`) ⟸ `2^{L+1} > log₂ y_{J−1}`.
With `L` read off `yBotG` — as the schedule originally had it — the second is **false** whenever
the `min` in `JG` is taken at the mass branch: `log y_{J−1}/log yBotG ≍ (L₃N/u_N²)·2^{J₁−J}` is
unbounded while `2^L ≍ log₂ yBotG`, so the bottom band's chain stops far above `2J`.
Reading `L` off the bottom **site** cutoff `y_{J−1}` satisfies both at once (`LG_spec`).
`LG` is now `max 2 ⌊log₂ log₂ y_{J−1}⌋` and takes `P`.  Helper `cut_le_next`
(`⌊t²⌋^{1/c} ≤ ⌊t⌋` for `t ≥ 4`, `c ≥ 4`) is why `LG` is clipped at `2`.

### E4c (`termE4c_tendsto`)

`(2J)# ≤ 4^{2J} ≤ N^{0.09}` (`J ≤ L₃N ≤ L₂N/2`, `log N ≥ (1+L₂N/2)²` — `log_ge_sq`);
`∏_j ⌊T_j⌋ ≤ N^{0.25}` (`√(2^{−j}) ≤ (3/4)^j`, geometric);
`R² ≤ N^{0.09}` (`log R = ∑_b (128(b+1)+4u_b+14) log y_b ≤ 12(142+4u_N)/u_N²·log N`).
The last is exactly where the **graded** support level pays: a constant class count would give
`128 J log y_0`, a fixed fraction of `log N`.

## Statement changes made by this campaign (all to its own new declarations)

* the three graded-chain `∃ j₀` conclusions gained `(j₀ : ℕ) ≤ Nat.log 4 h.natAbs` (a pure
  strengthening; lap G5c-e/f);
* `LG` takes `P` and is read off `y_{J−1}` (this run);
* `schedule_admissible`, `windowMean_le_terms`, `termE4c_tendsto` gained `hS` / `hP`.

The ungraded chain (`PrimeModelKMT`, `PrimeModelTheoremA`, `window_bound_gradedG`,
`norm_model_expectation_le_graded`) and `PrimeModelBrunLower.lean` are untouched, as are
`papers/` and the Pair B files.  Nothing in the paper is refuted; two paper *gaps* were closed:
Astra §8 tacitly uses `j₀` fixed (now `exists_site_re_nonpos_le`), and it does not say which
cutoff the level count is read off (it must be `y_{J−1}`, see above).

## Next steps (for whoever picks this up)

1. **Audit surface.**  `Statement.lean`-style unwound statement of `SqrtFreshMassZero`,
   `DivergentRecip`, `IsNormal 4 (subsetLambert P 4)` — the faithfulness gate this repo uses for
   every headline.  This is the one piece of the campaign's own hygiene not yet done.
2. **Astra §10 abstract consumer** `F_N = ∑_j 4^{−j} S_P(y_j, 2N) → 0` — strictly weaker
   hypothesis than `SqrtFreshMassZero`, same schedule; the graded machinery now in kernel should
   take it with only the E1 leg re-run.
3. Off-campaign, untouched by the override: `PrimeLambertOscillation.phaseOscillation`,
   `MahlerDriftOne.exists_prime_nonresidue`.

`PENDING_WORK.md` and `STATUS.md` carry the same, with the axiom ledger re-run from real
`#print axioms` at 9161 jobs.
