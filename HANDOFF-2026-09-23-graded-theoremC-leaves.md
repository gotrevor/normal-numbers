# HANDOFF 2026-09-23 — Theorem C′: the tail crux resolved, five of eight leaves closed

Branch `wip/g5-prime-subset`, HEAD `83c697f`.  Working tree clean, `lake build` 🟢 **9161 jobs**.
Running `KICKOFF-2026-09-22-multicutoff-lean.md` under the 2026-09-22 17:12 EDT override, on the
graded route of `DIRECTION.md` → CURRENT DIRECTIVE.  Continues
`HANDOFF-2026-09-22-graded-theoremC.md` (which listed eight open leaves).

## The route finding of this run

`exists_site_re_nonpos` returns `Nat.find hex − 1`, and `Nat.find hex ≤ log₄|h| + 1` because
`|h/4^j| ∈ (0,1)` once `4^j > |h|`.  So **Theorem A's contracting site `j₀` has a bounded index
for fixed `h`, uniformly in `N`** — new file `src/NormalNumbers/PrimeModelSiteIndexBound.lean`,
`exists_site_re_nonpos_le`, sorry-free and axiom-clean.

That is what unlocks Astra §8.  Previously `windowMean_le_terms` discarded `j₀` by monotonicity
down to the **bottom** cutoff `yBot N`, which forced a fresh-mass bound whose root chain costs
`≍ L₃N` halvings — not implied by `ε_N → 0`, and the lap-G5c-d crux.  With the index bound E5
sits at the **near-top** cutoff `y_{cIdx}`, `cIdx = min (log₄|h|) (J−1)`, whose chain to `N` is
`O(log u_N)`.  `J_N` may then be tied to the **full** mass `S_P(N)`, exactly as the paper has it
(`S_N = S_P(0,N)`), and the tail needs only the ONE-step chain `S_P(N,2N) ≤ ε_N`.

## Landed this run (each its own green commit, all headlines axiom-clean)

| commit | what |
|---|---|
| `07ee6ad` | `yBotG_tendsto` (via `epsN_le_aMinG`), `termE4b_tendsto` (+`sum_uuG_le`) |
| `0191fd0` | `termE4a_tendsto` (+`yBotG_le_yG`, `aG_ge_invL3`, `geom_sum_le_two`) |
| `fd03522` | `JG_tendsto`, `tail_graded`; tail crux isolated as `freshMassTwo_graded` |
| `0ae12f0` | **`exists_site_re_nonpos_le`** — the site-index bound (new file) |
| `5f1f6ff` | threaded it through `norm_model_expectation_le_gradedM` → `window_bound_gradedGM` → `window_bound_schedule` |
| `3e5b6f7` | **route correction**: `JG` retied to `S_P(N)`, `termE5` at `y_{cIdx}`, `freshMassTwo_graded` and `tailOK_graded` PROVED |
| `076a229` | `yBotG_le_yG_nat`, `epsG_mul_uG_sq_le` (`ε_N u_N² ≤ 1`) |
| `815c76e` | **`recipSumIoc_yG_le`** — the short root chain at every site |
| `83c697f` | **`termE1_tendsto`** (+`sum_quarter_weight_le`, `JG_div_tendsto`) |

Statement changes: the three graded-chain `∃ j₀` conclusions gained the conjunct
`(j₀ : ℕ) ≤ Nat.log 4 h.natAbs` — a pure **strengthening** of this campaign's own statements.
The ungraded chain (`PrimeModelKMT`, `PrimeModelTheoremA`, `window_bound_gradedG`,
`norm_model_expectation_le_graded`) is untouched, as is `PrimeModelBrunLower.lean`.

Nothing in the paper is refuted.  One paper *gap* was closed rather than refuted: Astra §8 tacitly
uses `j₀` fixed; the Lean chain needed the explicit bound, which is now proved.

## Open leaves — all three in `src/NormalNumbers/PrimeModelFamilyGraded.lean`

1. **`termE5_tendsto (hS) (hP) (h)`** (l. ~575 sorry is `schedule_admissible`; E5 is l. ~974).
   Astra (8.6), and the last structurally new estimate.  With `c = cIdx P h N ≤ log₄|h|`:
   `∑_{p ∈ midPrimes(2J, y_0), p ≤ y_c} 1/p = S_P(y_c) − S_P(2J)`,
   `S_P(y_c) ≥ S_P(N) − S_P(y_c,N) ≥ 8J − (c + 2 + 2log₂u_N)/u_N²` by **`recipSumIoc_yG_le`**
   (already proved — it takes any `j ≤ J1 N`, and `c ≤ J−1 ≤ J1 N`), `8J ≤ S_P(N)` is
   `JG_le_mass`, and `S_P(2J) ≤ 1 + log(2J)` is Mertens (`recipSumLe_le_crude` /
   `primeRecipSum_le`).  Exponent `≥ 8J − 1 − log 2J − o(1)`, so the term is `≤ e^{−5J} → 0`
   off `JG_tendsto`.
2. **`termE4c_tendsto`** — `log R ≤ (540+8u_N)/u_N² · log N` (from `∑_b (b+1)2^{−b} = 4`),
   `(2J)# ≤ 4^{2J}`, `∏_j ⌊T_j⌋ ≤ N^{0.22}`; product is `N^{−1+o(1)}`.
3. **`schedule_admissible`** — eleven pointwise clauses.  `hybot` = `yBotG_le_yG`, `hmono` =
   `yG_antitone` (both proved).  `hcutlo` needs `L ≥ 2` (`⌊t²⌋^{1/4} ≤ ⌊t⌋` for `t ≥ 2`, which
   is why `LG = max 2 …`), `hcut2` needs `2^{−L} log yBot ∈ [log 2, 2 log 2]`.

Suggested order: 1 → 3 → 2.  `PENDING_WORK.md` carries the same list with the arithmetic.

`src/` also still holds the two pre-existing off-campaign `sorry`s
(`PrimeLambertOscillation.phaseOscillation`, `MahlerDriftOne.exists_prime_nonresidue`).
