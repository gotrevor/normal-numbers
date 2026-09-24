# Handoff — pd-refute, lap 1: checklist discharged, CRT half PROVED, no counterexample

**Branch** `wip/pd-refute` · **HEAD** `35cbd42` · tree clean, NOT pushed
**Build**: full `lake build` green, **9190 jobs** (pre-commit hook verified on every commit)
**Objective**: `KICKOFF-2026-09-24-pd-refute.md`.  `DIRECTION.md` → CURRENT DIRECTIVE has been
re-set to match it and OUTRANKS this file.

## The crux and the confidence

**Crux**: `PairDecouple b p q t` (`SwingC1Decouple.lean`), the sole open input of
`conjC1_of_delange_katai_decouple`.  This worktree's target is its negation,
`not_pairDecouple_all` (`src/NormalNumbers/PairDecoupleRefute.lean`) — still an open ratified
`sorry`, and that is the honest state: **no counterexample found**.

**Confidence that `PairDecouple` is TRUE: 93%** (Ren's prior 85%; 92% at mid-lap, raised again by
the band theorem).  Reasons: (a) every boundary case in the kickoff's checklist is now a theorem
saying it cannot produce a class bias; (b) refuting `PairDecouple` is *equivalent* to refuting
`PairDecorr`, so there is no cheap boundary route; (c) **every bounded prime band is now PROVED
decoupled**, so a counterexample must be manufactured by the primes `r ≍ N` alone; (d) the band
probe shows intermediate truncations are 4–5× WORSE than the full remainder — cancellation across
bands, the opposite of a conspiracy.

## Three commits, all sorry-free and `#print axioms` = `[propext, Classical.choice, Quot.sound]`

| file | content |
|---|---|
| `PairDecoupleLower.lean` | **the twist** `progMean_pairRemainder` (on the class `c` the truncation is the constant `truncPairTail c`, so `progMean B Q R c = conj(A c)·progMean f Q R c`); the **test-function certificate** `norm_test_le_classDeviation` / `norm_test_le_pairDefect` (every mean-zero `χ` on `ℤ/Q` bounds `pairDefect` BELOW — with `χ(c)=e(−ac/Q)` these are `Q−1` computable refutation certificates); the finitary two-sided pin `norm_fullMean_pairTail_le` : `‖fullMean f (QR)‖ ≤ 2·pairDefect + ‖∏_{r≤P} pairLocalFactor‖`; the refuter's entry point `not_pairDecouple_of_pairCorr_ge` (no hypothesis on `P`); degenerate cases (`P<2 ⇒ pairDefect ≡ 0`; `pairLocalFactor = 1` EXACTLY when `p ≡ q [MOD r]`; `primorialLe P ∣ p−q ⇒` model term exactly `1`; `P=2` odd ⇒ `pairDefect = ‖M₀−M₁‖/2`) |
| `PairDecoupleAttacks.lean` | `classDeviation` (arithmetic-free `pairDefect`); all six kickoff attacks closed as theorems — constant shifts (`classDeviation_phase_add_primePeriodicTerm_self`), the `n=0` term and any finite exceptional set (`classDeviation_perturb`, `≤ 4n₀/(QR)`), a prime pinned on a class (`no_prime_dvd_class_beyond_cut` — **the CRT reason**: `r ∣ pQ`, so `r = p` or `r ≤ P`) |
| `PairDecoupleBand.lean` | **the CRT half of `PairDecouple`, PROVED.**  Crux decomposition `pairRemainder b P = bandPairTail b P y + pairRemainder b y` (`P ≤ y`) with the phase factorisation; `classDeviation(band) ≤ 4(R mod M)/R`, `M = bandModulus P y`, and **exactly `0` when `M ∣ R`**.  Engine (reusable by `wip/pd-prove`): `iterate_period`, `sum_range_mul_of_periodic`, `norm_mean_sub_periodMean_le` (sharp incomplete-period bound `2(R mod M)/R`), `const_of_coprime_periods`, `sum_class_period_const`, `classDeviation_le_of_periodic_coprime`, `coprime_primorialLe_bandModulus` |

## Probes (`probes/pair_defect.py`, stdlib only)

⚠️ `uv run` does NOT work on this box — no egress to PyPI, no numpy.  Write stdlib-only Python.
Exact `ω` by sieve; the tail by the exact backward recurrence `T(M) = (ω(M+1)+T(M+1))/b`, so there
is no `k`-truncation.  Five controls, all passing (`--selftest`): `C1` `B≡1 ⇒ defect 0`; `C2`
`B(n)=e(an/Q) ⇒ defect EXACTLY 1, LB(a)=1`; `C3` `e(φn)` against the closed-form geometric sum;
`C5` `∑_k ω(k)/b^k = ∑_r 1/(b^r−1)` to 16 digits; **`C4`** — `pairRemainder` by two independent
routes agrees to `≤ 9e-16` on every case.

* `data-2026-09-24-pair-defect.txt` — `b∈{3,4}`, `m∈{1,2,4}`, `P∈{2,3,5,7}`, `N ≤ 1.2e5`: every
  defect and every certified lower bound decays monotonically, roughly like `1/log N`.
* `data-2026-09-24-pair-defect-degenerate.txt` — the `primorialLe P ∣ p−q` family:
  `|periodMean A| = 1.000000` exactly in all ten cases (the Lean theorem, measured), and
  `|fullB| = |fullf|` exactly.  `maxLB` decays slowly (`≈ (log N)^{-1/2}`).
* `data-2026-09-24-pair-defect-bands.txt` — **the mechanism.**  Clean zeros exactly where the band
  modulus divides `R` (= `classDeviation_bandPairTail_eq_zero`); `O(y/R)` decay for each fixed
  `y`; intermediate truncations 4–5× worse than the full remainder.

## THE next move

1. **The tension, sharpened.**  The tail factor `phase(t·pairRemainder b y p q ·)` is uniformly
   near `1` only for `y ≳ max(p,q)·N` (below that the primes just above `pn` contribute
   `≍ b^{-gap}`, not `o(1)`), but there `bandModulus P y = e^{(1+o(1))y} ≫ R` and the counting
   bound `4(R mod M)/R` is vacuous.  The probe shows how lossy it is (band deviation `0.05` at
   `y=10^5`, not `4M/R`).  **So the next formal step is an incomplete-period EXPONENTIAL-SUM bound
   for the band factor**, replacing `norm_mean_sub_periodMean_le`'s counting bound: the band factor
   is a product of `r`-local factors, and the class-`c` mean is a complete-plus-incomplete character
   sum to modulus `Q·bandModulus`.  Formalize the abstract lemma first (no arithmetic).
2. **Probe the last regime.**  Split `n < QR` by `P⁺(pn+1)` above/below `√N` and compute each
   part's class deviation.  If the bias is not in the large-`P⁺` part, `PairDecouple` is
   numerically settled.  (Not run yet.)
3. **The degenerate family** `primorialLe P ∣ p−q` (`(5,11)` at `P=3`, `(7,37)` at `P=5`,
   `(11,431)` at `P=7`, all verified in Lean): there the proved model half is exactly `1`, so any
   bias found is a counterexample to `PairDecorr` itself.
4. Do NOT re-attack the six closed boundary cases.  Do NOT attack Selberg–Delange or the Kátai
   criterion inside this swing (named known theorems; separate mathlib-scale projects).

## Standing constraints (unchanged)

* Never delete, rename or weaken `not_pairDecouple_all`; an open named `sorry` is acceptable.
* Do not edit `SwingC1*.lean`, `CastingOut*.lean`, `Maze.lean`, `papers/`, `agent-mail/`, other
  KICKOFFs.  New helpers in `src/NormalNumbers/PairDecouple*.lean` only.
* Never use `axiom`; named hypotheses are the sanctioned device.
* `hDepthAll` (`SwingC1.lean` l. 920) and `hAutoCorrAll` (l. 2201) stay as `sorry`s.
* `src/` open `sorry`s: 5 — the two above, `not_pairDecouple_all`, and the two designated-open
  off-campaign ones (`PrimeLambertOscillation`, `MahlerDriftOne`).  Nothing was relocated.

## Read next, in order

1. `DIRECTION.md` → CURRENT DIRECTIVE (binding, outranks this file).
2. `FINDINGS-2026-09-24-pd-refute.md` — what `PairDecouple` says after the twist, the checklist
   table, the degenerate family, the numbers, the confidence argument.
3. `PENDING_WORK.md` top two sections — open items, and the three routes refuted this lap.
4. `STATUS.md` — the C1-swing overview and axiom ledger.
