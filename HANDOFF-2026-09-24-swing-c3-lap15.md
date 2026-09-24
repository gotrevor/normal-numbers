# HANDOFF 2026-09-24 (laps 5–15) — swing at C3, branch `wip/swing-c3`

**Checkpoint.**  HEAD `7c347f1`, working tree CLEAN, nothing to push (host pushes).
`lake build` green, 9196 jobs.  `src/` holds **2** swing sorries plus the 2 designated-open
off-campaign ones (`PrimeLambertOscillation`, `MahlerDriftOne`) — do not touch those.

Obey `DIRECTION.md` → CURRENT DIRECTIVE (swing-c3), then `KICKOFF-2026-09-24-swing-c3.md`.
Previous: `HANDOFF-2026-09-24-swing-c3-lap4.md`.  Running log: `PENDING_WORK.md` (laps 5–15
entries are the detailed record; read those first).

## Headline: `ConjC3` is now ONE inequality about ONE explicit constant

`CastingOut.conjC3_of_weylLambertTwist` (axiom-clean) derives `ConjC3` from

    WeylLambertTwist b :  (1/N) ∑_{n<N} e(jn/Q)·e(h · b^n · L_P)  →  0,  0 < j < Q,
    L_P = ∑_{p > P prime} 1/(b^p − 1)      (`largeLambert_eq_tsum`)

with audit surface `audit_conjC3_of_weylLambertTwist` (`SwingC3Statement.lean`) — every
abbreviation unwound.  Aristotle, given only the PROSE, produced a structurally identical
formalization (faithfulness check PASSED) and independently judged the general case
research-level, proving only the `h = 0` case — the same sub-case lap 4 found elementary.

## The new files (all green, all axiom-clean)

| file | content |
|---|---|
| `SwingC3Closed.lean` | **Closed form** `tailLarge P b n = ∑_{p>P} b^{n mod p}/(b^p−1)`; free truncation `tailLarge − trunc_K ∈ [0, 2b^{n−K}]`. |
| `SwingC3Period.lean` | **Complete sums vanish exactly** (`sum_addChar_mul_periodic_eq_zero`); `primePeriod`, `tailTrunc`; `norm_sum_range_le_of_period` (`‖∑_{n<N}‖ ≤ L`); `addCharTailTrunc_tendsto` (the crux holds for EVERY fixed `K`). |
| `SwingC3Subset.lean` | **REFUTATION**: `∏_{p∈S} p ≤ N ⟹ ∑_{p∈S} 1/p ≤ log N/(min S · log min S)`.  No prime subset escapes the window. |
| `SwingC3Lambert2.lean` | `largeLambert_eq_tsum`, `ee_tailLarge_eq_ee_orbit`, `WeylLambertTwist`, `conjC3_of_weylLambertTwist`. |
| `SwingC3Mean.lean` | **Obstruction budget proved** (`sum_range_tailPrimeTerm_period` = exactly `1/(b−1)`; `sum_range_tailTrunc_sub_le`) and **the MASTER INEQUALITY** `norm_sum_addChar_tailLarge_le`. |
| `SwingC3Leaf.lean` | The crux as ONE named sorry `weylLambertTwist_holds`; `conjC3_via_weylLambert`. |
| `SwingC3Statement.lean` | The audit surface. |
| `SwingC3Convergent.lean` | The same machinery for an ARBITRARY set `S` of primes; both halves proved (see below). |
| `probes/swingc3_closed_form.py`, `probes/swingc3_weyl_lambert_twist.py` | exact-rational verification of the closed form; direct measurement of the conditional. |

## What the crux IS now, exactly

The **master inequality** (`norm_sum_addChar_tailLarge_le`), for every `K`:

    ‖∑_{n<N} e(jn/Q)·e(h·tailLarge P b n)‖ ≤ (∏_{P<p≤K} p)·Q + 16|h|·∑_{n<N}(tailLarge − trunc_K)

* term 1 is paid by EXACT complete-period cancellation; it needs `∏_{P<p≤K}p ≈ e^K ≪ N`, i.e.
  **`K ≲ log N`**;
* term 2 is priced EXACTLY by `sum_range_tailTrunc_sub_le` at `∑_{K<p≤K'}(N/p+1)/(b−1)`; it
  needs **`K ≳ N`**.

`ConjC3` is precisely: some `K = K(N)` makes both small.  The gap is the single window
`log N ≪ K ≪ N`.  Refuted escapes: prime subsets (lap 8), first-order-only expansion (the
`loglog` budget beats it), plus lap 4's list (B5, effective disjunctivity, exact `ω`-prescription,
`ω mod b` alone, §5 schedule sharpening, fixed-depth truncate-and-CRT).

**Numerics** (`probes/swingc3_weyl_lambert_twist.py`): the conditional decays like `(log N)^{−a}`,
`a ≈ 1.3–3.7`, never plateauing; for `h = 1`, `a ≈ 1.9`, independently reproducing lap 4's B4
measurement `a ≈ a₀+1` by a different computational route.

## IMMEDIATE NEXT STEP (lap 16): finish `setTail_addChar_tendsto`

`SwingC3Convergent.lean` has BOTH halves proved and needs only the assembly:

    ‖∑_{n<N}‖/N ≤ setPeriod(S,K)·Q/N + 16|h|·(2·recipTail(S,K)/(b−1) + 2/((b−1)·N))

from `norm_sum_addChar_setTail_le` + `sum_range_defect_le`.  Given `ε > 0`: pick `K` making
`recipTail(S,K)` small — rewrite `recipTail S K = ∑'_i g(i+(K+1))` with `g p = if S p then 1/p
else 0` (same head/tail split as `setTail_sub_setTrunc_eq`) and apply `tendsto_sum_nat_add` —
then let `N → ∞` with `K` fixed.  Use `NormedAddCommGroup.tendsto_nhds_zero`.

Result: **unconditionally, for any set `S` of primes coprime to `Q` with `∑_{p∈S} 1/p < ∞`, the
twisted Weyl sum of `L_S` tends to `0`.**  That closes the swing's machinery end to end and
isolates the sole missing input for `ConjC3` as exactly the DIVERGENCE of `∑_p 1/p`.

### After that
1. The only structurally untried handle: a SUB-TRIVIAL bound on `‖∑_{n<N} g‖` for `L`-periodic
   unimodular `g` with vanishing complete sum when `L ≫ N` (large sieve over the moduli
   `p ∈ (P,K]`, Erdős–Turán, or Weyl differencing in the CRT coordinates `(n mod p)_p`).  The
   master inequality is the frame it plugs into: replace `((primePeriod P K * Q : ℕ) : ℝ)`.
2. `tailLargeDecouple_holds` (the ratified arc-form leaf) STAYS a sorry per the kickoff
   addendum; lap 4 showed the arc form is the wrong leaf (unreachable from Fourier).

## Gotchas recorded this session
* `IsRich` is stated under `open Classical in`, so its `Finset.filter` carries
  `Classical.propDecidable`; an unwound restatement with a genuinely decidable predicate picks a
  DIFFERENT instance and is not defeq.  Bridge: `Finset.filter_congr (fun _ _ => Iff.rfl)` after
  `congr 2`.
* `set X := … with hX` then `rw [hX]` leaves the lambda un-beta-reduced; use `simp only [hX]`.
* Finite/infinite sum swap is `Summable.tsum_finsetSum`, not `tsum_sum`.
* `Finset.range_subset` is not the `m ≤ n` iff in this mathlib; prove the subset by hand.
