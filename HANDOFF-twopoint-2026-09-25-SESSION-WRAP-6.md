# HANDOFF twopoint — SESSION WRAP 6 (laps 62–68), 2026-09-25

Branch `wip/twopoint-avg`.  HEAD **`5c5ad92`**.  Working tree **clean**.  Seven laps, seven green
commits, each gated by the pre-commit `lake build` (**9306 jobs** at wrap).  Every new declaration
`#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`).  **No `sorry` introduced
anywhere this run.**

## Rules honoured
`twoPointWeightedAvg_all` never deleted, renamed or weakened (and never touched).  No edits to
`PairDecouple*.lean`, `SwingC1*.lean`, `CastingOut*.lean`, `Maze.lean`, `papers/`, `agent-mail/`,
other KICKOFFs, or `DIRECTION.md`.  All new code in new files
`src/NormalNumbers/TwoPointC3{Scales,Wall,Pin,Budget,Alt,Trade,Link}.lean`, each imported from
`src/NormalNumbers.lean`.  One new probe, `probes/c3_alt_cancellation.py`.

## What this session did

`DIRECTION.md`'s lap-61 directive mandated a four-rung ladder on `ConjC3`.  **All four rungs are
discharged, plus four extensions**, and the entire TT2025 §5.2 mechanism is now in the kernel.

| lap | commit | result |
|---|---|---|
| 62 | `6978dd5` | **Rung 0, the scale re-plumb.**  `WeylTailAlong l b` (crux along a filter of scales), `ScalesDense ε S`, the **absorption lemma** `lower_of_monotone_of_scalesDense`, the new rung **`IsRichSubpoly`** pinned strictly between disjunctivity and `IsRich`, and the whole rotation route re-run along an arbitrary scale filter (filter-relative Weyl criterion `wgoodAt_*`, `density_lower_of_decoupleR_at`, `occCount_lower_of_rotationRouteCAt`).  Headline `isRichSubpoly_of_weylTailAlmostAll`. |
| 63 | `81606d2` | **Rung 2, the wall.**  `tendsto_mean_tailLarge_atTop`: `(1/N)∑_{n<N} tailLarge P b n → ∞`, unconditional, with quantitative form.  Uses only the `i=1` term plus the double count `∑_{n<N} ω_{>P}(n+1) = ∑_{P<p≤N}⌊N/p⌋` and Mertens 2nd in divergence form. |
| 64 | `f7f8d1c` | **Rung 3, the pin.**  Exact peel identity `tailLarge_eq_depthPeel_add`; `addCharTail_iff_depthWeighted` (at every fixed depth the crux IS the `K`-point weighted correlation — depth is free, the weight is the content); `no_constant_depth_budget` (rung 2 kills every constant schedule); `addCharTail_iff_plain_of_budget`. |
| 65 | `7021f54` | **Rung 3′.**  `tailLarge_le_log` (the mirror of rung 2), `peelBudget_id`, and hence `addCharTail_iff_plain_id`: the crux ⟺ the growing-depth **unweighted** surface, **no hypothesis**.  C3's analogue of `twoPointWeighted_iff_growing_id`. |
| 66 | `2e4ee6b` | **TT2025 §5.2.**  `altSum_eq_zero_of_indep` (the engine: a summand factoring through a toggle-invariant quantity has vanishing alternating sum), `altShift`/`altShift_toggle_eq` ((5.7), independent of coordinate `h−1`), `altSum_depthHead_eq_zero` ((5.8): the depth-`K` head cancels).  Probe confirms cancellation for `h=1..K` and its failure at `h=K+1` for every `K ≤ 8`, with a hand-computed anchor. |
| 67 | `4e85afd` | **The price, and `b ≥ 3` earned.**  `altSum_bound` (`≤ 2^{K+1}Mb^{−(K+1)}`), `altSum_bound_three` (`≤ M(2/3)^K` for `b ≥ 3`).  The §5.2 trade is a gain **iff `b ≥ 3`**, break-even at `b=2` — explaining both `ConjC3`'s standing `3 ≤ b` and TT2025's own "`b > 2` is somewhat easier". |
| 68 | `5c5ad92` | **The link.**  `altShift_eq_mul`: TT2025 (5.5)'s congruence *is a dilation*, `n + r_{S,h} = p_S(m+h)`, pure `ℤ` algebra.  `altSum_const_eq_zero`, `altSum_dilatedHead_eq_zero`, `altSum_dilatedTail_eq` ((5.8) in full).  **Inventory hit**: `G4Transport.dilatedTailB_eq` (G4 entropy campaign, general dilation, never consumed by C3) *is* TT2025 (5.2) — `corrB` = the paper's `δ_p`, `ω(d)/(b−1)` = the paper's `q` term, and in `ℝ` rather than mod 1. |

## The two things a reader should take away

1. **The C3 leaf is no longer flat 🔴.**  Conditional on the 2026 literature statement in the form
   it is actually available (bad scales allowed, `WeylTailAlmostAll`), `G4_b` is **subpolynomially
   rich** — machine-checked.  The structural reason is the asymmetry the lap-61 reflection spotted
   and lap 62 proved: `IsRich`'s count is monotone and absorbs an exceptional set of scales, while
   `ConjC1`'s two-sided `CastLaw` does not.
2. **The depth resource is fully characterised, in kernel.**  No fixed depth can work (rungs 2, 3);
   every growing depth states the same problem (rung 3′); and the literature's way to pay for
   growing depth (§5.2) is formalised with its price computed (laps 66–68).  The only remaining half
   of §5.2 is the sieve input.

## NEXT SESSION — in this order

1. **The sieve input — the one missing half of §5.2.**  Everything landed holds for *arbitrary*
   `p₀, v`; the paper needs `p_ε = p₀ + ∑ε_kv_k` **simultaneously prime for all `2^K` values of
   `ε`**, with (5.5) then solvable by CRT (`SwingC3Mean.primePeriod` is the vocabulary).  For a
   **fixed** `K` this is a bounded-length prime constellation, so a sieve *upper* bound suffices to
   run the argument for infinitely many `p₀` — much weaker than it first looks.  Check `master`'s
   `KICKOFF-brun-*` and `PairDecoupleBand.lean` before deriving anything.
2. **Cross-campaign audit before the next new file.**  This lap found the fourth inventory
   near-miss of the session's lineage.  `G4Transport.lean` / `G4RemainderW.lean` /
   `G4EntropyTransport.lean` hold a whole transport calculus the C3 ladder touched for the first
   time yesterday — notably `tailB_eq : tailB b k = b^k·G_b − integer`, i.e. the tail *is* `b^k G_b`
   mod integers, which is exactly the object the irrationality route needs.  Read them end-to-end.
3. **The adjacent unconditional item** `SwingC3Signed.lean`'s own docstring names and nobody has
   done: `∏_{P<p≤K} ‖primeFactor b p h‖ → 0`, via the one-term lower bound
   `Sig_p ≥ ‖1 − e(h·b^{p−1}/(b^p−1))‖²` into the proved `norm_primeFactor_sq_le`, then
   `mertens_lower` (the right shape for that lemma, unlike rung 2).
4. **Harden rung 0**: derive `ScalesDense` from a logarithmic-density hypothesis on the exceptional
   set, so the input is literally TT2025's `log dens E ≪ L^{−c}` rather than its consequence.

**Standing rule, reaffirmed and three-for-three this session: grep `src/` for the statement AND
`papers/` for the theorem before writing a line.**  Laps 63, 65 and 68 each consumed an in-tree
asset that a handoff had not known about; lap 68 avoided re-deriving a published identity entirely.

## Confidence at wrap
- `twoPointWeightedAvg_all` TRUE **90%**; provable with known techniques **3%** (untouched, as
  ratified — the C1 swing stays closed).
- `WeylTailHypothesis` (every scale) TRUE **97%**; provable with known techniques **8%**.
- `WeylTailAlmostAll` provable from the 2026 literature **70%**; `⇒ IsRichSubpoly` **in the kernel**.
- No fixed-depth route to the crux exists, weighted or unweighted: **certain**.
- `b ≥ 3` essential to the route rather than a convenience: **proved** (lap 67).
- §5.2 mechanism formalised bar the sieve input: **done**.  Sieve input reachable here: **40%**.
