# HANDOFF c3-mrt 2026-09-25 — SESSION WRAP (laps 43–51)

**Branch** `wip/c3-mrt` · **HEAD** `79a3b07` · working tree **clean** · both targets green at
every commit.  Read `DIRECTION.md` → CURRENT DIRECTIVE first (it OUTRANKS this file; item 4
authorises exactly this work: "resume the `K`-fold assembly").  Per-lap detail:
`HANDOFF-c3mrt-2026-09-25-lap43.md`, `-lap44.md` (with laps 45–48 and 50–51 appended as
addenda), `-lap49.md`.  Earlier: `-session-wrap-laps40-42.md`.

## BUILD HYGIENE

    lake build                             # 9257 jobs
    lake build NormalNumbers.C3MrtBudget   # 8983 jobs — THE CHAIN TIP

Chain: `… → C3MrtMultiMass → C3MrtMultiTrunc → C3MrtMultiTupleMass → C3MrtMultiInner →
C3MrtMultiChase → C3MrtMultiRung → C3MrtBudget`.

## The crux is untouched

`weylLambertTwist_holds` (`SwingC3Leaf.lean`) unchanged — still the only campaign `sorry` in
`src/`.  `QuantDepthElliott` not edited.  This session is pure addition: **5 new files, 22 new
declarations, every one `[propext, Classical.choice, Quot.sound]`, zero sorries.**

## Session result — the `K`-fold assembly is COMPLETE; the `D ≥ 3` route now rests on ONE input

All five steps of the directive's item 4 are done, and the chain from `KPointLogElliott K` to
the `D ≥ 3` rung is closed except for one purely bookkeeping lemma.

| lap | file | declarations |
|---|---|---|
| 43 | `C3MrtMultiTrunc` | `truncA`, `truncB`, `truncA_nonneg`, `truncB_nonneg`, `truncB_tendsto`, **`multi_truncation_telescope`**, `multi_truncation_bound` |
| 44 | `C3MrtMultiTupleMass` | `extendFin`, `extendFin_apply/_pos`, `range_lcm_extendFin`, `prod_div_univLcm_le`, **`kfold_lcm_mass_le`** |
| 45 | `C3MrtMultiTupleMass` | **`multi_full_sum_bound`** |
| 46 | `C3MrtMultiInner` | `inner_harmonic_le_generic`, `window_gap_generic`, `progression_sum_bound_generic` |
| 47 | `C3MrtMultiInner` | `multi_rung_spelling`, **`inner_multi_bound`** |
| 48 | `C3MrtMultiInner` | **`multi_bound_of_rung`** |
| 49 | `C3MrtMultiChase` | `univLcm_le_prod`, `univLcm_le_pow`, **`multi_correlation_of_uniform_rung`** |
| 50 | `C3MrtMultiRung` | **`initial_segment_bound_of_kElliott`** |
| 51 | `C3MrtMultiRung` | `nondegenerateForms_of_tuple`, **`rung_multi_of_named_inputs`** |

### The two real insights of the session

1. **The truncation telescope's invariant** (lap 43).  A naive iteration of the truncation
   accumulates `∏_{j>m} sqfWPartial ≍ Y^{(K−m−1)/2}` against a `bridgeTail ≍ Y^{−1/2}` and
   DIVERGES for `K−m ≥ 3`.  The fix is to carry the *two-term block-mass invariant*
   `∑_{n∈S, block} ‖F n‖ ≤ α/g_0 + β/∏ g_s` through the induction; peeling one shift with
   modulus `e` acts as `(α,β) ↦ (α, β/e)`, which keeps the `log`-carrying mass attached to the
   CONVERGENT `sqfWMass` and the head attached to the harmless `sqfWPartial`.  `F`, `S`, `α`, `β`
   are all quantified inside the induction.
2. **The archimedean side does not grow with `K`** (lap 50).  `KPointLogElliott` constrains only
   the FIRST factor's pretentiousness, so `nonPretentious_zOm` (laps 18–21) is reused verbatim
   at every `K`.  That was the last place the `D ≥ 3` route could have demanded a new analytic
   input beyond the `K`-point correlation itself.  It does not.

### Where the ledger now stands

`multi_correlation_of_uniform_rung`: for every `K ≥ 1`, granting the rung uniformly over the
admissible tuples below `Y`, the log-averaged `K`-point correlation of `z_i^ω` at the shifts
`n+1,…,n+K` is `≤ C + ε log N` for every `ε > 0`.  Its hypothesis `hrungU` is the *only* thing
between `KPointLogElliott K` and the `D ≥ 3` rung, and `rung_multi_of_named_inputs` already
proves the per-tuple case of it.

## NEXT — resume here

1. **`rung_multi_uniform`** (the last gap, pure bookkeeping).  `exists_common_threshold` over
   `Fintype.piFinset (fun _ : Fin K => range (Y+1)) ×ˢ range (Y^K + 1)` — the admissible
   `(d, a)` — applied twice (common `A`, then common `I`), exactly as `rung_two_uniform`
   (`C3MrtArchimedean:849`) does over triples `(d,e,a)`.  Feed it `rung_multi_of_named_inputs`
   at `nondegenerateForms_of_tuple`; degenerate tuples get the dummy witness `⟨2, le_rfl, …⟩`.
   Note the base point is bounded by `univLcm_le_pow : lcm d ≤ Y^K`.
2. Then `rung_multi_correlation` = `multi_correlation_of_uniform_rung` ∘ `rung_multi_uniform`:
   the `D ≥ 3` rung on `KPointLogElliott K` + `TwistedPrimeSumSavingAllLevels` alone.
3. Then wire it to `weylLambertTwist_of_kfold_bound` (`C3MrtBudget`) — note the budget lap
   already checked `K^{K²}` fits — and the crux's ledger is complete: `ConjC3` reduced,
   axiom-clean, to `KPointLogElliott` (= Tao–Teräväinen's `ProductLogElliott`, laps 35–39) plus
   the VK input, with the sharp decay class of lap 40.

## Still refuted — DO NOT RETRY

Everything in `-session-wrap-laps40-42.md` (notably: `K^{K²}` is NOT `(log log N)^{o(1)}`;
`(log log N)^{-c}` decay does not suffice; sharpening `prod_le_lcm_mul_pow`'s exponent is
worthless; bounding the joint mass by ONE congruence in the telescope diverges).  Nothing was
retried this session.

## Confidence

* `K`-fold assembly completable: **done** (was ≈88%) — only `rung_multi_uniform` remains, and it
  is a transcription of an already-executed proof.
* leaf TRUE ≈ 97%.
* leaf PROVABLE with known techniques ≈ 22% (unchanged — the gap is the decay class pinned in
  lap 40, not the assembly, and this session did not move the literature).
