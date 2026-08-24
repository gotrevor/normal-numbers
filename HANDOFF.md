# HANDOFF — pointer

**JUDGE-FLAG (2026-08-24)**: Tier-2's remaining crux (step 2, the
log-average/frequency assembly, `Khinchin.lean`'s `xstar_log_digit_avg_tendsto`
sorry) appears to be **operator-gated**, not merely hard. Three attack paths
tried this session (full quantitative detail in `PENDING_WORK.md`'s top three
entries), all dead-ended at the same wall:
1. Escaping-mass argument from the existing `wSched_log_sum_le` total-mass
   bound + `uSched_spec`'s per-digit frequency bound — REFUTED with an
   explicit computation: the frequency bound's error, summed with `log a`
   weight over `a ≤ t`, grows like `n·log t` (Stirling), which does NOT
   vanish as a fraction of `n` for any cutoff choice (fixed or growing).
2. Dug into the underlying construction (`kminFn_spec` →
   `TBrick.exists_refinement_uniform`, `TBrickRefine.lean:432`) for a hidden
   sharper fact — confirmed there isn't one: the frequency bound is a direct
   consequence of which "bad zones" got unioned in the point-selection
   argument, and no log-weighted zone is unioned, by construction.
3. The natural fix — add a NEW concentration/large-deviation "bad zone" for
   the log-digit-sum statistic to that same union-bound selection, additively
   — is mathematically the right shape (and matches `KHINCHIN.md`'s ORIGINAL
   W6 plan, "digit caps `D_t` in the refinement", which an EARLIER lap this
   campaign had concluded was unnecessary — that earlier conclusion looks
   wrong per path 1's refutation above). But it requires generalizing
   `exists_good_avoiding_bad_of_large`/`exists_refinement_uniform` to accept
   an extra bad-zone parameter, i.e. editing `TBrickRefine.lean` — squarely
   "the schedule"/"Lemma 13", which `DIRECTION.md`'s CURRENT DIRECTIVE
   explicitly forbids re-attacking. Re-deriving the union-bound machinery
   independently in a new file (to avoid touching the forbidden file) is not
   practically tractable (it's the bulk of `TBrickRefine.lean`, thousands of
   lines).

**The operator ask**: either (a) authorize touching `TBrickRefine.lean`
additively (new lemma/parameter, no existing Tier-1 statement weakened) to
carry a digit-cap/concentration bad zone through the schedule construction —
this is real new work, comparable in size to a fresh W3-scale work package
per `KHINCHIN.md`'s own estimate, not a quick unblock; or (b) revise the
Tier-2 objective (e.g. accept a weaker Khinchin-adjacent statement, or drop
Tier 2 and consider Tier 1 the campaign's deliverable). A grind lap should
not decide between these unilaterally. Also worth an explicit correction:
the `44fb8bb`/`e018429`-lap "route insight" (goodC total-mass bound suffices,
no digit-cap re-plumb needed) that `DIRECTION.md`'s CURRENT DIRECTIVE and
prior HANDOFFs cite should be treated as REFUTED, not confirmed, pending
review.

This is a thin pointer (plain file, never a symlink). The durable overview and
the live baton live elsewhere:

- **STATUS.md** — living project overview + axiom ledger (refreshed on review laps).
- **DIRECTION.md** — CURRENT DIRECTIVE (binding; outranks any baton). Currently:
  TIER 1 LOCKED (`exists_absolutely_normal_cf_normal` proved, axiom-clean).
  Objective now: Tier 2, Khinchin-typical (`Headline.lean:134`), no longer fenced.
- **Newest dated baton** — see `PENDING_WORK.md` top entry (`42ec6a7`,
  2026-08-24): Gauss-Kuzmin single-digit law PROVED
  (`gaussMeasure_digit_cylinder`, `CFCylinder.lean`) — step 1 of the Tier-2
  assembly is done. `gaussMeasure_Ioo` relocated to `CFDefs.lean` (avoids a
  circular import with `CFCylinder.lean`). Next: step 2, the log-average /
  frequency assembly — a dominated-convergence-style interchange combining
  `xstar_cf_freq_tendsto`, `gaussMeasure_digit_cylinder`, and
  `wSched_log_sum_le`'s uniform tail bound; full decomposition sketch in
  `PENDING_WORK.md`'s top entry. Prior `HANDOFF-2026-08-26-0730.md` is
  superseded but still has useful background on the overall Tier-2 route.
- **PENDING_WORK.md** — open-items / attack-path scratchpad (top entry is newest).

Build: 🟢 green (8745 jobs). `src/` open sorries: `Headline.lean:136` only
(Tier 2 / Khinchin — the sole remaining obligation; step 1 of the assembly
closed this lap, step 2 — the log-average limit — is the genuine remaining
crux).
