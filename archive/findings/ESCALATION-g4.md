# G4 campaign: what to do when the lap finishes early

*Trevor, 2026-09-13 23:4x EDT: "If the lap finished early, consider expanding the scope & doing
more lean work or cleanup in the repo, or bigger, more ambitious goals.  We have plenty of
tokens."*

⚠️ This **supersedes** the handoff's "Trevor is conserving Astra tokens: do not escalate to Astra
automatically."  Astra is available.

Idle box time is waste.  If the run self-stops (`box done`), or a lap closes its objective with
budget left, do not stop — take the next rung.  Do **not** silently change the frozen G4 endpoint
to something easier; expansion means *more*, never *weaker*.

## Ladder, in order

1. **Finish the frozen endpoint.**  Unconditional `IsDisjunctive 4 primeLambertFour` and the base-2
   corollary, including the series identity `∑_p 1/(4^p − 1) = primeLambertFour`.  Nothing below
   this rung matters until the conditional wiring theorem's hypotheses A–D are discharged.

2. **The whole power-of-two tower, free.**  `Disjunctive.isDisjunctive_pow_iff` is an *iff*, so
   base 4 ⟺ base 2 ⟺ 8 ⟺ 16 ⟺ every `2^k`.  State it once as a clean corollary; it is a few lines,
   not a campaign.

3. **The fixed-base family `G_b`, b ≥ 3.**  Per
   `~/personal/claude/knowledge/core/projects/normal-numbers-fixed-base-disjunctivity-extension-2026-09-14.md`,
   every fixed `b ≥ 3` is *easier* than b = 2: the very-large-prime term is pointwise small once
   `b > 2^(5/4)`, so the external Tao–Teräväinen two-point input drops out entirely.  Generalize to
   `primeLambertAtBase b` with the base kept explicit in every statement.  ⚠️ This is a **different
   number per base**; it is not absolute disjunctivity of one constant, and must never be stated as
   such.

4. **The entropy consequence — strictly stronger than disjunctivity.**  The audit
   `normal-numbers-normality-after-disjunctivity-2026-09-14.md` derives
   `Ent₂(Z) ≥ mH − O(H√K)` (eq. 8) from the *same* zonotope mechanism, giving uniform ℓ-bit word
   frequencies on a structured sparse average (§4).  This is the reusable part of the machinery —
   a transfer principle, not a fact about G4.  ⚠️ It is **not** ordinary normality, and §5's
   synchronization bridge is *not* derived.  Never report it as normality.

5. **Repo cleanup, when the frontier is genuinely blocked.**  Real, not busywork:
   - `PrimeLambertOscillation.lean` — 4 sorries under the *old* irrationality endpoint.  It is not
     a prerequisite for this campaign.  Either discharge it or record it as a dead route with the
     exact obstruction; do not leave it ambiguous.
   - `CFScheduleA.lean` (4) beside `CFScheduleARefuted.lean` — a refutation that was never tidied.
   - ⚠️ `~/src/normal-numbers-cfsched` is a **live** worktree on `wip/cfschedulea-prop-nodes`.
     Do not touch any `CF*` file.  Same for `Adder*` (live in `~/src/nn-fable`).

## If the frontier is unclear

Launch a **codex-Astra sidecar** for next-step suggestions rather than guessing or idling
(Trevor, 2026-09-13, explicitly authorized).  Feed it the frozen endpoint, the current dependency
map, and the exact obstruction.  Its output is a *suggestion*, never a licence to move the
endpoint.

## Standing constraints that expansion does not relax

- No trusted axiom for any candidate lemma; no hypothesis carrying the hard result presented as
  proved.
- Report mathematics proved / refuted / isolated.  Never sorry counts, never their direction.
- A refutation that closes an invalid route is a successful outcome — record the exact statement,
  the counterexample, the downstream casualty, and the weakest honest repair.
- No publishing, no outreach, no public posts.
