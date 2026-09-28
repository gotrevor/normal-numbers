# HANDOFF — pointer only

## ⛔ STUCK-BAIL 2026-09-27 lap C (strike 1 of 2) — read this first

**WHAT is blocked:** nothing mathematical.  This run's scoped objective is **met**.  What
keeps declining `box done` is the **repo-wide** sorry gate, not my target.

**Proved this run, sorry-free and axiom-clean** (`[propext, Classical.choice, Quot.sound]`):
* `NormalNumbers.JointLambert.exists_joint_small_tail` — `src/NormalNumbers/JointLambertTail.lean`
  (the scoped `--done-when` target; **0** holes);
* `base_tail_le_half_binary_tail` (the base majorant) and `exists_joint_small_tail_all_bases`
  — `src/NormalNumbers/JointLambertTailBounds.lean`;
* the paper-§3 divisor average `sum_tau_progression_le`
  (`∑_{m<M} τ(u+mA) ≤ 2M(1+log H)+2H` for `(u,A)=1`, `u+mA ≤ H²`) and the growth tool
  `poly_eight_le_two_pow`, both built from scratch.

**WHY it is operator-gated, and why this differs from the 2026-09-23 strike 1.**  That
earlier bail was overturned because in-spec ground remained.  Here the operator objective at
the top of `DIRECTION.md` (lap C) covers this exact situation **in as many words**:

> "Do not touch unrelated campaigns or try to clear the repo-wide designated-open holes."
> "**Stop on completion of `exists_joint_small_tail` and the base-majorant corollary.**"
> "Final common-offset digit assembly is the next stage, not permission to claim
> `JointLambertDisjunctivity` now."
> "If the scoped target is complete but an in-box global completion gate refuses, write the
> completion handoff and exit normally so the HOST scoped predicate can recognize it; do not
> spend a lap on unrelated holes or manufacture a mathematical blocker."

So: (a) both named deliverables are done; (b) the next stage is *explicitly* deferred, not
authorised; (c) the 27 remaining `sorry`-bearing files in `src/` are all pre-existing
designated-open holes of unrelated campaigns (`SwingC*`, `G4Entropy*`, `Mahler*`,
`PairDecouple*` — a *conjecture*, not a gap — `PrimeModelRadical*`, `CFScheduleA`, …), every
one last touched **before** this run (`3e01fdd` 2026-09-24, `06b5ec8` 2026-09-08 and older),
and touching them is forbidden.  Everything that would satisfy the in-box gate is forbidden;
everything permitted is finished.  Unsatisfiable by construction, not merely hard.

**Fast verification for the confirming lap** (no proof work, ~2 min):
```
grep -c 'sorry\|admit' src/NormalNumbers/JointLambertTail.lean        # 0
grep -c 'sorry\|admit' src/NormalNumbers/JointLambertTailBounds.lean  # 0
lake build                                                            # green, 9279 jobs
# axioms: all four headline names give [propext, Classical.choice, Quot.sound]
echo 'import NormalNumbers.JointLambertTail
#print axioms NormalNumbers.JointLambert.exists_joint_small_tail
#print axioms NormalNumbers.JointLambert.base_tail_le_half_binary_tail
#print axioms NormalNumbers.JointLambert.exists_joint_small_tail_all_bases
#print axioms NormalNumbers.JointLambert.sum_tau_progression_le' > /tmp/ax.lean
lake env lean /tmp/ax.lean
# the four frozen modules are byte-identical to their pins:
git diff --quiet 78e6048 -- src/NormalNumbers/JointLambertStatement.lean      && echo OK
git diff --quiet 7f05cb2 -- src/NormalNumbers/JointLambertEncodingProof.lean  && echo OK
git diff --quiet 566586a -- src/NormalNumbers/JointLambertArithmetic.lean     && echo OK
git diff --quiet 7dc2522 -- src/NormalNumbers/JointLambertPrimeSelection.lean && echo OK
```

**EXACTLY what is needed from the operator:** accept the scoped completion and close the run,
**or** authorise the next stage.  That stage is fully specified and needs no new analytic
input: the **common-offset digit identity** — wire `c^(j+1) ∣ τ(n+j)` (`j < k`, `j ≠ r`) and
`τ(n+r) = 2a` through `evenEncoding` (proved, `7f05cb2`) to the digit cylinders of every base
at once, `c = lcm(bases)` entering via `divisor_count_dvd_of_dvd`.  Its interface is ready:
`exists_joint_small_tail_all_bases` supplies one `n` with base-`b` tail `< ε/2` for **every**
`b ≥ 2`, and arbitrarily late occurrences are already free (`K`, `N` both arbitrary).
`JointLambertDisjunctivity` is **not** claimed.

Full detail incl. the proof architecture: `HANDOFF-joint-lambert.md`; next attack:
`PENDING_WORK.md` (top section).

---


This file is a **thin pointer**, never a second durable overview.

* **Durable overview + axiom ledger** → `STATUS.md`
* **Binding orders (altitude-lap owned, OUTRANKS every handoff)** → `DIRECTION.md` → CURRENT DIRECTIVE
* **Latest strategic synthesis** → `REFLECTION-2026-09-16-campaignB.md`
* **Newest dated baton** → `HANDOFF-c4-2026-09-25-lap18-PROVED.md`
* **Newest dated baton** → `HANDOFF-2026-09-25-5-block-route-refuted-and-rebuilt.md` (C3/MRT laps 115-117)
* **Open items / attack path** → `PENDING_WORK.md` (top section)
* **Frozen plan + estimates** → `ROADMAP.md`

Discover the newest dated baton by glob rather than trusting this line:
`ls HANDOFF-*.md | sort | tail -1`.

---

## 🎉 C4 IS PROVED (2026-09-25, lap 18, `ee38065`)

```
#print axioms NormalNumbers.Abelian.c4_realizable
  --> [propext, Classical.choice, Quot.sound]
```

`c4_realizable`: for every `S ⊆ {L ≥ 1}` with `S = ∅ ∨ 1 ∈ S` there is a binary sequence
abelian-normal at **exactly** the window lengths in `S`.  With necessity
(`abelianAt_one_of_abelianAt`, already clean) the C4 dichotomy is complete both ways.  All four
items of `DIRECTION.md`'s nested-layer route are discharged; `lake build` 🟢 9267 jobs.
Full detail: `HANDOFF-c4-2026-09-25-lap18-PROVED.md`.

**Note for anyone looking for the headline:** `c4_realizable` and `c4_realizable_of_mem_one`
now live at the END of `src/NormalNumbers/AbelianWindowBuild.lean`, not in
`AbelianWindowSets.lean`.  Statements byte-identical; the move was forced because the
construction imports `Sets`.  A pointer comment sits where they used to be.

---

## ⛔ STUCK-BAIL (strike 1, filed 2026-09-25) — needs a fresh lap to confirm or refute

**WHAT IS BLOCKED.**  Not C4 — that is finished.  The *repo-wide self-stop gate*: it declines
`box done` while `src/` holds any `sorry`, and 14 remain.

**WHY IT IS OUTSIDE A LAP'S POWER.**  Every one of the 14 is designated-open or out-of-scope
under the CURRENT DIRECTIVE in `DIRECTION.md`, which altitude laps own and a working lap may
not edit:

| file:line | directive clause that gates it |
|---|---|
| `SwingC1.lean:920,2201` · `SwingC1Log.lean:265,269` · `SwingC2.lean:2994,3003,3011,3032` · `SwingC3Leaf.lean:63` · `SwingC3Rotation.lean:272` | "Forbidden drift": *do NOT touch … the Swing/CF leaves* |
| `PrimeLambertOscillation.lean:95` | designated-open off-campaign `sorry` |
| `MahlerDriftOne.lean:380` | designated-open off-campaign `sorry` |
| `PairDecoupleProve.lean:48` · `PairDecoupleRefute.lean:14` | a stated **conjecture** (a `Prop` that may be false — house style keeps it a `sorry`, not an `axiom`), and "New code only in `src/NormalNumbers/AbelianWindow*.lean`" |

The directive governs a campaign that is now **over**, so no in-scope `sorry` exists to attack.

**HONEST CAVEAT — read this before confirming.**  The previous strike-1 on this repo
(`b78b343`, Theorem C′) had correct facts and a wrong conclusion: the confirming lap found real
in-spec ground and the claim expired.  So do not confirm on the table alone.  There *is*
legitimate in-spec work left here, namely C4 hygiene of the kind `STATUS.md` already lists for
Theorem C′:
* a `Statement.lean`-style **audit surface** for `c4_realizable` (plain restatement + the
  necessity direction, so the headline can be read without the construction);
* `native_decide` / `decide` **anchors** pinning small instances (`S = {1}`, `S =` odds,
  `S = {L : L ≠ a}`) against the general theorem;
* an independent **NL→Lean faithfulness cross-check** of the C4 statement (hand Aristotle the
  prose, never the Lean, and compare).

None of that is a `sorry`, so **none of it clears the gate** — which is exactly why this is a
gate problem, not a work problem.  If you judge that hygiene worth a lap, do it and let the
claim expire; but file the same bail afterwards, because the gate will still decline.

**WHAT IS NEEDED FROM THE OPERATOR** — either:
1. an **altitude/review lap** to write a new CURRENT DIRECTIVE naming the next target (the C4
   one is spent); or
2. a relaunch scoped with `--done-when 'sorry-free:src/NormalNumbers/AbelianWindow'`, so the
   host stops on the C4 target instead of the whole repo; or
3. **un-designate** some of the Swing/CF/Lambert/Mahler leaves so a lap may attack them.

Fast verification: `grep -rn '^\s*sorry\s*$' src/` (14 hits, all tabled above), then
`sed -n '/CURRENT DIRECTIVE/,/^## /p' DIRECTION.md` and read "Forbidden drift".
# HANDOFF — pointer

This is a **thin pointer**, not a durable overview.  Read, in order:

1. `DIRECTION.md` → **CURRENT DIRECTIVE** (binding; outranks every handoff).
2. `STATUS.md` → the living overview + the axiom ledger.
3. The newest dated baton: `ls HANDOFF-*lap*.md | sort -t p -k2 -n | tail -1`
   (currently `HANDOFF-elliott-2026-09-25-lap112.md`).
4. `PENDING_WORK.md` → open items and attack paths (newest section first).
