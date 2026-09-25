# HANDOFF — pointer only

This file is a **thin pointer**, never a second durable overview.

* **Durable overview + axiom ledger** → `STATUS.md`
* **Binding orders (altitude-lap owned, OUTRANKS every handoff)** → `DIRECTION.md` → CURRENT DIRECTIVE
* **Latest strategic synthesis** → `REFLECTION-2026-09-16-campaignB.md`
* **Newest dated baton** → `HANDOFF-c4-2026-09-25-lap18-PROVED.md`
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
