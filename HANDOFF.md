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
* **Newest dated baton** → `HANDOFF-2026-09-23-theoremC-reach-and-crosscheck.md`
* **Open items / attack path** → `PENDING_WORK.md` (top section)
* **Frozen plan + estimates** → `ROADMAP.md`

Discover the newest dated baton by glob rather than trusting this line:
`ls HANDOFF-*.md | sort | tail -1`.

---

## ⛔ STUCK-BAIL CONFIRMED (strike 2, filed 2026-09-23) — run halts for the operator

**Full detail + the exact asks:** `HANDOFF-2026-09-23-theoremC-reach-and-crosscheck.md`.

**State.**  `lake build` 🟢 9166 jobs.  `DIRECTION.md` → CURRENT DIRECTIVE objective —
`isNormal_subsetLambert_of_sqrtFreshMassZero` (Theorem C′) sorry-free and trust-triple — is
**MET**, re-verified this run together with its audit surface and the lap-0 deliverables.
`src/` holds exactly the two `sorry`s the directive designates open
(`PrimeLambertOscillation.phaseOscillation`, `MahlerDriftOne.exists_prime_nonresidue`).

**On strike 1 (`b78b343`).**  Its facts were correct; its conclusion that nothing workable
remained was not.  This run landed five additive, sorry-free, trust-triple nodes inside the
ratified kickoff spec — Astra §10's `F_N → 0` from C′'s hypothesis, the double-exponential
block criterion **and its converse** (so the block condition is a *reformulation* of
`SqrtFreshMassZero`, and Astra §10's prime-burst example is already covered by C′), and an
independent NL→Lean faithfulness cross-check whose three discrepancies are now all proved
equivalences.  That in-spec ground is now genuinely worked out.

**WHAT IS NEEDED FROM THE OPERATOR** — any one of:
1. authorise the **Astra §10 consumer** with permission to generalise
   `PrimeModelFamilyGraded.lean` **in place** over a supplied `u : ℕ → ℕ` (feasibility is now
   known good: `hS` enters through exactly five derived facts, so the file is an interface,
   not a weave — but `u_N` is read off `epsG`, and "no existing statement changes" would
   otherwise force a parallel ~1800-line file);
2. authorise a **Mertens campaign** (two-sided `∑_{p≤x} 1/p = log log x + O(1)`, absent from
   mathlib), which is the sole blocker for every strictness/sharpness question about the
   hypothesis;
3. **un-designate** `phaseOscillation` and/or `exists_prime_nonresidue`.


