# Proposal: normality's "master conjectures" as hypothesis Props  (2026-09-29, parked)

Parked for when the Vandehey §7 objective settles.  It is not urgent and nothing depends on it.

## Origin

In `~/src/lean-formalizations`, phases 15-17 stated **Schanuel's conjecture** as a named
hypothesis `Prop` and proved its consequences:
- Gelfond–Schneider, Lindemann–Weierstrass and Nesterenko as consistency edges;
- `e, π` algebraically independent;
- `e+π` transcendental;
- four exponentials;
- … (`NumberTheory/Transcendence/Schanuel.lean`, `Exponentials.lean`).

Trevor's framing: *"gathering up a bunch of facts & see what falls out"*; *"If transcendentals can have one, why can't normals?  That would seem unfair."*

Ren's suggestion, which Trevor asked to have parked here:

> If you want the normal-numbers version of this pass, I'd write Borel's conjecture and the general Hypothesis A in as named hypotheses there, with their consequences.  Hypothesis A could also run against the Maze entries already recorded there, to test which routes it would reopen.

## The candidates

1. **Borel's conjecture (1950).**  Every irrational algebraic number is normal in every base.
   - It covers `√2`, `∛2`, … but none of `π`, `e`, `log 2`.
   - Consequences worth deriving:
     - `√2` normal in base 2;
     - the base-2 digits of `√2` are disjunctive;
     - no algebraic irrational is a Liouville-like, sparse or automatic number.  Adamczewski–Bugeaud 2007 proves a weak version of this last one unconditionally; see below.
2. **Bailey–Crandall "Hypothesis A", general form** (D. H. Bailey and R. E. Crandall, *On the random character of fundamental constant expansions*, Experimental Math. **10** (2001)).
   - It is one statement about equidistribution of the "BBP recurrence" orbits `xₙ = (b·xₙ₋₁ + r(n)/q(n)) mod 1`, for rational functions `r/q`.
   - It implies normality of every BBP-type constant in its base: `π` in base 16, `log 2` in base 2, `π²`, `ζ(3)`-type sums, Catalan-type sums.
   - **This repo already machine-checks the `ln 2` instance** (README target 4, the Bailey–Crandall reduction).  The general form would make it one hypothesis `Prop` with many consequences, which is the Schanuel pattern.
3. **The Maze test.**  For each `Maze.lean` row, ask whether Hypothesis A (or Borel) implies the missing input.  A row whose `reopenIf` is implied by a stated hypothesis becomes a conditional theorem, i.e. a new edge.  A row that is *not* reopened even by these strong hypotheses is itself informative.

## Why there is no single Schanuel for normality (Ren's view, about 70%)

Schanuel works because transcendence is *algebraic*: there is a count (transcendence degree), and one inequality about `exp` constrains it.  Normality is *statistical* (equidistribution of an orbit), so there is no field or degree to count.  "Everything we believe" becomes the vague principle "constants with simple definitions behave like random numbers".  Nobody has made that precise in a way that is both believable and strong.

Hypothesis A is the best precise fragment.  Normality instead got the unconditional prize: Borel 1909, almost every number is normal.

## Related bridge (transcendence tool ⇒ digit fact)

Adamczewski–Bugeaud 2007: via the Subspace Theorem, an algebraic irrational's `b`-ary expansion has block complexity `p(n)/n → ∞`.  It is formalized by Ralf Stephan in `rwst/Subspace-Theorems`, `AdamczewskiBugeaud2007/`.  lean-formalizations consumes Stephan's results as Literature Props.  This is the natural unconditional companion to Borel's conjecture here.

## Also parked: Champernowne

- Normality of Champernowne's constant (base 10) belongs here, and `Bridge.lean` already anticipates it.
- Its transcendence (Mahler 1937, via Roth) is queued in lean-formalizations as phase 18.
