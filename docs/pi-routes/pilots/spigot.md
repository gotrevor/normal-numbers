# Spigot pilot

Read the shared pilot contract.  Prove or refute the frozen target
`PositiveWidthAlternatingPrefix` in `RoundTwoSpigot.lean`.

Critical arithmetic: for n fixed, q=3r, p>0 and 8p<r, the next two spigot steps
emit 0 then 1 without refining.  Their net action is `(p,r,q) -> (4p,r,q)`.
With p=1, r=4^(L+1), q=3r this repeats L times.  Check L=1,2,3 cheaply first.

This defeats any word-search argument that claims a waiting bound depending only
on the input index n uniformly over valid positive-width states: n=0 stays fixed
while arbitrarily many alternating bits avoid 00 and 11.  State that obstruction
with explicit quantifiers if feasible.  It is NOT a counterexample to the pi
initial state's `SpigotEscapeBudget`, because these states are not shown reachable
from `spigotInitial`.

Use remaining budget to identify what a pi-specific ranking invariant would need
to exclude this family.  Test proposed constraints against the true integer
recurrence, not just a digit table.  An invariant saying "this state is reachable
from the true initial state" is circular unless reduced to independently usable
arithmetic conditions.  An exact two-cycle at p=0 is a useful auxiliary control,
but alone does not rule out invariants requiring p>0.

Do not spend the lap proving SpigotSound, the hypergeometric series, or longer
finite coverage.  Deliver exact theorem names, assumptions, positive controls,
and the precise rank family excluded, with its reopening condition.
