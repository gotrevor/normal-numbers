# PI-ROUTES-NEXT — three parallel lanes on disjunctivity of π 🥧

**Historical brief; these three lanes are retired.**  Read [MAZE.md](../MAZE.md)
and the original-route Maze entries before using any instructions below.
The claim below of an “uncancellable” source did not survive the investigation.
Second-round proposals, not launched jobs: [round-two.md](pi-routes/round-two.md).

**Sink:** `IsDisjunctive 2 Real.pi` (open; every binary block occurs in π).  Three routes are stated
in `src/NormalNumbers/PiDisjunctiveRoutes/`, one file per route.  Three treadmills work them at once,
one per worktree; each lap reads this file and works **its own lane only**.

| Lane | Worktree / branch | File | Route premise |
|---|---|---|---|
| 1 | `nn-pi-triple` / `research/pi-triple` | `TripleReturn.lean` | `PiQuantitativeTripleReturn` |
| 2 | `nn-pi-reservoir` / `research/pi-reservoir` | `PrimeReservoir.lean` | `PiPrimeReservoirSupport` |
| 3 | `nn-pi-disk` / `research/pi-disk` | `DiskResidue.lean` | `DiskResidueCover` |

## Objective (all lanes) 🎯

The goal is **new mathematics** - a conjecture graph whose nodes move toward the sink - not
formalization.  A lap's unit of progress is one of:

- a **green edge**: a proved implication between nodes, sorry-free;
- a **new node** strictly weaker than the lane's route premise, with a stated mechanism, an odds
  estimate, and a refutation probe;
- a **probe-refuted node**: a numeric or exact computation, plus a Lean witness where feasible,
  showing a node (including a route premise) false or its constant wrong.

Lane 2 was ranked first by the session that stated the routes (65% confidence in that ranking):
it has an uncancellable arithmetic source and a precisely missing correlation estimate.

## Standing rules (every lap, every lane) 🚦

1. **Stay in your lane's files**: your route file, new files named
   `src/NormalNumbers/PiDisjunctiveRoutes/<Lane>*.lean`, `scripts/pi_route<N>_*.py`,
   `docs/pi-routes/route<N>.md`, and `HANDOFF-pi-route<N>.md`.  The other two lanes' files, the
   top-level `PiDisjunctiveRoutes.lean`, `DIRECTION.md`, and this file belong to no lane - leave them.
2. **Frozen statements**: never restate, weaken, rename or delete the route premise, the transfer
   theorems, or the bridge theorems.  New nodes go alongside them.
3. **Costume audit on every new node, the lap it is named**: (a) does the sink, or normality of π,
   already imply it?  If yes it is a restatement, not an advance.  (b) Is it equivalent to the sink,
   or to the route premise it was meant to weaken?  Then it is the sink in a costume.  Route 1's `TripleReturn` is *equivalent* to the
   sink, and all three route premises imply it; the routes are worth something only where their
   arithmetic gives a lever the plain digits lack.  Record the verdict in the node's docstring.
4. **Degenerate-corner check before freezing a node**: plug in index 0, k = 0, empty ranges, the
   smallest prime; try `¬ Node` at the corner in a scratch file.  A false node makes every edge out of
   it free.
5. **Literature results enter as named hypothesis `Prop`s**, never `axiom`.  Known theorems are not
   destinations; prove one only when an edge needs it.
6. **Probes**: uv inline-dependency Python under `scripts/`, exact integer/rational arithmetic where
   possible (mpmath/gmpy2 for π bits).  A probe states the number it must reach before it runs, and
   includes a known-answer control (e.g. a rational or a square in place of the disk).
7. **Build only your module**: `lake build NormalNumbers.PiDisjunctiveRoutes.<Lane>` (plus any new
   lane modules).  Never a whole-project `lake build`.
8. **Handoff**: overwrite `HANDOFF-pi-route<N>.md` each lap - the lane's current node graph (nodes,
   edges, odds, probe results), what this lap did, the single next move.  Keep a false-starts list
   (idea / why it looked promising / why it fails / witness) in `docs/pi-routes/route<N>.md`.
9. **Self-stop** only when the bridges are green AND the lane's research question has an answer: a
   mechanism-backed node strictly between premise and known facts, or a stated obstruction (in Lean
   where possible) plus the false-starts doc.

## Lane 1 - triple return (`TripleReturn.lean`)

**First (one lap):** prove `tripleReturn_iff_disjunctive` and
`pi_disjunctive_of_quantitativeTripleReturn`.  Ingredients exist: `Furstenberg.isClosed_invariant_finite_or_univ`
is proved; `IsDisjunctive` is in `Disjunctive.lean`.

**Research question:** `TripleReturn` is the sink re-targeted, so the lane's value is whether a
*single, specially chosen* membership in the ×2-orbit closure `K` of π is provable from arithmetic.
Candidates to examine: targets `t` tied to π by a known identity (BBP-type, `3π`, `π/2`, a rational
multiple); orbit-closure facts that hold for every irrational (e.g. `K` contains a non-periodic point,
accumulation structure); what extra closure property short of ×3-invariance Furstenberg's argument
actually uses.
**Probe:** first-return index `n_k` of `‖(2^n − 3)π‖ < 2^-k` for k up to ~20, against the heuristic
`~2^k` and the premise's `C·4^k`.  This tests the premise's constant, nothing more.

## Lane 2 - fresh BBP prime denominators (`PrimeReservoir.lean`)

**First (one lap):** prove `fresh_prime_dvd_head_den` (p-adic valuation: the pole at p survives) and
`pi_disjunctive_of_primeReservoirSupport` (rectangle inside the target cylinder, BBP tail
`O(n^-2)` below the margin, `bbp_split`).

**Research question:** the joint support of `(fract bbpPrimeReservoir n, fract bbpResidual n)`.  Each
fresh prime p = 8j+1 or 8j+5 in (4n, 8n) contributes `c·16^(n−j) mod p / p`; the residues of a power
of 16 modulo many distinct primes are the uncancellable arithmetic.  Separate marginals do not
suffice (a rational telescoping control can lock the sum on a diagonal), and conditioning on the exact
residual is forbidden (it can encode n).  Find the weakest node that gives joint support: e.g. a
two-variable Weyl-sum bound `Σ_{n≤N} e(h·R_n + l·S_n) = o(N)` for (h, l) ≠ 0 restricted to a
structured subsequence, or a statement that the reservoir is dense along every residual-interval
subsequence, with the costume audit applied.
**Probe:** exact computation for n up to a few thousand: 2-D discrepancy of the pair, the
correlation of the two coordinates, and the same statistics with the reservoir replaced by a
non-prime denominator set (control).

## Lane 3 - integer disk residues (`DiskResidue.lean`)

**First (one lap):** prove `diskPhase_shadow` (lattice squares sandwich the disk between radii R ± √2)
and `pi_disjunctive_of_diskResidueCover` (the middle-half margin absorbs the shadow error).
`DiskDivisorIdentity` stays a hypothesis `Prop` unless an edge needs it.

**Research question:** `DiskResidueCover` is close to "π's binary blocks cover every window"
re-encoded through a lattice count.  It is worth something only if the quadratic arithmetic gives a
handle: via `DiskDivisorIdentity`, `diskCount(4^n) mod 8^n` is a χ₄-weighted divisor sum of floors
`⌊16^n/d⌋`.  Ask which range of d carries the residue modulo `8^n` (small d, hyperbola-method
middle, large d), and whether the small-d part is an explicit, analysable function.  The square count
is the negative control: its phases tend to zero, so any argument that works for squares proves too
much.
**Probe:** `diskResidue n` exactly for n up to ~13 (integer square roots), decomposed by d-range via
the identity, with the square count as control.
