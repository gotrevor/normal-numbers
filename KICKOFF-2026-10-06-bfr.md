# KICKOFF 2026-10-06: the BFR bet (operator directive; supersedes the stretch kickoff)

Branch `proof/cantorexp-stretch`, worktree `~/src/nn-stretch`.  The stretch node is proved and
landed on trunk (`dfff8dca`).  This directive is the BFR thread, which is **not drift**: Trevor
authorized it explicitly ("dig into this until that 15% drops below 1%; I'll take that bet on
notable").  Current estimate: 5% (lap 3).

## Question

Does the method that proved the stretch (3-adic Farey separation, `padic_sep` /
`hit_mass_padic`: bound the **union** of hitting numerators, not the incidences) yield a new
statement about rationals near the Cantor set `K` (Broderick–Fishman–Reich, Bugeaud–Durand), or
a restricted-digit / modular-hyperbola count of independent interest?

## Candidate statements (freeze each in `StretchBFR.lean`, then decide it)

1. **Dual BFR count.**  `#{P ∈ C_b : ∃ p/q, q ≤ Q, 0 < |P/3^b − p/q| < δ}` (Cantor endpoints
   near rationals) for `δ` below the cylinder scale.  Is the 3-adic union bound sharp here, and
   is this count known?  Compare the measure-level analogue (Weiss / Kleinbock–Lindenstrauss–Weiss
   quantitative nondivergence for the Cantor measure).
2. **Restricted-digit hyperbola count.**  `RunEnteringCount` is provable by a card version of
   `hit_mass_padic` (lap-3 handoff).  Prove it, then state the cleanest standalone form:
   `#{P ∈ C_b : ∃ q ≤ Q, |P q mod 3^b| ≤ R}` versus `(R Q)^{log₃ 2}`.  Sweep prior art
   (Shparlinski and coauthors on modular hyperbolas; Kristensen–Thorn–Velani simplex lemma,
   whose archimedean form this dualizes).
3. **Does it touch `N_K(Q, δ)` itself?**  The lap-3 verdict is "the elementary analogue of the
   trivial `Q^{2 dim K}` bound".  Make that precise as a Lean statement, and test whether combining
   the 3-adic and archimedean separations beats it in any regime of `(Q, δ)`.  This is where the
   remaining percentage sits.
4. **Other bases.**  Does `padic_sep` need a prime base?  Port the statement to `K₅` (base 5,
   prime) and ask what breaks for a composite base such as 10.

## Rules

- Every candidate becomes a frozen statement plus a verdict: proved, refuted with a Maze row, or
  known (a cited `Literature` Prop).  Prior-art sweep before claiming novelty
  (`papers followups` on BFR 1011.xxxx, Bugeaud–Durand 2016, Schleischitz, He–Liao).
- Restate the BFR-bet confidence in the `StretchBFR.lean` module doc at the end of every lap.
  Stop when it is below 1% with every route in the Maze, or when a route survives with frozen
  statements and a plan.
- Root audits must be green before each handoff (`lake build` of the root, retrying EMFILE).
