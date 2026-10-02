# KICKOFF: normality's master conjectures (LAUNCHED 2026-10-02)

**Target.**  The Schanuel pattern for normality: `BorelConjecture` and `BaileyCrandallHypA`
(`src/NormalNumbers/MasterConjectures.lean`) as named hypothesis `Prop`s, and everything that
follows from them.  Frozen byte-identical from the launch commit: `circDist`, `bcOrbit`,
`HasFiniteAttractor`, both conjecture `Prop`s, and the three planted theorem statements.
Proposal: `docs/proposal-normality-master-conjectures-2026-09-29.md`.

**Phase 1: the planted consequences.**
1. `hypA_lnTwo`: show `bcOrbit 1 X 2 = lnTwoOrbit`; rule out the finite-attractor branch
   (Bailey–Crandall Thms 2.8-2.10: an attractor of the surrogate orbit transfers to `{2ⁿ ln 2}`,
   which forces `ln 2` rational; irrationality of `ln 2` may enter as a cited `Literature` Prop if
   mathlib lacks it); then `LnTwo.lean:333`.
2. `hypA_pi_base16`: the BBP surrogate orbit (Bailey–Crandall eq. (3), `p = 120n²−89n+16`,
   `q = 512n⁴−1024n³+712n²−206n+21`) via the `PiBBP`/`KickedOrbit` machinery.
3. `borel_sqrt_two`: `√2` irrational and algebraic.

**Phase 2: the consequence graph.**  State (then prove) further consequences, each a theorem in
`MasterConjectures.lean` or a sibling module in the root import:
- Hypothesis A ⇒ `π` normal in base 2 (base change `16 = 2⁴`), `ln 2` normal in base 3
  (Bailey–Crandall Thm 1.1), `π²` in base 64 via `PiSqBBP` if the surrogate fits Hypothesis A's
  shape (if it does not, say so in Lean: a theorem or a Maze row).
- Borel ⇒ every irrational algebraic is disjunctive in every base; Borel ⇒ the BBCP-type count
  statement already in the repo, as a consistency edge.
- Consistency edges, Hypothesis A ⇒ results the repo already proves unconditionally (e.g. Stoneham),
  where the shape fits.

**Phase 3: the Maze test** (the proposal's item 3).  For every `Maze.lean` row whose `reopenIf`
mentions equidistribution, normality or a BBP/Bailey–Crandall orbit, decide whether Hypothesis A
or Borel implies the missing input.  Implied: a wiring theorem (a new conditional edge).  Not
implied even by these: record that as Lean (a theorem showing the gap, or an annotated Maze row
citing a declaration).  `#maze_audit` must stay green.

**Rules.**  Every new `Prop` obeys the guard rule (content locator + degenerate cases, same lap).
Never weaken a frozen statement; a false one is recorded as an obstruction.

**Done when.**  Phases 1-3 complete: the three planted theorems proved, at least four further
consequence theorems proved, the Maze test recorded for every qualifying row, build green, axioms
= trust base, STATUS/OVERVIEW/HEADLINES (bet 3) rows.

**Engine.**  Opus/low treadmill, review lap every 4.
