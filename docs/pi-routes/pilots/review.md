# Second-round pilot review, 2026-10-26

The mathematical results and their limits are recorded in `RoundTwoOscillator`,
`RoundTwoSpigot`, and `RoundTwoRadical`, with three scoped entries in `Maze.lean`
and checked declaration links in `MazeAudit.lean`.  Each route's main premise in
`RoundTwo.lean` remains open.  No unconditional digit-disjunctivity result follows.

## Provenance

All runs used Claude Opus, low effort, one lap, review/reflection disabled, no
Aristotle, and a 20,000 legacy context-token limit.  Run IDs:

- `nn-pi-oscillator-20261026-223405-513000`
- `nn-pi-spigot-20261026-223715-118000`
- `nn-pi-radical-20261026-223804-925000`

Worker sources were copied into `research/pi-routes` for host review.  The parent
added `not_quartic_endpoint_certificate`, frozen quintic/word-one targets, shared
imports, and the Maze links.  The spigot note's “center” was corrected to “affine
offset”; an unsupported suggested width formula was removed.  The oscillator
worker branch was separately preserved at `c9dc968e` with normal commit hooks.
Worker worktrees are retained.  This initial integration was committed at
`621ef0c7`; the subsequent trunk landing also includes the sharp follow-up and
the broader research-retirement decisions.

## Operational lesson

The legacy token setting counts inherited context, not just new proof work.  The
oscillator transcript showed roughly 49k context against a 20k limit.  The laps
ended with code 143 after producing their proofs, while background commit hooks
were still building.  A stopped lap is not a completed commit.  Host builds and
actual proof declarations are the evidence; supervisor exit alone is insufficient.

Future bounded follow-up: 80k legacy context tokens, one Opus/low lap, explicit
checkpoint near 25 minutes.  The 35-minute supervisor setting only applies between
laps.  Workers deliver targeted builds and axiom checks; the parent runs the full
host build and ordinary commit hooks.  This avoids spending worker context waiting
on cross-platform full builds without bypassing the repository gate.

## Checks

Exact rational preflight controls are in `scripts/pi_pilot_preflight.py` and
`scripts/pi_oscillator_quadrature.py`.  Host review artifacts are under
`tmp/20261026-pi-round-two/`: integration build, headline declaration/axiom audit,
and commit build log.  The committed sources and normal build gate are the durable
record; scratch logs are local evidence only.

Host targeted build passed, including the Maze audit (207 rows, 100 linked,
107 disclosed legacy rows).  The seven headline declarations were inspected with
`#check` and `#print axioms`; each depends only on `propext`, `Classical.choice`,
and `Quot.sound`.  This validates the stated scoped results, not their open
pi-specific premises.

## Sharp follow-up and round closure

Run `nn-pi-oscillator-sharp-20261026-232845-782000` used one Opus/low lap and an
80k legacy context budget.  It delivered `RoundTwoOscillatorSharp.lean` and its
result note without a worker commit, as requested.  The supervisor reported exit
143; the parent reviewed the delivered source rather than treating that code as
proof success.  `minimumDegreeWordOne` proves degree five is necessary and
sufficient for the word `[1]`.  `FixedDegreeBlindInterval` remains open.

All three broad second-round routes are now recorded as abandoned with current
methods in the Maze, with their exact failed subfamilies kept separately.  No
construction for `OscillatorCertificateSupply`, invariant for `SpigotEscapeBudget`,
or word-sensitive radical estimate was found.  The exact reopening requirements
are in `MAZE.md` and `round-two.md`.  No additional campaign is scheduled.
