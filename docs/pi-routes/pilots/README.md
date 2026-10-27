# Bounded second-round mechanism pilots

The user authorized digging into the three proposals and using cheap treadmills.
These pilots test concrete mathematical mechanisms before any extended campaign.
Read `MAZE.md`, `docs/pi-routes/round-two.md`, and `RoundTwoPilotTargets.lean`.

The first three pilots have finished; see [review.md](review.md) for results and
the context-budget/build lesson.  The settings below describe those initial runs.
The [oscillator follow-up](oscillator-followup.md) explicitly overrides its budget
and assigns the final host build and commit to the parent.

Each run gets one Opus/low lap, a 20,000-token legacy context budget, and a
35-minute supervisor duration setting.  The supervisor duration is checked between
laps, not a hard deadline for a running lap.  Independently, check the actual clock
and finish a compiling checkpoint after about 25 minutes; do not begin another
large proof at that point.  No adaptive escalation or automatic extra laps.

## Shared contract

- Work only on the named pilot's new Lean file, its result note, and its probe script.
- Original premises, `RoundTwo.lean`, `RoundTwoPilotTargets.lean`, root imports,
  Maze files, pins, and other pilots' files are frozen for the worker.
- State every finding in Lean.  Prefer exact refutations and quantified scope.
  An open Prop is acceptable when a proof cannot be finished; label it accurately.
- Use targeted builds during work.  Run `#print axioms` and inspect types for the
  delivered results.  Keep the normal commit hooks; never bypass a build gate.
- The first checkpoint should compile even if hard leaves remain open.  Do not
  spend the entire lap on setup, routine bridges, or increasing a numerical range.
- A successful pilot gives a reusable mechanism, a scoped obstruction with a
  positive control, or a precise unresolved question.  Equivalence alone is not
  a proof that every possible approach is impossible.
- Record a prospective Maze entry, aliases, exact crux, and reopening requirement
  in the result note if a family is abandoned.  The parent integrates the shared
  Maze files after reviewing the proof and its actual scope.
- No web search, remote proof services, new dependencies, other agents, or further
  treadmills.  Use `git-safe`.  Scratch belongs under `tmp/<pilot-name>/`.
- Finish by committing your files and returning normally.  One lap is the host
  completion boundary; do not loop on the repository-wide sorry census.

## Files

| Pilot | Brief | New Lean module | Result note |
|---|---|---|---|
| oscillator | `oscillator.md` | `RoundTwoOscillator.lean` | `oscillator-result.md` |
| spigot | `spigot.md` | `RoundTwoSpigot.lean` | `spigot-result.md` |
| radical | `radical.md` | `RoundTwoRadical.lean` | `radical-result.md` |

Lean modules live under `src/NormalNumbers/PiDisjunctiveRoutes/`; briefs and notes
live in this directory.  Optional scripts are `scripts/pi_pilot_<name>.py`.
