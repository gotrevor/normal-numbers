# HANDOFF 2026-10-10: product blocks → word blocks → run covers 🌱

State note for the product-block lane (`src/NormalNumbers/MahlerProductBlock.lean`).  The working
session ended cleanly after commit `90207c77` (2026-10-10 00:51 EDT) and was later recorded by a
recovery session; nothing was in flight.  Background: `docs/base5-product-block-2026-10-05.md`,
`docs/product-block-rungs-and-words-2026-10-06.md` (latest section: "Run blocks grow, by a real
witness").

## Where things stand (all committed on `wip/g5-prime-subset`, build green at `90207c77`)

- **Run blocks grow** (`runBlocks_grow`, `IsWordSetBlock.runs_card`, `IsWordBlock.two_card`): a run
  block of order `k`, and a binary `k`-word block, has more than `2^⌊k/4⌋/16` members.  Wiring
  proved; the core `exists_irrational_noOnes` (if `16·|S| ≤ 2^⌊k/4⌋`, one irrational `X` keeps `1^k`
  out of every `m·X`) is `sorry` with a hand proof in its docstring, confidence 90%.  Method: nested
  intervals + a per-scale union bound (cf. the Yavicoli / Falconer–Yavicoli many-set gap lemma).
  Waiver in `BarrierAudit.lean`.
- So the member count is pinned between exponential (this) and doubly exponential
  (`IsWordBlock.exists_ge`, `Literature.SzuszVolkmann1983`).
- **Run covers** (`RunCover`, `RunCoversGrow`): exact carry automaton
  `experiments/mahler_run_cover_exact.py`.  The earlier ILP "k=3 optimum 3" was a `B ≤ 2000`
  artifact (`{137,213,243}` fails at `B = 5177`); `{1,3,5,7}` is the k=3 cover
  (`runCover_three_one_three_five_seven`, units mod 8).  `twoAdic_runFree` solves the 2-adic side.
  Mixed obstruction `{3,7,21,35}` (`runCover_three_mixed`): covers every positive integer, yet
  `B = −23/127` works 2-adically and `y = 1/7` works in ℝ, so gluing the two completions fails.
  Maze row "Run covers from their 2-adic and real completions" (refuted, frozen).
  `RunCoversGrow` stays open (65%); block growth no longer depends on it.
- Tests: `experiments/test_mahler_product_block.py`, 15 pass
  (`uv run --with pytest --with numpy --with scipy python -m pytest -q`).
- Earlier, still valid: base-5 12-block inclusion-minimal; `IsRung.mul` (ladder dead); binary 2-word
  block `{1,3,5}` with hand proof; binary 3-word 13-block in Lean (a 12-member swap exists, not
  ported; low value).

## Open candidates (no work started)

1. **Cardinality gap for k-word blocks**: letting each `m` avoid its own word should push the lower
   bound to about `2^(k/2)`; the real question is whether the member count must be doubly
   exponential.
2. **`RunCoversGrow` junction window**: a two-sided count across the 2-adic/real seam.

## Scope notes

- Constructions and mechanisms over sweeps; block-shrinking by 3-word swaps judged low value.
- Lean statements + small `decide` wiring only; no proof grinding in an attended session.
- Tooling: `experiments/mahler_block_rs` (cargo --release, binary `mahler_block`).  Traps: greedy
  stalls when one constraint is too weak (4-words, runs k≥4); use `python -u` and a milp
  `time_limit`; Liouville bounds put ternary 2-word hand proofs out of reach (m ≥ 729).
