# KICKOFF 2026-09-13 — `S(7,1) ≤ 7` as a theorem, and the base-7 lower wiring 🧵

*Context: `docs/hitting-set-invariant-2026-09-13.md` (table row `(7,1)`, recount of 21:50).  The
invariant `S(g,k)` is the least size of a per-block hitting set (`Literature.IsHittingSet`,
`src/NormalNumbers/Literature.lean` ≈ line 149).  `src/NormalNumbers/HittingSetBounds.lean` (lap of
19:43–20:43) proved `S(4,1) ≤ 3`, `S(5,1) ≤ 5`, `S(2,2) ≤ 2`, `S(2,3) ≤ 4` from emitted
certificates with the signed base-`g` engine, plus `IsHittingSet.mono` and the base-5 lower wiring.
This kickoff does the same for base 7, where the search found `{1,2,3,4,5,6,13}` (88 s, three
channel-distinct 7-sets below 24, no 6-set below 24).  One new file.*

## Objective

New file `src/NormalNumbers/HittingSetBase7.lean` (add `import NormalNumbers.HittingSetBase7` to
`src/NormalNumbers.lean`, next to the `HittingSetBounds` line), namespace `NormalNumbers.Adder`,
proving:

```lean
/-- `S(7,1) ≤ 7`: seven multipliers hit every base-7 digit.  Certificates `h71_d0..d6`. -/
theorem hitting_7_1_seven : Literature.IsHittingSet 7 1 {1, 2, 3, 4, 5, 6, 13}

/-- The initial segment `{1..8}` is NOT a hitting set at base 7: digit `1` is absent from every
`m·α`, `m ≤ 8`, for Mahler's `α` (`Mahler.mahler_lower_bound_base7`, `MahlerPrimeLowerBound.lean`
line 80). -/
theorem not_hitting_7_1_eight : ¬ Literature.IsHittingSet 7 1 {1, 2, 3, 4, 5, 6, 7, 8}

/-- Hence `{1..6}` is not one either (`IsHittingSet.mono` contrapositive). -/
theorem not_hitting_7_1_six : ¬ Literature.IsHittingSet 7 1 {1, 2, 3, 4, 5, 6}
```

## Certificates (already emitted and Python-verified)

`experiments/adder_baseg_emit.py h71` (FAMILIES entry added 21:58) wrote
`experiments/certs/adder_cert_h71_d{0..6}.json`: ambient `9360` states (mixed radix over the
channel list `1, 2, 3, 4, 5, 6, 13`, `gwinSize = 1`), alphabet `7`, `n_live` between 14 and 21,
C1/C1'/C3' verified in Python.  Same encoding as `h51` (`adder_cert_h51_d*.json`), which
`HittingSetBounds.lean` lines 177–240 transcribe as

```lean
def h51Chans (d : ℕ) : List ZChannel := ...
def h51d0live : ℕ → Bool := fun s => [24, 30, 56, 87, 113, 143].contains s
def h51d0rho : ℕ → ℕ := ...        -- 0 off the listed states
def h51d0omega : ℕ → ℕ := ...
def h51d0forced : ℕ → Option (ℕ × ℕ) := ...
theorem h51d0_cert : checkCertA (fun σ s' => gfamPred 5 (h51Chans 0) (σ % 5) (σ / 5) s')
    5 144 h51d0live h51d0rho h51d0omega h51d0forced = true := by decide +kernel
```

Do exactly that with `h71Chans d := [⟨1,0,[d]⟩, ⟨2,0,[d]⟩, ⟨3,0,[d]⟩, ⟨4,0,[d]⟩, ⟨5,0,[d]⟩, ⟨6,0,[d]⟩, ⟨13,0,[d]⟩]`
and ambient `9360`.  The JSON fields are `live`, `rho`, `omega`, `forced_sig`, `forced_dst`
(lists indexed by state) and `n_live`; read them with a short Python one-liner rather than by eye.

Kernel cost: `9360 · 7` edges per certificate, about a third of the `h23` family (`26880`), which
needed sixteen `1680`-state chunks glued by `checkEdgesOnA_of_chunks` (`HittingSetBounds.lean`
line 77, with `checkCertA_of_edgesOn`).  Try `decide +kernel` on the whole certificate first; if
it does not close within a few minutes, chunk exactly as `h23w000_c0..c13` do (line 360 on).
`native_decide` is acceptable at this tier if both fail; say so in the docstring.

Conclude per digit with `signed_engine_g_single 7 (by norm_num) (h71Chans d) rfl h71d{d}_cert α hα
(by decide) (by decide) (by decide)` and `interval_cases d`, exactly as `hitting_5_1_five`
(`HittingSetBounds.lean` line 1131) does; `fin_cases` on the channel membership gives the
multiplier.  The word orientation is the JSON `word` of each certificate; for `k = 1` it is `[d]`.

## The lower wiring

`Mahler.mahler_lower_bound_base7 : ∃ α, Irrational α ∧ ∀ m, 1 ≤ m → m ≤ 8 → ∃ N, ∀ n, N ≤ n →
¬ OccursAt 7 (m * α) [1] n`.  Unfold `IsHittingSet` at that `α` and `w = [1]` exactly as
`not_hitting_5_1_four` does; then `not_hitting_7_1_six` is `IsHittingSet.mono` (subset
`{1..6} ⊆ {1..8}`) composed with it.

## What this means (docstrings, no headlines)

With the search's lower half (`no 6-set below 24`), `S(7,1) = 7` has its upper half as a theorem;
`{1..8}` and `{1..6}` failing are theorems.  Nothing here claims the lower bound `S(7,1) ≥ 7`
(every 6-set fails), which is open (node N4′ territory).

## Ground rules

- Touch only the new file and the one import line.  Never edit `DIRECTION.md` or any existing
  Lean file.  The tree may contain an uncommitted `papers/*.md`; leave it alone (do not `git add`
  it).  Commit on the current branch (`wip/adder-tower-c9`), message naming what was proved.
- Report the ADVANCE: which of the three theorems are proved and by which route (direct kernel
  decide / chunked / native), which remain and why; never a sorry tally.  Evidence: `lake build`
  green and `lean-green --axioms NormalNumbers.Adder.<name>` on each theorem.
