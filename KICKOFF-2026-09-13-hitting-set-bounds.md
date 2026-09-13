# KICKOFF 2026-09-13 — hitting-set upper bounds as theorems (U1–U4) and the base-5 lower wiring (L1) 🧵

*Context: `docs/hitting-set-invariant-2026-09-13.md`.  The invariant `S(g,k)` is the least size of a
per-block hitting set (`Literature.IsHittingSet`, `src/NormalNumbers/Literature.lean` ≈ line 149).
Node N1 (`SparseAdversary.lean`) landed today.  This kickoff turns four automaton verdicts into
theorems with the repo's signed base-`g` engine, exactly the way `MahlerBase5Exact.lean` proves
`M(5,1) ≤ 6`, and wires one existing lower bound.  One new file.*

## Objective

New file `src/NormalNumbers/HittingSetBounds.lean` (add `import NormalNumbers.HittingSetBounds` to
`src/NormalNumbers.lean`), proving:

```lean
theorem IsHittingSet.mono {g k : ℕ} {S T : Finset ℕ} (h : Literature.IsHittingSet g k S)
    (hST : S ⊆ T) : Literature.IsHittingSet g k T

/-- `S(4,1) ≤ 3`: three multipliers hit every base-4 digit. -/
theorem hitting_4_1_three : Literature.IsHittingSet 4 1 {1, 10, 14}          -- certs h41_d0..d3
/-- `S(5,1) ≤ 5`; contrast `M(5,1) = 6` (`mahler_M_five_eq_six`): the set is not an initial segment. -/
theorem hitting_5_1_five : Literature.IsHittingSet 5 1 {1, 2, 3, 4, 6}       -- certs h51_d0..d4
/-- `S(2,2) ≤ 2`. -/
theorem hitting_2_2_two : Literature.IsHittingSet 2 2 {1, 3}                 -- certs h22_w00..w11
/-- `S(2,3) ≤ 4`. -/
theorem hitting_2_3_four : Literature.IsHittingSet 2 3 {1, 3, 5, 7}          -- certs h23_w000..w111
/-- The initial segment `{1,2,3,4}` is NOT a hitting set at base 5 (so `{1,2,3,4,6}` above is
minimal among its subsets containing `6`... state only what is proved): from
`Mahler.mahler_lower_bound_base5`. -/
theorem not_hitting_5_1_four : ¬ Literature.IsHittingSet 5 1 {1, 2, 3, 4}
theorem not_hitting_5_1_five : ¬ Literature.IsHittingSet 5 1 {1, 2, 3, 4, 5}
```

## Certificates (already emitted and Python-verified)

`experiments/adder_baseg_emit.py h41 | h51 | h22 | h23` (FAMILIES entries added 2026-09-13) wrote
`experiments/certs/adder_cert_h41_d{0..3}.json` (140 ambient states, ≤ 11 live),
`adder_cert_h51_d{0..4}.json` (144 ambient), `adder_cert_h22_w{00,01,10,11}.json` (12 ambient),
`adder_cert_h23_w{000..111}.json` (26880 ambient, ≤ 30 live).  Each JSON carries `live_list`,
`rho`, `omega`, `forced` in the emitter's encoding, which mirrors `AdderBaseG.lean` bit-for-bit
(carry offset, `gwinSize = g^(k−1)`, mixed radix over the channel list, channel 0 least
significant; single-track alphabet `σ = x < g`).  The emitter re-verified C1/C1'/C3' in Python
before writing.

Transcribe exactly as `MahlerBase5Exact.lean` does for `m5Chans w`:

```lean
def h41Chans (d : ℕ) : List ZChannel := [⟨1, 0, [d]⟩, ⟨10, 0, [d]⟩, ⟨14, 0, [d]⟩]
def h41live0 : ℕ → Bool := fun s => [...].contains s
def h41rho0 : ℕ → ℕ := ...        -- 0 off the listed states
def h41omega0 : ℕ → ℕ := ...
def h41forced0 : ℕ → Option (ℕ × ℕ) := ...
theorem h41_cert0 : checkCertA (fun σ s' => gfamPred 4 (h41Chans 0) (σ % 4) (σ / 4) s')
    4 140 h41live0 h41rho0 h41omega0 h41forced0 = true := by decide +kernel
```

and conclude per block with
`signed_engine_g_single 4 (by norm_num) (h41Chans d) rfl h41_certd X hX (by decide) (by decide) (by decide)`,
which yields `∃ ch ∈ h41Chans d, ∀ N, ∃ n, N ≤ n ∧ OccursAt 4 (ch.a * X) ch.word n`; `fin_cases`
on the membership gives the multiplier (`1`, `10`, `14`) with `simpa`.  The per-block quantifier in
`IsHittingSet` ranges over lists `w` with `w.length = k` and digits `< g`: for `k = 1` write
`w = [d]` and `interval_cases d`; for `k = 2, 3` destructure `w = [a, b]` / `[a, b, c]` and
`interval_cases` each digit.  ⚠️ Word orientation: the emitter's JSON `word` field is the ground
truth for which certificate serves which `w`; the engine concludes `OccursAt g (ch.a * X) ch.word n`
with `ch.word` the same list, so pair each block with the certificate whose `word` equals it.
For `h23` (26880 ambient states) kernel `decide` may be slow: try `decide +kernel` first, then
`native_decide` (acceptable at this tier); if neither closes in reasonable time, leave U4 as a
named leaf with the certificate defs in place and say so.

## The lower wiring (L1)

`Mahler.mahler_lower_bound_base5 : ∃ α, Irrational α ∧ ∀ m, 1 ≤ m → m ≤ 5 → ∃ N, ∀ n, N ≤ n →
¬ OccursAt 5 (m * α) [1] n` (used in `MahlerBase5Exact.mahler_M_five_eq_six`).  Unfold
`IsHittingSet` at that `α` and `w = [1]`: the hitting clause gives some `m ∈ {1,2,3,4}` with
occurrences beyond every `N`, the lower bound gives an `N` beyond which there are none.  Ten lines.

## What this means (docstrings, no headlines)

With `SparseAdversary.lean`: `S(2,2) ≤ 2`, `S(2,3) ≤ 4`, `S(4,1) ≤ 3`, `S(5,1) ≤ 5` are theorems;
`{1,11}` fails at base 4 and `{1,3,5}` at `(2,3)` are theorems; `{1,2,3,4}` fails at base 5 is a
theorem.  The matching lower bounds `S(g,k) ≥ s` (every set of size `s−1` fails) remain open - they
are the frozen nodes N2/N4′ - and nothing here claims them.

## Ground rules

- Touch only the new file and the one import line (the emitter and certificates are already
  committed).  Never edit `DIRECTION.md` or any existing Lean file.  Commit on the current
  branch (`wip/adder-tower-c9`), message naming what was proved.
- Report the ADVANCE: which of U1–U4, L1, mono are proved, which leaves remain and why; never a
  sorry tally.  Evidence: `lake build` green and `lean-green --axioms <name>` on each theorem
  (standard triple, plus `Lean.ofReduceBool` where `native_decide` was needed - fine).
