# T3c verdict: the critical-slice run cap is provable and nearly empty 🧱

Ren / Fable 5.1, host session 2026-09-20.  Direction pushed at Trevor's request ("push those
two directions") after the FFT / Euler-formula conversation.  Instrument:
`experiments/t3c_critical_runs.py` (+ `experiments/test_t3c_critical_runs.py`, hand-computed
expectations).  Nothing here changes the status of 6-disjunctivity of α₂,₃.

**The one ask.**  Park T3c as a named node; do not spend a lap on it.  The theorem is real,
one wiring lap away, and says almost nothing.

## 1. What T3c is, precisely

Block `K` of the base-6 expansion of `α = α₂,₃ = Σ 1/(3^k 2^(3^k))` is positions
`3^(K−1) < n ≤ 3^K`, with `a = n − K`, `c = 3^K − n`, and readout
`v_n ≈ (3^a mod 2^c)/2^c` (`stoneham_base6_readout`, formalized, error `2·3^(a−1)/2^(3^(K+1)−n)`).
Along the block `a` rises and `c` falls, so `log₂(3^a/2^c)` climbs by `1 + log₂3 ≈ 2.585`
per position.  The **critical position** `n*` is the last `n` with `3^a < 2^c`; there
`v = 3^a/2^c ∈ [1/6, 1)` and the two-log form `δ = c·log 2 − a·log 3 ∈ (0, 2.585)`.

A run of `L` fives at positions `n*+1 … n*+L` means `v ≥ 1 − 6^(−L)`, i.e. `D·6^L ≤ 2^c` with
`D = 2^c − 3^a`.  Every lower bound on `D` is a cap on `L`:

| bound on D | source | cap on L |
|---|---|---|
| `D ≥ 1` | trivial | `c·log₆2 ≈ 0.237·3^K` |
| `D ≥ 3^a·2^(−a/3)` | `sep_two_three` (collatz-moonshot, first-principles) | `≈ 0.129·a ≈ 0.050·3^K` |
| `δ ≥ C/a^436`, `1−v ≥ δ/2` | `rhinLite_log23_measure` (same repo) | `436·log₆a + 15 077` |

`log₂(1/C) = 1 + 6000·log₂(396/5) + 436·log₂6 ≈ 38 972.6` (`rhinLiteSepC`).  The polynomial
cap beats the `β = 1/3` cap from `K = 12` on and is `O(log n)`, which is the right *shape*.

## 2. What the digits actually do

| K | n* | a | c | L (true) | cap 1/3 | cap poly | δ |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 4 | 33 | 29 | 48 | 0 | 4.5 | 15 896 | 1.41 |
| 5 | 97 | 92 | 146 | 1 | 11.9 | 16 177 | 0.127 |
| 8 | 2 543 | 2 535 | 4 018 | 1 | 326.9 | 16 984 | 0.083 |
| 13 | 616 776 | 616 763 | 977 547 | 0 | 79 532.5 | 18 321 | 0.536 |

(Full table `K = 4 … 13` from the probe; `K ≤ 9` cross-checked against α's actual digit
stream computed by exact integer arithmetic, independent of the readout theorem.)

The true run at the critical position is **0 or 1 in every block computed**, and it must
be: `δ` is one sample per block of a quantity spread over `(0, 2.585)`, so a long run needs
`δ` tiny, i.e. `c/a` a convergent-quality approximation to `log₂3` at the one value of
`(a, c)` the block happens to land on.  That is a Diophantine coincidence of the same rarity
as the deep-approach events censused for ln 2 (N1); at most a handful ever.

Consistency check worth recording: `n*` of block 8 is **2543**, the last position of the
Bailey–Borwein forced zero-run `2188 … 2543` (the zero-run is exactly `3^a < 2^c/6`, and it
ends where `3^a` crosses `2^c/6`, one step before the critical crossing).

## 3. Verdict

- **Provable**: yes, one wiring lap.  Ingredients all exist: `stoneham_base6_readout` here,
  `rhinLite_log23_measure` (or `sep_two_three`) in collatz-moonshot.  Same toolchain
  (`v4.33.1`) and Mathlib pin in both repos, so a `path`-dependency in `lakefile.toml` is the
  clean route; the alternative is a hypothesis-parameterised statement
  `TwoLogMeasure C κ → run cap` discharged where both are imported.
- **Content**: a cap of `436·log₆n + 15 077` on a run whose observed length is `≤ 1`, at one
  position per block.  Nobody would cite it.  Its only value is the milestone "the Diophantine
  engine outputs a digit statement", and that milestone is not worth a lap while the G₄ wiring
  is live.
- **Why the mid-block slice gives nothing**: `frac((3/2)^m)` at `m = (3^K − K)/2` has no
  unconditional lower bound at all (`3^m mod 2^m ≥ 1` is the whole of what is known for a
  single `m`); Mahler's `Z`-number problem is the reason.
- **What a general-position theorem would need**: a run of zeros or fives at an arbitrary `n`
  in the block is `|3^a − j·2^c|` small for `j ≤ 5` (`j = 1` only at the critical slice);
  the engine covers `j = 1` on one side only, so the general statement is outside it.

Parked node name: `CriticalSliceRunCap` (statement in §1, third row).
