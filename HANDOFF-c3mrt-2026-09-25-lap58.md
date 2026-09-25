# HANDOFF c3-mrt 2026-09-25 lap58 — obligation A, brick 3: the inner layer along a progression

**New file** `src/NormalNumbers/C3MrtProgInner.lean` (chain tip:
`lake build NormalNumbers.C3MrtProgInner`, 8989 jobs).  Sorry-free, 3 declarations, trust triple.
`lake build` green (9257).

* `inner_multi_bound_prog_witness` — `inner_multi_bound` with `lcm(d)` replaced by
  `progLcm Mo d`, for the class of a JOINT witness `n₀` (one satisfying both the progression and
  the `d`-congruences).  `inner_sum_prog_forms` (lap 56) supplies the class and the reindexing;
  `inner_harmonic_le_generic` / `window_gap_generic` / `progression_sum_bound_generic` (lap 46)
  were deliberately stated generic in the modulus and take `L'` verbatim; `multi_rung_spelling`
  needs only `0 < L'/d i` (`dvd_progLcm`).
* `inner_multi_bound_prog` — the class of an ARBITRARY `r`.  **The subtlety this lap surfaced**:
  the progression base `r` and the `d`-class witness are *independent*, and the two classes need
  not meet (CRT compatibility fails when `gcd(Mo, d i) ∤ r + i + 1`).  When they don't, the index
  set is empty and the bound is trivial; when they do, `Finset.filter_congr` moves the predicate
  to the joint witness.  My first statement conflated `r` with the witness — a real error the
  kernel caught.
* `multi_bound_of_rung_prog` — brick 2 (`multi_truncation_bound_set`) + `multi_full_sum_bound`
  + brick 3.

**`multi_full_sum_bound` is used UNCHANGED.**  It asks for `‖Inner d‖ ≤ 1 + R/lcm(d)`; brick 3
delivers `1 + R/progLcm Mo d` with `progLcm ≥ lcm`, i.e. *stronger*.  That is exactly the payoff of
lap 56's observation that nothing in the chain needs `L` to be least — the progression is free
here too.

## NEXT — obligation A, brick 4 (the last one)

The ε-chase and the uniform rung, along the progression:

1. `multi_correlation_of_uniform_rung_prog` — transcribe `multi_correlation_of_uniform_rung`
   (`C3MrtMultiChase`) with `multi_bound_of_rung_prog` in place of `multi_bound_of_rung`.  The
   only arithmetic change is the base-point bound: `univLcm_le_pow` gave `lcm d ≤ Y^K`; now
   `progLcm Mo d ≤ Mo · Y^K` (`Nat.lcm_le_mul` style: `lcm Mo L ≤ Mo * L`), so the threshold
   becomes `N₀ = Mo·Y^K·A^I + Mo·Y^K + 2`.  `Mo` is fixed, so nothing else moves.
2. `rung_multi_uniform_prog` — `rung_multi_uniform` (lap 52) with the admissible index set
   `Fintype.piFinset (range (Y+1)) ×ˢ range (Mo·Y^K + 1)` and `nondegenerateForms_prog` in place
   of `nondegenerateForms_of_tuple`.
3. Compose ⇒ **`ProgressionLogRung K`** discharged, and the ledger's obligation A becomes a
   theorem.  Then the only open item left is `LogToNaturalCorrelation` (the log-Chowla barrier)
   plus the `D`-uniformity/rate bookkeeping of lap 40.
