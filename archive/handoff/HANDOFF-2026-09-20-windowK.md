# HANDOFF 2026-09-20 — `windowK` / `PrefixDecay` lap: DONE, `src/NormalNumbers/G4WindowK.lean` sorry-free

Branch `wip/g5-prime-subset`.  Commits `a532c74` (skeleton), `ca643ff` (leaves 2+6), `7a47c0d` (leaf 3, sorry-free).

## Result

`src/NormalNumbers/G4WindowK.lean` is **sorry-free**; all 14 ratified kickoff statements are present
verbatim.  Axiom-clean (`[propext, Classical.choice, Quot.sound]`) for
`isNormal_G4_of_prefixDecay`, `isNormal_G4_of_windowDecayK`, `window_tail_tendsto_zero`,
`windowDecayK_of_prefixDecay`, `norm_fullWindowMean_sub_le`, `fullWindowMean_eq_prefixSum`,
`windowK_le_windowJ`, `tendsto_windowK`.  Pure addition: no existing statement touched (the only edit
outside the new file is one `import` line in `src/NormalNumbers.lean`).

## The crux advance

The G₄ window law now rests on **one sector-free `o(1)` statement**:

    PrefixDecay h : ∀ ε > 0, ∀ᶠ M, ∀ k, 1 ≤ k ≤ windowK M → ‖∑_{m<M} e(h · truncTail k m)‖ ≤ ε M

— no Chowla/SD split, no main terms, no constants, no rate — and `isNormal_G4_of_prefixDecay` closes
the headline from it.  This is strictly weaker input than the `G4WiringSummatory` route
(`RoughSummatory`, an SD-with-shifts asymptotic on parity classes), which stays valid beside it.

The mathematical content of the lap is **leaf 3**, `window_tail_tendsto_zero`, now a theorem:
dropping all window sites above `K = windowK N = ⌊log₂log₂log₂N⌋+1` costs at most

    28 π |h| / log₂ log₂ N   →  0.

Two facts make the triple-log schedule work, and they are the reason the fixed-`K` answer of probe 13
("no for fixed `K`") does not block the route:

* `sum_window_omegaR_le` (new) + `logB_le` (new): the window **average** of `ω(n+j+1)` on `[N,2N)` is
  `≤ log₂(4(log 4N + 1)) ≤ log₂log₂N + 6`, via `G4FarTail.sum_omegaR_add_le` with `X = 2N`, `ρ = j+1`
  (the `j`-dependence inside the log is absorbed by `2N + j + 1 ≤ 4N`).  Only the average is needed —
  the pointwise maximum `≍ log N`, which forced `windowJ` to be double-log, never appears.
* `sq_lt_four_pow_windowK` (new): `(log₂log₂N)² < 4^{windowK N}`, from `Nat.lt_pow_succ_log_self`.

Quotient `(L₂+6)/L₂² ≤ 7/L₂ → 0`.  So the schedule genuinely drops **double-log → triple-log**, which
is what shrinks the number of shifts the crux must handle from `log₂log₂N` to `log₂log₂log₂N`.

Supporting leaf: `geom_tail_le` (`∑_{K ≤ j < J} 4^{-(j+1)} ≤ 4^{-K}`).

## Where the crux now stands

`PrefixDecay h` is a frozen node (never proved here, by design).  Two routes remain open for it:

1. via `G4WiringSummatory` / `G4SummatorySplit` (`RoughSummatory` → `RoughSummatoryPrefix` + `SDOdd`) —
   the asymptotic route, still with the multi-shift Selberg–Delange obligation;
2. directly, as an Elliott/Daboussi-type decay statement for `∏_{j≤k} e(h/4^j)^{ω(m+j)}` with
   `k ≤ windowK M` shifts.  The triple-log bound on `k` is the new leverage: any shift-uniform decay
   with a loss up to `exp(O(k))`, or even `(log M)^{o(1)}` per shift, now suffices — a loss budget that
   was NOT available under the double-log `windowJ` schedule.  Next attack: state the one-shift Halász
   input with an explicit shift-uniform constant and see whether `k ≤ log₂log₂log₂M` absorbs it.

## Next

Per the operator override, this lap is the last one; every other section of `DIRECTION.md` is DONE or
CLOSED.  Stopping here.

## Note on the repo-wide stop gate

`box done` was signalled but the repo-wide gate counts two *pre-existing, off-path* sorries, neither
touched by this lap and both predating it:

* `src/NormalNumbers/PrimeLambertOscillation.lean:95` — `phaseOscillation` (the disclosed open node
  gating `irrational_primeLambert`);
* `src/NormalNumbers/MahlerDriftOne.lean:380` — `exists_prime_nonresidue`.

This lap was a BOUNDED subset (the `windowK` override); if it is relaunched it should carry
`--done-when 'sorry-free:src/NormalNumbers/G4WindowK.lean'`, which is already satisfied.
