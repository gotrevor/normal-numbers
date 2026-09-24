# Handoff — PairDecouple, the PROOF direction, laps 1–8

**Branch** `wip/pd-prove` · **HEAD** `8ff1294` · tree clean, NOT pushed
**Build**: full `lake build` green, **9190 jobs**.
**Objective**: `KICKOFF-2026-09-24-pd-prove.md` (supersedes `DIRECTION.md` and older handoffs).

## State

`src/NormalNumbers/PairDecoupleProve.lean` carries **exactly one `sorry`**, `shiftCorr_all`.
The ratified target `pairDecouple_all` is untouched in statement and is PROVED from it.
Everything else added this session is sorry-free with `#print axioms` = `[propext,
Classical.choice, Quot.sound]`.

## New files (all additive, all sorry-free)

| file | content |
|---|---|
| `PairDecoupleSplit.lean` | prime-range split, exact-CRT middle range, `L²`/variance entry |
| `PairDecoupleVdC.lean` | van der Corput, proved from scratch; the abstract criterion |
| `PairDecoupleDigits.lean` | `b`-adic digit form; the root-of-unity correlation shape |

## The chain, as it now stands

`ConjC1` ⟸ Kátai + Delange + `PairDecorr` (pre-existing, `SwingC1Decouple.lean`)
`PairDecorr` ⟸ **`PairShiftCorr`** directly — `pairDecorr_of_pairShiftCorr`, lap 8.
No `PairDecouple`, no cut `P`, no second cut `y`, no periodic model, no primorial.

The ratified target keeps its own (longer) route:
`pairDecouple_all` ⟸ `largeDecay_all` ⟸ `shiftCorr_all` (the single open sorry).

## What was REFUTED (do not re-attempt)

1. **Mass route** (`TopMassVanishing`, lap 1).  For fixed `y` the top range has `≍ log log N`
   large prime factors, so its phase mass → `4/π`, not `0`.  The middle range needs `y ≲ log N`
   and the mass needs `y = N^{1−o(1)}`: disjoint.
2. **Iterating the split** (lap 3) — the handoff's "one genuinely new idea".  Level-`k` gives
   `N_P ≤ Σ_{j<k} 2^j model_j + 2^k N_{y_k}`; models are free but the residual is only bounded
   by `2^k`.  The factor `2` is the triangle inequality, so **no `L¹` route closes this crux**.
3. Lap 6's claim that the crux is a *two-point* Elliott correlation — corrected in lap 7.  Only
   the leading digit is two-point.

## The identification (the session's main mathematical result)

`omegaTail` is *defined* as the `b`-adic digit sum, so
`pairTail = Σ_k (ω(pn+1+k) − ω(qn+1+k))·b^{−(k+1)}` (`pairTail_eq_tsum_digit`), and with
`t = m/b` each digit is a root-of-unity correlation (`phase_digit`), so the truncated phase is a
product of `2K` such factors (`phase_digitTrunc`).  Hence the crux is a **`2K`-point Elliott
correlation** for the non-pretentious multiplicative function `ζ^ω` along the shifted forms
`pn+1+k`, `qn+1+k`, with `K` forced to grow (`≍ log log log R`) because `ω` is unbounded.

* leading digit (`e=1`) CANCELS between `p` and `q` (for `r > max(p,q)`, `r ∣ pn ⟺ r ∣ n`);
* first digit with content is `ω(pn+1) − ω(qn+1)` seen mod `b²` — two-point, settled in
  LOGARITHMIC average by Tao (Forum of Math Pi, 2016);
* the full statement is multi-point, **open even logarithmically**.

**Confidence that `PairDecouple` is TRUE: 85%.**  Heuristic and every finite model support it;
the literature does not supply it on one named published theorem.

## NEXT (start here)

1. **Tail mean bound.**  `(1/R)Σ_{n<R} Σ_{k≥K}(ω(pn+1+k)+ω(qn+1+k))b^{−(k+1)} ≪ b^{−K} log log R`.
   Needs `Σ_{m≤X} ω(m) = X log log X + O(X)`; check `HANDOFF-2026-09-16-mertensAP.md` and
   `SwingC1.lean` lines ~520–550 / ~2035–2045 for reusable `(A+k)b^{−(k+1)}` machinery.
2. With it, reduce `PairShiftCorr` (and `shiftCorr_all`) IN LEAN to the `2K`-point correlation at
   `K = K(R)`, and state that as the named open hypothesis `MultiElliott` — never an `axiom`,
   house style is a named hypothesis.  That completes the kickoff's item 3: the swing becomes
   `ConjC1 ⟸ Kátai + Delange + MultiElliott`, all three precise and literature-checkable.
3. Only if (1)–(2) land early: attempt the shifted local factor separation
   (`norm_pairLocalFactor_le` with four residues instead of two) — but note it feeds the
   periodic-model route, which laps 1–3 showed cannot close the gap on its own.

## Standing constraints (unchanged)

* Do not edit `SwingC1*.lean` statements, `CastingOut*.lean`, `Maze.lean`, `papers/`,
  `agent-mail/`, other KICKOFFs.  New work goes in `src/NormalNumbers/PairDecouple*.lean`.
* Never use `axiom`; named hypotheses are the sanctioned device.
* `PENDING_WORK.md` carries the full per-lap record, including all refutations above.
