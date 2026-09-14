# HANDOFF 2026-09-14 — prime Lambert irrationality (bounded campaign, lap 1 complete)

Branch `master`, HEAD `d1a0fa4` (five green checkpoints this lap: 3eb36d7, df68fd8, 26bbfc6,
9f155e3, d1a0fa4).  Working tree clean.  Not pushed (host pushes).
Brief: `~/personal/claude/knowledge/core/projects/normal-numbers-prime-lambert-lean-brief-2026-09-14.md`
(read the 00:34 UTC addendum too).  Footprint: `src/NormalNumbers/PrimeLambert*.lean`,
`docs/prime-lambert-irrationality.md`, this file.  Root module / lakefile / DIRECTION untouched.
Build: `lake build NormalNumbers.PrimeLambertTail NormalNumbers.PrimeLambertHexagonCounterexample`
(targeted; both green, 8710 / 8706 jobs).  Full `lake build` green via pre-commit (8888 jobs).

## Proved (all `[propext, Classical.choice, Quot.sound]`)

- `PrimeLambertDefs`: `primeLambert = ∑ ω(n)/2^n`, `tailT_eq`, `rational_tail_int`, exact
  ω-transport `omega_mul_eq` / `dilatedTail_eq`, exact periodicity `transportCorr_congr`.
- `PrimeLambertConfig`: `TConfig`, `CancelsAt`, `phaseSum`, `phaseSum_eq`, **Theorem A**
  `phaseSum_sub_int`.
- `PrimeLambertGeometry`: group-ring hexagons, `hexagon_eq_six`, `hexTensor_cancels` (sites
  `1..6r`), coprime transform `cancelsAt_toConfig`, `transform_coprime`,
  `exists_tconfig_cancelling`.
- `PrimeLambertOscillation`: `PhaseOscillation` (draft (5)), `norm_phaseAverage_eq_one`,
  `irrational_of_phaseOscillation`.
- `PrimeLambertAnalytic`: exact prime split `truncPhase_split`, four Props `TailTruncation`,
  `LargePrimeNegligible`, `BadPrimeFrozen`, `SmallPrimeDecay`; wiring `phaseOscillation_of_chain`,
  `ChainExists → Irrational primeLambert` (`irrational_of_chainExists`).
- `PrimeLambertTail`: `badPrimeFrozen_of_residue`, `abs_truncation_error_le` (draft (20) exact),
  `tailTruncation_of_bound`.
- `PrimeLambertHexagonCounterexample`: `not_meanRetention_seven` (addendum refutation, full
  complex inequality, `c = 2cos(2π/7)` identified).

## Open

Exactly one `sorry`: `phaseOscillation` (`PrimeLambertOscillation.lean`).  It is equivalent to
`ChainExists`; unreduced pieces are `LargePrimeNegligible` and `SmallPrimeDecay`.
`irrational_primeLambert` is sorry-gated and must not be reported as proved.

## Next lap (lap 2 of the bounded campaign)

1. `LargePrimeNegligible`: pointwise, each argument `m ≤ 3N` has `≤ log m / log R` prime
   factors `> R`; bound `|classSum large| ≤ ‖c‖₁ 2^{-K} · #{large primes dividing some arg}`.
   Exact lemma: `|primePart p n| ≤ ∑_a |c a| 2^{-K}` when at most one indicator fires per atom
   (needs distinct-root hypothesis for `p ∤ W`) — state that hypothesis explicitly.
2. Decompose `SmallPrimeDecay` into `def … : Prop`s: independent-model characteristic-function
   decay `≤ exp(-cV)`, CRT moment comparison `|𝔼S^k − 𝔼S'^k| ≤ A R^{2k}/N`, even-moment Taylor
   transfer; prove the transfer step (pure real analysis: Taylor remainder of `e` at degree
   `M−1` with even `M`).
3. Geometry still lacking: distinct first coordinates for `B ≥ 7`, mass `6^{K/3}`, surviving
   squared mass at site `K+1`.
4. Do not touch the root module; host owns pointers.  No Aristotle, no outreach.
