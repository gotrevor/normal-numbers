# HANDOFF 2026-09-20 — sparse-subset lap: `G4WiringSparse` leaves 1–7 + block leaves

Branch `wip/g5-prime-subset`.  Kickoff: `KICKOFF-2026-09-19-sparse-subset-lap.md`
(DIRECTION.md top override).  All commits green via the pre-commit `lake build` gate.

## What is now a theorem

`isNormal_subsetLambert_of_KMT_along` — **normality of `c_S(4)` from `KMT_along S Jsched` +
`TailOK S Jsched`, no sorry in the chain.**  And `exists_sparse_normal_of_KMT_quant` rests on
exactly one remaining hypothesis, `exists_good`.

Closed this lap, in the kickoff's order:

| leaf | note |
|---|---|
| 1 `orbit_eq_fract_tailB_subset` | `tailB_eq` + `lambert_subset` + `Int.fract_sub_natCast` |
| 2 `tail_error_le_subset` | G₄ proof transported through `omegaS_le_omegaR ∘ omegaR_le_log` |
| 3 `tailOK_windowJ` | reuses `tail_error_uniform` verbatim (its `2N` dominates the prefix range) |
| 4 `prefix_fourier_tendsto_zero` | prefix analogue of the dyadic one, `‖e(a)−e(b)‖ ≤ 4π|a−b|` |
| 5 inline | `fourierMean = prefixMean ∘ ePhase` |
| 7 `tail_error_L1` | **the crux** — see below |
| 8 | `recipSumIoc_le`, `recipSumLe_ge`, `recipSumLe_le`, `blockIndex_spec`, `blockIndex_tendsto`, `divergentRecip`, `kmt_along`, `tailOK`, `exists_block` |

## The crux: `tail_error_L1`

The Mertens-shaped L¹ bound is what lets the schedule be `J_N ≈ log₄ S_S(N)` instead of the crude
`log₂ log₂ N`.  Three ingredients, all now proved:
* `ω_S(n+j) = ∑_{p ∈ P} [p ∣ n+j]` for `P = (Iic (N+j)).filter (Prime ∧ S)` — `p ∣ m → p ≤ m`
  makes the index set uniform in `n`, so `Finset.sum_comm` applies;
* `#{n < N : p ∣ n+j} ≤ N/p + 2`, by injecting into `Icc (j/p) ((N+j)/p)` and `Nat.add_div`;
* `recipSumLe S (N+j) ≤ recipSumLe S (2N) + j/(2N)` — primes in `(2N, N+j]` each contribute
  `< 1/(2N)` and number `≤ j`.  **This removed the kickoff's case split at `j = N` entirely**:
  the `j > N` fringe folds into the same geometric series, no separate `4^{-N}` term.

Constant restated to `(recipSumLe S (2N) + 5J + 12)/4^J` (leaf 7 is not a frozen statement; the
kickoff permits weakening the constant while keeping the shape).  The `5J` overhead is absorbed in
`BlockData.tailOK` by `(5k+11)/4^k → 0` off `Good.J_tendsto`, so **`Good` needed no new field**.

## Two findings worth keeping

* `Good` needs **no sign hypothesis on `C`**: `0 ≤ C (J i)` is derivable inside `kmt_along` from
  the `KMT_quant` bound itself, since `exp(−1/(8J²ε)) > 0` and the left side is a norm.
* Frozen statements were honoured: `KMT_sparse`, `KMT_along`, `KMT_quant`, `TailOK`, `BlockData`,
  `BlockData.Good` are untouched; `G4WiringCRT.lean` untouched.

## Open: two sorries

1. **`exists_good`** — out of scope by operator instruction.  All its consumers are proved, so it
   is the single remaining obligation of `exists_sparse_normal_of_KMT_quant`.  `exists_block` (now
   proved) supplies the blocks; explicit parameter choices are in its docstring.
2. **`exists_relDensityZero_divergent` (leaf 6)** — **PNT wall**, and the kickoff pre-authorised
   leaving it ("allowed to be hard; if it costs more than one lap, leave it and report").  This is
   the report.  It is **off the main line**: `exists_sparse_normal_of_KMT_quant` never mentions
   `RelDensityZero`; it consumes only `DivergentRecip`, supplied by `BlockData.divergentRecip`.

### Leaf 6, in full (docstring + `PENDING_WORK.md` carry the detail)

*Sharp obstruction.*  The only count bound available without prime counting is "a fraction of the
integers", off by `log x` from `π(x)`.  So any free-count construction has integer-density
`≤ 1/log v`, mass rate `≤ dL/L²`, and `∫dL/L² < ∞`: **every free-count construction has a
convergent reciprocal sum.**  (This subsumes the three routes tried: all-primes blocks, residue
classes, general thin subsets.)

*The construction that does work* — found this lap, in the coordinate `L = log y`.  Blocks
`Bᵢ` = primes of `(yᵢ, vᵢ]`, `log vᵢ = Lᵢ + εᵢ`, gaps `ΔLᵢ = εᵢ gᵢ`.  Count fraction `≈ 1 − e^{-εᵢ}`;
accumulated density `≈ 1/gᵢ`; total mass `∑ (ΔLᵢ/Lᵢ)/gᵢ`.  With `gᵢ = log Lᵢ` the mass is
`∫ dL/(L log L) = ∞` while the density is `1/log log x → 0` — which reproduces the file's own
`π_S ≍ π(x)/log log x` hint from first principles.

*Exact input, and two dead ends ruled out.*  Needs `π(x) = Li(x) + O(x e^{-c√log x})`.  **Elementary
Mertens does not suffice**: its error is `O(1/L)` and the block mass is `εᵢ/Lᵢ` with `εᵢ → 0`, so
the error swamps the mass; raising `εᵢ` to a constant makes the block a `1 − e^{-A}` fraction of
`π(v)`.  The regimes are exclusive.  **Brun–Titchmarsh does not help** either — it bounds the count
from above, and the binding constraint is the mass from below.  Mathlib has only constant-factor
Chebyshev (`Chebyshev.pi_ge`, `Chebyshev.pi_le_log4_mul_div`); the repo has hit this same wall
before (`LnTwoExpSepSharp.lean:55`).

## Next lap

`exists_good` (needs the operator to put it in scope), or leaf 6 once PNT-with-error-term reaches
mathlib.  Nothing else in `G4WiringSparse.lean` is open.

---

## ⛔ STUCK CLAIM (strike 1) — for the verifying lap

**What is blocked.** `exists_relDensityZero_divergent` (leaf 6), the only in-scope sorry left in
`src/NormalNumbers/G4WiringSparse.lean`.  The other sorry, `exists_good`, is forbidden by DIRECTION.

**Why it is not a tactic problem.**  Verify in three cheap steps:
1. `grep -rn "PrimeNumberTheorem\|IsEquivalent.*primeCounting" .lake/packages/mathlib/Mathlib/`
   → only a provenance comment in `Chebyshev.lean`.  Mathlib has **no** `π(x) ~ x/log x`.
2. `grep -n "theorem" .lake/packages/mathlib/Mathlib/NumberTheory/Chebyshev.lean | grep pi_`
   → only `pi_ge` (constant `log 2 ≈ 0.69`) and `pi_le_log4_mul_div` (constant `≈ 2.77`).
   A constant-factor gap of 4 cannot produce a ratio tending to `1`, which density-zero forces.
3. `grep -n "theorem" src/NormalNumbers/G4Mertens.lean` → one-sided Mertens only.

**The impossibility argument** (not a failed attempt — a proof that the cheap routes cannot work):
the only count bound available without prime counting is "a fraction of the integers", off by
`log x` from `π(x)`; so any such construction has integer-density `≤ 1/log v`, reciprocal-mass rate
`≤ dL/L²`, and `∫ dL/L² < ∞`.  Every free-count construction has a **convergent** reciprocal sum.
Elementary Mertens (error `O(1/L)`) and Brun–Titchmarsh are separately ruled out above.

**The exact ask — one of:**
* (a) accept leaf 6's disclosed `sorry` and let the lap close `--green` (the kickoff already says
  "This leaf is allowed to be hard; if it costs more than one lap, leave it and report"; the terse
  "no sorry except `exists_good`" gate contradicts that clause); **or**
* (b) put `exists_good` in scope, since it is the last obligation on the main line and is
  elementary-but-long (explicit parameter choices are already in its docstring); **or**
* (c) authorise restating `exists_sparse_normal` to take the density-zero witness as a hypothesis,
  moving leaf 6 out of the theorem's body.

**Do not** spend a lap re-deriving the PNT wall; it is fully written up in the leaf's docstring and
in `PENDING_WORK.md`.  Everything else the kickoff asked for is proved and committed.
