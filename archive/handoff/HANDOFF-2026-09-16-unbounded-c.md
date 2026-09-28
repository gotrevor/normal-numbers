# HANDOFF 2026-09-16 (late) — campaign B: unbounded coefficients, B0–B2c′ landed

Branch `wip/g5-prime-subset`, HEAD `fa20992`, tree clean, `lake build` 🟢 **9070 jobs**.
`src/` carries exactly the two pre-expedition forbidden-drift `sorry`s (`phaseOscillation`,
`exists_prime_nonresidue`); **zero `axiom`s**.  Every declaration added this lap prints
`[propext, Classical.choice, Quot.sound]`.

## This lap was a review lap + five grind steps

**Review verdict (`DIRECTION.md` → CURRENT DIRECTIVE, re-set this lap).**  Campaign A is
**closed**: `isDisjunctive_residueClass`, `isDisjunctive_Omega`, `isDisjunctive_weight` are all
unconditional and trust-triple clean, so the previous directive's ladder was finished.  New
objective: the **master additive weight with `c` UNBOUNDED**.  Two probes recorded:

* `TWeight.ovC` was consumed at exactly ONE site (`G4TransportW.summable_corrB`) and only for
  *summability* — the transport interface was never the obstacle;
* **base 2 stays a machine-checked dead end** (`G4RowMassOptimal.two_pow_le_sum_abs` ⇒
  `one_le_rowMass_two`: every line-sum-annihilating integer array has row-ℓ¹ mass `≥ 2^K`), so
  it is forbidden drift, not a target.

## Landed (in dependency order)

| step | content |
|---|---|
| **B0** | `TWeight.ov_le` relaxed to a per-`d` bound `ovB : ℕ → ℕ` (`G4TransportW`); five instances updated.  This is what makes an unbounded `c` *statable*: `ov_c(d,m) = ∑_{p∣d,p∣m}(1−c_p)` has no uniform bound. |
| **B1** | `G4UnboundedJunk.sum_junk_le'` — the junk estimate with the coefficients **inside** the sum: `≤ (X/P₀)(∑_{p∣P₀} c_p/(p−1) + ∑_{p<N+1} c_p/(p(p−1))) + log₂(N)·∑_{p<√N+1} c_p`.  Plus `junkShiftBoundC` (monotone in `ρ`), `sum_junk_C_le'`, and the faithfulness check `sum_junk_le_of_bounded` (the old estimate is the `c ≤ C` case — nothing lost). |
| **B1b** | `G4UnboundedAvg.junkAvgC_le'` — the block average against `junkShiftBoundC`, with **no hypothesis on `c` at all**. |
| **B2a** | `sum_weightW_shiftG_le` — the far-field sample sum via the §4D split `w_c = ω + frozenExcess_c + junk_c`, replacing the pointwise `w_c ≤ (max C 1)·Ω` (which has no unbounded analogue: `max_{p²∣m} c_p` grows with `m`).  `frozenCap c P₀ = ∑_{p∣P₀} c_p·v_p(P₀)` is a genuine constant — the frozen part only sees `m mod P₀`. |
| **B2b** | `Tame c A` and **`effC`** — see below. |
| **B2c** | `TWeight.weightU c hT` (`G4UnboundedTW`) — the unbounded weight IS a `TWeight`, so §4A/§4B/§4C are free.  `ovB d = ω(d) + ∑_{p∣d} c_p` needs nothing; only `summable` uses `Tame`, via `weightW_le_tame : w_c(m) ≤ (1+A)(m+1)²`. |
| **B2c′** | `sum_abs_farPartW_le_of_layer` — the far-field estimate generic in the `TWeight` *and* in `κ`, taking the per-layer bound as a hypothesis. |

### The structural payoff: `Tame` and `effC`

`Tame c A` := `1 ≤ A`, `∀ M, ∑_{p<M} c_p/(p(p−1)) ≤ A` (tail), `∀ M, ∑_{p<M} c_p ≤ A·M`
(linear prime prefix).  `tame_of_bounded` shows it strictly contains `c ≤ C`.  The prefix
condition is **Chebyshev-shaped**, so it admits unbounded `c`:

> **the concrete target — `c_p = ⌊log₂ p⌋`** — satisfies it because
> `∑_{p≤M} log₂ p = log₂(primorial M) ≤ 2M` (mathlib `Nat.primorial_le_4_pow`).

With `effC c P₀ A = max (A + ∑_{p∣P₀} c_p/(p−1)) (frozenCap c P₀)`:

* `junkShiftBoundC c P₀ X ρmax ≤ effC · junkShiftBound P₀ X ρmax` (`junkShiftBoundC_le_effC`);
* `frozenCap c P₀ ≤ effC · Ω(P₀)` (`frozenCap_le_effC_mul`);
* hence **`sum_weightW_shiftG_le_effC`**, which is *literally* `sum_abs_farPartC_le`'s `h3`
  with `κ = max C 1` replaced by `effC`.

So the whole `C`-dependence of the closed bounded proof collapses to one real number.

## Resume here — B2d, then B2e, then the headline

1. **B2d (the only real work left): make the §4D frame plumbing generic in `W`.**  Four
   declarations have `TWeight.weight c C hC` as their *subject*, and use it only through
   `TWeight.weight_wN`, so adding `(W : TWeight) (hW : ∀ m, ((W.wN m : ℕ) : ℝ) = weightW c m)`
   and replacing `TWeight.weight_wN c C hC m` by `hW m` is mechanical:
   * `G4WeightRemainder.gridFrameW_weightC_Ffull_decomp` (its proof already isolates the point
     as `hw : (fun m => (W.wN m : ℝ)) = weightW c`);
   * `G4WeightRemainder.farAvgC` (→ a `farAvgW W` def) and `gridFrameW_weightC_propD`;
   * `G4WeightJunkAvg.gridFrameW_weightC_propD_of_bounds` (pure plumbing).
   Decide in the first lap whether to **edit those in place** (37 occurrences of
   `TWeight.weight c C hC` across 4 files, one chain at the end) or to **copy them generically**
   into `G4Unbounded*` (≈200 lines, two parallel chains).  In-place is the better end state;
   commit a compiling skeleton before starting it.
2. **B2e (free): the schedule at `C := ⌈effC⌉₊`.**  `G4SchedWeight.hjunk_holdsCE`
   (`100000·C·k₄³ ≤ 2^{k₄}`) and `hfarC_holdsE` take `C : ℕ`, and `exists_good_k₄` picks `k₄`
   *after* `C`, so the natural number `⌈effC⌉₊ ≥ effC` feeds them unchanged.  Nothing to re-derive.
3. **B3: `isDisjunctive_weight_of_tame`**, then `isDisjunctive_logWeight` at `c_p = ⌊log₂ p⌋`
   (the first unbounded-coefficient instance), and finally the merge `w_{c,S}`
   (`G4SubsetCWeight` already has the `TWeight` instance and §4A/B/C).

New files this lap: `G4UnboundedJunk.lean`, `G4UnboundedAvg.lean`, `G4UnboundedTW.lean`
(all three registered in `src/NormalNumbers.lean`).  Ranked ladder: `PENDING_WORK.md` top.
