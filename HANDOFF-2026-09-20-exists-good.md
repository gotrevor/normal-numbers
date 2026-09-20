# HANDOFF 2026-09-20 — `exists_good` DONE (and a frozen statement refuted)

**Branch** `wip/g5-prime-subset` · build GREEN (pre-commit `lake build` gate ran on every commit)
· `src/NormalNumbers/G4WiringSparse.lean` is **sorry-free**.

```
#print axioms NormalNumbers.G4Sparse.exists_sparse_normal_of_KMT_quant'
  => [propext, Classical.choice, Quot.sound]        -- no sorryAx
#print axioms NormalNumbers.G4Sparse.exists_good            => same
#print axioms NormalNumbers.G4Sparse.exists_sparse_normal   => same
```

## ⚠️ The headline finding: `BlockData.Good` as frozen was UNSATISFIABLE

`sep_eps_incompatible` (machine-checked, in the file) says: for any `x₀ : ℕ` and any `ε < 1/2`,

* `Good.ε_range` at `i = 0` (`1/log log N < ε` for **every** `N > x₀`) forces `x₀ ≥ exp exp 2 > 1600`
  — else take `N = 16`, where `1/log log 16 ≈ 0.98 > 1/2`;
* `Good.sep` at `i = 0` (`x (0-1) = x 0 ≤ ⌊N^{ε}⌋₊` for every `N > x₀`) at `N = x₀+1` forces
  `x₀ ≤ (x₀+1)^ε < (x₀+1)^{1/2}`, i.e. `x₀ ≤ 1`.

Both are quantified over *all* `N > x i`, and `ℕ`-subtraction makes `i-1 = 0` at `i = 0`.  So the
old `exists_good` was a false statement; no amount of construction could have closed it.

**Minimal repair (the only deviation from the freeze, deliberate and documented):** `Good.sep`
gains a hypothesis `1 ≤ i`.  Nothing else in the structure changed.  The single consumer,
`BlockData.kmt_along`, proves an `∀ᶠ N` statement and already filters `N`; one extra conjunct
`D.blockIndex_tendsto.eventually_ge_atTop 1` supplies `1 ≤ blockIndex N`, so `sep` is only ever
used at `i ≥ 1`.  `ε_range` was left alone (it is satisfiable at `i = 0` on its own).

## The explicit schedule (`namespace GoodExists`)

* `Kn i := 8(i+3)³`, `εᵢ := 1/Kn i` (so `εᵢ < 1/2` and `1/(8Jᵢ²εᵢ) = (i+3)³/Jᵢ² ≥ i`);
* `JF C i := Nat.findGreatest (fun J => ∀ J' ≤ J, |C J'| ≤ ⁴√i) i`.  **`|C|`, not `C`** — mathlib's
  `Real.log` is `log |·|`, so `hgrow` says `log|C k| = o(4^k)` and says nothing about the sign of
  `C`.  A predicate on `C` itself would not have been enough.
* `EF i := ⌈exp exp (Kn i)⌉₊`; `XF 0 := EF 0`,
  `XF (i+1) := max(2·XF i + 1, EF (i+1), (XF i)^{Kn (i+1)}, sup (blk (XF i) i))` — the four maxima
  are exactly `x_double`+`StrictMono`, `ε_range`, `sep`, `B_prime`.
* `blk y i := ` the greedy block of `exists_block` at `(y, δ = 1/(i+1))` (`Classical.choose` behind
  a named `blkAux`, to keep `whnf` away from the `dite`).

Leaves, all proved: `delta_ge/​delta_le` (`1/(i+1) ≤ δᵢ ≤ 2/(i+1)`, using `XF i ≥ i+1`),
`harm_lower`/`harm_upper` (the telescoping `log`-sandwich for `∑_{k<m} 1/(k+1)`), `delta_div`,
`eps_range`, `sep_holds`, `JF_tendsto`, `JF_C_le`, `JF_max` (maximality), `log_o_pow`,
`terms_tendsto`, `tail_tendsto`.

`log_o_pow` (`log i / 4^{Jᵢ} → 0`) is the only place `hgrow` is used: by maximality
`|C(Jᵢ+1)| > ⁴√i`, so `log i ≤ 4 log|C(Jᵢ+1)|` and `log i/4^{Jᵢ} ≤ 16·(log C(Jᵢ+1)/4^{Jᵢ+1})`;
the degenerate branch `Jᵢ = i` is absorbed by the crude `log i/4^i → 0` (`i ≤ 4^i`).

`terms_tendsto` majorant: bracket `≤ √(log Kᵢ)·√(8/i) + 2/i`, and `|C(Jᵢ)| ≤ ⁴√i`, so
`‖terms‖ ≤ √(8 log Kᵢ/√i) + 2/√i → 0`.

## Gotchas worth keeping

* `Real.log x = Real.log |x|` in mathlib — a `log C k = o(4^k)` hypothesis constrains `|C|` only,
  and not at all when `C ≤ 0`.  Any schedule built from such a hypothesis must use `|C|`.
* `Nat.findGreatest_is_greatest` wants `(k := …)` given explicitly, or `k` is left a metavariable
  and the `omega` side goal becomes unprovable.
* `div_le_div_of_nonneg_right` takes `0 ≤ c`, not `0 < c`; `div_lt_div_iff` is now `…₀`;
  `pow_le_pow_left` is now `pow_le_pow_left₀`; `√x ≤ x` is `Real.sqrt_le_self_iff`.

## Next

The wiring is complete: `exists_sparse_normal_of_KMT_quant'` now rests **only** on the frozen
analytic input `KMT_quant C` (KMT 2023 Prop. 4.3 with its `J`-dependent constant `C J` satisfying
`log C J = o(4^J)`).  That is the whole remaining debt on this line, and it is a genuine
analytic-number-theory obligation, not bookkeeping.  Also still open repo-wide:
`PrimeLambertOscillation.lean:94` (pre-expedition).
