# Handoff 2026-10-05 — computable-algebraic (DONE)

`NormalNumbers.ComputableReal.isComputableReal_of_isAlgebraic` is proved (commit a4a23d23),
axioms `[propext, Classical.choice, Quot.sound]`; its BarrierAudit waiver is removed.

Route (leaves in `src/NormalNumbers/ComputableAlgebraic.lean`):
- `exists_simple_root`: `derivative^[r-1] p` (r = root multiplicity) has `x` as a simple root; sign-flipped so `q'(x) > 0`. No minpoly/separability needed.
- `exists_shifted_root`: `q.comp (X - C c)` moves the root to `x + c ≥ 0`.
- `exists_primrec_floor`: strict monotonicity near `y`, hard-coded dyadic interval `[a/2^k,(a+1)/2^k]`, sign test as `ℕ` sum ≤ `ℕ` sum (`scaled_eval`), `Nat.findGreatest` = `⌊2ⁿy⌋₊`.
- `primrec_int_sub`: `ℕ - ℕ → ℤ` Primrec via `Primrec.encode_iff` and ℤ's Denumerable encoding.

Out of scope and untouched: `KurtzRandom.lean`.
