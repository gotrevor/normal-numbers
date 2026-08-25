# OBSTRUCTION (route-decisive) — `variance_blockCount_psi_pushed` is FALSE

**Date:** 2026-08-25 (review lap #2, mid-grind).  **Severity:** kills the single-stream
passive-Chebyshev z-side route.  **Status:** rigorous counterexample below; the schedule
route is obstructed, pivot to the measure route (see `ROUTE-ESCALATION-2026-08-25.md`).

## The claimed lemma (CFScheduleA.lean:4254, disclosed `sorry`)

For all `q>0, r, wx'≠[] (digits ≥1), v (digits ≥1), n`:
```
∫_{cfCyl wx'} (blockCount (cfCyl v) n (ψx) − n·γv)² dγ ≤ (8|v|+80)·n·γv·γ(cfCyl wx')
```
where `ψ = affineMap q r`, `γv = γ(cfCyl v)`.  It is the sole analytic obligation the whole
clean single-stream z-selector rests on (`psi_pushed_chebyshev_brick` (`:4418`, line 4473)
applies it directly, → `gaussMeasure_aggregate_psi_pushed_le` → `exists_scale_cfCylinder_psi_avoid_zbad_poly`).

## Counterexample (the bound fails for `n ≳ 1/γv`)

Take `v = [1]`, so `γv = γ(cfCyl [1]) = 2 − log₂ 3 ≈ 0.415`.  Fix a depth `m` (chosen below).

- `ψ⁻¹(cfCyl [2,2,…,2])` (m twos) is a nonempty open interval (affine preimage of an interval).
  Pick a **deep CF cylinder** `cfCyl wx' ⊆ ψ⁻¹(cfCyl [2,…,2])` with `|wx'| ≥ m` (exists: every
  interval contains cylinders of every large depth; digits ≥1, nonempty — hypotheses met).
- Then for every `x ∈ cfCyl wx'`: `ψx ∈ cfCyl [2,…,2]`, so the first `m` CF digits of `ψx` are
  all `2`.  Hence for `k < m`, `a_{k+1}(ψx) = 2 ≠ 1`, i.e. `gaussMap^[k](ψx) ∉ cfCyl [1]`.  So
  `blockCount (cfCyl [1]) n (ψx) = 0` for every `n ≤ m` and every `x ∈ cfCyl wx'`.
- The integrand is therefore the **constant** `(0 − n·γv)² = n²γv²` on `cfCyl wx'`, so
  ```
  LHS = n²·γv²·γ(cfCyl wx').
  ```
- RHS `= (8·1+80)·n·γv·γ(cfCyl wx') = 88·n·γv·γ(cfCyl wx')`.
- `LHS > RHS  ⟺  n·γv > 88  ⟺  n > 88/γv ≈ 212`.

So pick `m ≥ 213`, `n = m`, `|wx'| ≥ m`: **LHS > RHS.  The lemma is FALSE.**  (Any fixed `v` with
`γv>0` and any `wx'` whose ψ-image is trapped in a `v`-avoiding cylinder for its first `~|wx'|`
digits gives the same failure once `n·γv > 8|v|+80`.)

## Why it fails — the structural reason (not a fixable constant)

A deep cylinder `cfCyl wx'` is a tiny interval; its affine image `J = ψ(cfCyl wx')` has length
`~q·φ^{−2|wx'|}`, so **all** points of `J` share their first `~|wx'|` CF digits.  Hence for scales
`n ≲ |wx'|` the pushed block count `blockCount n (ψ·)` is **nearly constant** over `cfCyl wx'`
(≈ the count of pattern `v` in that shared prefix), and that prefix is an arbitrary word the affine
map hands us — it need not have `v`-frequency `≈ γv`.  A near-constant observable has ~zero
variance but its value can be `Θ(n)` away from `n·γv`, so the *second moment about `n·γv`* is
`Θ(n²)·γ(cfCyl wx')`, not `O(n)·γ(cfCyl wx')`.  **The `γ(cfCyl wx')` base factor cannot rescue a
second moment that is quadratic in `n`.**

This is the SAME wall in a new disguise: passively (by measure/Chebyshev on `cfCyl wx'`) you cannot
force `ψ(cfCyl wx')` to sit in a frequency-typical region — that requires ACTIVE z-steering, which is
the two-stream route (proven infeasible: super-exponential blocks, `OBSTRUCTION-2026-08-28`).  The
scale regime that bites (`n ≲ |wx'|`) is exactly the regime the digit-agreement transfer needs
(goodness of `ψp` transfers to `ψxA` only up to the shared-prefix depth `~|wx'|`), so there is no
"only large `n`" escape.

## Consequence

`psi_pushed_chebyshev_brick`, `gaussMeasure_aggregate_psi_pushed_le`, and
`exists_scale_cfCylinder_psi_avoid_zbad_poly` are all derived from this false lemma (they carry
`sorryAx`, so nothing unsound entered the kernel — the sorry is disclosed).  They do NOT actually
establish their conclusions.  Both z-side schedule routes (conditional-at-`wz` walled `5816044`;
x-cylinder-relative refuted here) are dead.  **Pivot to the measure route** (existence is trivially
true a.e.; see `ROUTE-ESCALATION-2026-08-25.md`).
