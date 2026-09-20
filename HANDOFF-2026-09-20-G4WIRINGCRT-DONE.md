# HANDOFF 2026-09-20 — `G4WiringCRT.lean` SORRY-FREE (closing lap complete)

Branch `wip/g5-prime-subset`, HEAD `a9fdd5d` (2026-09-20, lap end; treadmill STOP honoured). Scope was leaves 2–7 of `KICKOFF-2026-09-19-closing-lap.md`; all six landed.

```
#print axioms NormalNumbers.G4.isNormal_G4_of_CRTConstant
  → [propext, Classical.choice, Quot.sound]
```

`IsNormal 4 (primeLambertAtBase 4)` now follows, in-kernel, from the two frozen Props
`CRTConstant` (all `h ≠ 0`) and `SiteDecayFull`. Both `DyadicToPrefix.lean` (W4, last lap) and
`G4WiringCRT.lean` are sorry-free.

## ⚠️ The one statement change: `CRTConstant` quantifier order

`∀ J, ∀ᶠ N` → **`∀ᶠ N, ∀ J`** (uniform in `J`). This is the strengthening the kickoff explicitly
authorised, and it is *forced*, not convenience:

> With per-`J` thresholds `n_J`, nothing bounds the growth of `J ↦ n_J`. The L1 tail needs a
> schedule with `4^{-J_N} log N → 0`, i.e. `J_N ≳ log₂ log₂ N`. If `n_J` grows like a tower, every
> schedule certified by the weak form grows like `log*`, too slow. No diagonalisation escapes this:
> the schedule must be fixed before the law is applied, because the *tail* lemma constrains it from
> below and the *law* from above. So the two-sided constraint is unsatisfiable unless the law is
> uniform in `J`.

KB verdict §2f is the intended reading (`C / log N` carries no `J`-dependence), and the docstring
now records the argument above. `SiteDecayFull` and `isNormal_G4_of_CRTConstant` are untouched.

## What each leaf actually needed

* **2 `orbit_eq_fract_tailB`** — no `AddCircle` at all. `tailB_eq` already writes
  `tailB = 4^n·x − (nat)`, so `Int.fract_sub_natCast` is the whole proof. The kickoff's
  `coe_eq_coe_iff_of_mem_Ico` route is unnecessary.
* **3 `tail_error_le`** — no base-4 geometric series. Factor `4^{t+J+1} = 4^J · 4^{t+1}` and drop
  `4^{t+1}` to `2^{t+1}`; the existing base-2 `PrimeLambertTail.tsum_majorant` at `J = 0` then gives
  `(A+J+1)/4^J`, inside the allowed `+3` slack.
* **4 `tail_error_uniform`** — `4^{windowJ N} ≥ (log₂ N)²` from `Nat.lt_pow_succ_log_self` applied
  twice (once to `N`, once to `log₂ N`); numerator `≤ 2 log₂ N + 5`; squeeze against `4/log₂ N`.
* **5 `fullWindowMean_tendsto_zero`** (the route-decisive leaf) — no minimal-`j` search needed:
  `j₀ := |h| + 1` already has `4^{j₀} > |h|`, so `h/4^{j₀} ∉ ℤ`. Every site mean has norm `≤ 1`
  (`Nat.card_Ico`), so the `Icc 1 J` product is `≤` the single `j₀` factor, and the law gives
  `‖W‖ ≤ (B + |C|)·‖m_{j₀}‖ → 0`.
* **6 `dyadic_fourier_tendsto_zero`** — `ePhase` absorbs `Int.fract` (`ePhase_add_int`), so the
  dyadic mean *is* the untruncated window mean; the truncation defect is termwise
  `‖e(a) − e(b)‖ ≤ 4π|a−b|` (reuse `PrimeLambert.norm_e_sub_one_le` after proving
  `ePhase = PrimeLambert.e`) times `tail_error_le`, made uniform on `[N,2N)` by
  `Nat.log_mono_right`.
* **7** — `fourierMean u h = prefixMean (ePhase ∘ (h·u))` after a `push_cast; ring` on the exponent.

## Gotchas for the corpus
`div_le_div_iff` is gone → `div_le_div_iff₀`. `Nat.log_pow_mul_self` does not exist; bound
`Nat.log 2 (4N)` by `Nat.log_lt_of_lt_pow` off `Nat.lt_pow_succ_log_self` instead. `Int.one_le_abs`
takes `a ≠ 0` (omega cannot see through `|·|`). `Filter.Tendsto.atTop_pow` needs an
`IsOrderedMonoid` instance ℝ does not get here — reshape the majorant to a single `c/L` instead.

## What is still open downstream
`CRTConstant` and `SiteDecayFull` themselves remain frozen Props (Hardy–Littlewood CRT law;
Delange–Wirsing–Halász). Discharging `SiteDecayFull` is the natural next crux — it is a single-site
mean of `e(α ω(n))` on `[N,2N)`, a classical Halász/Delange statement with no mathlib analogue yet.
`G4WiringSparse.lean` remains out of scope.


## Exact next steps for a fresh session

1. Nothing in `src/NormalNumbers/G4WiringCRT.lean` or `src/NormalNumbers/DyadicToPrefix.lean` is
   open; do not reopen them. `lake build` is green repo-wide (pre-commit gate ran on every commit
   this lap).
2. The closing-lap override in `DIRECTION.md` (2026-09-19 21:55) is now **satisfied** — a new
   operator override is needed before further work on this line.
3. The next real crux, if the campaign continues, is discharging `SiteDecayFull`
   (`G4WiringCRT.lean:~70`): for `h/4^j ∉ ℤ`, `𝔼_{n∈[N,2N)} e(h 4^{-j} ω(n+j)) → 0`. This is
   Delange–Wirsing–Halász for the completely-additive-ish `ω`; mathlib has no Halász mean-value
   theorem, so expect a multi-lap decomposition (Turán–Kubilius or a direct Halász–Montgomery
   estimate) rather than a citation. Do not attack `CRTConstant` first: it is the genuinely deeper
   of the two (Hardy–Littlewood CRT law, measured only numerically to N = 10⁸).
4. `G4WiringSparse.lean` is still out of scope and still holds its own open leaves.
