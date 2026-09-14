# HANDOFF 2026-09-14 — G4 disjunctivity, lap 3 (review lap: crux moved B → C; C1, C2 proved)

Branch `wip/g4-disjunctivity`, working tree clean, not pushed (host pushes).
**`DIRECTION.md`'s CURRENT DIRECTIVE is now the G4 campaign** — this lap was an altitude lap
and rewrote it (the old Mahler run+jump directive was stale and is filed as SUPERSEDED).  Grind
laps READ and OBEY it and do not edit it.  `STATUS.md` refreshed; `PENDING_WORK.md` §G4 carries
the full attack path.

Build: `lake build NormalNumbers.G4LocalContraction NormalNumbers.G4Wiring
NormalNumbers.G4TubePiece NormalNumbers.G4TorusProjection NormalNumbers.G4Covering`.
No `sorry` in any G4 file; every declaration below prints `[propext, Classical.choice, Quot.sound]`.

## Why the direction changed

Laps 1–2 both spent themselves on §4B.  §4B is now **input-complete**; what remains there is
assembly (Markov, torus marginals, finite unions) — labour, not risk.  §4C — the half the brief
itself leaves unproved — had received **zero** laps.  It is now the mandated target, and the
crux inside it is named: **C3**, the transfer from the independent residue model to the actual
arithmetic progression.

Also checked on paper (recorded in `PENDING_WORK.md`, not yet in Lean): the §5 schedule is
self-consistent on all four of the brief's essential comparisons — `H/r → 1`, tube exponent
`−Θ(rK)+O(r√K) → −∞`, covering ratio `→ 1`, `L·8^{−K}=L^{1−o(1)} ≫ rK=L^{0.02+o(1)}`.  **The
parameter budget is not where this route dies.**

## Proved this lap

`src/NormalNumbers/G4MinWeight.lean` (§4A)
* `wt`, `MinWeight`, `two_le_wt_of_sum_eq_zero`, `wt_cons`, `kronPow`, `vecMul_kronPow_cons`.
* **`minWeight_kronPow`** — minimum distance of a **product code**: `MinWeight M d` ⟹
  `MinWeight (M^{⊗K}) (d^K)`.
* **`minWeight_diff`** — `D_s` has minimum weight `2` (telescoping rows + injectivity from
  `det T_s = s+1`); **`minWeight_tensorDiff`** — `‖supp(Aᵀq)‖₀ ≥ 2^K`.
* `colSum_diff_le`, `abs_vecMul_kronPow_le`, **`abs_vecMul_tensorDiff_le`** — `‖Aᵀq‖∞ ≤ 2^K‖q‖∞`.

`src/NormalNumbers/G4FreqSep.lean` (§4C seed)
* `distZ`, `le_distZ`; **`freqDepth K w = K+1+⌈log₄|w|⌉`**, `lt_freqDepth` (`j > K`),
  `mem_window_freqDepth`, `le_distZ_freqDepth`.
* `diffZ`, `cast_vecMul_kronPow_diffZ`, `minWeight_kronPow_diffZ`,
  `natAbs_vecMul_kronPow_diffZ_le`; **`freqDepth_le`** (uniform `j_α` over the box `‖q‖∞ ≤ D`).
* **`sum_sq_distZ_freqDepth_ge`** — `∑_α dist(w_α4^{−j_α},ℤ)² ≥ 4^{−4}·8^{−K}`, every `q ≠ 0`.

`src/NormalNumbers/G4LocalContraction.lean` (§4C, C1 and C2)
* **C1 `eight_mul_distZ_sq_le_one_sub_cos`** — `1 − cos2πx ≥ 8·dist(x,ℤ)²`.  This IS the
  brief's "reduce modulo one before moment comparison".
* **C2 `norm_localSum_le` / `norm_localSum_le'`** — with `k` active roots carrying phases `xᵢ`
  and `p−k ≥ p/2` default classes, `‖(p−k) + ∑ e(xᵢ)‖ ≤ p − 4∑dist(xᵢ,ℤ)²`.  The gain comes
  from the cross term in `‖m+b‖² = m² + 2m·Re b + ‖b‖²`, *not* the triangle inequality; with
  `m = 0` the bound degenerates, which is exactly why a positive-density default class is a
  hypothesis and not a convenience.
* `norm_localAvg_le_of_sum_sq` — normalised: `≤ 1 − 4θ/p` whenever `∑dist² ≥ θ`.
* `prod_one_sub_le_exp_neg_sum`, `prod_contraction_le_exp` — `∏(1−c/p) ≤ exp(−c∑p⁻¹)`.

Chaining these: for one good prime `p`, `‖avg‖ ≤ 1 − 4·4^{−4}·8^{−K}/p`, hence over the good
primes `≤ exp(−c·8^{−K}·∑_{p≤R}p⁻¹) = exp(−c·8^{−K}(L−o(L)))` — the brief's
`exp(−cL8^{−K})`, **in the independent model**.

## Open, in priority order (mirrors `DIRECTION.md`)

1. **C3 — THE CRUX.**  Transfer the independent-model product bound to the actual progression:
   with `f_p(n) = e(θ_p(n)) − 𝔼e(θ_p)`, expand `𝔼_{n∈P∩[1,X]} ∏_p(𝔼e(θ_p)+f_p(n))` to even
   degree `M`, CRT-count the residue tuples on modulus `P·∏_{p∈T}p ≤ P·R^M`, and sum the
   finite-sample errors `P R^{2m}/X`.  `R = X^{1/(20M)}` makes `PR^M = X^{o(1)}`.  State it as a
   named `Prop` in `src/` first, then decompose.  Trigger **G-T1**: 5 grind laps.
2. **C4** — `Λδ₃ < 1` with `Λ = (2D+1)^r = exp(O(rK))`, uniformly on the box.
3. **B assembly to `PropB`** — the five steps in `PENDING_WORK.md` §G4; all inputs proved.
   Use `G4FreqSep.diffZ` + `cast_vecMul_kronPow_diffZ` as the ℤ↔ℝ bridge for `Frame.A`.
4. **A** (§4A transport) and **D** (§4D remainders); then the §5 schedule module.

Nothing refuted this lap.
