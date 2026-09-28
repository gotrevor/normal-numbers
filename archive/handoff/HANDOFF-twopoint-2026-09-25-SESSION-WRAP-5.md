# HANDOFF twopoint — SESSION WRAP 5 (laps 43–52), 2026-09-25

Branch `wip/twopoint-avg`.  HEAD `d019a00`.  Working tree **clean**; every lap committed green
(pre-commit runs `lake build`, 9292 jobs).  All new declarations `#print axioms`-clean
(`[propext, Classical.choice, Quot.sound]`).  **No `sorry` introduced anywhere this run.**

## Rules honoured
`twoPointWeightedAvg_all` never deleted, renamed or weakened.  No edits to `PairDecouple*.lean`,
`SwingC1*.lean`, `CastingOut*.lean`, `Maze.lean`, `papers/`, `agent-mail/`, other KICKOFFs, or
`DIRECTION.md`.  All new code in `src/NormalNumbers/TwoPoint*.lean`
(`TwoPointMertensLower.lean` extended; `TwoPointDelangeOmega.lean` new), import added to
`src/NormalNumbers.lean`.

## C1 (the DIRECTION objective): unchanged, and already discharged
The directive's success criterion — "pin the route's depth to a named open problem with a theorem
in `src/`" — was met in SESSION WRAP 4 (`pairDecorr_iff_unweighted`,
`multiElliottGrowing_schedule_invariant`, `multiElliottWeighted_iff_growing`).  No C1 work this
run; no cheap work exists there.  Confidence unchanged: `twoPointWeightedAvg_all` TRUE **90%**,
provable with known techniques **3%**.

## The run's work: the 🟡 `DelangeMean` axiom

### Part A (laps 43–48) — the `v`-direction programme, closed out
| lap | commit | result |
|---|---|---|
| 43 | `25edb1d` | `tendsto_primeSum_div_log`, `delangeKernelMean_of_converges` — **part II closes**: `S` converges ⟹ `DelangeKernelMean` (`(z−1)L = 0` forces `L = 0`).  Also `sum_weight_tail_le`. |
| 44 | `98dfce9` | `delangeOmegaT_eq` — the `ω`-weighted Levin–Fainleib identity (no log, no Abel, no Mertens); `delangeS_grade`. |
| 45 | `9371cdc` | `hasDerivAt_delangeSv` — `∂_v S(N;v) = Σ_{p≤N}(1/p)S^{(p)}(N/p;v)`, `S(N;0)=1`. |
| 46 | `c821e95` | `norm_delangeSv_le` — integrating factor: `‖S(N;ξ)‖ ≤ e^{L·Re ξ} + B‖ξ‖/(L|Re ξ|)`. |
| 47 | `9795469` | `sum_inv_prime_sdiff_le` (`Σ_{K<p≤N}1/p` bound); `norm_delangeE_le_split`. |
| 48 | `ee249fa` | `tendsto_delangeL_atTop` (Mertens 2nd); **`delangeKernelMean_of_errorBounded`** — the axiom reduced to ONE uniform `O(1)` bound. |
| 49 | `425acca` | `sum_inv_sq_prime_le`; `norm_delangeE_sub_toeplitz_le` — the core becomes a pure Toeplitz statement. |
| 50 | `124b3db` | `delangeToeplitz_swap`, `delangeW_le` — the core becomes a short-interval statement. |

**Refuted and recorded (do NOT retry): absolute majorisation of `E_N`.**  `Σ_p (1/p)(A(N)−A(N/p))
≍ (log N)^u → ∞` while the truth is `O(1)`; the extra weight `w_N` changes only the constant.
So the `v`-direction core is irreducibly a cancellation statement.  It is left as a *stated,
machine-checked conditional* (`delangeKernelMean_of_errorBounded`), not a `sorry`.

### Part B (laps 51–52) — THE SCALE ROUTE, which looks like it closes
The `v`-direction multiplier, once normed, is `u = ‖z−1‖` (lap 35's refuted fixed point).  The
**scale** multiplier is `1+(z−1) = z`, of modulus **exactly one**, and its error is measured
against `A(N) = Σ_{n≤N}‖h(n)‖/n ≍ (log N)^u`, which is `o(log N)` exactly in the repo's regime
`u < 1`.  Lap 35's refutation does not apply: it normed a different equation's multiplier.

* 51 (`c5a8309`): `delangeAbel_eq_hyperbola` and `sum_primeWeight_delangeS_eq` — both sides of the
  equation are the same hyperbola sum `Σ_{n≤N}(h(n)/n)·(weight)`.
* 52 (`d019a00`): **`delange_scale_equation`** :
  `‖z−1‖ ≤ 1 → ‖S(N)·log N − z·Abel(N)‖ ≤ 19·A(N)`.
  Supporting: `log_natDiv_ge`, `abs_mertens_sub_log_le`, `norm_delangeSrestr_le_delangeA`,
  `sum_log_div_sq_prime_le`.  **No bound on `‖S‖` is assumed anywhere** — the trivial `‖S‖ ≤ A`
  suffices, because the sign rides on the integrating factor `σ^{-z}` and is never normed.

## NEXT SESSION — start here, two bricks

1. **`A(N) ≤ C_u·(log N)^u`.**  `delangeA_le_prod` (lap 36) gives `A(N) ≤ Π_{p≤N}(1+u/p) ≤
   exp(u·Σ_{p≤N}1/p)`, so what is needed is the *upper* Mertens bound `Σ_{p≤N}1/p ≤ log log N + C`.
   Route: sum `sum_inv_prime_sdiff_le` (already proved) over the `⌈log₂ log N⌉` dyadic blocks
   `K_j = N^{2^{-j}}`, each contributing `≤ 1 + O(2^j/log N)`.  Elementary, ~1 lap.
2. **The discrete integrating factor.**  `Z(N) := Abel(N)·(log N)^{-z}`;
   `Abel(N+1) − Abel(N) = (log(N+1) − log N)·S(N)` (from `delangeAbel`'s definition), so the scale
   equation gives `‖Z(N+1) − Z(N)‖ ≲ A(N)(log N)^{-1-Re z}(log(N+1) − log N)`.  Summing with (1)
   yields `‖Abel(N)‖ ≲ (log N)^{Re z} + (log N)^{u}`, and the scale equation then returns

       ‖S(N)‖ ≲ (log N)^{Re z − 1} + (log N)^{u−1} → 0 ,

   i.e. `DelangeKernelMean z` for `Re z < 1`, `‖z−1‖ < 1` — **unconditionally**.  The continuous
   analogue of this step is `norm_delangeSv_le`, already formalised in the same file; here the
   factor is a real power rather than an exponential, so `Complex.cpow` handling
   (`Complex.norm_cpow_eq_rpow_re_of_pos`) is the only new API.
   Est. 2–3 laps.

If both land, the 🟡 `DelangeMean` axiom becomes a theorem in the regime `‖t‖_{ℝ/ℤ} < 1/6`, which
is what `delangeKernelTail_of_norm_lt_one` (lap 28) already requires — i.e. the axiom is fully
discharged on its stated regime.

## Confidence at wrap
- `twoPointWeightedAvg_all` TRUE: **90%**; provable with known techniques: **3%** (unchanged).
- C1 equivalent to a named open problem, as a theorem in `src/`: **done** (WRAP 4).
- `DelangeKernelMean` (hence `DelangeMean` on `‖t‖<1/6`): 15% at WRAP 4 → **80%**.
