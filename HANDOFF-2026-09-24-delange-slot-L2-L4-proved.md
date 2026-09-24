# HANDOFF 2026-09-24 — Delange slot: L2 and L4 PROVED; chain L1–L7 complete

Branch `wip/delange-slot`, HEAD `b309021`, tree clean, `lake build` green (9176 jobs).
Objective (`KICKOFF-2026-09-24-delange-slot.md`): prove `omegaLarge_mean_tendsto_zero` and
`twisted_omegaLarge_mean_tendsto_zero` in `src/NormalNumbers/DelangeSlot.lean` — both still `sorry`.

## Landed this lap

**L4 (the crux) — `exists_L4`, axiom-clean.**  New `src/NormalNumbers/DelangeSlotPNT.lean`:
* `log_sq_mul_exp_le` — converts `MediumPNT`'s `exp(−c (log x)^{1/10})` saving into a power of
  `log` with an **explicit** inequality, not a limit argument: `y²⁰/20! ≤ eʸ` at
  `y = c (log x)^{1/10}` gives `(log x)² e^{−y} ≤ 20!/c²⁰`.
* `exists_abs_psi_sub_le` — `|ψ(x) − x| ≤ C₀ x/(log x)²` for large `x`.
* `telescope_step` / `telescope_sum` — the discrete form of `∫ du/u² < ∞`:
  `∑_{k≤K} 1/(k v_k²) ≤ 2/v_K + 1/(K v_K²)` for positive antitone `v` with gaps `≥ 1/(k+1)`.
  **This is what makes the `O(N)` budget close**; a dyadic bound loses a factor `log N`.
* `exists_sum_abs_deltaN_le` — splice at `k = ⌊N/n₁⌋`.  Small-quotient range: `≤ N` terms each
  `≤ ψ(n₁)+n₁` (uniform by monotonicity of `ψ` — no `Finset.sup'`).  Large-quotient range: the
  telescope, using that floors lose at most a factor 2 inside the log (`log 8 > 2` is the slack).
* `exists_sum_psi_sub_le` — L4 in real form (adds the `O(N)` floor error).

**L2 — `exists_L2`, axiom-clean.**  New `src/NormalNumbers/DelangeSlotPrimePow.lean`:
* `sum_le_primePow_rectangle` — the reindexing that makes L2 work at all.  Neither error sum is
  termwise summable over `ℕ` (the chain `d = 2^j` decays only geometrically **in `d`**), so
  `d ↦ (d.minFac, Nat.log d.minFac d)` is used: injective on prime powers, lands in
  `T ×ˢ Icc 1 (Nat.log 2 N)`, all weights nonneg ⟹ bounded by the whole rectangle.
* `geom_Icc_mul` / `geom_Icc_le` / `geom_Icc_succ_le` — the geometric series in the exponent.
* `sum_log_div_sq_le` — `∑_{2≤n≤N} log n/n² ≤ 4`, uniformly, by the telescoping majorant
  `4(1/√(n−1) − 1/√n)` off `log n ≤ 2√n`.  **No `Summable` and no `rpow` needed.**
* `sum_vonMangoldt_mul_div_minFac_le` — large primes: `∑_d Λ d ⌊N/(d·minFac d)⌋ ≤ 8N`.  The
  extra `1/p` beyond `1/d` is exactly what converges.
* `sum_vonMangoldt_smooth_le` — the fixed-`P` block: `≤ 2N ∑_{n≤P} log n/n`.

`#print axioms` on `exists_L2`, `exists_L4`, `exists_sum_abs_deltaN_le`,
`recursion_tendsto_zero` — all `[propext, Classical.choice, Quot.sound]`.

## Chain status (`DelangeSlotAnalytic.lean` header table is current)

L1 `sum_hfun_mul_log` ✔ · L2 `exists_L2` ✔ · L3 `sum_Lambda_mul_Ssum` ✔ · L4 `exists_L4` ✔ ·
L5 `norm_sum_hfun_mul_log_sub` ✔ · L6 `mSum_eq` ✔ · L7 `recursion_tendsto_zero` ✔.

## Next (in order) — nothing structurally hard is left in rung 1

1. **`sigmaMean_tendsto_zero_of_recursion`** (`DelangeSlotAnalytic.lean` l. ~250, the ONE
   remaining `sorry` outside `DelangeSlot.lean`).  A wrapper: make `DelangeSlotAnalytic` import
   `NormalNumbers.DelangeSlotRecursion` and apply `recursion_tendsto_zero`, supplying
   `hσ := norm_sigmaMean_le hz` and `z.re < 1`.  For the latter: `|z.re| ≤ ‖z‖ = 1`
   (`Complex.abs_re_le_norm`); if `z.re = 1` then `Complex.normSq z = 1` forces `z.im = 0`,
   hence `z = 1` by `Complex.ext` — contradiction with `hz1`.
2. **Assemble rung 1.**  Chain the five identities/estimates into
   `‖(log N − z) σ N − z Ψ N‖ ≤ C` for `N ≥ 2`:
   * L1+L2: `A N = z ∑_d Λ d S(N/d) + O_P(N)`;  L3: `= z ∑_k h k ψ(N/k) + O_P(N)`;
   * L4: `= z N m N + O_P(N)`;  L5: `A N = S N log N + O(N)`.
   * So `S N log N = z N m N + O_P(N)`.  Divide by `N` (`N ≥ 1`): `σ N log N = z m N + O_P(1)`.
   * L6: `m N = σ N + Ψ N`, so `(log N − z) σ N − z Ψ N = O_P(1)`.  Feed `recursion_tendsto_zero`.
   * Finally `∑_{m ∈ Icc 1 N} z^{ω_{>P} m} / N = Ssum z P N / N = σ N` — note the headline uses
     `Icc 1 N` and `Ssum` uses `Ioc 0 N`; these Finsets are equal (`Finset.Icc 1 N = Ioc 0 N`).
3. **Rung 2 (the twist).**  `m = s·t` (`P`-smooth × `P`-rough), reduce to residue classes of `t`
   mod `Q' ∣ Q`, expand in Dirichlet characters, rerun on `χ·h` (the Λ-identity holds verbatim).

## Watch-outs (this lap's friction)

* `field_simp` frequently closes the goal on its own — a trailing `ring` then errors with
  "No goals to be solved".  Same for `norm_num`.
* `div_le_div_iff` → **`div_le_div_iff₀`**; `abs_add` → **`abs_add_le`**;
  `Real.pow_div_factorial_le_exp` needs the **explicit** `(x := …)`.
* `rw [hdk]` where `hdk : d = d.minFac ^ k` rewrites *inside* `d.minFac` too.  Use
  `nth_rewrite 2 [...]`, or cast the equation first
  (`exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hpow`) and rewrite the cast.
* `sum_hfun_shift_small` has `{P : ℕ}` implicit *before* `hP`; pass `(P := P)` or `omega` cannot
  see which `P` it is proving `¬ P < p` for.
* `Nat.div_lt_iff_lt_mul (hk : 0 < k) : a / k < b ↔ a < b * k` is the clean way to get
  `N < (N/k + 1) * k`; `omega` cannot handle `k * (N / k)` with a variable divisor.

## Pointers
`DIRECTION.md` → CURRENT DIRECTIVE (owns the route; do not edit outside an altitude lap) ·
`STATUS.md` · `PENDING_WORK.md` · `DESIGN-2026-09-24-delange-route.md` ·
`KICKOFF-2026-09-24-delange-slot.md`
