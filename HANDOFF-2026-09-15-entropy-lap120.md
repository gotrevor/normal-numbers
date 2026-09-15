# HANDOFF — lap 120: `entropy_E1_march` proved, `card_bandTtr_ge` proved, the head deleted

**Branch** `wip/g4-entropy`.  **HEAD** `ab34a3d`.  Working tree **clean**.
`lake build` 🟢 **9010 jobs**.  **No `sorry` remains in the expedition's part of `src/`.**
Every new endpoint prints `[propext, Classical.choice, Quot.sound]`.

(The two `sorry`s still in `src/` — `MahlerDriftOne.exists_prime_nonresidue`,
`PrimeLambertOscillation.phaseOscillation` — belong to other campaigns and are on the
forbidden-drift list.)

## What this lap did

Executed `HANDOFF-2026-09-14-entropy-lap119.md`'s "Next lap — in order", steps 1 and 2, and then
found that steps 3 and 4 are not needed in the form they were written.

### Step 1 — `Sched.entropy_E1_march` ✅ PROVED (commits `2d779eb`, `4ea8a5d`, `3ab6487`)

Four new modules, all sorry-free:

| module | content |
|---|---|
| `G4EntropyMTowerHarmonic` | the two Mertens bounds stated **generically in the cutoff exponent** (`sum_inv_smallPrimes_ge_gen` / `_le_gen`, cutoff `2^{2^e}`), plus the marched instances at `e = mm₁ K j`.  Nothing in either proof used anything about `m₁ K` beyond its being a natural number — the audit's claim, now checked by the kernel. |
| `G4EntropyMTowerBudget` | the five `smallPrimeBound` terms at `R ↦ Rm K j`, `Mc ↦ Mcm K j`, sample at any `X' ≥ Xlom K j`; `R_pow_two_Mc_le_m`, `inv_card_le_down_m`, `main_term_le_m`, `term_{a,b,c,d}`, `smallPrime_term_tiny_down_m`. |
| `G4EntropyMTowerDown` | `hbig`/`hfar` **downward inside the marched window**: `sample_term_le_down_m`, `log_Mx_div_le_down_m`, `hbig_small_down_m`, `farC_le_down_m`, `hfar_holds_down_m`, `hfar_small_down_m`. |
| `G4EntropyMTowerAssembly` | `entropy_E1_march` (the assembly, `entropy_E1_down`'s proof verbatim with the three ported inputs), `entropy_E1_march_zero`, and **`entropy_E1_tile`**. |

`entropy_E1_march`, `entropy_E1_march_zero` and `entropy_E1_tile` **moved** out of
`G4EntropyMTower.lean` (where they were stated with a `sorry`) into the new downstream module;
statements unchanged.

> **`Sched.entropy_E1_tile` is now a theorem**: the E1 conclusion at **every** outer scale in
> `[Xlo K, Xlo (K+4)]`.  `G4EntropyScaleGap`'s obstruction was an artifact of pinning `m` to `K`.

The audit's prediction held exactly everywhere: the only place the march could have hurt is the
dyadic Chebyshev factor, and `dyadic_factor_le_m` is the original proof *verbatim* because
`mm − mm₁ = m₂ K` by definition of the march.

### Step 2 — `Sched.card_bandTtr_ge` ✅ PROVED (commit `665ba46`)

New ingredients in `G4EntropyBandTrunc`:

* `m_step_seven` — `m (KK i) + 7 ≤ m (KK (i+1))`, from `m₂ (K+4) − m₂ K = 64K + 128` alone.
  `two_pow_m_step`'s `+1` is **too weak** here: the count needs `101·2^{m_i} ≤ 49·2^{m_{i+1}}`
  and `+1` only delivers `98·2^{m_i}`.  This was the one real obstacle in step 2.
* `exponent_gap_Xlo`, `band_gap_strong_Xlo` — the band gap against the **downward** floor:
  `12·Dm(K_{i+1})·X(K_i) + 4P₀ ≤ Xlo(K_{i+1})`, not merely `≤ X(K_{i+1})`.
* `bandTtr_eq_filter` — the truncated band is the truncated *sample*'s part above the band
  floor, which is what lets `card_bandT_ge`'s count run verbatim at `X'`.

So `H₂_bandTLawTr_ge` and `abs_posAvg_bandTLawTr_le` are now unconditional.

### Steps 3–4 — superseded.  `G4EntropyBandHead` (commit `ab34a3d`)

Item 3 (`density_antitone`) and item 4's level-switch existed **only to pay for an uncertified
head**.  With `entropy_E1_tile` the head can be *deleted* instead, structurally:

> **`bandLoH i := 2·Xlo (KK i)`.**  `bandLo` is a free design parameter — it only ever had to
> clear the previous band's ceiling.  Raising it to twice the level-`i` certificate floor makes
> every sample time of the band satisfy `n ≥ gridDm·2·Xlo (KK i) ≥ Xlo (KK i)`
> (`Xlo_le_of_mem_bandTH`), so **every** mid-band truncation `X'` is inside
> `G4EntropyBandTrunc`'s certified range.

The two things that could have broken both hold with enormous margin:

* `card_bandTH_ge` — the raised band still keeps **half** the sample, because
  `X (KK i) = Xlo (KK i)²`: the dropped stretch is the *square root* of the range.  Gate:
  `head_gate : 8·gridDm·Xlo (KK i) + 4P₀ ≤ X (KK i)`, slack `2^{49·2^m}`.
* `bandTop_le_bandLoH` — the raised floor still clears band `i`'s ceiling: exponents
  `100·2^{m_i}` against `50·2^{m_{i+1}} ≥ 6400·2^{m_i}`.

The cost is a skipped **position** gap between `bandTop i` and `bandLoH (i+1)`.  Harmless: the
read was already a density-zero subsequence (`tendsto_density_fullPos`).

`density_antitone` is **withdrawn** as an objective (recorded in `PENDING_WORK.md`).

## Next lap — in order

1. **`fullPosH`** — re-run `G4EntropyFullSeq`'s construction on `bandTH` in place of `bandT`:
   `winStartsH`, `fnthH`, `fLH`, `fTH`, `fullPosH`, `fullDigH`, `fullRealH`.  New module
   (keep `fullReal` and its theorems untouched, per the 19:06 override).
   * The window-gap (`windows_eq_or_disjoint`) and overhang arguments are `bandLo`-free and
     port verbatim.
   * What changes: `card_bandTH_ge` in place of `card_bandT_ge'`, and
     `bandLoH_le_pos_of_mem_bandTH` in place of `bandLo_le_pos_of_mem_bandT`.
   * Strict monotonicity of `fullPosH` needs `bandTop_le_bandLoH` where `fullPos_strictMono`
     used `bandLo (i+1) = bandTop i` **definitionally** — this is the one place the raised
     floor is not a drop-in: the old proof had an equality, the new one has an inequality.
     Check `G4EntropyFullSeq.lean:171` before porting.
2. **Mid-band prefix control.**  For a cutoff `a` inside band `i`, the read's first `a` window
   starts come from the truncation at `X' = ` (the `a`-th sample time in increasing order), and
   `Xlo_le_of_mem_bandTH` puts that `X'` above the floor, so `abs_posAvg_bandTLawTr_le` applies
   with **no** restriction price.  Needed: the order-isomorphism between "first `a` window
   starts" and "sample times `< X'`" — `G4EntropyMultiplierSpread.kIdx_cross` is the per-atom
   bracket that makes a single `X'` work for all atoms.
3. **`IsNormalSequence 2 (fullDigH …)`** and `Bridge.isNormal_realOfDigits` → `IsNormal 2 fullRealH`.

## Hygiene notes (new this lap)

* `∑ p ∈ ((2 : ℕ) ^ 2 ^ e + 1).primesBelow, (p : ℝ)⁻¹` **fails to elaborate** — the binder's
  type gets fixed to `ℝ` by the coercion and the `Finset` is then expected to be `Finset ℝ`.
  With a *variable* `Rg : ℕ` (`(Rg + 1).primesBelow`) it elaborates fine.  Hence the generic
  Mertens lemmas take `{Rg : ℕ} (hRg : Rg = 2 ^ 2 ^ e)` rather than the closed form, and do
  **not** `subst` it.
* After `set i := j + 1`, a lemma stated at `j + 1` no longer unifies syntactically with the
  goal's `i`, and the unifier falls back to `whnf` on `Xlo (KK (j+1))` — an instant timeout.
  Don't `set` an index that appears inside a schedule `def`; spell `j + 1` out.
* `exact_mod_cast` / `positivity` on goals mentioning `(gridAt i).P₀` or `Xlo (KK i)` can blow
  the heartbeat budget (they unfold).  Use `Nat.cast_le.2 h` and `show … by linarith` against a
  positivity fact already in context.
* `Finset.card_filter_add_card_filter_not` into a cast goal: `rw [heq, ← h]; push_cast; ring`
  works where `exact_mod_cast h.symm` times out.
* A theorem carrying `open Classical in` *and* a `classical` tactic can produce two decidability
  instances for the same predicate and an `isDefEq` blow-up.  Drop the `open Classical in`.

## Do not re-derive

`DIRECTION.md`'s CURRENT DIRECTIVE (review lap 119) still forbids re-litigating the scale gap.
`certified_granule_exceeds_previous_scale`, `ScheduleWitness.X_lt_X_step`, `X_lt_Xlo_step`,
`Xhi_succ_lt_Xlo_step` remain true statements about the **one-dimensional** ladder and are now
non-binding.  `density_antitone` is withdrawn — do not start it.
