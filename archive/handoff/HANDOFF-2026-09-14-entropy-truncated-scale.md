# HANDOFF — the truncated-scale route: E1 down, the per-atom caveat closed, the head pinned

**Branch** `wip/g4-entropy`.  **HEAD** `bbeb413`.  Working tree **clean**.
`lake build` 🟢 **9003 jobs**.  Four new modules; **one** named `sorry` leaf, in `src/`,
on the active decomposition (`Sched.card_bandTtr_ge`).  No `axiom` introduced.  Every new
sorry-free endpoint prints `[propext, Classical.choice, Quot.sound]`.

## The session in four lines

0. **`a0901ed`** — the operator's required hygiene commit (docs-only): the wall's scope.
1. **`d9e5b3b`** — the crux is the **head** of each band, and no rung of the ladder covers it.
2. **`dac4935`** — `entropy_E1_down`: the `50√K` rate at every truncated outer scale.
3. **`06132c8`** — the **per-atom truncation caveat is closed**, with the factor `1 + 1/K`.
4. **`bbeb413`** — the truncated band law, a compiling skeleton with one named leaf.

## 0. Hygiene (`a0901ed`, docs-only) — DONE

`DIRECTION.md` `0ed0103` required, before anything else, rewriting the docstring of
`certified_granule_exceeds_previous_scale` and the matching prose in `STATUS.md`,
`PENDING_WORK.md` and `HANDOFF-…-laps61-118.md` to the corrected scope: it is a **size
comparison** between a certificate's non-vacuity threshold and the previous scale's output; it
does **not** prove prefix frequencies diverge; "closed on this mechanism" = closed for deduction
from the fixed sampled data alone, not for every arithmetic extension.  Done.

## 1. Where the crux actually is (`G4EntropyScaleGap.lean`)

A band-`i` window start is `2·kIdx(n,α)`, increasing in `n`, so a **position cutoff selects the
truncated sample `n ≤ X'`**: a mid-band prefix of the read *is* a sample at a smaller outer
scale, which `entropy_E0_down`/`entropy_E1_down` certify for `X' ∈ [Xlo K, X K]`.
**Mid-band prefix control is therefore NOT the obstruction.**  The obstruction is the **head**,
`X' < Xlo K_i`, and the previous rung cannot cover it either:

```
Sched.Xhi K k₄ := 2^2^(m K + 3k₄) + X K      A0's ceiling: every rung-K witness has W.X ≤ Xhi
Sched.Xhi_succ_lt_Xlo_step                    Xhi K k₄ + 1 < Xlo (K+4)
Sched.Xhi_lt_Xlo_step, ScaleGap, scaleGap     the gap is inhabited
ScheduleWitness.X_lt_Xlo_step                 no rung-K witness reaches rung K+4's FLOOR
```

`X_lt_X_step` (A0) said a rung cannot reach the next band's *scale*; this says it cannot reach
the point where the next band's certificate even switches on.  Outer scales in
`(Xhi (K−4), Xlo K)` are certified by **no rung**.  The separation is a tower
(`m₁(K+4) ≥ 4096·m₁ K`), so no constant, no deficit improvement, no residue class (objective B).

### Sub-approaches tried and REFUTED (do not retry; computations in `PENDING_WORK.md`)

* **Skip the head** — the chunk `[Xlo, X']` is then an `(X'−Xlo)/X'` fraction of the certified
  `[0,X']`; error `≈ 2ε·Xlo/(X'−Xlo)` blows up exactly where the chunk first dominates the
  history.  Gap relocated, not closed.
* **Certified annuli** (differences of nested certified truncations) — same computation.
* **Pad the history** (all `P₀` classes at rung `K−4`, longer windows, more atoms) — gains are
  polynomial in `K` or bounded by `P₀`, against a tower.
* **Raise the previous rung's reach** — that is A0, verdict NO (`G4EntropyXCeiling`).

The only mechanism in the repo that solves a prefix problem of this shape is `BlockConcat.rep`
(repetition, `G4EntropyConcat`) — exactly what forfeits strict monotonicity.  That is the
tension, stated honestly.  **`IsNormal 2 fullReal` is blocked here**; do not spend laps
re-deriving it.

## 2. `entropy_E1_down` (`G4EntropyE1Down.lean`)

Everything downstream of the entropy input consumes `entropy_E1`, not `entropy_E0`.  Ported with
the three leaves `G4EntropyE0Down` already supplies:

```
smallPrimeBound_tiny_down, smallPrime_term_tiny_down   ← term_a_le_down, term_d_le_down
hbig_small_down             ← sample_term_le_down, log_Mx_div_le_down
hfar_small_down             ← hfar_holds_down
entropy_E1_down             m_K·H_K − 50√K·H_K < H₂(Z^{G4}_{K,X'}),  Xlo K ≤ X' ≤ X K
```

Nothing else in the E1 cone noticed `X K → X'` — a third independent confirmation of A0's audit.

## 3. The per-atom caveat is CLOSED (`G4EntropyMultiplierSpread.lean`)

Last session's open caveat: a position cutoff truncates **per atom** (`X'_α = t_α + d_α c/2`).
Route (i) holds, with factor `1 + 1/K`, because the schedule grid takes `d_α = 1 + Q(D₀ + u_α)`
with `D₀ = K·U` and `u_α ≤ U` — the atom-dependent part is a `1/K` perturbation:

```
gridOf.d_ge, gridOf.d_le'
gridOf.mul_d_le_mul_d      K·d_α ≤ (K+1)·d_β   for EVERY pair of atoms
G4Entropy.mul_kIdx_le, two_mul_le_of_two_kIdx_le
G4Entropy.kIdx_cross       2·kIdx(n,β) ≤ c  →  K·(2·kIdx(n,α)) ≤ (K+1)(c+4)
```

The truncation vector is sandwiched between two plain outer scales of ratio `(K+1)/K + O(1/c)`;
the sandwich costs a relative `≈ 1/K`, negligible against the `O(K^{−1/4})` capture errors.
**Route (ii) — restating the entropy theorems for a truncation vector — is not needed.**

## 4. The truncated band law (`G4EntropyBandTrunc.lean`) — ⚠️ THE OPEN LEAF

```
PKtr i X' = apSample X' P₀ b₀ ;  bandTtr i X' = bandT i ∩ {n < X'}
deficit_primeLambertFour_down   PROVED   E1 at X', in |Atom| form
card_bandTtr_ge                 ⚠️ SORRY  σ ≥ 1/2 at every X' ≥ Xlo (KK i)
H₂_bandTLawTr_ge                PROVED   per-window deficit ≤ 101√K, at X'
abs_posAvg_bandTLawTr_le        PROVED   capture 2√(808 log2·ℓ/√K), at EVERY X' ≥ Xlo
```

The content is what is **absent**: no `(δ+1)|P_K|/a` restriction price, because the truncated
prefix is certified in its own right.  That is what drops the bad initial portion of each band
from a `K^{−1/2}` fraction (`abs_midRead_freq_sub_le`) to an `X^{−1/2}` fraction.

### How to close `card_bandTtr_ge` (next lap, first thing)

Mirror `G4EntropyBand.card_bandT_ge` with `X'` in place of `X (KK i)`:

```
|PKtr i X'| ≥ X'/P₀ − 1                              card_apSample_ge
|PKtr \ bandTtr| ≤ |{n ∈ PKtr : n < Dm·bandLo i}| ≤ Dm·bandLo i/P₀ + 1
```
so it suffices that **`4·Dm·bandLo i + 4·P₀ ≤ Xlo (KK i)`**, where `Dm = gridDm (KK i) (N (KK i))`
and `bandLo (j+1) = bandTop j = 2·X (KK j) + kk j` (`bandLo 0 = 0`, trivial case).
Available inputs: `gridDm_le_Xlo`, `two_mul_exp_le_Xlo`, `logP₀Nat_le_two_pow_m`,
`Sched.Xhi_lt_Xlo_step`, `Sched.m_add_lt`, `Xlo_cast` (`Xlo K = 2^{50·2^{m K}}`).
Target shape: `Dm ≤ 2^{2^{m (KK i)}}` and `X (KK i − 4) ≤ 2^{2^{m (KK i)}}`, then
`8·2^{2^m}·2^{2^m} + 4·2^{2^m} ≤ 2^{4·2^m} ≤ 2^{50·2^m}`.

### After that

1. Render `abs_posAvg_bandTLawTr_le` as a **count** over the truncated band (mirror
   `posAvg_bandTLaw_eq_count`), then as digits.
2. Feed it through the `fullPos` machinery (`read_freq_error_bound`,
   `abs_fullRead_sub_bandRatio_le`) with `kIdx_cross` supplying the sandwich, to get:
   *every cutoff beyond an `X^{−1/2}` fraction of its band is good.*
3. That is the maximal statement the mechanism supports (§1).  It is **not** normality.

## Hygiene notes (carried + new)

* `X K → X'` ports keep working by verbatim copy + substitution; `entropy_E1_down` compiled after
  two `1 ≤ X'` fixes (`Nat.one_le_two_pow` no longer applies — use `Xlo_pos K` + `omega`).
* `omega` cannot see through `set a := … with ha` once a later `unfold` re-introduces the
  unfolded form: state the folded equation as `have … := by rw [ha]; rfl`.
* `omega` cannot multiply two atoms: give it the product identity as a `have … := by ring` first.
* `set G : GridParams := gridOf K N hK` breaks elaboration of hypotheses whose *type* mentions
  `(gridOf …).Atom` (you get `β✝` mismatches).  Write `gridOf K N hK` out in full instead.
