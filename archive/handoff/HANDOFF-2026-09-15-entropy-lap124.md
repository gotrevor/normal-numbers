# HANDOFF — lap 124: **`head_frac_tiny` is proved**; the active decomposition has no open leaf

**Branch** `wip/g4-entropy`.  `lake build` 🟢 **9020 jobs**.  `src/` carries **two** `sorry`s, both
the pre-expedition off-path ones (`PrimeLambertOscillation.phaseOscillation`,
`MahlerDriftOne.exists_drift_one_background`).  **The active crux has none.**  Every new endpoint
prints `[propext, Classical.choice, Quot.sound]`.

## What this lap did — lap 123's "Next lap" item 1

| commit | content |
|---|---|
| `eaa10e1` | `G4GridP0Lower.lean` — the **lower** bound on `P₀` and the level-to-level growth |
| (this) | `G4EntropyWHead` — `head_growth`, `head_slack`, `head_core`, and `head_frac_tiny` |

### The obstruction, and why the guessed route fails

Lap 123 named the leaf exactly right: *what is missing is a LOWER bound on `P₀`*.  Its suggested
route was `Mprod = ∏_α d_α² ≥ gridQ^{2|Atom|}`.  **That route cannot close it.**  Count logs:
`log Mprod(K+4) ≈ 2·H(K+4)·log Q ≈ K^{6K}`, while `log P₀(K) ≳ T(K)²·log Q ≈ K^{8K}` — the upper
bound on the *previous* level is bigger, because `H(K)² = K^{4K}` dwarfs `H(K+4) = K^{2K+8}`.
The Chebyshev/primorial fallback is worse still (`2^{2T'}`, i.e. `K^{2K+10}` in the exponent).

### What does work: `freezeQ` counts PAIRS

`freezeQ = (∏_{p ≤ 2T} p)·∏_{i≠i'} |ρ_i − ρ_{i'}|`.  The second factor has `T²` factors, which is
the same order as the *upper* bound `((K+N)Dm)^{T²}` — so it is the only place with enough room.

* **`gridQ_le_dist`** — for two distinct atoms **on the same layer**, `shiftG_eq` gives
  `ρ_{α,j} = j + Q(jD₀ + proj B j α)`, so the difference is `Q·(proj α − proj β)`, nonzero by
  `ρ_injective`.  Hence `dist ≥ Q`.  (Different layers give only `dist ≥ 1`: `ρ ≡ j (mod Q)`.)
* **`distProd_ge` / `P₀_ge_pow`** — there are `T·(H−1)` same-layer ordered pairs, so
  `P₀ ≥ Q^{T(H−1)}`.
* **`P₀_le_pow_gridQ`** — the other side, in the same base: `Dm ≤ Q²`, `2T+1 ≤ Q`, `K+N ≤ Q`
  turn `gridP₀Bound` into `Q^{7T²}`.  The only factorial fact needed is `W! ≥ W(W−1)`.
* **`exponent_growth`** — `H(K+4) ≥ (K²+1)⁴·H K` and `N' ≥ N`, so `T'(H'−1) ≥ 7T²+3` with a
  factor `K^{14}` of slack.
* **`P₀_growth`** — `256·(K+4)²·Dm(K+4)·H(K+4)·P₀ K ≤ P₀ (K+4)`.

### The head estimate

`wFloor (i+1) = 4·Dm_{i+1}·wTop i`, so the head's window count is
`≈ 60·Dm'·wTop i·|Atom'|/P₀'` against a history `≥ (wTop i − wFloor i)/P₀_i · kk_i`; the scale
`wTop i` cancels and `head_growth` (= `P₀_growth` transported) closes the multiplicative part
while `head_slack` (`8·P₀·junk ≤ wTop i`, via `|Atom'| ≤ 2^{2(K+4)²} ≤ Xlo (KK i)`) closes the
additive part.  `head_core` is the schedule-free real arithmetic, with minimal hypotheses.

## Next lap — DIRECTION item 4, the squeeze and the endpoint

Unchanged from lap 123's item 2, now with **no gated/ungated hole**:

For `n` in band `i`, write `n = fTW i + a·kk i + s`, `s < kk i`; `winCount` is monotone so the
cutoffs `fTW i + a·kk i` suffice (`fTW_kk_le` gives `kk i/fTW i → 0`).  Use `aLe_fnthW` to turn
the read index `a` into the cutoff `c := fnthW i (a−1)`, then `fullW_prefix_winCount_bounds` +
`abs_prefix_ratio_sub_le` when gated, and `aLe_le_headW` + **`head_frac_tiny`** when not.  Then
`IsNormalSequence 2 (fullDigW …)`, `properDigits_fullDigW`, `fullRealW`,
`Bridge.isNormal_realOfDigits` → **`IsNormal 2 fullRealW`**.
(`exists_matchesAt_fullDigW` still needs a wide non-vacuity witness.)

## Hygiene (new this lap)

* `set G := gridOf K N hK` **blocks the `G.K = K` defeq** — `congrArg Prod.fst (G.ρ_injective h)`
  then fails to typecheck against `α ≠ β`.  Write `(gridOf K N hK)` out instead of `set`.
* `Fin.sum_univ_eq_sum_range` will not `rw` in this shape; apply it as a term
  (`exact Fin.sum_univ_eq_sum_range (fun i => B ^ (i+1)) K`).
* `nlinarith` cannot do AM-GM in `ℕ` (`4ab ≤ (a+b)²`): cast the one step to `ℤ` and feed
  `sq_nonneg ((a:ℤ) - b)`, then `exact_mod_cast`.
* Proof-irrelevant `gridOf` arguments: `gridOf_congr` (`subst`, then `rfl`) is the way to move
  between `gridAt (i+1)` and `gridOf (KK i + 4) …`; `rw [KK_succ i]` alone hits the dependent
  proof argument.

## Do not re-derive

`DIRECTION.md`'s CURRENT DIRECTIVE still forbids re-litigating the scale gap or the head
obstruction, lowering the band floor, adding joint-ladder rungs or sharpening constants, and
touching `fullReal`/`fullPos`/`bandT`.  `density_antitone` stays withdrawn.  **`Mprod`/primorial
as a route to a `P₀` lower bound is refuted above — do not retry it.**
