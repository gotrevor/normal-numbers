# HANDOFF — the scale gap, and E1 downward

**Branch** `wip/g4-entropy`.  Working tree clean at commit time.  `lake build` 🟢 **9001 jobs**.
Two new modules, both sorry-free; no `axiom` introduced.  Every new endpoint prints
`[propext, Classical.choice, Quot.sound]`.

## 0. Operator hygiene commit — DONE (`a0901ed`)

`DIRECTION.md` `0ed0103` required, before anything else, rewriting
`certified_granule_exceeds_previous_scale`'s docstring and the matching prose to the corrected
scope: a **size comparison** between a certificate's non-vacuity threshold and the previous
scale's output; not a proof that prefix frequencies diverge; "closed on this mechanism" = closed
for deduction from the fixed sampled data alone.  Done in `G4EntropyMixture.lean`,
`STATUS.md`, `PENDING_WORK.md` and the laps-61–118 wrap.

## 1. The crux, relocated and then pinned (`G4EntropyScaleGap.lean`, `d9e5b3b`)

A band-`i` window start is `2·kIdx(n,α)`, increasing in `n`.  So a **position cutoff inside band
`i` selects the truncated sample `n ≤ X'`**: a mid-band prefix of the read *is* a sample at a
smaller outer scale, and `entropy_E0_down` certifies it for every `X' ∈ [Xlo K, X K]`.
**Prefix control inside a band is therefore not the obstruction.**

The obstruction is the **head** — cutoffs with `X' < Xlo K_i` — and the previous rung cannot
cover it:

```
Sched.Xhi K k₄ := 2^2^(m K + 3k₄) + X K     A0's ceiling: every rung-K witness has W.X ≤ Xhi
Sched.Xhi_succ_lt_Xlo_step                   Xhi K k₄ + 1 < Xlo (K+4)
Sched.Xhi_lt_Xlo_step, ScaleGap, scaleGap    the gap is inhabited
ScheduleWitness.X_lt_Xlo_step                no rung-K witness reaches rung K+4's FLOOR
```

`X_lt_X_step` (A0) said a rung cannot reach the next band's *scale*; this says it cannot reach
the point where the next band's certificate even switches on.  The outer scales in
`(Xhi (K−4), Xlo K)` are certified by **no rung of the ladder**.  The separation is a tower
(`m₁(K+4) ≥ 4096·m₁ K`), so no constant, no deficit improvement, no residue class (objective B).

### Sub-approaches tried and refuted this lap

* **Skip the head** (band `i` read starts at `Xlo K_i`): the chunk `[Xlo, X']` is then an
  `(X'−Xlo)/X'` fraction of the certified `[0,X']`, error `≈ 2ε·Xlo/(X'−Xlo)`, which blows up
  exactly where the chunk first dominates the history.  Gap relocated, not closed.
* **Certified annuli** (differences of nested certified truncations): same computation.
* **Pad the history** (all `P₀` classes at rung `K−4`, longer windows, more atoms): gains are
  polynomial in `K` or bounded by `P₀`, against a tower.
* **Raise the previous rung's reach**: that is A0, verdict NO.

The only mechanism in the repo that solves a prefix problem of this shape is `BlockConcat.rep`
(repetition) — which is precisely what forfeits strict monotonicity.  That is the tension, stated
honestly.

## 2. E1 downward (`G4EntropyE1Down.lean`)

Everything downstream of the entropy input consumes `entropy_E1` (deficit `50√K`), not
`entropy_E0`.  Ported, with the same three leaves:

```
smallPrimeBound_tiny_down, smallPrime_term_tiny_down   ← term_a_le_down, term_d_le_down
hbig_small_down            ← sample_term_le_down, log_Mx_div_le_down
hfar_small_down            ← hfar_holds_down
entropy_E1_down            m_K·H_K − 50√K·H_K < H₂(Z^{G4}_{K,X'}) for Xlo K ≤ X' ≤ X K
```

Nothing else in the E1 cone noticed `X K → X'`: the cover term, the Jackson term, `PropC`'s
combinatorics and the budget arithmetic are literally `X`-free.  (Confirms the A0 audit from a
third side.)

## 3. Next steps, in order

1. **Port the consumers of `entropy_E1` at a truncated scale.**  `G4EntropyGoodAtoms.atomDeficit`
   / `card_good_ge`, then `abs_posAvg_preLaw_le`, then a truncated `abs_midRead_freq_sub_le`.
   Target statement: for every cutoff `a` whose truncation satisfies `Xlo K_i ≤ X'(a)`, the read
   frequency at `bT i + a·m_i` is within `O(K^{−1/4})` of `2^{−|v|}` — **with no `|P_K|/a`
   term**.  That drops the bad initial fraction of each band from `K^{−1/2}` to `X^{−1/2}`.
2. **The per-atom caveat — CLOSED this lap** (`G4EntropyMultiplierSpread.lean`).  Route (i),
   with the factor `1 + 1/K`: the grid takes `d_α = 1 + Q(D₀ + u_α)`, `D₀ = K·U`, `u_α ≤ U`, so
   `gridOf.mul_d_le_mul_d : K·d_α ≤ (K+1)·d_β` for every pair of atoms, and
   `G4Entropy.kIdx_cross : 2·kIdx(n,β) ≤ c → K·(2·kIdx(n,α)) ≤ (K+1)(c+4)`.  The truncation
   vector is sandwiched between two plain outer scales of ratio `(K+1)/K + O(1/c)`; the sandwich
   costs a relative `≈ 1/K`.  Route (ii) is not needed.
3. Port the mid-band refinements from `bandPos` to `fullPos` (wrap next-step 1), carrying the
   multiplicity term through `overhang_frac_le`.
4. `IsNormal 2 fullReal` remains blocked by §1's head.  Do not spend laps re-deriving that;
   spend them on §1–§3, which are the maximal statement the mechanism supports.

## Hygiene notes

* The `X K → X'` ports keep working by verbatim copy + substitution; `entropy_E1_down` compiled
  on the first attempt after two `1 ≤ X'` fixes (`Nat.one_le_two_pow` no longer applies — use
  `Xlo_pos K` + `omega`).
* `omega` cannot see through `set a := … with ha` when a later `unfold` re-introduces the
  unfolded form: state the folded equation as a `have … := by rw [ha]; rfl` instead.
