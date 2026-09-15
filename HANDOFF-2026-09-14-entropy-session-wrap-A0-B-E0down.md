# HANDOFF — session wrap: A0, B, and **E0 downward**

**Branch** `wip/g4-entropy`.  **HEAD** `3f94f7f`.  Working tree **clean**.
`lake build` 🟢 **8999 jobs**.  Four new modules, **all sorry-free**; no `axiom` introduced;
no pre-expedition G4/G5 file edited.  Every new endpoint prints
`[propext, Classical.choice, Quot.sound]`.

## ⚠️ FIRST ACTION NEXT LAP — the operator's hygiene commit (not yet done)

`DIRECTION.md` commit `0ed0103` (Astra's attended review, landed mid-session) requires, *before
anything else*: rewrite to the corrected scope the docstring of
`G4EntropyMixture.certified_granule_exceeds_previous_scale`, the "Part I — the wall" sentence of
`HANDOFF-2026-09-14-entropy-session-wrap-laps61-118.md`, and the matching `PENDING_WORK.md` /
`STATUS.md` lines.  The correction: that theorem is a **size comparison between a certificate's
non-vacuity threshold and the previous scale's output**.  It does NOT prove that prefix
frequencies fail to converge; "normality closed on this mechanism" means *closed for deduction
from the fixed sampled data alone*, not for every arithmetic extension.  This session did not do
it (the review landed after the laps had started).  It is docs-only.

The same commit re-ordered the objectives to **B, then A0, then A**.  This session ran A0 then B;
both have verdicts, so the ordering is moot now.

## The session in three lines

1. **A0 = NO**, and the obstruction is a theorem: `hbig`'s `log Mx / log Y` caps the outer scale.
2. **B = NO**, and the refutation is a theorem: the union over *all* residue classes is still
   sparse, because `d_α ∣ kIdx` is a fact about the multipliers, not about `b₀`.
3. **A new route**: E0 survives *shrinking* `X` down to `√(X K)` — which is the direction prefix
   control actually needs — and that is now proved.

## Part I — objective A0 (`G4EntropyXCeiling.lean`)

`X` enters the whole E0 cone through **one** field of `gridFrame`, `P := apSample X G.P₀ G.b₀`.
`θ, γ, S, A, d, t, η, ε, D`, hence `goodSets`, `pieceCube`, `res`, the cover sum, and E0's target
`M = k₄(K²+1)^K`, are all literally `X`-free.  Of the five `X`-sensitive terms, three are
monotone, `hfar`'s `log log X` is a never-binding ceiling (`X ≲ 2^{2^{2^{200K²}}}`), and
**`hbig`'s `(log Mx / log Y)` binds**, `hMx` forcing `Mx ≥ X − P₀`.

```
ScheduleWitness.log_Mx_div_log_Y_le, Mx_le_rpow, X_le_rpow   -- X ≤ Y^{3·2^K δbig ε η} + P₀
Sched.m₁_step, m_add_lt, pow_add_X_lt_X_step                 -- the ladder arithmetic
ScheduleWitness.X_lt_X_step                                  -- W.X < Sched.X (K+4)
```

Raising `Y` with `X` does not rescue it: `hbig`'s dyadic summand allows `m − m₁ ≲ 2^{5K/2}`, and
one rung costs `m₁(K+4) − m₁(K) ≥ 4095·1000·8^K·K^{2K+1}`.  The ladder's jump is set by the
**small**-prime budget, the fixed-`K` headroom by the **medium**-prime one — incommensurable.
Full per-declaration table: `HANDOFF-2026-09-14-entropy-A0.md`.

## Part II — objective B (`G4EntropyResidueProbe.lean`)

Per-declaration audit: **all-YES on the estimates** (two structural re-basings — `kIdx → kIdxOf`
and `θ`'s offset, which is already a parameter of `propA_of_progression` — and no constant
moves; only `kIdx_pos`, a non-vacuity lemma, fails off `b₀`).  But the payoff fails anyway:

```
G4Entropy.kIdxOf, exists_kIdxOf_eq      -- d_α ∣ kIdx in EVERY class (needs only d_α² ∣ P₀)
G4Entropy.sampledPosOf, periodCol₀
G4Entropy.card_filter_le_of_classes     -- ≤ |D|·((L/2dm)+1)·m, no |B| in it
Sched.not_dense_of_any_residue          -- union over ANY set of classes misses half of [0,L)
                                        --   (read at the RE-CENTRED index kIdxOf; see scope note)
```

*Scope note (attended correction, 2026-09-14 brief; formalized 2026-09-15 in
`G4ResidualConfinement.lean`): `kIdxOf = (n − b mod d_α²)/d_α` is not the physical orbit index
`(n − t_α)/d_α` once the multiplier residue varies (`d=5,t=1,c=2,q=3,n=86`: 17 vs 15), so this
closes B as posed for that sampler; it is not a universal impossibility for every way of varying
the CRT phases.  The physically indexed bound is `G4Confine.density_bound`.*

Class-side companion of `G4EntropyFamily.not_dense_of_scale` (which covered only grids, each
sampling its own `b₀`).  Together they close the brief's §6 positive branch on both axes.
**The named gap is not an estimate**: it is `d_α² ∣ P₀`, exactly what `PropA` consumes to make
the transport exact.  Exactness and density are in direct tension.  Table:
`HANDOFF-2026-09-14-entropy-B.md`.

## Part III — the new route: E0 downward (`G4EntropyE0Down.lean`) 🎯

A band-`i` window start is `2·kIdx(n,α) = 2(n − t_α)/d_α`, **increasing in `n` at fixed `α`**.
So a *position cutoff* inside band `i` selects the sub-sample `n ≲ d_α c/2` — a **truncation**
of the outer scale, not an extension.  A0 asked the wrong direction.  Downward:

| term | as `X` shrinks |
|---|---|
| `hbig`'s `(log Mx / log Y)` — the A0 obstruction | **improves** (pure monotonicity) |
| `hfar`'s `farC G X' Dm` | **improves** |
| `hbig`'s `2Y²·rowL2²/|P'|` | degrades — needs `|P'| ≳ Y²8^K` |
| `smallPrimeBound` (a),(d) | degrades — needs `Psz ≳ Λ R^{Mc}` |

Both degrading terms are fixed powers of `Y` against `X K = Y^{100}`, so `Xlo K := Y K^50` sits
comfortably inside the window.

> **`Sched.entropy_E0_down`** — for every `K = 4k₄ ≥ 33856` and every `Xlo K ≤ X' ≤ X K`,
> `(1/5)·k₄·(K²+1)^K < H₂(Z^{G4}_{K,X'})`.

```
Xlo, Xlo_pos, Xlo_le_X, Xlo_cast, two_mul_P₀_le_Xlo, two_mul_exp_le_Xlo,
  gridDm_le_Xlo, b₀_lt_of_Xlo_le
sample_term_le_down, log_Mx_div_le_down               →  hbig_holds_down
farC_le_down                                         →  hfar_holds_down
inv_card_le_down, two_pow_div_le_down,
  term_a_le_down, term_d_le_down                     →  smallPrime_term_le_down
entropy_E0_down                                      -- entropy_E0 verbatim with X'
```

Nothing else in the E0 cone noticed the substitution `X K → X'`, which independently confirms
the A0 audit from the other side.  The exponent budget is not tight:
`2Kr + 4Mc + 3 + 12·2^m + 6 ≤ 19·2^m ≤ 50·2^m`.

## Also landed

`Sched.tendsto_density_fullPos` (`G4EntropyFullDensity.lean`) — the schedule-only read visits a
**density-zero** set of positions, stated about `fullPos` itself rather than routed through
`IsSampled`.  (Wrap next-step 2.)

## Next steps, in order

0. **The hygiene commit above.**  Docs-only, required by `DIRECTION.md` `0ed0103`.
1. **Prefix control for `fullPos`, using `entropy_E0_down`.**  This is the live crux.  The plan:
   * The trivial regime: for a cutoff `c` with partial band count `≤ fT i`, `fT_kk_le`
     (`fT i · kk i ≤ 4 fL i`) already makes the partial band negligible.  This covers
     `c ≲ 8·X/(dmin·kk i)`.
   * The entropy regime: for `c ≳ Xlo/dmin`, the windows below `c` form a sub-sample at outer
     scale `X'(c)`, and `entropy_E0_down` applies.
   * They **overlap**, since `X/(dmin·kk) ≫ √X/dmin`.  Formalize the overlap as a single
     `∀ r < fL i` estimate on the partial-band count, then feed it to `read_freq_error_bound`.
   * Caveat to check first: the cutoff truncates **per atom** (`X'_α = t_α + d_α c/2`), not at a
     single `X'`.  Either (i) show the per-atom truncations are within a bounded factor, or
     (ii) restate `entropy_E0_down` for an atom-indexed truncation vector.  **Do (ii) only if
     (i) fails** — `d_α` varies over `multipliers i`, whose spread is what `dmin`/`card` control.
2. Port the mid-band refinements (`abs_midRead_freq_sub_le`, `tendsto_midRead_freq_of_depth`,
   `abs_freq_sub_freq_mid`, stated for `bandPos`) to `fullPos`, carrying the multiplicity term
   through `overhang_frac_le`.  (Wrap next-step 1.)
3. Endpoint: `IsNormal 2 fullReal` — the strictly-monotone, schedule-only read.
   (`isNormal_realOfDigits_samplePos`, lap 52, already gives a normal number read off `G₄` along
   a *non-injective* schedule-only map; `fullReal` is the injective upgrade Trevor's DIRECTION
   note asks for.)

## Hygiene notes

* The `X K → X'` ports in `G4EntropyE0Down` were done by copying the `X K` proof verbatim and
  substituting; every one of them worked with only the `card_apSample_ge_half` input swapped.
  Expect the same for further downward ports.
* `div_le_div_of_nonneg_right` wants `0 ≤ c`, not `0 < c`; `div_le_div_iff₀`'s positivity side
  goals need explicit `show` terms (metavariable order), not bare `by positivity`.
* `Real.log_le_log` needs strict positivity of the *smaller* argument — thread `0 < X'` from
  `Xlo_pos` rather than hoping `positivity` sees it.
