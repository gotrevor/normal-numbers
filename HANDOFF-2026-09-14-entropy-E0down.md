# HANDOFF — the new route: **E0 downward**, skeleton landed with three named leaves

**Branch** `wip/g4-entropy`.  `lake build` 🟢 **8999 jobs**.  New module
`src/NormalNumbers/G4EntropyE0Down.lean` — assembly complete, **three** disclosed `sorry` leaves.

## The insight

A0 asked whether E0 survives `X` getting **larger**, and the answer was no
(`ScheduleWitness.X_lt_X_step`).  But that is not the direction prefix control needs.

A band-`i` window start is `2·kIdx(n,α) = 2(n − t_α)/d_α`, **increasing in `n` at fixed `α`**.
So a *position cutoff* `c` inside band `i` selects, atom by atom, the sub-sample `n ≲ d_α c/2` —
a **truncation** of the outer scale, not an extension.  The partial-band statistic `fullPos`
needs for prefix control is therefore E0 at `X' ≤ X K`, and there the four `X`-sensitive terms
line up the *other* way:

| term | as `X` shrinks |
|---|---|
| `hbig`'s `(log Mx / log Y)` — the A0 obstruction | **improves** (`Mx ≤ 2X' ≤ 2X K`) |
| `hfar`'s `farC G X' Dm` | **improves** |
| `hbig`'s `2Y²·rowL2²/|P'|` | degrades — needs `|P'| ≳ Y²8^K` |
| `smallPrimeBound` (a),(d): `2R^{Mc}/Psz` | degrades — needs `Psz ≳ Λ R^{Mc}` |

Both degrading terms are fixed powers of `Y`, and `X K = Y^{100}`.  So there is a wide window,
and `Xlo K := Y K ^ 50 = √(X K)` sits comfortably inside it.

**Why the two regimes cover everything.**  For a cutoff below `Xlo`, the read has produced fewer
than `fT i` digits and the trivial bound `fT_kk_le` (`fT i · kk i ≤ 4 fL i`) already makes the
partial band negligible; above `Xlo`, E0-downward applies.  They overlap because
`X/(dmin·kk) ≫ √X`.

## What landed

```
Sched.Xlo, Xlo_pos, Xlo_le_X, two_mul_P₀_le_Xlo, b₀_lt_of_Xlo_le    -- proved
Sched.hbig_holds_down          -- LEAF 1 (sorry)
Sched.hfar_holds_down          -- LEAF 2 (sorry)
Sched.smallPrime_term_le_down  -- LEAF 3 (sorry)
Sched.entropy_E0_down          -- ASSEMBLED, consumes exactly those three
```

`entropy_E0_down` is `entropy_E0` verbatim with `X'` for `X K`; nothing else in the E0 cone
noticed the change, which confirms the A0 audit from the other side.

## The three leaves, and how each will go

Each is the `X'`-version of an existing `X K` lemma whose `X` dependence runs through
`card_apSample_ge_half : X/(2P₀) ≤ |apSample X P₀ b₀|`.

1. ✅ **`hfar_holds_down` — DONE.**  `farC G X' Dm = log((X'+Dm)/|P'|) + log(log(X'+Dm)+1)`.
   With `2P₀ ≤ Xlo K ≤ X'`, the first term is `≤ log(4P₀)` exactly as in `farC_le`; the second
   is `≤ log(log(2 X K)+1) ≤ m K + 8`, monotone, so `farC_le`'s bound
   `farC ≤ logP₀Nat K + m + 10` holds verbatim.  Then `four_mul_le_four_pow_N` finishes.
   Landed as `farC_le_down` (+ `two_mul_exp_le_Xlo`, `gridDm_le_Xlo`), then `hfar_holds`'s own
   proof verbatim.  Confirms the design: the `X` dependence really was only through
   `card_apSample_ge_half` and monotone `log`s.
2. ✅ **`hbig_holds_down` — DONE.**  `log Mx'/log Y ≤ 101` by `hhi` (monotone, `log_Mx_div_le` verbatim).
   The finite-sample term needs `|P'| ≥ Y^{50}/(2P₀)`; the `X K` proof wanted
   `Y²P₀/X ≤ 2^{−96·2^m}`, here `Y²P₀/Xlo ≤ 2^{−46·2^m}` — the same computation with `96 → 46`.
   Landed as `sample_term_le_down` + `log_Mx_div_le_down`, then `hbig_holds`'s proof verbatim.
   Note the A0 obstruction term `log Mx/log Y` is handled by pure monotonicity here — downward
   it costs nothing.
3. ⏳ **`smallPrime_term_le_down` — the last leaf.**  Only `term_a_le` and `term_d_le` see `Psz`; both need
   `R^{Mc}·Λ·(stuff) ≤ X'/(4P₀)`.  The `X K` proofs go through `R^{2Mc} ≤ X^{1/10}` and
   `2^{2Kr+4Mc+O(1)} ≤ X^{1/2}`; against `Xlo = X^{1/2}` those become `X^{1/5}` and `X^{1/4}`,
   still true with room (`Mc ≤ K^{6K+9}` against `2^{8K²}` in the exponent of `Y`).
   The other three terms (`main_term_le`, `term_b_le`, `term_c_le`) are `X`-free.

## Then: prefix control for `fullPos`

With `entropy_E0_down` in hand, the partial-band statistic at cutoff `c` becomes a genuine
sampled statistic at scale `X'(c)`, and the mid-band refinements of laps 84–89 port to `fullPos`
with the cutoff as the truncation parameter.  That is the remaining path to `IsNormal 2 fullReal`
— the strictly-monotone, schedule-only read.  (`isNormal_realOfDigits_samplePos`, lap 52, already
gives a normal number read off `G₄` along a *non-injective* schedule-only map; `fullReal` is the
injective upgrade Trevor's DIRECTION note asks for.)
