# HANDOFF — review lap 119: the scale gap is an ARTIFACT; the two-dimensional ladder

**Branch** `wip/g4-entropy`.  **HEAD** `eefb7c8` (lap-end; `e0a56ef` was the review commit).
Working tree **clean**.  `lake build` 🟢 **9005 jobs**.  One new module,
`src/NormalNumbers/G4EntropyMTower.lean`, with **one** named `sorry` leaf
(`Sched.entropy_E1_march`) on the active decomposition; the carried leaf
`Sched.card_bandTtr_ge` is untouched.  No `axiom` introduced.  Every new sorry-free endpoint
prints `[propext, Classical.choice, Quot.sound]`.

## What this lap did

A fresh-mind review.  The 19:06 operator override's stop condition is **discharged** — A0 = NO
(`ScheduleWitness.X_lt_X_step`), B = NO (`not_dense_of_any_residue`), A's obstruction named
(`ScheduleWitness.X_lt_Xlo_step`) — so the lap owed a successor objective.  It found one by
auditing the source rather than accepting the previous handoff's verdict.

### The finding

The previous handoff concluded: *"`IsNormal 2 fullReal` is blocked here; do not spend laps
re-deriving it."*  The blocker is the **head of each band** — position cutoffs below the
certificate floor `Xlo (KK i)` — and `G4EntropyScaleGap` proves no rung of the ladder covers it,
because consecutive rungs are separated by a tower (`m₁ (K+4) ≥ 4096·m₁ K`).

**That separation is an artifact of pinning `m` to `K`.**  In the implemented schedule
`m K = m₁ K + m₂ K`, `m₁ K = 1000·8^K·K^{2K+1}`, `m₂ K = 8K²`, `R = 2^{2^{m₁}}`, `Y = 2^{2^m}`,
`X = Y^{100}`, `Xlo = Y^{50}`.  But `m₁` is the small-prime cutoff exponent, and the audit of
every `m`/`m₁`-sensitive hypothesis in `entropy_E0`'s cone shows it is constrained **only from
below**, bar two ceilings with astronomical slack:

| declaration | how `m₁`/`m` enters | under `m₁ → m₁ + j` |
|---|---|---|
| `Sched.dyadic_factor_le` | only through `m − m₁ = m₂` | **unchanged** |
| `Sched.sample_term_le` | `K ≤ 2^m`, `Y²·P₀·4 ≤ X` | improves |
| `Sched.log_Mx_div_le` | `Mx ≤ 2X = 2Y^{100}` | **constant `≤ 101`** |
| `m₁_ge_cube`, `twentyone_sq_le_m`, `logP₀Nat_le_two_pow_m`, `two_mul_P₀_le_X`, `gridDm_le_X`, `J_mul_gridDm_le_X` | lower bounds on `m` | improve |
| budget main term (`hm₁`) | `(1/8)^K·m₁ = 1000·K·r`, used as a lower bound | improves |
| **`Sched.Mc_le_two_pow_m₂`** | `Mc = 10⁵·T·m₁ ≤ 2^{8K²}` | ⚠️ ceiling `j ≲ 2^{8K²}/(10⁵TK)` |
| **`Sched.four_mul_le_four_pow_N`** | `4K(logP₀Nat + m + 2J + 13) ≤ 2^{200K²}` | ⚠️ ceiling `j ≲ 2^{200K²}/(4K)` |

And raising `m₁` by one at fixed `K` (with `m₂` fixed) **squares `Y`**, so

    Xlom K (j+1) = Y_{j+1}^{50} = Y_j^{100} = Xm K j

— the certified outer-scale windows `[Y^{50}, Y^{100}]` **tile contiguously, with no gap**.

**Why A0's NO does not apply.**  A0 raised `X` with `Y, R, Mc` FIXED, so `log Mx / log Y` grew
and broke `hbig`'s ceiling `Y^{2^{3K/4}}`.  The march raises `X, Y, R, Mc` together, keeping
`X = Y^{100}` and that ratio pinned at `≤ 101` — three orders of magnitude inside the ceiling.

## `G4EntropyMTower.lean` — what is proved

```
mm₁ K j = m₁ K + j,  mm K j = m K + j,  Rm, Ym, Xm, Xlom, Mcm     the marched scales
mm_zero / Xm_zero / Xlom_zero / Rm_zero / Ym_zero / Mcm_zero      j = 0 is the old schedule
Xlom_succ             Xlom K (j+1) = Xm K j                        THE TILING IDENTITY
m_lt_step             m K + 1 ≤ m (K+4)
jstar K               = m (K+4) − m K − 1
Xm_jstar              Xm K (jstar K) = Xlo (K+4)                   reaches the next rung EXACTLY
m_step_le_two_pow     m (K+4) ≤ 2^{3K²+28K+64}
Mcm_le_two_pow_m₂     Mcm K j ≤ 2^{m₂ K}  for j ≤ jstar K          binding: 6K²+31K+81 ≤ 8K²
four_mul_le_four_pow_N_m                  the hfar ℕ inequality on the whole march
exists_tile           ∀ X' ∈ [Xlo K, Xlo (K+4)], ∃ j ≤ jstar K, Xlom K j ≤ X' ≤ Xm K j
entropy_E1_march      ⚠️ SORRY — the E1 chain at the marched parameters (K, j)
entropy_E1_march_zero the j = 0 instance IS `entropy_E1_down`      ← definitions line up
entropy_E1_tile       E1 at EVERY outer scale in [Xlo K, Xlo (K+4)]  ← THE GAP CLOSED
```

`entropy_E1_march_zero` is deliberate: it discharges the `j = 0` case from `entropy_E1_down`,
which is the compiler's confirmation that `Xlom K 0 = Xlo K` and `Xm K 0 = X K` really do
recover the implemented schedule, so the leaf is the genuine generalization and not a
mis-stated cousin.

## Next lap — in order

1. **`Sched.entropy_E1_march`** (the leaf).  Port the cone to `(K, j)` in the same
   verbatim-copy-plus-substitution shape `G4EntropyE0Down`/`G4EntropyE1Down` already ran for
   `X'`: `hbig_holds_m` (inputs unchanged/monotone), `hfar_holds_m` (`farC_le` with
   `m ↦ mm K j`, then `four_mul_le_four_pow_N_m`), the five `smallPrimeBound` terms
   (`Mcm_le_two_pow_m₂` for `Mc_le_two_pow_m₂`; `R_pow_two_Mc_le` becomes
   `Rm^{2·Mcm} ≤ 2^{10·2^{mm}}` by the same two lines), `hm₁` as an inequality.
2. **`Sched.card_bandTtr_ge`** — the carried leaf, unchanged plan (previous handoff §4).
3. **`density_antitone`** — the one new estimate the level switch needs.
4. **`fullPos'` + `IsNormalSequence 2`** — the objective.

## Hygiene notes (new this lap)

* `congr 1` on a goal `2 ^ (a * 2 ^ e₁) = (2 ^ (2 ^ e₂)) ^ b` **times out at `whnf`** when `e₂`
  is a schedule `def`.  Prove the exponent identity as a separate `have` and close with
  `rw [← pow_mul, hexp]` instead.
* `rw [← h]` where `h : mm K (jstar K) + 1 = m (K+4)` loops/blows up, because `jstar K` is
  *defined* in terms of `m (K+4)`.  Use `conv_lhs => rw [← h]`.
* `unfold m m₂` then `omega` also times out (it drags `m₁`'s closed form in).  Use
  `show m₁ K + m₂ K + 1 ≤ m₁ (K+4) + m₂ (K+4)` — the `def`s are reducible enough for `show`,
  and `omega` then sees only atoms.
* Don't put a proof of `b₀ < X'` inside the *statement* of a theorem about `jointLaw`; take it
  as an explicit hypothesis `hb`.  Proof irrelevance makes it interchangeable with
  `b₀_lt_of_Xlo_le …` at the use site, and the embedded `show` costs an `isDefEq` timeout.

---

## Continuation (same lap): `hbig` and `hfar` at `(K, j)` are DONE

`src/NormalNumbers/G4EntropyMTowerBig.lean` — build 🟢 **9005 jobs**, sorry-free, every endpoint
`[propext, Classical.choice, Quot.sound]`.

```
X_le_Xm, two_mul_P₀_le_Xm, gridDm_le_Xm, J_mul_gridDm_le_Xm, sample_nonempty_m
K_le_two_pow_mm, P₀_le_two_pow_m, Xm_cast, Ym_cast
natLog_Ym, natLog_Rm
dyadic_factor_le_m     the ORIGINAL proof verbatim — `mm − mm₁ = m₂ K` by definition
sample_term_le_m       4·2^{mm} + 2 + K ≤ 100·2^{mm}
log_Mx_div_le_m        ≤ 101, a CONSTANT — the A0 ceiling is never approached
hbig_holds_m           ✅
farC_le_m              ≤ logP₀Nat K + mm K j + 10
hfar_holds_m           ✅  (closed by `four_mul_le_four_pow_N_m`)
```

The audit's prediction held exactly: the dyadic Chebyshev factor is the *only* place the march
could have hurt `hbig`, and it does not move at all.

**Remaining for `entropy_E1_march`**: the small-prime side — a marched `R_pow_two_Mc_le`
(`Rm^{2·Mcm} ≤ 2^{10·2^{mm}}`, from `Mcm_le_two_pow_m₂` by the same two lines), `inv_card_le_m`,
`term_a_le_m`/`term_d_le_m`, `main_term_le_m` (the `hm₁` equality becomes `≥`), then
`smallPrime_term_le_m` and the `entropy_gt_of_budget` assembly (template:
`G4EntropyE0Down.entropy_E0_down`, lines 595–739).


---

## Lap end — state and the next lap's first move

**Branch** `wip/g4-entropy` · **HEAD** `eefb7c8` · tree clean · `lake build` 🟢 **9005 jobs**.
Two commits this lap:

* `e0a56ef` — the review: the scale gap is an artifact; `G4EntropyMTower.lean`.
* `eefb7c8` — `hbig_holds_m` and `hfar_holds_m`; `G4EntropyMTowerBig.lean`.

**Open `sorry`s in `src/` (expedition):** two.
* `Sched.entropy_E1_march` (`G4EntropyMTower.lean:296`) — the active decomposition's leaf.
* `Sched.card_bandTtr_ge` (`G4EntropyBandTrunc.lean:100`) — the carried leaf from the previous
  session, plan unchanged.

(`MahlerDriftOne.exists_prime_nonresidue` and `PrimeLambertOscillation.phaseOscillation` are
other campaigns' and are on the forbidden-drift list.)

### Next lap — first move, concretely

Finish `entropy_E1_march`'s **third** input, the small-prime side, in a new
`G4EntropyMTowerBudget.lean`.  Template: `G4ScheduleBudget.lean` lines 103–420 and
`G4EntropyE0Down.lean` lines 380–595.  In order:

1. `R_pow_two_Mc_le_m : (Rm K j : ℝ)^{2·Mcm K j} ≤ 2^{10·2^{mm K j}}` — copy
   `R_pow_two_Mc_le`, feeding `Mcm_le_two_pow_m₂` (already proved) in place of
   `Mc_le_two_pow_m₂`, and `2^{mm} = 2^{mm₁}·2^{m₂}` in place of `2^m = 2^{m₁}·2^{m₂}`.
2. `inv_card_le_m : 1/|apSample (Xm K j) P₀ b₀| ≤ 2P₀/Xm K j` — copy `inv_card_le`.
3. `main_term_le_m` — the only place `m₁`'s closed form is used as an *equality* (`hm₁`,
   `G4ScheduleBudget.lean:241`): replace `(1/8)^K · m₁ K = 1000·(K·r)` by
   `1000·(K·r) ≤ (1/8)^K · mm₁ K j` (`m₁ K ≤ mm₁ K j` by definition), which only improves the
   bound.
4. `term_a_le_m`, `term_b_le_m`, `term_c_le_m`, `term_d_le_m`, then `smallPrime_term_le_m`
   via `budget_terms_le`.  The exponent budget to re-check is
   `2Kr + 4·Mcm + 3 + 12·2^{mm} + 6 ≤ 50·2^{mm}` — same shape as E0-down's, with `Mc ↦ Mcm`.
5. The assembly `entropy_E0_march` / `entropy_E1_march`: copy `entropy_E0_down`
   (`G4EntropyE0Down.lean:595–739`) substituting `R K ↦ Rm K j`, `Y K ↦ Ym K j`,
   `Mc K ↦ Mcm K j`, `X' ↦ X'` with `Xlom K j ≤ X' ≤ Xm K j`, and the three `*_m` inputs.
   Then the E1 step exactly as `G4EntropyE1Down.lean` does it from `entropy_E0_down`.

When that lands, `entropy_E1_tile` becomes axiom-clean and the scale gap is closed
unconditionally; the next targets are then `card_bandTtr_ge`, `density_antitone`, and `fullPos'`
(see `PENDING_WORK.md`'s ACTIVE section, items 2–4).

### Do not re-derive

`DIRECTION.md`'s CURRENT DIRECTIVE (review lap 119) forbids re-litigating the scale gap / the
head obstruction, and forbids adopting "every cutoff beyond an `X^{−1/2}` fraction of its band
is good" as the headline.  `certified_granule_exceeds_previous_scale`,
`ScheduleWitness.X_lt_X_step`, `X_lt_Xlo_step` and `Xhi_succ_lt_Xlo_step` remain true but are
statements about the **one-dimensional** ladder only.
