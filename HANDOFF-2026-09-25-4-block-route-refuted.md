# HANDOFF 2026-09-25 session 4 (lap 115, REVIEW) — laps 112-114's block route is FALSE

**Branch** `wip/c3-mrt`  **Working tree** clean  **`lake build`** 🟢 green (9443 jobs)
No `sorry` added; every new statement is `#print axioms`-clean (`propext`, `Classical.choice`,
`Quot.sound` only).  New file `src/NormalNumbers/C3MrtBlockDefect.lean`; `Maze.lean` +3 rows;
`DIRECTION.md`, `STATUS.md`, `PENDING_WORK.md` refreshed.

## 0. The operator's scoped objective was already met — and then the same bug recurred

Items (a)-(c) of the RESTATEMENT run were complete at session start (`25149e0`, `3a7e84a`;
verified this lap: four `Maze.lean` rows aliased onto the refutations, `TTNonPretentiousAt` /
`TTNonPretentiousUnif` / `TwoPointDyadicCorrelation` / `KPointNoExcAtWith` with guards, SURVIVORS
table in `HANDOFF-2026-09-25-tt-interface-restated.md`).  So this lap did the review it was due,
and the review found something worth the whole lap:

**Laps 112, 113 and 114 — written AFTER the lap-102 repair — reduced the archimedean debt onto
statements that are FALSE.**  Each lap made the target "cleaner" by making it stronger, and none
checked its degenerate cases.  Three `conjC3_of_geom_input_*` variants are therefore vacuous.

## 1. The refutations (all trust-triple clean, all in `C3MrtBlockDefect.lean`)

| theorem | kills | witness |
|---|---|---|
| `not_blockPhasePairing` (∀ `d < 1`) | lap 114's "purely geometric" endpoint | `X = 3, q = 1, t = 2, j = 1, m = 3`: the initial segment is the **singleton** `{2}`.  An injective self-map of a singleton is the identity, and `Re(u · conj u) = ‖u‖² = 1 > d`. |
| `not_wideBlockPartial` (∀ `κ > 0`) | lap 113's reciprocal-free form | same witness: the segment sum has norm exactly `1` against the demanded `(1−κ)·1`. |
| `not_wideBlockSaving` (∀ `κ > 0`) | lap 112's one-block target | **structural** — no segment parameter to abuse, so the witness is the truncated TOP block: `X = 16/5`, `⌈X²⌉₊ = 11`, `j = 3`, block `{11}`, weighted sum of norm exactly its own mass `1/11`.  Every truncation at `X²` has such a block. |

Supporting: `dirichletChar_one_apply` / `_ne_zero` (mod 1 every character is `1`),
`wide_witness_admissible` (`q = 1`, `t = 2` are admissible in the wide range for `3 ≤ X ≤ 7`),
`seg_one_eq_singleton`, `block_three_eq_singleton`, `goodSeg_one_eq_singleton`.

## 2. SURVIVORS table — consumers of the three refuted `Prop`s

Blast radius is small and entirely inside `C3MrtArchFaithful.lean`; nothing upstream touched them.

| declaration | verdict |
|---|---|
| `wideTwistSmall_of_blockSaving` | **theorem, vacuous use** — the implication is true, its hypothesis is false.  Kept. |
| `conjC3_of_geom_input_blocks` | **VACUOUS** (`not_wideBlockSaving`).  Marked ⚠️ in place. |
| `wideBlockSaving_of_partial` (the Abel transfer) | **theorem, vacuous use**.  `norm_sum_smul_le_of_partial_bound` is sound and reusable. |
| `conjC3_of_geom_input_blockPartial` | **VACUOUS** (`not_wideBlockPartial`).  Marked ⚠️. |
| `wideBlockPartial_of_phasePairing` | **theorem, vacuous use**.  `norm_sum_le_of_pairing` is sound and reusable. |
| `conjC3_of_geom_input_pairing` | **VACUOUS** (`not_blockPhasePairing`).  Marked ⚠️. |
| `WideTwistSmall`, `TwistedPrimeSumSmall`, `NarrowTwistSmall`, `CharPrimeSumLogQ`, `UniformResonantMass`, `faithfulArchLower_of_twist_small`, `faithfulArchLower_of_urm_of_logQ`, `archSupply_of_faithfulArchLower`, `conjC3_of_geom_input_at`, `conjC3_of_geom_input_lower` | **CONTENT INTACT** — none of them mentions a per-block statement.  The additive constant in `WideTwistSmall` is exactly what absorbs the singleton blocks, which is why the aggregate form survives and the per-block forms do not. |
| laps 108-111 (`NonPrincipalLocalBound`, `TwistedPrimeSumSmall`, `OneNonPretentious`, `RootOrderCase`, `nonPrincipalTwistSmall_of_logQBound`) | **CONTENT INTACT.** |

## 3. The repair

    conjC3_of_geom_input_band :
      (∀ A > 0, ∀ b ≥ 3, ∀ K, KPointNoExcAtWith A (cKgeom c₀ θ b) (CstKdeg m) K) →
      UniformResonantMass → CharPrimeSumLogQ D →
      BlockBandCost J Jtop ε C₁ → WideBlockSavingBand J Jtop κ₁ → ConjC3     (ε < κ₁ ≤ 1)

* `WideBlockSavingBand J Jtop κ` — the saving asked only of blocks in a **band** `J X ≤ j ≤ Jtop X`.
  The top end excludes the truncated block (the lap-112 witness class); the bottom end excludes the
  small ones.
* `BlockBandCost J Jtop ε C` — the mass discarded outside the band, `≤ ε·log log X + C`.  A
  **purely arithmetic** obligation: no characters, no twists, no cancellation.
* `wideTwistSmall_of_blockSavingBand` — band saving `κ` + band cost `ε` ⟹ `WideTwistSmall (κ − ε)`.
  Outside the band the trivial bound `norm_blockSum_le_mass`; inside it the hypothesis.

**Why the bottom threshold cannot be a constant** (and so why it is a function of `X`): a block at a
*fixed* index holds finitely many primes, whose `log p` are `ℚ`-independent, so a large twist drives
all their phases into one arc (Kronecker) — and the wide range permits `|t| ≤ X²`.  For a TWO-prime
block this is exact and needs no equidistribution: at `t = 2π/log(p'/p)` the two twists coincide.

## 4. Guards — the new binding GUARD RULE (`DIRECTION.md` ①)

Both defect rounds have the same shape, so the fix is process-level and now binding: a lap may not
hand the chain a new `Prop` without, in the same lap and in the kernel, (i) a **content locator**
(the trivial/extremal instance) and (ii) a **degenerate-case verdict** for *empty*, *singleton*,
*truncated/boundary* and *constant-function* configurations — either survival or exclusion by the
statement's own hypotheses.  Instances landed here:

* `wideBlockSavingBand_zero` — at `κ = 0` the statement IS the trivial bound, so all content is `κ > 0`.
* `band_block_complete` — the intended `Jtop X = log₂⌈X²⌉₊ − 1` yields only **complete** blocks.
* `witness_block_above_band`, `witness_block_below_band` — the §1 witnesses provably do not apply.

Also registered: 🚦 C3-T6 **reset and re-aimed** at the archimedean surface (the `K`-point surface is
final in shape); 🚦 C3-T7 **new** — a lap that refutes an earlier reduction must install the missing
guard for the *class*, not just the instance.

## 5. Next attack (directive order — do these, in this order)

1. **`blockBandCost_holds`.**  Top: blocks above `Jtop X = log₂⌈X²⌉₊ − 1` hold only primes
   `p > n/2` (`n = ⌈X²⌉₊+1`), so their total mass is `≤ 2` (count `≤ n`, each term `< 2/n`).
   Bottom: `small_prime_mass_le` on the primes `< 2^{J X}` gives `log(J X·log 2) + mertensBound`.
   With this, the band route rests on ONE analytic input plus a discharged cost.
2. **`¬ WideBlockSavingBand (fun _ => J₀) Jtop κ` for `J₀ ≤ 3`** — exact two-prime phase alignment.
   Blocks `j = 1,2,3` are `{2,3}`, `{5,7}`, `{11,13}`; at `t = 2π/log(p'/p)`,
   `exp(-it log p') = exp(-it log p)` (`Complex.exp_two_pi_mul_I`), so the block sum has norm
   exactly its mass.  Need `X² ≥ t` and `X ≥ 3` — both free.  This is the kernel proof that the
   threshold must GROW, and it is the guard the class needs (C3-T7).
3. **`CharPrimeSumLogQ D` at `t = 0`** from `L(1,χ) ≫ q^{-1/2}` — mathlib has only the qualitative
   `DirichletCharacter.LFunction_apply_one_ne_zero`, so this needs the elementary `f = 1 ∗ χ ≥ 0`
   argument, or it stays a cited classical bound.
4. **`UniformResonantMass`** — the route's pre-existing analytic input, untouched by all the repairs.
5. `RootOrderCase` / `OneNonPretentious` (lap 110) — the alternative `z`-free route; cheap, keep both.

## 6. Do NOT re-attempt

* `WideBlockSaving`, `WideBlockPartial`, `BlockPhasePairing` — refuted in the kernel.  Do not delete
  them or their implications (`norm_sum_le_of_pairing` and the Abel transfer are reusable).
* Any per-block constant-fraction saving *without* a band: the truncated top block kills it.
* Any `log log(q(2+|t|))` upper bound for the wide range — scale-degenerate (lap 112, stands).
* Discharging the non-principal narrow range from mathlib's L-function non-vanishing (qualitative).
* Restricting to `p ≡ 1 (mod q)` for the non-principal saving — gives `κ/φ(q)`, dies.
* The root-of-unity averaging `∑_{j<b} z^j = 0` — gives the average, not the saving at `j = 1`.
* `K ≥ 3` from `K = 2`; removing TT's exceptional set; new fixed-`K` `Tendsto` statements; the
  `QuantDepthElliottGen` budget layer.  All source- or kernel-refuted.
