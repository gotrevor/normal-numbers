# HANDOFF — entropy expedition, lap 8 (2026-09-14, Opus review+grind)

**Branch** `wip/g4-entropy`.  `lake build` green, 8951 jobs.  Three new modules, all
**sorry-free**, no new axioms, no pre-expedition file edited.

Spec: `BRIEF-entropy-expedition-2026-09-14.md`; the binding orders are the **entropy CURRENT
DIRECTIVE** at the top of `DIRECTION.md` (set by this lap's review pass).  Previous baton:
`HANDOFF-2026-09-14-entropy-lap7.md`.

## Headline: brief §6's primary transfer target `T_E` is **REFUTED**

```
NormalNumbers.G4.Sched.T_E : Prop :=
  ∀ x : ℝ, 0 ≤ x → x < 1 → E0 x → IsNormal 2 x

NormalNumbers.G4.Sched.not_T_E : ¬ T_E          -- [propext, Classical.choice, Quot.sound]
```

with, on the way,

```
NormalNumbers.G4.Sched.E0_primeLambertFour : E0 (primeLambertAtBase 4)
```

— brief §4's **qualitative E0**, now a genuine limit (`H₂(Z^{G₄}_K)/(m_K H_K) → 1`), squeezed
between `1 − 200/√K` (from lap 7's `entropy_E1`) and `1` (the alphabet bound).  Laps 6–7 had
only the inequality family.

### The witness

`maskedReal G₄ = realOfDigits 2 (fun j => if IsSampled j then digitOf 2 (fract G₄) j else 0)`:
the digits of `G₄` at every position some admissible scale actually reads, and `0` everywhere
else.  It is a single fixed binary expansion (not a different string at each `K`), it lies in
`[0,1)`, and it satisfies the **exact** premise — indeed its joint quantized sample law is
*literally equal* to `G₄`'s at every scale (`jointLawAt_maskedReal`), so it satisfies
`entropy_E0` and `entropy_E1` verbatim, not merely some weakened form.  And it is not normal:
at most a quarter of its digits are `1`.

## The two mathematical points

**1. The sample is DIGIT-LOCAL** (`G4EntropyLocality.lean`).  `ZSample_eq_blockVal` makes
`Z^x_{K,α}(n)` the `m_K`-bit binary window of `x` at position `2·kIdx G n α`.  A window reads
only its own digits, so `Z`, `jointLaw` and `H₂` are functions of the digits of `x` on

  `sampledPos G X m = {2·kIdx G n α + h : n ∈ P, α : Atom, h < m}`

and nothing else (`blockVal_congr → ZSample_congr → ZVec_congr → empirical_congr →
jointLaw_congr → H₂_jointLaw_congr`).  Any transfer theorem from a digit-local hypothesis to
normality therefore *forces* the sampled positions to carry density ≥ 1/2.

**2. They carry density ≤ 1/4** (`G4EntropyPositions.lean`, `card_isSampled_le`).  The input was
already in `kIdx_spec`: **`d_α ∣ kIdx G n α`**.  Two additions turn it into sparsity.

* `kIdx_pos` — the index never vanishes.  `kIdx = 0` forces `n = t_α`; with
  `t_α < d_α² ≤ Mprod ≤ P₀` and `b₀ < P₀` that forces `b₀ = t_α`, and then `b₀ ≡ t_β (mod d_β²)`
  with `t_α, t_β < d_β²` forces `t_α = t_β` for *every* `β` — i.e. a constant offset, which the
  implemented grid does not have (`gridV 0 = 0`, `gridV e₀ = B > 0`).
* So `kIdx = d_α·c` with `c ≥ 1`, every sampled position is `2 d_α c + h`, and
  `|S_K ∩ [0,L)| ≤ Σ_α m·⌊L/(2 d_α)⌋ ≤ H_K·m_K·⌊L/(2 d_min)⌋`, `d_min = 1 + Q·D₀`.

The union over *all* admissible scales needed no asymptotics: every scale-`i` position is
`≥ 2 d_min(i) > i`, so at each `L` only the scales `i < L` contribute, and `key_size`
(`2^{i+3}·H_K·m_K ≤ 2 d_min(i)`) makes scale `i`'s share `≤ L/2^{i+3}`; `sum_div_two_pow_le`
closes the geometric sum at `L/4`.  `key_size` has enormous slack: `Q ≥ U ≥ B^K` and `D₀ = K·U`
give `Q·D₀ ≥ K·(B²)^K`, against a left side `≤ (2(K²+1))^K·K`, and `2(K²+1) ≤ B²` because
`B = K²(K+N)+1 ≥ K³`.

## What this means (claim discipline)

`entropy_E0`/`entropy_E1` stand exactly as before: unconditional, axiom-clean statements about
the joint quantized sample of `G₄`.  What lap 8 settles is that **they cannot be upgraded to
normality by any generic argument**, because the sample only ever looks at a set of digit
positions of density ≤ 1/4 — and the same witness kills `T_S` and `T_mix` too, since it has the
same laws (state those two next; the proof is the identical `jointLawAt_maskedReal`).

Nothing here says `G₄` is or is not normal.  Nothing here weakens the disjunctivity theorems.

## Declaration map (lap 8)

`src/NormalNumbers/G4EntropyLocality.lean` — `blockVal_congr`, `sampledPos`, `mem_sampledPos`,
`mem_sampledPos_of`, `ZSample_congr`, `ZVec_congr`, `FinLaw.ext'`, `empirical_congr`,
`jointLaw_congr`, `H₂_jointLaw_congr`.

`src/NormalNumbers/G4EntropyPositions.lean` — `t_lt_d'`, `t_lt_sq_d`, `kIdx_pos`, `kIdx_ge_d`,
`exists_kIdx_eq`, `card_sampledPos_lt_le`, `card_sampledPos_lt_le'`, `gridOf_t_nonconstant`,
`gridOf_dmin_le`, `card_sampledPos_gridOf_le`.

`src/NormalNumbers/G4EntropyTransfer.lean` — `kk`, `KK`, `gridAt`, `sampledPosAt`, `IsSampled`,
`jointLawAt`, `maxH`, `E0`, `T_E`, `ratio_le_one`, `one_sub_le_ratio`, `E0_primeLambertFour`,
`dmin`, `pow_le_gridSum`, `pow_le_gridUmax`, `one_le_gridD₀`, `two_mul_succ_le_gridB_sq`,
`key_size`, `mul_div_mul_le`, `card_sampledPosAt_lt_le`, `le_of_mem_sampledPosAt`,
`sum_div_two_pow_le`, `card_isSampled_le`, `maskedDigits`, `exists_not_isSampled`,
`properDigits_maskedDigits`, `maskedReal`, `digitOf_maskedReal`, `jointLawAt_maskedReal`,
`E0_maskedReal`, `countOcc_one_le`, `not_isNormal_maskedReal`, `not_T_E`.

## Next, hardest first

1. **`T_S` and `T_mix`** — state them over the same family and refute both with the same
   witness (`jointLawAt_maskedReal` gives identical laws, so every sampled statistic agrees).
   Cheap, and it completes brief §6's column.
2. **The frontier is now brief §6's POSITIVE branch.**  The refutation says exactly what is
   missing: an arithmetic input that reads a *positive-density* set of digit positions.  The
   brief's item 1 is the right first test — average over a proved family of admissible
   samplers (translated grids / varied frozen residues) and compute the resulting position
   weights `w_{K,ℓ}`.  The obstruction to beat is quantitative and now explicit:
   `d_α ∣ kIdx` puts scale-`K` positions on multiples of `2 d_α` with `d_α ≥ 1 + Q_K D₀_K`, so
   a single grid can never exceed density `H_K m_K/(2 d_min)`.  Any repair must vary `t_α`
   (equivalently `b₀`) across a family large enough to cover a positive fraction of residues
   mod `2 d_α` — name that property and prove the implication it supplies.
3. Brief §5's (S) is still open and still a leaf; it is worth doing only as a *statement* of
   what entropy controls, not as a step toward normality.

## Lean gotchas from this lap

- `Finset.range_succ` is now **`Finset.range_add_one`**; `Finset.card_insert_of_not_mem` is
  **`card_insert_of_notMem`**; `Nat.pos_pow_of_pos` is gone (use `pow_pos`).
- A structure with proof fields (`FinLaw`) needs its own `ext'` lemma: `cases`, `cases`,
  `simp only at h`, `subst h`, `rfl` — `congrArg₂`/`congr 1` does not close the proof fields.
- `omega` abstracts nonlinear atoms but will not relate `G.d α * c` to `kIdx`: replace the
  offending step by an explicit `calc … := by ring` chain.
- `Filter.Tendsto.inv_tendsto_atTop` produces `f⁻¹` (`Pi.inv`), not `fun i => (f i)⁻¹`;
  `simpa` fails on the difference but `exact` succeeds (they are defeq).
- `tendsto_of_tendsto_of_tendsto_of_le_of_le` takes *pointwise* `≤`, so a `fun i => …` works —
  but remember to apply the lemma to all its explicit arguments.
