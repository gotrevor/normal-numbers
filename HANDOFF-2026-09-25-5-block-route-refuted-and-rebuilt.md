# HANDOFF 2026-09-25 session 5 (laps 115-117) — the block route REFUTED, then rebuilt on forced foundations

**Branch** `wip/c3-mrt`  **HEAD** `cfdf4c8`  **Working tree** clean  **`lake build`** 🟢 green (9443 jobs)
No `sorry` added.  Every new statement is `#print axioms`-clean (`propext`, `Classical.choice`,
`Quot.sound` only) — verified by a direct `lake env lean` audit, not just build `info` lines.
All new code in `src/NormalNumbers/C3MrtBlockDefect.lean` (new file, ~915 lines); `Maze.lean` +4 rows;
⚠️ markers added in `C3MrtArchFaithful.lean` (docstrings only).

## 0. Where the session started, and why it went here

The operator's scoped objective — the RESTATEMENT run, items (a)-(c) — was **already complete** at
session start (`25149e0`, `3a7e84a`), and I re-verified it end to end: four `Maze.lean` rows aliased
onto the lap-102 refutations, `TTNonPretentiousAt` / `TTNonPretentiousUnif` /
`TwoPointDyadicCorrelation` / `KPointNoExcAtWith` with their non-vacuity guards, SURVIVORS table in
`HANDOFF-2026-09-25-tt-interface-restated.md`.  So lap 115 did the review it was due — and the review
found that **the same defect class had recurred in laps 112-114, written after the lap-102 repair**.

## 1. Lap 115 — laps 112-114 are FALSE (three kernel refutations)

| theorem | kills | witness |
|---|---|---|
| `not_blockPhasePairing` (∀ `d < 1`) | lap 114's "purely geometric" endpoint | `X = 3, q = 1, t = 2, j = 1, m = 3`: the initial segment is the **singleton** `{2}`.  An injective self-map of a singleton is the identity, and `Re(u · conj u) = ‖u‖² = 1 > d`. |
| `not_wideBlockPartial` (∀ `κ > 0`) | lap 113's reciprocal-free form | same witness: norm exactly `1` against the demanded `(1−κ)·1`. |
| `not_wideBlockSaving` (∀ `κ > 0`) | lap 112's one-block target | **structural** — no segment parameter, so the witness is the truncated TOP block: `X = 16/5`, `⌈X²⌉₊ = 11`, `j = 3`, block `{11}`, weighted sum of norm exactly its mass `1/11`.  Every truncation at `X²` has such a block. |

`conjC3_of_geom_input_blocks`, `_blockPartial` and `_pairing` are therefore **vacuous**.  Blast radius
is 6 declarations, all inside `C3MrtArchFaithful.lean`; the SURVIVORS table is in
`HANDOFF-2026-09-25-4-block-route-refuted.md`.  Everything from `WideTwistSmall` upward keeps its
content, because its **additive** constant is exactly what absorbs a singleton block — which is the
one-line reason the aggregate form survives and every per-block form died.

Nothing deleted or weakened: the implications are all still theorems, and `norm_sum_le_of_pairing`
plus the Abel transfer `norm_sum_smul_le_of_partial_bound` stay sound and reusable.

## 2. The repair, and the GUARD RULE (`DIRECTION.md` ①, binding)

    conjC3_of_geom_input_band :
      (∀ A > 0, ∀ b ≥ 3, ∀ K, KPointNoExcAtWith A (cKgeom c₀ θ b) (CstKdeg m) K) →
      UniformResonantMass → CharPrimeSumLogQ D →
      BlockBandCost J Jtop ε C₁ → WideBlockSavingBand J Jtop κ₁ → ConjC3     (ε < κ₁ ≤ 1)

Both defect rounds have the same shape — a statement made *stronger* to look *cleaner*, with its
degenerate cases never checked — so the fix is process-level and is now in the CURRENT DIRECTIVE: a
lap may not hand the chain a new `Prop` without, in the same lap and in the kernel, (i) a **content
locator** (its trivial/extremal instance) and (ii) a **degenerate-case verdict** for *empty*,
*singleton*, *truncated/boundary* and *constant-function* configurations.  Instances here:
`wideBlockSavingBand_zero`, `band_block_complete`, `witness_block_above_band`, `_below_band`.
🚦 C3-T6 reset and re-aimed at the archimedean surface; 🚦 C3-T7 added (a refuting lap must install
the missing guard for the *class*).

## 3. Laps 116-117 — the band's two ends are now FORCED, not chosen

**Lap 116 (directive ②1): `BlockBandCost` DISCHARGED** for `bandTop X = log₂⌈X²⌉₊ − 1`.
* `blockMass_le_one` — every single block has mass `≤ 1` (`≤ 2^j` primes, each reciprocal `≤ 2^{-j}`).
  This is why lap 112's defect was a *boundary* defect and not a fatal one.
* `sum_blockMass_above_le` — the TOP costs `≤ 1`: above `bandTop` only `j = log₂⌈X²⌉₊` can be nonempty
  (`blockMass_eq_zero_of_lt`).
* `sum_blockMass_range_eq` / `_le` — the BOTTOM costs `log(J·log 2) + mertensBound`: the blocks below
  `J` regroup fiberwise into the primes `< 2^J`, where `small_prime_mass_le` (Mertens) applies.  **The
  `log` is the whole point** — a threshold growing like any power of `log X` is affordable, the
  threshold itself would not be.
* `blockBandCost_of_log_bound` (the criterion), `blockBandCost_const` (constant `J₀`: `ε = 0`).

**Lap 117 (directive ②2): a CONSTANT bottom threshold is REFUTED.**
* `blockSum_norm_eq_mass_of_pair` — the alignment identity.  On a two-prime block `{p,p'}` the twist
  `t = 2π/log(p'/p)` makes the phases COINCIDE, so the block sum is `exp(−it log p)·(1/p + 1/p')` and
  its norm is **exactly** the mass.
* `log_diff_bounds` (`1 − a/b ≤ log b − log a ≤ b/a − 1`, both directions of `log x ≤ x − 1`) is all
  the transcendence control needed; `pair_twist_admissible` puts the aligned twist in the wide range.
* `not_wideBlockSavingBand_const_le_three` — `J₀ ≤ 3` refuted via `{11,13}` at `X = 7`
  (`t = 2π/log(13/11) ∈ [11π,13π]`, `13π ≤ 49 = X²`, `bandTop 7 = 4`).
  `not_wideBlockSavingBand_const_le_one` keeps the readable `{2,3}` case at `X = 5`.
* `Maze.lean`: `hall_const_band_threshold_false`.

**②1 and ②2 are exactly complementary: a growing threshold is CHEAP, and it is NECESSARY.**

## 4. Ledger state (real `#print axioms`, 9443 jobs — see STATUS.md)

`conjC3_via_weylLambert` : trust triple + `sorryAx` (the ratified open crux, disclosed).
Clean (trust triple): `conjC3_of_geom_input_band` ← **the live reduction**, `_at`, `_lower`, all the
refutations, all the band machinery.  **VACUOUS** and marked ⚠️ in place: `conjC3_of_geom_input`
(lap 90, killed lap 102), `_blocks`, `_blockPartial`, `_pairing` (killed lap 115).

Carried hypotheses: `KPointNoExcAtWith …` 🔴 (TT Thm 3.1(ii) with the exceptional set deleted —
strictly stronger than published, disclosed); `UniformResonantMass` 🟡, `CharPrimeSumLogQ D` 🟡,
`WideBlockSavingBand J bandTop κ` 🟡.  `BlockBandCost` is **no longer carried** (lap 116).
Vacuity is a ledger hazard in the OPPOSITE direction from a missing axiom: it makes the headline look
cheaper than it is.  That is why the GUARD RULE exists.

## 5. Next steps (CURRENT DIRECTIVE order — read `DIRECTION.md` first, it outranks this file)

1. **②3 `CharPrimeSumLogQ D` at `t = 0`** from `L(1,χ) ≫ q^{-1/2}`.  Mathlib has only the qualitative
   `DirichletCharacter.LFunction_apply_one_ne_zero`, with no uniformity in `q`, so this needs the
   elementary `f = 1 ∗ χ ≥ 0` argument (`∑_{n≤N} f(n)/n ≥ ...` against the Euler factorisation), or it
   stays a cited classical bound with the citation in the ledger.  Recall lap 111: in TT's range
   `log q ≤ (1/125)·log log X`, so a `log`-sized bound suffices — the conductor is NOT the obstruction.
2. **②4 `UniformResonantMass`** — the route's pre-existing analytic input, untouched by every repair.
3. `RootOrderCase` / `OneNonPretentious` (lap 110) — the alternative `z`-free route to
   `FaithfulArchLower`.  Cheap; keep both.
4. Optional, and only with a guard: a *growing* threshold instance, e.g. `J X = ⌈log log X⌉`, feeding
   `blockBandCost_of_log_bound`.  Needs `log log log X ≤ ε·log log X + C_ε` — `log u ≤ 2√u` twice.

## 6. Do NOT re-attempt (kernel- or source-refuted)

* `WideBlockSaving`, `WideBlockPartial`, `BlockPhasePairing`, and any per-block constant-fraction
  saving without a band.  Do not delete them or their implications.
* A CONSTANT bottom threshold for `WideBlockSavingBand` (lap 117).
* Any `log log(q(2+|t|))` upper bound for the wide range — scale-degenerate (lap 112, stands).
* Discharging the non-principal narrow range from mathlib's L-function non-vanishing (qualitative, no
  uniformity); restricting to `p ≡ 1 (mod q)` (gives `κ/φ(q)`, dies); root-of-unity averaging
  `∑_{j<b} z^j = 0` (gives the average, not the saving at `j = 1`).
* `K ≥ 3` from `K = 2`; removing TT's exceptional set (`exceptional_set_can_pin_a_scale`); new
  fixed-`K` `Tendsto` statements (lap 87 F2); the `QuantDepthElliottGen` budget layer (lap 87 F1).
