# HANDOFF — lap 123: **MID-BAND PREFIX CONTROL is proved**; one named leaf left

**Branch** `wip/g4-entropy`.  **HEAD** `f5c2896`.  Working tree **clean**.
`lake build` 🟢 **9019 jobs**.  `src/` carries **three** `sorry`s: the two pre-expedition off-path
ones (`PrimeLambertOscillation.phaseOscillation`, `MahlerDriftOne.exists_drift_one_background`)
and **one active-crux leaf**, `Sched.head_frac_tiny`.  Every new endpoint prints
`[propext, Classical.choice, Quot.sound]`.

## What this lap did — `DIRECTION.md` review-lap-122 items 1–3

Item 1 was already done.  **Item 2, THE CRUX, is closed**; item 3 is structurally done with its
arithmetic core isolated as the one leaf.

| commit | content |
|---|---|
| `93f19e7` | `G4EntropyWCount` — `posAvg_bandWLaw_eq_count`/`_eq_digits` at a **general gated `X'`** (they were pinned to `wTop i`; their content is scale-generic, the gate supplies `bandWtr_nonempty`), packaged as **`abs_occ_bandWtr_sub_le`**; `pairCount_prod_eq` (the triple count over any sample set = the pair sum over `S ×ˢ univ`) |
| `5e24950` | `G4EntropyWOverhang` — the multiplicity overhang **charged against the flank's own scale**: `badPairsAt`, `overhang_gen_le_at`, `card_badPairsAt_le_real`, `overhang_gen_le_band` (`ov T ≤ 8·\|bandWtr i X'\|`).  Needed `card_Atom_sq_le_PKtr`: `\|Atom\|² ≤ \|PKtr i X'\|` at every gated scale (`\|Atom\| ≤ 2^{K³+K}`, gate forces `X' ≥ 16·Xlo = 16·2^{50·2^m}`, `P₀ ≤ 2^{2·2^m}`, `2(K³+K) ≤ 48·2^m` since `m ≥ K³`) |
| `3417d45` | `G4EntropyWMid` — `gate_cutLo`/`gate_cutHi`, `fullGoodWPre_eq_startsOf`, `sum_pairsLe_sandwich`, `abs_flank_sum_sub_le` (the multiplied-out capture at a flank), `card_pairsLe_ge/_le`, `aLe_ge_real` |
| `c1f1c65` | the ratio arithmetic in closed form: `mid_core_lower`, `mid_core_upper`, **`mid_ratio_arith`** — `\|S/(A·F) − r\| ≤ ε + 128/K` from the flank bracket, the spread, the certified sums and `Q ≥ K ≥ 160000` |
| `6886073` | 🎯 **`abs_prefix_ratio_sub_le`** — MID-BAND PREFIX CONTROL |
| `f5c2896` | `G4EntropyWHead` — `aLe_fnthW`, `cutHi_le_of_ungated`, `headW`, `aLe_le_headW`; the leaf `head_frac_tiny` |

### The headline estimate now in kernel

> `abs_prefix_ratio_sub_le i c v (hg : 8·wFloor i ≤ cutLo i c) (hhi : cutHi i c ≤ wTop i) …` :
> `|fullGoodWPre i (aLe i c) x v / (aLe i c · (kk i − ℓ + 1)) − 2^{−ℓ}|`
> `  ≤ 2√(808 log 2·ℓ/√K_i) + 128/K_i`

i.e. the read's word frequency at an **arbitrary read index**, not just at a band end.  The whole
price of mid-band control is `128/K` — negligible against the capture error `O(K^{−1/4})` already
carried.  **Route trigger E-T11 did NOT fire.**

## Next lap — in order

1. **`head_frac_tiny` — THE one open leaf.**  `headW (i+1) · kk (i+1) · KK (i+1) ≤ fTW (i+1)`.
   The reduction is written out in its docstring and in `PENDING_WORK.md`: the head consumes
   `≈ 16·wFloor_i·|Atom_i|/P₀_i` windows, `fTW i ≥ fLW (i−1) ≥ Xlo (KK i)·kk_{i−1}/(4·P₀_{i−1})`,
   `wFloor i = 4·gridDm_i·Xlo (KK i)`, the `Xlo (KK i)` cancels, and what is left is
   `256·gridDm_i·|Atom_i|·kk_i·P₀_{i−1}/(P₀_i·kk_{i−1})`.
   **What is missing is a LOWER bound on `P₀`** — the repo has only upper bounds (`P₀_le`,
   `P₀_le_two_pow`, `logP₀Nat_le_two_pow`), because every E0-cone estimate wants `P₀` small.
   *Cheapest route to try first*: `P₀ = Mprod·freezeQ` with `Mprod = ∏_α d_α²`
   (`G4Progression.lean:100`) and `d_α = mult B Q D₀ α` — check in `G4ScheduleGrid`/`mult` whether
   `d_α ≥ gridQ`; if so `Mprod ≥ gridQ^{2|Atom|}` and the comparison against
   `P₀_{i−1} ≤ gridP₀Bound (K−4)` is a pure exponent computation.
   *Fallback*: a Chebyshev lower bound on `∏_{p ≤ 2|Idx|} p` (mathlib has only
   `Nat.primorial_le_4_pow`).
2. **Item 4 — the squeeze and the endpoint.**  Independent of 1; can be built on top of the leaf.
   For `n` in band `i`, write `n = fTW i + a·kk i + s`, `s < kk i`; `winCount` is monotone so the
   cutoffs `fTW i + a·kk i` suffice (`fTW_kk_le` gives `kk i/fTW i → 0`).  Use `aLe_fnthW` to turn
   the read index `a` into the cutoff `c := fnthW i (a−1)`, then `fullW_prefix_winCount_bounds` +
   `abs_prefix_ratio_sub_le` when gated, and `aLe_le_headW` + `head_frac_tiny` when not.  Then
   `IsNormalSequence 2 (fullDigW …)`, `properDigits_fullDigW`, `fullRealW`,
   `Bridge.isNormal_realOfDigits` → **`IsNormal 2 fullRealW`**.
   (`exists_matchesAt_fullDigW` still needs a wide non-vacuity witness.)

## Hygiene (new this lap, carried forward)

* **`positivity` is dangerous on schedule terms.**  `positivity` on `√(KK i)`, on a `Nat`-cast of
  `fullGoodWPre`, or on `((kk i − ℓ + 1 : ℕ) : ℝ)` sends `whnf` into the tower terms and times
  out.  Use `mul_nonneg` / `Nat.cast_nonneg` / `Nat.succ_pos` explicitly.
* **`nlinarith` times out on a big context.**  Split a real inequality into standalone lemmas with
  *minimal* hypotheses (that is what made `mid_ratio_arith` go through), and feed `linarith` the
  products as named `have`s (`mul_le_mul_of_nonneg_left/right`, `mul_le_mul`) rather than hoping
  `nlinarith` finds them.
* `le_or_lt` is gone — use `le_or_gt`.
* `field_simp` sometimes closes the goal outright; a following `ring` then errors with
  "No goals to be solved".
* To turn `|S/D − r| ≤ ε` into `|S − r·D| ≤ ε·D`: `have hfac : S − r*D = (S/D − r)*D := by
  field_simp`, then `rw [hfac, abs_mul, abs_of_pos hD]` — rewriting with `← abs_of_pos` first
  rewrites *every* occurrence of `D`.
* `KK_le_card_Atom` lives in `G4EntropyJointSched`, which is **not** in the `W`-module import
  closure; import it explicitly.

## Do not re-derive

`DIRECTION.md`'s CURRENT DIRECTIVE (review lap 122) still forbids re-litigating the scale gap or
the head obstruction, lowering the band floor, adding joint-ladder rungs or sharpening constants,
and touching `fullReal`/`fullPos`/`bandT`.  `density_antitone` stays withdrawn.
