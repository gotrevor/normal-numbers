# HANDOFF — lap 126: 🏁 `IsNormal 2 fullRealW` — the expedition's endpoint, proved

**Branch** `wip/g4-entropy`.  **HEAD** `6c40f85`.  Working tree **clean**.
`lake build` 🟢 **9025 jobs**.
`src/` carries **two** `sorry`s, both pre-expedition and off-path and both on the
forbidden-drift list (`PrimeLambertOscillation.phaseOscillation`,
`MahlerDriftOne.exists_drift_one_background`).  **The entropy expedition's part of `src/` is
sorry-free.**

## The result

```
G4.Sched.isNormal_fullRealW : IsNormal 2 fullRealW
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

`fullRealW = realOfDigits 2 (fullDigW (primeLambertAtBase 4))` — the real whose `j`-th **binary**
digit is `G₄`'s `fullPosW j`-th binary digit.  The unwound audit statement
(`G4EntropyWStatement.isNormal_two_of_schedule_read`):

> `∃ p : ℕ → ℕ, StrictMono p ∧ (∀ j, digitOf 2 fullRealW j = digitOf 2 (Int.fract G₄) (p j))`
> `∧ IsNormal 2 fullRealW`

`fullPosW` takes **no real argument at all** — that is the machine-checkable form of "schedule
only".  `digitOf_fullRealW` is the faithfulness step: `fullRealW`'s **own** binary expansion *is*
the read, not merely a number assembled from those digits.  Corollaries:
`fullRealW_mem_Ico`, `isDisjunctive_fullRealW`, `irrational_fullRealW`.

**Scope, stated exactly**: this is a theorem about `fullRealW`.  It says **nothing** about the
normality of `G₄` itself, and the ACTIVE override forbids claiming otherwise.

## This lap's four commits

| commit | content |
|---|---|
| `927ad8c` | review lap 126: direction KEPT, narrowed to the squeeze + the endpoint |
| `d58cb25` | skeleton — the mediant lemma proved, five named leaves |
| `c1a55b7` | 🎯 `abs_ratio_mid_le` — mid-band control at an ARBITRARY read index |
| `c840b22` | 🎯🎯 `IsNormal 2 fullRealW` |
| `6abd3f0` | the audit surface (`G4EntropyWStatement`) + corollaries |
| `7d75a71` | handoff + STATUS |
| `6c40f85` | successor directive + its decisive probe `abs_posAvgR_sub_le`, proved |

## The two ideas that closed it (do not re-derive)

1. **`kk_mul_KK_le_fTW` — `head_frac_tiny` at `a = 1`.**  One read window is a `1/KK` fraction of
   the history before it.  That single fact pays for the ungated head, the partial window at the
   end of the increment, and the `a = 0` stub; none of them then needs a certificate of its own.
   It follows because `headW i ≥ 1` (`bandWtr i (16·wFloor i)` is nonempty, `P₀ ≤ wFloor`).

2. **The case threshold is `a` vs `⌊√(KK j)⌋`, and it *must* move with `K`.**  A fixed threshold
   cannot work: at `a = 1` the certified branch's leftover `2·kk/s` is `O(1)`.  Balancing the two
   branches at `2/√K` each gives
   `midErrW i ℓ = 2√(808·log2·ℓ/√(KK i)) + 128/KK i + 2ℓ/kk i + 2/⌊√(KK i)⌋`, and all three
   branches (short / gated / ungated) land under it:
   * `a ≤ A`: `s·A ≤ (A²+A)·kk ≤ 2·kk·KK ≤ 2T`, error `2/A`;
   * `a > A`, gated: leftover `2E/s = 2aℓ/s + 2kk/s ≤ 2ℓ/kk + 2/a ≤ 2ℓ/kk + 2/A`;
   * `a > A`, ungated: `aLe_le_headW` + `head_frac_tiny` give `s·KK ≤ 2T` again.

3. **Non-vacuity was free.**  Lap 125 expected `exists_matchesAt_fullDigW` to need "a wide
   non-vacuity witness".  It does not: once the frequency limit holds at every `n`, the limit
   `2^{−|v|} > 0` forces `winCount v n > 0` directly.

## New modules

* `G4EntropyWMediant.lean` — `mediant_abs_le`, `mediant_abs_le_max`, `mediant_abs_le_trivial`
  (pure ℝ; deviations of history and increment simply add).
* `G4EntropyWSqueeze.lean` — `winCount_mono`, `winCount_sub_le`, `one_le_headW`,
  `kk_mul_KK_le_fTW`, `incr_bounds`, `midErrW`, `mid_gated_core`, `mid_trivial_core`,
  `mid_assemble_gated`, `mid_assemble_trivial`, `abs_ratio_mid_le`, `tendsto_natSqrt_KK_atTop`,
  `tendsto_midErrW`, `tendsto_fgrpW_atTop`, `tendsto_winCount_fullDigW`,
  `isNormalSequence_fullDigW`, `exists_matchesAt_fullDigW`, `properDigits_fullDigW`,
  `fullRealW`, `isNormal_fullRealW`.
* `G4EntropyWStatement.lean` — the audit surface and the corollaries.

## Hygiene (new this lap)

* `abs_add` does not exist here — it is **`abs_add_le a b`**.
* `div_le_div_iff` does not exist here — it is **`div_le_div_iff₀`**.
* `Nat.sqrt_le' n : (Nat.sqrt n)^2 ≤ n` (a `^2`, not `n.sqrt * n.sqrt`); convert with `nlinarith`.
* `div_le_div_of_nonneg_right h hpos` wants `0 ≤ c`, not `0 < c`, in this mathlib.
* `omega` **does** atomize a nonlinear product like `a * kk i`, but `(a+1) * kk i` and
  `kk i * a` are *different atoms*.  Normalize the shape first (`rw [add_mul, one_mul]`, or add
  `Nat.mul_comm` as a hypothesis) before handing it to `omega`.
* `Nat.div_lt_of_lt_mul` wants `m < k * n` — the *other* factor order from `fLW`'s definition.
* Implicit variables that occur only in a lemma's **conclusion** (`mid_gated_core`'s `G`) cannot
  be inferred from the hypotheses: pass `(G := …)` explicitly when using it in a `have`.

## Status of the governing documents

* `DIRECTION.md`'s lap-126 CURRENT DIRECTIVE 🎯 objective: **MET**.
* The ACTIVE operator override's stop condition ("stop when the endpoint is proved axiom-clean"):
  **DISCHARGED**.
* Route trigger **E-T7** applies: this lap does **not** pick its own successor.  Candidates for
  the next altitude lap are recorded in `STATUS.md` → Outstanding → Short-term (chiefly
  `IsNormal 4 fullRealW` / `IsNormal (2^k)`, which needs the read's word frequencies restricted
  to a residue class of positions; the entropy machinery supports it at a cost of `√k`, since the
  block-entropy deficit over a sub-class is bounded by the total deficit).
* An independent NL→formalization **faithfulness cross-check** of the headline was run at
  Aristotle from prose only, never the Lean (project `48c7d703-d18e-4e47-ae9c-6734f6737047`).
  **Verdict: PASS on the structure.**  Its independent rendering has
  `dig b z j = (⌊Int.fract z * b^(j+1)⌋).toNat % b` (= the repo's `digitOf`),
  `IsNormalBase b y` as "for every `ℓ ≥ 1` and every word `w`, `blockCount b y w N / N → b^{−ℓ}`"
  (= `IsNormalSequence` through `isNormalSequence_of_tendsto_winCount`),
  `ω n = n.primeFactors.card` and `A = ∑' n, ω(n)/4^n` (= `primeLambertAtBase 4`), and the
  headline `∃ p strictly increasing, ∃ y ∈ [0,1), (∀ j, dig 2 y j = dig 2 A (p j)) ∧ y normal in
  base 2` — logically the conjunction of `isNormal_two_of_schedule_read` and
  `fullRealW_mem_Ico`.  ⚠️ This was read from the job's own summary; a line-by-line diff of the
  returned file (`aristotle download 48c7d703-…`) has **not** been done and is a cheap item for a
  future lap.

## 🔜 The successor is SET and its decisive probe is already PROVED

`DIRECTION.md`'s CURRENT DIRECTIVE (lap 126 close) is **`IsNormal 4 fullRealW`, then
`IsNormal (2^k) fullRealW`** — the natural strengthening of the *same* object.

**The finding that opens it** (`G4EntropyOffsetClass.lean`, both theorems trust-triple clean):
`abs_posAvg_sub_le` is not a monolithic average.  It splits the `m − ℓ + 1` window positions into
the `ℓ` offset classes `p ≡ r (mod ℓ)` — `posEquiv` is literally `(r, j) ↦ r + jℓ` — certifies
each class *separately*, and only then sums.  Extracted as **`abs_offset_class_le`** (each class
alone obeys the bound, at the *same* constant `B`), hence **`abs_posAvgR_sub_le`** (the average
over any sub-family `R : Finset (Fin ℓ)` obeys `B`).

> Restricting to positions of a fixed residue mod `k` therefore costs **nothing** — not a factor
> `√k`, not even a constant — whenever `k ∣ ℓ`.  A base-`2^k` word of length `ℓ'` is a binary word
> of length `ℓ = kℓ'`, so `k ∣ ℓ` holds exactly where it is needed.  (I expected to pay `√k` via
> Pinsker; the offset-class structure makes it free.)  E-T13's second failure mode is ruled out.

**Next lap, steps 2–4** (detail in `PENDING_WORK.md` ACTIVE):
2. parity ↔ offset classes against `posEquiv`;
3. transport to the read (in window `a` of band `i` the class needed is
   `q ≡ (fTW i + a·kk i) (mod k)` — depends on `a`, but every class carries the same bound);
4. the `digitOf (b^k)` ↔ `digitOf b` bridge, then `IsNormal 4 fullRealW`, then general `k`.

**Do not retry**: Wall + Maxfield as the route to base `2^k`.  It is a genuinely harder classical
theorem — u.d. of `(b^n x)` does not formally give u.d. of `(b^{kn} x)`, and the Fourier route
yields only `μ̂(hb) = −μ̂(h)`-type periodicity, not vanishing.  The offset-class route is strictly
easier *here* because we own the entropy certificate.
