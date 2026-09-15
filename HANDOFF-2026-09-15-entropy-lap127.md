# HANDOFF — lap 127: step 3 of the base-`2^k` directive REFUTED; the elementary successor is in kernel

**Branch** `wip/g4-entropy`.  **HEAD** `875dd64`.  Working tree **clean**.
`lake build` 🟢 **9030 jobs**, exit 0.
`src/` carries **two** `sorry`s, both pre-expedition, off-path, on the forbidden-drift list
(`PrimeLambertOscillation.phaseOscillation`, `MahlerDriftOne.exists_drift_one_background`).
Everything this lap added is **sorry-free**.

## This lap's commits

| commit | content |
|---|---|
| `50768b7` | step 2 PROVED — `G4EntropyResidue.abs_posAvgRes_sub_le` |
| `f537ec2` | step 3a — `G4EntropySubLaw` (arbitrary sample sub-family, residue-certified) |
| `07a2d43` | step 3b — `G4EntropyResRead` (`winCountR`, the restricted prefix bounds, `locRes`) |
| `34a1f8e` | **E-T13**: step 3 refuted + `BlockRigidity.Sys.eq_uniform` PROVED |
| `875dd64` | `PowerBaseCount` — the counting layer of "normal base `b` ⇒ normal base `b^K`" |

All new headline declarations print `[propext, Classical.choice, Quot.sound]`.

## What happened

Steps 1–2 of `DIRECTION.md`'s lap-126-close CURRENT DIRECTIVE went through exactly as designed:
`posEquiv` **is** the arithmetic map `(r,j) ↦ r + jℓ`, `k ∣ ℓ` makes the positions `≡ c (mod k)` a
union of offset classes, and the capacity bound survives at the *same* constant
(`abs_posAvgRes_sub_le`).  The sample-sub-family layer (`subLaw`, `H₂_subLaw_ge`,
`abs_posAvgRes_subLaw_le`, `posAvgRes_subLaw_eq_digits`) and the read-side counting layer
(`winCountR`, `fullGoodWPreR`, `fullW_prefix_winCountR_bounds`, `mem_res_iff_locRes`,
`locRes_mod`) are all proved and kept.

**Step 3 is refuted.**  See `ROUTE-ESCALATION-2026-09-15-base2k-step3.md` (full argument).  In one
paragraph: for a fixed READ class `c`, the local class inside window `b` is `locRes i k c b`,
which alternates with `b` because `kk i = 40000 + i` is odd for odd `i`.  The certificate bounds
`∑_{b<a} N_b(r)` for each **fixed** `r` — an average over the band — so the split must be over
`{b : b ≡ e (mod k)}`.  That family is neither a sample-time set nor a coordinate set: the window
index is the sorted **rank** of `2(n − t_α)/d_α` over `bandW i ×ˢ Atoms`, the multipliers `d_α`
differ by up to `1/K`, and `≈|bandW|·|A|/K` foreign starts interleave inside each `n`'s spread.
Two equations (sum over classes; each fixed `r`), four unknowns.  Three repairs refuted:
class rotations, the `∑_c` identity, and the `∑_b D_b²` second moment (pair correlations cost
`B(t+ℓ)` per `t`, and the alternating sum over `t ≤ kk i` accumulates `≫ 1`).

## The successor route — and its heart is PROVED

`IsNormal 4 fullRealW` is **true**: it follows from the proved `IsNormal 2 fullRealW` by
Maxfield's classical theorem.  The directive rightly bans "Wall + Maxfield": the u.d./Fourier
route yields only `∑_{j<K} S_N(h b^j) = o(N)` — literally the same "sum over classes" gap.
There is an **elementary** route that avoids both, and it is now in kernel:

```
NormalNumbers.BlockRigidity.Sys.eq_uniform   [propext, Classical.choice, Quot.sound]
```

> Let `F m k ≥ 0` be attached to the base-`b` word of length `m` and value `k < b^m`, with
> `F 0 0 = 1`, `F m k = ∑_{s<b} F (m+1) (k·b+s)`, `F m k = ∑_{t<b^K} F (m+K) (t·b^m+k)`, and
> `F m k ≤ C·b^{−m}`.  Then `F m k = b^{−m}`.

Proof, finite sums only: the energy `A m = ∑_k b^m (F m k)²` is bounded by `C` with nonnegative
increments `Var m` (Cauchy–Schwarz on the refinement), and the shift relation forces
`Var m ≤ Var (m+K)` (Cauchy–Schwarz again); a summable sequence that is nondecreasing along each
class mod `K` is identically `0`, so `A m = A 0 = 1`, and Cauchy–Schwarz equality gives
`F m k = b^{−m}`.  This is ergodicity of the Bernoulli shift ("a `σ^K`-invariant measure `≪`
Bernoulli must **be** Bernoulli") with **no measure theory, no compactness, no ergodic theorem**.

`NormalNumbers/PowerBaseCount.lean` supplies the combinatorial side, sorry-free:
`wordOf b m k`, `wordOf_append` (`k ↦ k·b+d` IS append), `wordOf_cons` (`k ↦ t·b^m+k` IS prepend),
`matchesAt_append`, `matchesAt_cons`, `resCount K c s v n`, `resCount_append` (an **exact**
partition — no boundary term, since `MatchesAt` never asks the window to fit in `[0,n)`),
`resCount_prepend_bounds` (class shifts by one, to within 1), `sum_resCount` (the `K` classes
partition `winCount`).

## Next lap — in order

1. **`PowerBaseLimit.lean` — the analytic glue.**  Fix an ultrafilter `g ≤ atTop`.
   `(K/n)·resCount K c s (wordOf b m k) n ∈ [0, K+1]`, so `IsCompact.ultrafilter_le_nhds` /
   `le_nhds_lim` give a limit; define `G c m k := lim (g.map ·)`.  Push the three counting
   relations through (`1/n → 0` along `g ≤ atTop` kills the `±1` in `resCount_prepend_bounds`):
   * `right`  ← `resCount_append` + `wordOf_append`;
   * `prepend` `G (c+1) m k = ∑_{d<b} G c (m+1) (d·b^m + k)` ← `resCount_prepend_bounds` +
     `wordOf_cons`; iterate `K` times (index `c` by ℕ with the predicate `p % K = c % K`, so `G`
     is `K`-periodic in `c` by construction) to get `Sys`'s `shift` at `c`;
   * `bdd` with `C = K` and `unit` ← `sum_resCount` + normality of `s` (`G 0 0 0 = 1` because
     `#{p<n : p ≡ 0} ≈ n/K`).
2. **`Sys.eq_uniform` ⇒ `G 0 m k = b^{−m}` for EVERY ultrafilter ⇒ `tendsto_iff_ultrafilter`**
   gives `Tendsto (fun n => (K/n)·resCount K 0 s (wordOf b m k) n) atTop (nhds (b^{−m}))`.
3. **`IsNormalSequence b s → IsNormalSequence (b^K) (blockOf b K s)`**, where
   `blockOf b K s j = ∑_{t<K} s (K·j+t)·b^(K−1−t)`: a base-`b^K` word `w` of length `ℓ'` matches
   `blockOf` at `j` iff its flattening (a base-`b` word of length `Kℓ'`) matches `s` at `K·j`, so
   `winCount (blockOf …) w N = resCount K 0 s (flatten w) (K·N)` up to `O(1)`.
   Needs the easy converse of `isNormalSequence_of_tendsto_winCount` (same sandwich).
4. **The real-level statement** `IsNormal b y → IsNormal (b^K) y` via `Bridge`, then the two
   corollaries off `isNormal_fullRealW`: **`IsNormal 4 fullRealW`** and
   **`IsNormal (2^k) fullRealW`** — the lap-126-close directive's 🎯, by a route it did not
   anticipate, and strictly more general (every base, every normal number).

## Governing documents

* `DIRECTION.md` lap-126-close CURRENT DIRECTIVE: **step 3 refuted, E-T13 fired**; the escalation
  doc is written.  An altitude lap owns whether to re-point; a grind lap may not edit DIRECTION.
  The successor above stays inside the ACTIVE override's scope (same object, same 🎯) and touches
  nothing frozen: `fullRealW`, `fullPosW`, `fullDigW`, `G4EntropyWStatement` are untouched.
* `PENDING_WORK.md` ACTIVE updated with both the refutation and the successor plan.
* Still open and untouched, as required: the Aristotle line-by-line diff of job
  `48c7d703-d18e-4e47-ae9c-6734f6737047` (cheap, optional).

## Hygiene learned this lap

* `Finset.range_add`, `Finset.sum_div`, `Finset.sq_sum_le_card_mul_sum_sq` do **not** exist here.
  Use the repo's `sum_range_mul` pattern, `div_eq_mul_inv` + `← Finset.sum_mul`, and the ROOT
  `sq_sum_le_card_mul_sum_sq`.
* `Nat.add_div_right_of_dvd` does not exist; `Nat.mul_add_div (0 < m) : (m*a+b)/m = a + b/m` is
  the workhorse — commute the product into `m * _` shape first.
* `List.getD_append` is awkward; go through
  `List.getD_eq_getElem?_getD` + `List.getElem?_append_left/right` and `simp`.
* Modular arithmetic with a *variable* modulus: `omega` will not do it.  Use `Nat.ModEq`,
  `Nat.ModEq.add_right`, `Nat.ModEq.add_right_cancel'`.
* `congr 1` on `c * ∑ f = c * ∑ g` can close the goal outright; a following `rw` then errors with
  "No goals".  Prefer `simp only [defn]` + `rw [← key]` so the two sides become syntactically equal.
