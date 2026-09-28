# Handoff: the Vandehey crux is down to ONE leaf

**Date**: 2026-09-28 · **Branch**: `wip/g5-prime-subset` · **HEAD**: see `git log`

## 🎯 What we're doing

Operator objective 2026-09-28 (b): the Vandehey crux, lap 1 to evaluate the Smith-normal-form
shortcut first.  **The shortcut works, and it is formalized, not just evaluated.**

## ✅ Landed this run (three green commits, all `#print axioms`-clean)

1. `1e73f46` **The Smith reduction** (`src/NormalNumbers/VandeheySmith.lean`).
   - `MobiusCFN a b c d` — the per-matrix predicate; `MobiusCFN.comp` — closed under matrix
     product.  The only CF content in composition is that a CF-normal number is irrational
     (it keeps `x` off the inner pole): `not_isCFNormal_of_not_irrational`, proved from
     scratch via the Euclidean descent of the Gauss orbit on rationals.
   - `exists_column_kill` + `mobiusCFN_of_leaves` — the Hermite descent on `|det|`:
     `M = M'' · diag(p,1) · V`, `V ∈ GL₂(ℤ)`, `|det M''| = |det M|/p`.
   - `vandeheyUniformFreq_of_matrix_action` — the crux is *equivalent* to Theorem 1.1.
   - Guard rule: `mobiusCFN_one` (locator), `not_mobiusCFN_const` (degenerate verdict).
2. `935cc04` **The tail-shift engine** (`src/NormalNumbers/CFTailFreq.lean`).
   `tendsto_occStart_of_shift`: `s (n+M) = r (n+N)` ⟹ every window has the same frequency.
   Plus `isCFNormal_of_digit_shift` and `isCFNormal_gaussMap` (the forward Gauss direction,
   which `CFAffineFamily.isCFNormal_of_gaussMap` does not give).
3. `5494002` **Serret leaf DISCHARGED** (`src/NormalNumbers/VandeheySerret.lean`).
   `mobiusCFNGL2_holds : MobiusCFNGL2`, by `PGL₂(ℤ) = ⟨x↦x+n, x↦1/x⟩` and a Euclidean descent
   on the bottom-left entry.  The one real computation is `t ↦ 1−t`:
   `T²(1−t) = T t` when `t < 1/2` (digits `1, a₁−1, a₂, …`), `T(1−t) = T² t` when `t > 1/2`
   (digits `a₂+1, a₃, …`); `t = 1/2` is excluded by irrationality.

## 🧠 The state of the crux

`vandeheyUniformFreq_of_scale (hScale : MobiusCFNScale) : VandeheyUniformFreq`.

**One leaf is left**: `MobiusCFNScale` — `x ↦ p·x` preserves CF-normality for prime `p`.
Composite determinants, the diagonal factor, division and all of `GL₂(ℤ)` are gone.

Already in the kernel for that leaf: `VandeheyTwo.tendsto_jointCount_classStep` — joint
(digit window, `ℙ¹(ℤ/p)` class) frequencies converge to an `x`-independent limit.

## 🎬 Next actions

1. **The output-frequency transfer principle** (Vandehey §5–§6, in abstract form): a finite-state
   transducer reads the input digits and emits blocks; if the joint (state, input-window)
   frequencies converge to `x`-independent limits, then `ℓ(n)/n → c₁`, `#occ_r(n)/n → c_r`, and
   every output word frequency converges to `c_r/c₁`.  Pure combinatorics — no CF theory, no
   analysis.  This is the piece that turns `tendsto_jointCount_classStep` into digit frequencies
   of `p·x`.
2. **Vandehey §2**: finiteness of the det-`±p` Raney normal forms and the transducer step.
3. **The fibre step**: state = (class ∈ `ℙ¹(ℤ/p)`) × (fibre, mergeable inside a class); a
   class-relative synchronization makes the joint (window, state) count a finite sum of joint
   (window, class) counts.

## ⚠️ Gotchas

- `MobiusCFN` quantifies over **all** real `x` off the pole, negative ones included.  That is why
  `x ↦ −x` (i.e. `t ↦ 1−t`) had to be proved and cannot be dodged.
- `Int.floor_eq_iff` (ℤ version) takes no positivity argument, unlike the ℕ one.
- `Int.emod_add_ediv` / `Int.ediv_add_emod` are not available under those names here; use
  `Int.emod_def` and `ring`.
- Don't rebuild `MobiusCFNGL2` from Smith normal form in mathlib: the explicit Euclidean
  descent on the bottom-left entry is shorter and needs no `Matrix` API at all.

## 📁 Key files

- `src/NormalNumbers/VandeheySmith.lean` — the reduction, the two leaf `Prop`s, the descent.
- `src/NormalNumbers/VandeheySerret.lean` — leaf 1, proved.
- `src/NormalNumbers/CFTailFreq.lean` — the shift engine.
- `src/NormalNumbers/VandeheyClassEquidist.lean` — the equidistribution input for leaf 2.
