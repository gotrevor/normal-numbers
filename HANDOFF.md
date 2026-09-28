# Handoff: the Vandehey crux is down to ONE leaf, and §2 is under way

**Date**: 2026-09-28 · **Branch**: `wip/g5-prime-subset` · **HEAD**: `347bc55` ·
`lake build` 🟢 10311 jobs · working tree clean · nothing pushed.

## 🎯 What this run did

Operator objective 2026-09-28 (b): the Vandehey crux, lap 1 to evaluate the Smith-normal-form
shortcut first.  **The shortcut works, and it is formalized, not just evaluated** — and the
`GL₂(ℤ)` half of it is now a proved theorem, so the whole of Theorem 1.1 rests on one leaf.

## ✅ Landed (six green commits, every headline `#print axioms`-clean)

1. `1e73f46` **The Smith reduction** (`VandeheySmith.lean`).
   `MobiusCFN a b c d` (per-matrix), `MobiusCFN.comp` (closed under matrix product — the only
   CF content is that a CF-normal number is irrational, which is what keeps `x` off the inner
   pole: `not_isCFNormal_of_not_irrational`, proved from scratch by the Euclidean descent of
   the Gauss orbit on rationals).  `exists_column_kill` + `mobiusCFN_of_leaves`: the Hermite
   descent on `|det|`, `M = M''·diag(p,1)·V`.  `vandeheyUniformFreq_of_matrix_action`: the crux
   is *equivalent* to Theorem 1.1.  Guard rule: `mobiusCFN_one`, `not_mobiusCFN_const`.
2. `935cc04` **The tail-shift engine** (`CFTailFreq.lean`).  `tendsto_occStart_of_shift`;
   `isCFNormal_of_digit_shift`; `isCFNormal_gaussMap` (the forward Gauss direction).
3. `5494002` **Serret leaf DISCHARGED** (`VandeheySerret.lean`): `mobiusCFNGL2_holds`.
4. `c4a2607` bookkeeping.
5. `d7b499b` **Serret's theorem proper**: `serret_cfEquiv` — for `det = ±1` and irrational `x`,
   the Gauss orbits of `fract (Mx)` and `fract x` MEET.  Plus `CFEquiv` (+`refl`/`symm`/`trans`,
   `CFEquiv.isCFNormal`), `irrational_mobius`, and `MobiusClosure`/`mobius_gl2_of_closure`
   (the `PGL₂(ℤ) = ⟨x↦x+n, x↦1/x⟩` descent written once, instantiated twice).
6. `0aec7a9` **`VandeheyMat2.lean`** — `Mat2` (4-tuple), `det`, product, Möbius action,
   `act_eq_iff`/`act_mul_den` (cross-multiplied form), `act_mul` (left action), `B`/`E`
   generators, and **`act_cfMat : (cfMat x n)·Tⁿx = x`**, the CF algorithm as a matrix identity.
7. `347bc55` **`VandeheyNormalForm.lean`** — Vandehey's six types, `IsMD D M`,
   `isMD_entry_bounds` (`|entries| ≤ D`), `finite_isMD`.  Guard rule: `isMD_diag`,
   `not_isMD_zero`.

## 🧠 Where the crux stands

`vandeheyUniformFreq_of_scale (hScale : MobiusCFNScale) : VandeheyUniformFreq`.

**The single open leaf is `MobiusCFNScale`**: `x ↦ p·x` preserves CF-normality for prime `p`.
Composite determinants, the diagonal factor, division and all of `GL₂(ℤ)` are gone.

The structural insight this run added: **the fibre merges by Serret.**  The probe
`probes/cf_transducer_class.py` observed that two transducer states merge exactly when their
row lattices agree up to scaling.  The reason is that a state `N = λ·U·M` with `U ∈ GL₂(ℤ)` is
computing the CF of a `GL₂(ℤ)`-image of the same tail, so by `serret_cfEquiv` the two tails
meet.  Class-relative synchronization is therefore a corollary of a kernel theorem, not a
small-`p` observation.

## 🎬 Next actions, in order

1. **Vandehey Lemma 2.1** (`VandeheyNormalForm.lean`), fully specified and the last structural
   piece of §2:
   `M · J A_j = A_{d₀} J A_{d₁} ⋯ J A_{d_m} · M'` with `M' ∈ M_D`, `d₀ ≥ −1`, `d_i ∈ ℕ`, and
   `d₀ = −1 → m ≥ 1`.  The paper's proof (pp. 6–7 of the arXiv PDF, `papers/`) is a Euclidean
   descent: `M₀ = A_{d₀}^{-1}(M·J A_j)` with `d₀ = min(⌊α₋₁/γ₋₁⌋, ⌊β₋₁/δ₋₁⌋)`, then
   `M_{i+1} = A_{d_{i+1}}^{-1} J M_i`; no coefficient ever grows, at least one drops by `1` each
   step, and the first negative coefficient lands you in Type V or VI, which is already in `M_D`.
   Heavy but elementary case analysis (four cases for `d₀`, then the loop).
2. **Lemma 2.2** (burst length uniformly bounded in `D`) and identity (9)
   `Mx = R([a₁…aₙ],M) · (U([a₁…aₙ],M)(Tⁿx))`.
3. **§5–§6**: trigger strings and the assembly `ℓ(n) = c₁n(1+o(1))`, `#occ_r(n) = c_r n(1+o(1))`.
   Note the paper says trigger lengths are NOT provably bounded, hence its `f_j^±`
   approximants — plan for that, don't assume boundedness.

## ⚠️ Gotchas

- **`probes/cf_transducer_sync.py` is not Vandehey's transducer and is infinite-state.**  Its
  reachable state count grows linearly with the digit cap (D=2: 61/147/384 at caps 6/15/40).
  Vandehey's `M_D` is finite because Types V/VI admit a negative entry, which lets the `d₀ = −1`
  emission absorb the straddling states the probe must keep waiting in.  Don't use the probe as
  a specification for §2.
- `MobiusCFN` quantifies over **all** real `x` off the pole, negatives included — that is why
  `x ↦ −x` (i.e. `t ↦ 1−t`) had to be proved and cannot be dodged.
- `Int.floor_eq_iff` (ℤ version) takes no positivity argument, unlike the ℕ one.
- `Int.emod_add_ediv` / `Int.ediv_add_emod` are unavailable under those names; use `Int.emod_def`
  and `ring`.  `natCast_floor_eq_intCast_floor` is the `(⌊a⌋₊ : R) = ⌊a⌋` bridge.
- When a `linear_combination` residual comes back as exactly twice the intended identity, the
  coefficient needs its sign flipped — that happened four times this run.
- `Mat2` deliberately avoids `Matrix (Fin 2) (Fin 2) ℤ`: only the product and the action are
  used, and the `Fin`-indexed API costs rewriting everywhere while buying nothing.

## 📁 Key files

- `src/NormalNumbers/VandeheySmith.lean` — the reduction, the two leaf `Prop`s, the descent.
- `src/NormalNumbers/VandeheySerret.lean` — leaf 1 (proved) and Serret's theorem.
- `src/NormalNumbers/CFTailFreq.lean` — the shift engine.
- `src/NormalNumbers/VandeheyMat2.lean` — the matrix layer of the CF algorithm.
- `src/NormalNumbers/VandeheyNormalForm.lean` — `M_D`, finite; Lemma 2.1 goes here.
- `src/NormalNumbers/VandeheyClassEquidist.lean` — the §3 replacement, already unconditional.
- `papers/vandehey-2017-matrix-actions-cf-normality.pdf` — §2 proof is on pp. 6–7.

---
**→ Next session: start at NEXT action 1, Lemma 2.1.  Everything it needs (`Mat2`, `IsMD`,
the entry bound, `act_mul`) is already in the kernel.**
