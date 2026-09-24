# HANDOFF 2026-09-24 — Delange slot: RUNG 1 PROVED; rung 2 down to plumbing

Branch `wip/delange-slot`, HEAD `cdb134c`, tree clean, `lake build` green (9196 jobs).
Objective: `KICKOFF-2026-09-24-delange-slot.md` — prove both theorems in
`src/NormalNumbers/DelangeSlot.lean`.

## Status

* **`omegaLarge_mean_tendsto_zero` — PROVED, axiom-clean** (`[propext, Classical.choice,
  Quot.sound]`).  Commit `8868051`.
* `twisted_omegaLarge_mean_tendsto_zero` — still `sorry`.  This is the ONLY sorry in
  `src/NormalNumbers/DelangeSlot.lean`.  Every mathematical ingredient is now proved; what
  remains is four routine plumbing steps (below).

## Landed this session (in order)

| commit | content |
|---|---|
| `8868051` | **RUNG 1 PROVED.** `sigmaMeang…of_recursion` wrapper + `exists_recursion_bound` (L5+L2+L3+L4 → L6 → L7). |
| `b835d61` | `DelangeSlotChar.lean`: the χ-generalised chain (L1, shifts, L2g, L3g, L5g) and the `o(x)` bridge `sum_psiChar_div_le`, payoff `Sgsum_tendsto_zero_of_psi_littleO`. |
| `861284b` | `DelangeSlotAP.lean`: `psiChar_littleO` from PNT in APs. |
| `44adaf0` | **`psiAP_tendsto` PROVED, axiom-clean** — PNT in arithmetic progressions is now in-kernel here.  `src/PNTPort/Wiener.lean` vendored. |
| `761d244` | `DelangeSlotPrincipal.lean`: L4g, L6g, `corrQ_le` (the sharp `ω(Q)·log X` bound). |
| `b8367cc` | **Principal branch PROVED**: `sigmaMeang_chiZero_tendsto_zero`. |
| `532adc4` | **`charSum_tendsto_zero` PROVED, axiom-clean** — the master dichotomy. |
| `cdb134c` | `hfun_mul_left_expand` / `sum_mul_left_expand` — the unfolding identity. |

## The three structural finds that made rung 2 tractable

1. **Non-principal χ needs no recursion.**  `ψ(x,χ)` has no main term, so the chain closes
   straight off `ψ(x,χ) = o(x)` — no L6/L7, no `mSum`, and crucially **no quantitative
   zero-free region**.  Qualitative `o(x)` suffices (`sum_psiChar_div_le`).
2. **Route through residue classes, not through `ψ(x,χ)`.**  Every Lean Wiener–Ikehara needs
   nonnegative coefficients; `Λ` restricted to a residue class is nonnegative, `Λ·χ` is not.
   So `psiChar_littleO` goes via `psiAP`, and `psiAP_tendsto` became a *vendor*, not a proof.
3. **"`p ∣ m`" is the principal character mod `p`.**  Hence
   `z^{ω_{>P}(cm)} = ∑_{U ⊆ bigPrimes P c} (z−1)^{|U|} χ₀^{(∏U)}(m) z^{ω_{>P}(m)}`, so the
   `m = s·t` (Q-primary × Q-coprime) factorisation is **never needed** — the single hardest-
   looking remaining construction evaporated.

## Next steps (all routine; no open mathematics)

1. `DirichletCharacter ℂ M` ⟹ `IsCharLike M (fun n => χ n)`.  Fields: `mul` = `map_mul` after
   `push_cast`; `per` from `ZMod.natCast_eq_natCast_iff'`; `zero` = `MulChar.map_nonunit` with
   `ZMod.isUnit_iff_coprime`; `norm_le` = `DirichletCharacter.norm_le_one`.
2. Residue-class indicator: `DirichletCharacter.sum_char_inv_mul_char_eq`
   (`Mathlib/NumberTheory/DirichletCharacter/Orthogonality.lean`) gives
   `1_{(m : ZMod M) = a} = (φ M)⁻¹ ∑_χ χ(a⁻¹) χ(m)` for `a` a unit.
3. **The reindexing** `m = e·m'`, `e = gcd(a,Q)`, `Q' = Q/e`, `b = a/e`:
   `{m ∈ Ioc 0 N : m % Q = a} ≃ {m' ∈ Ioc 0 (N/e) : m' % Q' = b}` by `Finset.sum_nbij'`
   (`m ↦ m/e`, `m' ↦ e*m'`).  `gcd(b,Q') = 1`, which is exactly why no induction on `Q` is
   needed.  Then step 2 + `sum_mul_left_expand` + `charSum_tendsto_zero` give `M_a(N) = o(N)`.
   (Check `a = 0`: `e = Q`, `Q' = 1`, `b = 0`, `Coprime 0 1` holds.)
4. `T(N) = ∑_{a ∈ range Q} e(2πi j a/Q) · M_a(N)` (regroup by `m % Q`, exactly as
   `psiChar_eq_sum_psiAP` does), then the headline.  Note `Finset.Icc 1 N = Ioc 0 N`.

## Refuted sub-routes (do not retry)

* **L²/Parseval on the additive-twist vector `(T_r)_{r mod Q}`.**  `j ↦ jd` does permute `ℤ/Q`
  for `gcd(d,Q)=1`, so Cauchy–Schwarz closes a system — but squaring destroys the phase of `z`
  and the result, `W(N) log N ≲ ∑_d Λ d W(N/d)/d`, is identity-strength.  `Re z < 1` is only
  usable linearly.
* **Coupled scalar recursion via the hat operator** `ŵ = (1/φ(Q)) ∑_{a ∈ U} w(a·)`.  It does
  collapse the `Q`-vector to one scalar recursion, but its error is `o(log N)`, not `O(1)`,
  because `psiAP` is only qualitative; `recursion_tendsto_zero` cannot consume that.  This is
  positive evidence that the character decomposition is the right architecture.
* **Contraction on `A_d(x) = ∑_{m ≤ x, d ∣ m} χ(m)g(m)`.**  Gives `α ≤ (|z−1|/p)·α`, which is
  a genuine contraction except in the borderline `p = 2`, `z = −1`, `P ≤ 1`.  Superseded by
  find 3 above.

## Watch-outs from this session

* `Finset.prod_add f g s` expands as `∑_{U ⊆ s} (∏_U f)(∏_{s∖U} g)` — the subset indexes `f`,
  so put the *non-trivial* factor first.
* `fun_prop` cannot see through `Multiplicative.ofAdd` once simp unfolds it to a raw `Equiv.mk`;
  rewrite instead with the `rfl`-level `𝐞 y = cexp ((2πy : ℝ) * I)`.
* `ae`-membership goals now present as `ofCountableUnion`; close with `mem_ae_iff` +
  `Measure.restrict_apply'`.
* `Nat.pow_le_iff_le_log` → **`Nat.le_log_iff_pow_le`**; `le_or_lt` → **`le_or_gt`**;
  `Nat.Ico_succ_right` gone (use `range (X+1) = insert 0 (Ioc 0 X)`).
* `field_simp` often closes the goal outright, so a trailing `ring` errors with "No goals".

## Pointers
`DIRECTION.md` CURRENT DIRECTIVE (L4 crux — now discharged; directive says "then rung 2") ·
`PENDING_WORK.md` (rung-2 decomposition, updated) · `KICKOFF-2026-09-24-delange-slot.md` ·
`DESIGN-2026-09-24-delange-route.md`
