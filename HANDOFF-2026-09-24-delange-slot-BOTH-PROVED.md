# HANDOFF 2026-09-24 — Delange slot: BOTH THEOREMS PROVED, axiom-clean

Branch `wip/delange-slot`, `lake build` green (9203 jobs).
Objective `KICKOFF-2026-09-24-delange-slot.md` is **complete**.

## Status

`src/NormalNumbers/DelangeSlot.lean` is **sorry-free**.  Both ratified statements are proved
with no change to any statement, definition or binder, and both are
`[propext, Classical.choice, Quot.sound]`:

* `omegaLarge_mean_tendsto_zero` (rung 1, untwisted) — proved earlier this campaign (`8868051`).
* `twisted_omegaLarge_mean_tendsto_zero` (rung 2, the Leaf-B slot) — proved this session.

Audit surface: `src/NormalNumbers/DelangeSlotCheck.lean` now prints the axioms of both.

## What landed this session: `src/NormalNumbers/DelangeSlotTwist.lean`

The four plumbing steps named by the previous handoff, in order, each green first or second try:

1. `isCharLike_dirichlet` — a `DirichletCharacter ℂ M` satisfies `IsCharLike M`
   (`map_mul` / `ZMod.natCast_eq_natCast_iff'` / `MulChar.map_nonunit` +
   `ZMod.isUnit_iff_coprime` / `DirichletCharacter.norm_le_one`).
2. `innerTwist_tendsto_zero` — for character-like `κ` and any fixed `c ≠ 0`,
   `∑_{m ≤ y} κ(m) z^{ω_{>P}(c·m)} = o(y)`: `sum_mul_left_expand` expands into
   `∑_{U ⊆ bigPrimes P c} (z−1)^{|U|} Sgsum (κ·χ₀^{∏U})`, and each summand dies by
   `charSum_tendsto_zero` applied to `IsCharLike.mul_chiZero`.
3. `indicator_eq_char_avg` + `coprimeClass_tendsto_zero` — `sum_char_inv_mul_char_eq`
   turns the indicator of a **unit** class `b` mod `Q'` into `(φ Q')⁻¹ ∑_χ χ(b⁻¹)χ(m)`.
4. `classSum_reindex` — `m = e·m'`, `e = gcd(a,Q)`, `Q' = Q/e`, `b = a/e`, via
   `Finset.sum_nbij'`.  `Nat.coprime_div_gcd_div_gcd` makes `b` a unit mod `Q'`, so a
   **general** class mod `Q` reduces to a unit class mod `Q'` with no induction on `Q`.
5. `classSum_tendsto_zero` (squeeze: `‖A(N)/N‖ ≤ ‖num(N/e)/(N/e)‖` since `N/e ≤ N`), then
   `exp_twist_of_mod` (`Complex.exp_int_mul_two_pi_mul_I`) and
   `twisted_tendsto_zero` regrouping by `m % Q` with `Finset.sum_fiberwise_of_maps_to`.

## Watch-outs added this session

* `Nat.Icc_succ_left` no longer exists; use
  `Finset.ext fun x => by simp [Nat.succ_le_iff]` for `Icc 1 N = Ioc 0 N`.
* `tendsto_finset_sum` → **`tendsto_finsetSum`**.
* Confirms the old note: `field_simp` closes the goal, so a trailing `ring` errors
  "No goals" — hit twice.
* `field_simp` will rewrite `((m / Q : ℕ) : ℂ)` into `(m:ℂ)/(Q:ℂ)`; `obtain ⟨k, hk⟩ : ∃ k,
  m = Q * k + a` and `subst` **before** calling it.

## Next

Nothing open in the Delange slot.  The downstream consumer is `TailLargeDecouple`
(C3 swing, `SwingC3Rotation.lean`) — wiring it is a separate kickoff.
