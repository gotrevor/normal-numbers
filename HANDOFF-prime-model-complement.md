# HANDOFF — prime-model complement lemmas (2026-09-21)

Scope: `KICKOFF-prime-model-complement.md` only.  Done.

`src/NormalNumbers/PrimeModelComplement.lean` now proves, with statements verbatim
as frozen and no axioms beyond `propext, Classical.choice, Quot.sound`:

- `probability_complement_tail`
- `probability_complement_L1`
- `probability_complement_phase`

Method (as briefed):
- Helper `sum_add_tsum_compl_finset`: `Summable.sum_add_tsum_compl` applies
  directly at the `{i // i ∉ B}` subtype (defeq to `↑(↑B : Set ι)ᶜ`), no coercion
  rewriting needed.
- Helper `abs_sum_sub_sum_le_sum_abs` via `Finset.sum_sub_distrib` +
  `Finset.abs_sum_le_sum_abs`.  Note the *two-sided* bound is needed: the tail
  lemma consumes `∑_B μ − ∑_B ν ≤ ∑_B |ν−μ|`, the opposite orientation from the
  naive `le_abs_self` version, so `abs_le.mp` is used.
- L1: split `∑'|ν−μ|` at `B`; off `B` dominate by `ν+μ` (`abs_sub` then
  `abs_of_nonneg`), using `Summable.tsum_le_tsum` with subtype summability from
  `Summable.subtype`; then feed in the tail lemma and `linarith`.
- Phase: `Summable.of_norm_bounded` for both weighted families, rewrite the
  difference as `∑' i, (ν i − μ i) • f i` (`Summable.tsum_sub`, `Complex.real_smul`),
  and close with `tsum_of_norm_bounded` + the L1 bound.

Pin notes (mathlib at lean4 v4.33.1): `Summable` carries a `SummationFilter`;
the order lemma is `Summable.tsum_le_tsum (h) (hf) (hg)` (namespaced, to_additive
of `Multipliable.tprod_le_tprod`) — the bare `tsum_le_tsum` indeed does not exist.
`Summable.abs` exists (to_additive of `Multipliable.abs`).

`src/NormalNumbers.lean` gained the import.  Full `lake build` green.
No other module touched; G4 work untouched.
