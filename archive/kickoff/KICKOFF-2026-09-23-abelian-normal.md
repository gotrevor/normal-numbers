# KICKOFF 2026-09-23 — abelian normality in base two: the symmetrized Walsh dual

Branch `wip/g5-prime-subset`.  Engine Opus/low.  Authorised by Trevor 2026-09-23 ("Do it!" /
"A opus treadmill for the lean work").  Work **only** in `src/NormalNumbers/AbelianNormal.lean`
(new helper files under `src/NormalNumbers/Abelian*.lean` are fine).  Never edit any other
existing file's statements; never touch `papers/`, `agent-mail/`, other KICKOFFs.

## Target

`src/NormalNumbers/AbelianNormal.lean` is seeded (Ren, 2026-09-23) with **ratified statements**
and four `sorry`s.  Prove all four; do not change any statement, definition, or binder (you may
add lemmas above them).  The run is done when the file is sorry-free.

1. `isAbelianNormalTwo_iff_symParityMean` — headline.  Suggested route (finite linear algebra at
   fixed `L`, then limits):
   - Pointwise: `∑_{S ∈ (range L).powersetCard j} parityChar s S n = K j (onesCount s L n)` where
     `K j w = ∑_i (-1)^i * choose w i * choose (L-w) (j-i)` (Krawtchouk).  Via
     `parityChar_eq_pow`/`windowSet`: the character is `(-1)^|S ∩ windowSet|`; count j-subsets by
     how many hit the window set.
   - Hence `symParityMean s L j N = ∑_{w ≤ L} K j w * onesFreq s L w N`, and
     `∑_w K j w * choose L w = 0` for `j ≥ 1` (it is `2^L` times the mean of a nonempty character
     over all words; `sum_neg_one_pow_inter_eq_zero` is the Walsh-side fact).  So (⇒) is a finite
     linear combination of limits.
   - (⇐): the indicator of `onesCount = w` is `2^{-L} ∑_{S ⊆ range L} c_S · parityChar S` with
     `c_S = ∑_{T ⊆ range L, |T| = w} blockSign (wordOf L T) S`, which depends only on `|S|`
     (= `K |S| w`, by symmetry).  Mirror `Walsh.lean`'s `matchesAt_indicator_eq` /
     `blockMean_eq`, summed over the `choose L w` words.  The `S = ∅` term gives `choose L w / 2^L`.
   - Both directions can also go through a single identity: onesFreq − choose/2^L =
     2^{-L} ∑_{j=1}^{L} K j w · symParityMean.
2. `isAbelianNormalTwo_of_isNormalSequence` — from 1 and `isNormalSequence_two_iff_parityMean`
   (each `parityMean → 0`, finite sums).
3. `rigid_three` — pure linear algebra over `ℚ` on 8 unknowns: unfold `Stationary`,
   `AbelianUpTo` at the relevant `(k, j)`, `Fin.sum_univ_*`, `funext` + `fin_cases`, `linarith`.
4. `separation_four` — witness: `p w = 1/16 + (1/16) * v w` with `v = +1` on words
   `0011, 0100, 1010, 1101`, `v = −1` on `0010, 0101, 1011, 1100` (reading `w 0 w 1 w 2 w 3`),
   `0` elsewhere.  Checked by an exact probe (nullspace of the stationarity+abelian system).
   Everything is decidable over a finite domain; `decide`/`simp [Fin.sum_univ_succ]`/`norm_num`.

## Tiers

Proof tier: `native_decide`, `maxHeartbeats` boosts and deprecations are all fine.  Prefer many
small lemmas over one giant proof.  Build: `lake build NormalNumbers.AbelianNormal` (the dep tree
is warm; never `lake exe cache get`).  Commit each green step.
