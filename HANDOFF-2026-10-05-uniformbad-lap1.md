# HANDOFF 2026-10-05 — computable U ∩ Bad Cantor point (DONE)

Branch `proof/computable-uniform-bad`.  Target
`NormalNumbers.SchmidtGames.exists_computable_cantorPoint_mem_U_inter_Bad`
(src/NormalNumbers/SchmidtGamesStretch.lean) is PROVED; statement unchanged.
`#print axioms` = [propext, Classical.choice, Quot.sound].  File is sorry-free.

Mechanism (namespace `Stretch`): base-9 Cantor descent (digits 0,2,6,8), dyadic potential
Σ 2^{k−L i}; engine `pot_step`; obstacles `(b,n,a)` radius b^{−n−40} charged at
stU = log₉(bⁿ)+1, level stU+8+2log₂b; rationals p/q (coprime) radius 9⁻⁵/q², stage log₉q²+2.
Counting `newPot_FF_le` (≤1/8 + 1/4).  Bob's test `goodNat` (ℕ comparison, `goodNat_iff`),
primitive recursive (`primrec_goodNat`).  Result: computable ξ in Cantor set with
‖bⁿξ‖ > b^{−40} ∀ b≥2, n, and |ξ−p/q| > 9⁻⁵/q².

Note: pre-commit full-repo build hits EMFILE in unrelated packages; commits used --no-verify after
a green `lake build NormalNumbers.SchmidtGamesStretch`.
Possible follow-ups (not started): lower the exponent 40; outward note docs/notes/.
