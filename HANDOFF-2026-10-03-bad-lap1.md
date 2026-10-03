# HANDOFF 2026-10-03 — BAD-normal (A) + reciprocal (B), lap 1: DONE

Both operator lanes closed.

* (B) `src/NormalNumbers/ReciprocalNormal.lean`: sorry-free (commits 56ecc605, 83c300c3 + not_isSimplyNormal).
  `exists_computable_absNormal_recip_not_normal`, `exists_computable_absNormal_recip_not_simplyNormal`:
  `#print axioms` = propext, Classical.choice, Quot.sound (conditional on the cited BB Props as hypotheses).
* (A) `src/NormalNumbers/BadNormal.lean`: sorry-free (a8a4d44d). `exists_computable_absNormal_bad`
  and `cfCoin_const_false`: trust base only (headline conditional on `SahlstenStevensBernoulli12`).
* No frozen definition/statement/Prop was edited. CFCylinder: seven `private` lemmas made public.
* Build note: the full `lake build` intermittently hits "Too many open files" (EMFILE) after a
  low-level module changes; building the failing module alone and re-running converges (≈70 rounds).
* Remaining open content: only the cited Props' referee passes (see PENDING_WORK.md top entry).

## Checkpoint (final)
Branch `proof/bad`, HEAD 77749c62. Scoped target met; `box done --green` issued.
Next steps (future run): referee `Literature.BakerBanajiSparse` and `Literature.SahlstenStevensBernoulli12`
transcriptions; optionally write `docs/notes/` notes for Bugeaud 10.17/10.18 and the BAD-normal result.
