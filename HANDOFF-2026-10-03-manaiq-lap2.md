# HANDOFF — Manai P/Q lane, lap 2 (2026-10-03) — DONE

Branch `proof/manaiq`.  Scope `sorry-free:src/NormalNumbers/ExplicitPQ.lean` met.
`#print axioms NormalNumbers.ExplicitPQ.exists_computable_PQ` = [propext, Classical.choice, Quot.sound].

Route: refuted `approx_GPfam` (deleted; `not_approxGPfamClaim` kept) replaced by family `GPfam2`
(slope-controlled normaliser), exact ℕ grid inverse of Q (`grid_bracket`), primrec affine test
(`affFail_iff`).  `exists_computable_isAbsNormal_GP` rewired (statement unchanged);
`exists_computable_approx_xPQ` proved from the grid.  See PENDING_WORK.md top entry.
