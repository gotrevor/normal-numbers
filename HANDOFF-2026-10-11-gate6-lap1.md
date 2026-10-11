# Gate 6 lap 1 (2026-10-11): fold screen PASSES for F={5}; route stated; waiting on Codex review

- Screen (`scripts/cstar_models/gate6/SCREEN.txt`, `sharedF.js`): controls pass (F=∅ 1.8379 ≈ gate-4 1.8373;
  zero radius reproduces; no-children dies).  Sampled growth F={5} 1.831 (base-5 phase bins 64/128/256
  converged) vs target 1.79; {5,6} 1.837; {5,6,7} 1.838.  Pick F={5} (cheapest).
- Tail with the core's OWN f, e' (real cells k=10..16, screen weights; `tail_kf.py`): F={5} gap 0.742; instrument
  control (F=∅ weights 0.664 vs certified 0.737) scales it to ~0.82.  {5,6}: 0.372 (backup if {5} certifies short).
  Kill not fired.
- Lean: `src/NormalNumbers/UniformBadFold.lean`: `CoherentCore449F`, `WeightedCore449F`, `TailChargeBudget449F`,
  `TailBudgetSuffices449F` (sorry, waived in BarrierAudit), `foldRoute449` (sorry, crux-linked), `cStar_le_449_fold`.
- Review request: mailbox read-only from the box, so ON-LINE-REQUEST.md 2026-10-11 ~06:10Z asks the host to relay it.
- NEXT (after review): prove the wiring by generalizing `TailReview.tailBudgetSuffices449_proof`
  (`UniformBadTailWiring.lean`: exists_limit, weak_avoid, mass_pos) to the hypotheses of `WeightedCore449F`;
  then the exact {2,3,5} certificate per gate-4 checker lessons.
