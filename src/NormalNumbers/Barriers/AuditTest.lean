/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.BarrierAudit

/-!
# Teeth test for `#barrier_audit`

Each check below feeds the audit a deliberately broken registry and pins the failure it must
report; the last one shows the repaired registry passing.  Run it with

    lake build NormalNumbers.Barriers.AuditTest

This module is **not** imported by the root file: its `fakeCrux` is a real `sorry`, which the
root audit would (correctly) reject.
-/

namespace NormalNumbers.Barriers.AuditTest

open NormalNumbers.Barriers

/-- A stand-in for a new headline `sorry`. -/
theorem fakeCrux : (2 : ℕ) + 2 = 4 := sorry

/-- A barrier that claims `proved` while its evidence is a `sorry`. -/
def lyingBarrier : Barrier := .proved "lie" fakeCrux [``fakeCrux] "nothing"

/-- A barrier that claims `frozen` while its evidence is a real proof. -/
def staleFrozen : Barrier :=
  .frozen "stale" Siblings.not_exists_prime_nonresidue_71
    [``Siblings.not_exists_prime_nonresidue_71] "nothing"

/--
error: barrier audit failed (1):
open sorry NormalNumbers.Barriers.AuditTest.fakeCrux is untagged: link it to a barrier (a CruxLink) or record why none applies (a Waiver)
-/
#guard_msgs in
#barrier_audit allBarriers, cruxLinks, waivers

/--
error: barrier audit failed (1):
crux NormalNumbers.Barriers.AuditTest.fakeCrux names no barrier
-/
#guard_msgs in
#barrier_audit allBarriers, cruxLinks ++ [⟨``fakeCrux, [], "x"⟩], waivers

/--
error: barrier audit failed (1):
barrier NormalNumbers.Barriers.AuditTest.lyingBarrier claims tier NormalNumbers.Barriers.Tier.proved but its evidence uses sorryAx
-/
#guard_msgs in
#barrier_audit allBarriers ++ [``lyingBarrier],
  cruxLinks ++ [⟨``fakeCrux, [``lyingBarrier], "x"⟩], waivers

/--
error: barrier audit failed (1):
frozen barrier NormalNumbers.Barriers.AuditTest.staleFrozen is now sorry-free: promote it to Barrier.proved
-/
#guard_msgs in
#barrier_audit allBarriers ++ [``staleFrozen],
  cruxLinks ++ [⟨``fakeCrux, [``staleFrozen], "x"⟩], waivers

/--
error: barrier audit failed (1):
waiver NormalNumbers.Barriers.Siblings.not_exists_prime_nonresidue_71 has no direct sorry: delete the waiver
-/
#guard_msgs in
#barrier_audit allBarriers, cruxLinks ++ [⟨``fakeCrux, [``stoneham_two_not_six], "x"⟩],
  waivers ++ [⟨``Siblings.not_exists_prime_nonresidue_71, "x"⟩]

-- Repaired: the crux names a registered barrier, and the audit passes (no error).
#guard_msgs (drop info) in
#barrier_audit allBarriers, cruxLinks ++ [⟨``fakeCrux, [``stoneham_two_not_six], "x"⟩], waivers

end NormalNumbers.Barriers.AuditTest
