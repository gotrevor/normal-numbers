/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderCertMainChunk0
import NormalNumbers.AdderCertMainChunk1
import NormalNumbers.AdderCertMainChunk2
import NormalNumbers.AdderCertMainChunk3
import NormalNumbers.AdderCertMainChunk4
import NormalNumbers.AdderCertMainChunk5
import NormalNumbers.AdderCertMainChunk6
import NormalNumbers.AdderCertMainChunk7

/-!
# Kernel-tier main certificate: assembly (module 3, phase-2)

The eight 9216-state chunk sweeps (`main_chunk0`–`main_chunk7`, each
`decide +kernel`) cover `[0, 73728)`; `checkForced` is one more kernel
sweep.  `main_cert_ok_kernel` therefore carries **no compiler axiom** —
the kernel-tier swap the brief's endgame asked for.
-/

namespace NormalNumbers.Adder

set_option maxHeartbeats 8000000 in
theorem main_forced_kernel :
    checkForced mainFamily 73728 mainLiveK mainForcedK = true := by
  decide +kernel

theorem main_edges_kernel :
    checkEdges mainFamily 73728 mainLiveK mainRhoK mainOmegaK mainForcedK = true := by
  apply checkEdges_of_edgeOk
  intro s' hs'
  have c0 := checkEdgesOn_spec main_chunk0
  have c1 := checkEdgesOn_spec main_chunk1
  have c2 := checkEdgesOn_spec main_chunk2
  have c3 := checkEdgesOn_spec main_chunk3
  have c4 := checkEdgesOn_spec main_chunk4
  have c5 := checkEdgesOn_spec main_chunk5
  have c6 := checkEdgesOn_spec main_chunk6
  have c7 := checkEdgesOn_spec main_chunk7
  rcases (by omega : s' < 9216 ∨ (9216 ≤ s' ∧ s' < 18432) ∨ (18432 ≤ s' ∧ s' < 27648)
      ∨ (27648 ≤ s' ∧ s' < 36864) ∨ (36864 ≤ s' ∧ s' < 46080)
      ∨ (46080 ≤ s' ∧ s' < 55296) ∨ (55296 ≤ s' ∧ s' < 64512)
      ∨ (64512 ≤ s' ∧ s' < 73728)) with
    h | h | h | h | h | h | h | h
  · have := c0 s' h
    rwa [Nat.zero_add] at this
  · have := c1 (s' - 9216) (by omega)
    rwa [show 9216 + (s' - 9216) = s' from by omega] at this
  · have := c2 (s' - 18432) (by omega)
    rwa [show 18432 + (s' - 18432) = s' from by omega] at this
  · have := c3 (s' - 27648) (by omega)
    rwa [show 27648 + (s' - 27648) = s' from by omega] at this
  · have := c4 (s' - 36864) (by omega)
    rwa [show 36864 + (s' - 36864) = s' from by omega] at this
  · have := c5 (s' - 46080) (by omega)
    rwa [show 46080 + (s' - 46080) = s' from by omega] at this
  · have := c6 (s' - 55296) (by omega)
    rwa [show 55296 + (s' - 55296) = s' from by omega] at this
  · have := c7 (s' - 64512) (by omega)
    rwa [show 64512 + (s' - 64512) = s' from by omega] at this

/-- The main certificate, **kernel tier**: no compiler axiom. -/
theorem main_cert_ok_kernel :
    checkCert mainFamily 73728 mainLiveK mainRhoK mainOmegaK mainForcedK = true :=
  checkCert_of_parts main_edges_kernel main_forced_kernel

end NormalNumbers.Adder
