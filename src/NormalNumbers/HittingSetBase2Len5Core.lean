/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.HittingSetBase2Len5Runs0
import NormalNumbers.HittingSetBase2Len5Runs1
import NormalNumbers.HittingSetBase2Len5Runs2
import NormalNumbers.HittingSetBase2Len5Runs3
import NormalNumbers.HittingSetBase2Len5Runs4
import NormalNumbers.HittingSetBase2Len5Runs5
import NormalNumbers.HittingSetBase2Len5Runs6
import NormalNumbers.HittingSetBase2Len5Runs7
import NormalNumbers.HittingSetBase2Len5Runs8
import NormalNumbers.HittingSetBase2Len5Runs9
import NormalNumbers.HittingSetBase2Len5Runs10
import NormalNumbers.HittingSetBase2Len5Runs11
import NormalNumbers.HittingSetBase2Len5Runs12
import NormalNumbers.HittingSetBase2Len5Runs13

/-! The run-compressed reachability of the `h25` family, assembled from `HittingSetBase2Len5Runs*.lean`. -/

set_option maxRecDepth 100000

namespace NormalNumbers.Adder

open NormalNumbers

theorem h25_runs_ok : runsCover h25P 0 h25runs h25N = true := by
  show runsCover h25P 0 (h25runsC0 ++ (h25runsC1 ++ (h25runsC2 ++ (h25runsC3 ++ (h25runsC4 ++ (h25runsC5 ++ (h25runsC6 ++ (h25runsC7 ++ (h25runsC8 ++ (h25runsC9 ++ (h25runsC10 ++ (h25runsC11 ++ (h25runsC12 ++ (h25runsC13 ++ (h25runsC14 ++ (h25runsC15 ++ (h25runsC16 ++ (h25runsC17 ++ (h25runsC18 ++ (h25runsC19 ++ (h25runsC20 ++ (h25runsC21 ++ (h25runsC22 ++ (h25runsC23 ++ (h25runsC24 ++ (h25runsC25 ++ h25runsC26)))))))))))))))))))))))))) h25N = true
  exact h25_runsCover_append (h25runsC1 ++ (h25runsC2 ++ (h25runsC3 ++ (h25runsC4 ++ (h25runsC5 ++ (h25runsC6 ++ (h25runsC7 ++ (h25runsC8 ++ (h25runsC9 ++ (h25runsC10 ++ (h25runsC11 ++ (h25runsC12 ++ (h25runsC13 ++ (h25runsC14 ++ (h25runsC15 ++ (h25runsC16 ++ (h25runsC17 ++ (h25runsC18 ++ (h25runsC19 ++ (h25runsC20 ++ (h25runsC21 ++ (h25runsC22 ++ (h25runsC23 ++ (h25runsC24 ++ (h25runsC25 ++ h25runsC26))))))))))))))))))))))))) 4070375147188350 h25N (h25_runsCover_append (h25runsC2 ++ (h25runsC3 ++ (h25runsC4 ++ (h25runsC5 ++ (h25runsC6 ++ (h25runsC7 ++ (h25runsC8 ++ (h25runsC9 ++ (h25runsC10 ++ (h25runsC11 ++ (h25runsC12 ++ (h25runsC13 ++ (h25runsC14 ++ (h25runsC15 ++ (h25runsC16 ++ (h25runsC17 ++ (h25runsC18 ++ (h25runsC19 ++ (h25runsC20 ++ (h25runsC21 ++ (h25runsC22 ++ (h25runsC23 ++ (h25runsC24 ++ (h25runsC25 ++ h25runsC26)))))))))))))))))))))))) 8286816388175325 h25N (h25_runsCover_append (h25runsC3 ++ (h25runsC4 ++ (h25runsC5 ++ (h25runsC6 ++ (h25runsC7 ++ (h25runsC8 ++ (h25runsC9 ++ (h25runsC10 ++ (h25runsC11 ++ (h25runsC12 ++ (h25runsC13 ++ (h25runsC14 ++ (h25runsC15 ++ (h25runsC16 ++ (h25runsC17 ++ (h25runsC18 ++ (h25runsC19 ++ (h25runsC20 ++ (h25runsC21 ++ (h25runsC22 ++ (h25runsC23 ++ (h25runsC24 ++ (h25runsC25 ++ h25runsC26))))))))))))))))))))))) 12274924425063300 h25N (h25_runsCover_append (h25runsC4 ++ (h25runsC5 ++ (h25runsC6 ++ (h25runsC7 ++ (h25runsC8 ++ (h25runsC9 ++ (h25runsC10 ++ (h25runsC11 ++ (h25runsC12 ++ (h25runsC13 ++ (h25runsC14 ++ (h25runsC15 ++ (h25runsC16 ++ (h25runsC17 ++ (h25runsC18 ++ (h25runsC19 ++ (h25runsC20 ++ (h25runsC21 ++ (h25runsC22 ++ (h25runsC23 ++ (h25runsC24 ++ (h25runsC25 ++ h25runsC26)))))))))))))))))))))) 16480222607723875 h25N (h25_runsCover_append (h25runsC5 ++ (h25runsC6 ++ (h25runsC7 ++ (h25runsC8 ++ (h25runsC9 ++ (h25runsC10 ++ (h25runsC11 ++ (h25runsC12 ++ (h25runsC13 ++ (h25runsC14 ++ (h25runsC15 ++ (h25runsC16 ++ (h25runsC17 ++ (h25runsC18 ++ (h25runsC19 ++ (h25runsC20 ++ (h25runsC21 ++ (h25runsC22 ++ (h25runsC23 ++ (h25runsC24 ++ (h25runsC25 ++ h25runsC26))))))))))))))))))))) 20703859396119900 h25N (h25_runsCover_append (h25runsC6 ++ (h25runsC7 ++ (h25runsC8 ++ (h25runsC9 ++ (h25runsC10 ++ (h25runsC11 ++ (h25runsC12 ++ (h25runsC13 ++ (h25runsC14 ++ (h25runsC15 ++ (h25runsC16 ++ (h25runsC17 ++ (h25runsC18 ++ (h25runsC19 ++ (h25runsC20 ++ (h25runsC21 ++ (h25runsC22 ++ (h25runsC23 ++ (h25runsC24 ++ (h25runsC25 ++ h25runsC26)))))))))))))))))))) 24644271345704010 h25N (h25_runsCover_append (h25runsC7 ++ (h25runsC8 ++ (h25runsC9 ++ (h25runsC10 ++ (h25runsC11 ++ (h25runsC12 ++ (h25runsC13 ++ (h25runsC14 ++ (h25runsC15 ++ (h25runsC16 ++ (h25runsC17 ++ (h25runsC18 ++ (h25runsC19 ++ (h25runsC20 ++ (h25runsC21 ++ (h25runsC22 ++ (h25runsC23 ++ (h25runsC24 ++ (h25runsC25 ++ h25runsC26))))))))))))))))))) 28834627247919675 h25N (h25_runsCover_append (h25runsC8 ++ (h25runsC9 ++ (h25runsC10 ++ (h25runsC11 ++ (h25runsC12 ++ (h25runsC13 ++ (h25runsC14 ++ (h25runsC15 ++ (h25runsC16 ++ (h25runsC17 ++ (h25runsC18 ++ (h25runsC19 ++ (h25runsC20 ++ (h25runsC21 ++ (h25runsC22 ++ (h25runsC23 ++ (h25runsC24 ++ (h25runsC25 ++ h25runsC26)))))))))))))))))) 32859028460938680 h25N (h25_runsCover_append (h25runsC9 ++ (h25runsC10 ++ (h25runsC11 ++ (h25runsC12 ++ (h25runsC13 ++ (h25runsC14 ++ (h25runsC15 ++ (h25runsC16 ++ (h25runsC17 ++ (h25runsC18 ++ (h25runsC19 ++ (h25runsC20 ++ (h25runsC21 ++ (h25runsC22 ++ (h25runsC23 ++ (h25runsC24 ++ (h25runsC25 ++ h25runsC26))))))))))))))))) 37046943853019100 h25N (h25_runsCover_append (h25runsC10 ++ (h25runsC11 ++ (h25runsC12 ++ (h25runsC13 ++ (h25runsC14 ++ (h25runsC15 ++ (h25runsC16 ++ (h25runsC17 ++ (h25runsC18 ++ (h25runsC19 ++ (h25runsC20 ++ (h25runsC21 ++ (h25runsC22 ++ (h25runsC23 ++ (h25runsC24 ++ (h25runsC25 ++ h25runsC26)))))))))))))))) 41258802628318275 h25N (h25_runsCover_append (h25runsC11 ++ (h25runsC12 ++ (h25runsC13 ++ (h25runsC14 ++ (h25runsC15 ++ (h25runsC16 ++ (h25runsC17 ++ (h25runsC18 ++ (h25runsC19 ++ (h25runsC20 ++ (h25runsC21 ++ (h25runsC22 ++ (h25runsC23 ++ (h25runsC24 ++ (h25runsC25 ++ h25runsC26))))))))))))))) 45222652806089850 h25N (h25_runsCover_append (h25runsC12 ++ (h25runsC13 ++ (h25runsC14 ++ (h25runsC15 ++ (h25runsC16 ++ (h25runsC17 ++ (h25runsC18 ++ (h25runsC19 ++ (h25runsC20 ++ (h25runsC21 ++ (h25runsC22 ++ (h25runsC23 ++ (h25runsC24 ++ (h25runsC25 ++ h25runsC26)))))))))))))) 49399552922694975 h25N (h25_runsCover_append (h25runsC13 ++ (h25runsC14 ++ (h25runsC15 ++ (h25runsC16 ++ (h25runsC17 ++ (h25runsC18 ++ (h25runsC19 ++ (h25runsC20 ++ (h25runsC21 ++ (h25runsC22 ++ (h25runsC23 ++ (h25runsC24 ++ (h25runsC25 ++ h25runsC26))))))))))))) 53429314570632000 h25N (h25_runsCover_append (h25runsC14 ++ (h25runsC15 ++ (h25runsC16 ++ (h25runsC17 ++ (h25runsC18 ++ (h25runsC19 ++ (h25runsC20 ++ (h25runsC21 ++ (h25runsC22 ++ (h25runsC23 ++ (h25runsC24 ++ (h25runsC25 ++ h25runsC26)))))))))))) 57597722302220100 h25N (h25_runsCover_append (h25runsC15 ++ (h25runsC16 ++ (h25runsC17 ++ (h25runsC18 ++ (h25runsC19 ++ (h25runsC20 ++ (h25runsC21 ++ (h25runsC22 ++ (h25runsC23 ++ (h25runsC24 ++ (h25runsC25 ++ h25runsC26))))))))))) 61806267819384660 h25N (h25_runsCover_append (h25runsC16 ++ (h25runsC17 ++ (h25runsC18 ++ (h25runsC19 ++ (h25runsC20 ++ (h25runsC21 ++ (h25runsC22 ++ (h25runsC23 ++ (h25runsC24 ++ (h25runsC25 ++ h25runsC26)))))))))) 65777584147350075 h25N (h25_runsCover_append (h25runsC17 ++ (h25runsC18 ++ (h25runsC19 ++ (h25runsC20 ++ (h25runsC21 ++ (h25runsC22 ++ (h25runsC23 ++ (h25runsC24 ++ (h25runsC25 ++ h25runsC26))))))))) 69944489930440125 h25N (h25_runsCover_append (h25runsC18 ++ (h25runsC19 ++ (h25runsC20 ++ (h25runsC21 ++ (h25runsC22 ++ (h25runsC23 ++ (h25runsC24 ++ (h25runsC25 ++ h25runsC26)))))))) 73976979397946625 h25N (h25_runsCover_append (h25runsC19 ++ (h25runsC20 ++ (h25runsC21 ++ (h25runsC22 ++ (h25runsC23 ++ (h25runsC24 ++ (h25runsC25 ++ h25runsC26))))))) 78140372559549300 h25N (h25_runsCover_append (h25runsC20 ++ (h25runsC21 ++ (h25runsC22 ++ (h25runsC23 ++ (h25runsC24 ++ (h25runsC25 ++ h25runsC26)))))) 82355014513842525 h25N (h25_runsCover_append (h25runsC21 ++ (h25runsC22 ++ (h25runsC23 ++ (h25runsC24 ++ (h25runsC25 ++ h25runsC26))))) 86321736353177325 h25N (h25_runsCover_append (h25runsC22 ++ (h25runsC23 ++ (h25runsC24 ++ (h25runsC25 ++ h25runsC26)))) 90495901554007950 h25N (h25_runsCover_append (h25runsC23 ++ (h25runsC24 ++ (h25runsC25 ++ h25runsC26))) 94534903310240250 h25N (h25_runsCover_append (h25runsC24 ++ (h25runsC25 ++ h25runsC26)) 98709581465319825 h25N (h25_runsCover_append (h25runsC25 ++ h25runsC26) 102905290744606350 h25N (h25_runsCover_append h25runsC26 106880173219719900 h25N (h25_runs_c26) h25runsC25 102905290744606350 h25_runs_c25) h25runsC24 98709581465319825 h25_runs_c24) h25runsC23 94534903310240250 h25_runs_c23) h25runsC22 90495901554007950 h25_runs_c22) h25runsC21 86321736353177325 h25_runs_c21) h25runsC20 82355014513842525 h25_runs_c20) h25runsC19 78140372559549300 h25_runs_c19) h25runsC18 73976979397946625 h25_runs_c18) h25runsC17 69944489930440125 h25_runs_c17) h25runsC16 65777584147350075 h25_runs_c16) h25runsC15 61806267819384660 h25_runs_c15) h25runsC14 57597722302220100 h25_runs_c14) h25runsC13 53429314570632000 h25_runs_c13) h25runsC12 49399552922694975 h25_runs_c12) h25runsC11 45222652806089850 h25_runs_c11) h25runsC10 41258802628318275 h25_runs_c10) h25runsC9 37046943853019100 h25_runs_c9) h25runsC8 32859028460938680 h25_runs_c8) h25runsC7 28834627247919675 h25_runs_c7) h25runsC6 24644271345704010 h25_runs_c6) h25runsC5 20703859396119900 h25_runs_c5) h25runsC4 16480222607723875 h25_runs_c4) h25runsC3 12274924425063300 h25_runs_c3) h25runsC2 8286816388175325 h25_runs_c2) h25runsC1 4070375147188350 h25_runs_c1) h25runsC0 0 h25_runs_c0

/-- **Reachability**, by run compression: 5328 kernel checks instead of 109530094869795600. -/
theorem h25_section (k : ℕ) (hk : k < h25N) :
    h25Lget (h25idx (stateOfKW 2 h25N 5 h25ms k)) = stateOfKW 2 h25N 5 h25ms k
      ∧ h25idx (stateOfKW 2 h25N 5 h25ms k) < 5328 := by
  refine runsCover_spec (P := h25P) (Q := fun k =>
    h25Lget (h25idx (stateOfKW 2 h25N 5 h25ms k)) = stateOfKW 2 h25N 5 h25ms k
      ∧ h25idx (stateOfKW 2 h25N 5 h25ms k) < 5328) ?_ h25runs 0 h25N h25_runs_ok k (by omega) hk
  intro lo hi hP j hj1 hj2
  simp only [h25P, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hP
  have hconst : stateOfKW 2 h25N 5 h25ms j = stateOfKW 2 h25N 5 h25ms lo := by
    refine stateOfKW_congr 2 h25N 5 (by omega) h25ms j lo ?_
    intro b hb
    exact quot_const_of_run b h25N lo hi j hj1 hj2 (hP.1 b hb)
  have h := hP.2
  simp only [h25ok, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [hconst]
  exact h

end NormalNumbers.Adder
