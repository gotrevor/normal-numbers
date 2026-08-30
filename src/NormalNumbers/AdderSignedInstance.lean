/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderSigned
import NormalNumbers.AdderMain

/-!
# The flagship as an engine instance (brief follow-on 2, objective 2)

Unsigned channels are the `off = 0` fibre of the signed world:
`Channel.toZ` embeds, `ZChannel.pred` collapses to `Channel.pred`
(`toZ_pred_eq`), so `zfamPred (chs.map toZ) = famPred chs`
(`zfamPred_map_toZ`) and the kernel-tier main certificate transfers with
NO recheck.  `adder_sixfold_disjunction_universal_via_engine` re-derives
the frozen universal flagship statement byte-identically from the engine
meta-theorem `signed_engine` — families are now data.
-/

namespace NormalNumbers.Adder

open NormalNumbers

/-- Embed an unsigned channel into the signed world. -/
def Channel.toZ (ch : Channel) : ZChannel := ⟨ch.a, ch.b, ch.word⟩

theorem toZ_off (ch : Channel) : ch.toZ.off = 0 := by
  show (-(ch.a:ℤ)).toNat + (-(ch.b:ℤ)).toNat = 0
  omega

theorem toZ_winSize (ch : Channel) : ch.toZ.winSize = ch.winSize := rfl

theorem toZ_wordVal (ch : Channel) : ch.toZ.wordVal = ch.wordVal := rfl

theorem toZ_carrySize (ch : Channel) : ch.toZ.carrySize = ch.carrySize := by
  show max ((ch.a:ℤ).toNat + (ch.b:ℤ).toNat + ((-(ch.a:ℤ)).toNat + (-(ch.b:ℤ)).toNat)) 1
      = max (ch.a + ch.b) 1
  omega

theorem toZ_size (ch : Channel) : ch.toZ.size = ch.size := by
  unfold ZChannel.size Channel.size
  rw [toZ_winSize, toZ_carrySize]

/-- On the unsigned fibre the signed predecessor IS the unsigned one. -/
theorem toZ_pred_eq (ch : Channel) (x y c : ℕ) :
    ch.toZ.pred x y c = ch.pred x y c := by
  unfold ZChannel.pred Channel.pred
  rw [toZ_winSize, toZ_wordVal, toZ_off]
  have hv : (ch.toZ.a * x + ch.toZ.b * y + ((c / ch.winSize : ℕ) : ℤ) - ((0:ℕ) : ℤ))
      = ((ch.a * x + ch.b * y + c / ch.winSize : ℕ) : ℤ) := by
    unfold Channel.toZ
    push_cast
    ring
  rw [hv]
  generalize ch.a * x + ch.b * y + c / ch.winSize = n
  have h₁ : (((n : ℤ)) % 2).toNat = n % 2 := by omega
  have h₂ : (((n : ℤ)) / 2 + ((0:ℕ):ℤ)).toNat = n / 2 := by omega
  rw [h₁, h₂]

/-- The signed family predecessor restricted to the unsigned fibre. -/
theorem zfamPred_map_toZ (chs : List Channel) :
    zfamPred (chs.map Channel.toZ) = famPred chs := by
  funext x y s'
  induction chs generalizing s' with
  | nil => rfl
  | cons ch rest ih =>
    show zfamPred (ch.toZ :: rest.map Channel.toZ) x y s' = famPred (ch :: rest) x y s'
    simp only [zfamPred, famPred, toZ_size, toZ_pred_eq, ih]
    rfl

/-- **The frozen universal flagship, re-derived as a data instance of the
engine meta-theorem** (`signed_engine` at the unsigned fibre of
`mainFamily`, kernel-tier certificate transferred without recheck). -/
theorem adder_sixfold_disjunction_universal_via_engine (X Y : ℝ)
    (hXY : ¬ (∃ p : ℚ, (p:ℝ) = X) ∨ ¬ (∃ q : ℚ, (q:ℝ) = Y)) :
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 X [0, 0] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 Y [0, 0, 1] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (X + Y) [1, 1] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (X + 2 * Y) [0, 0, 1] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (2 * X + Y) [0, 1, 0] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (X + 3 * Y) [0, 0, 0] n) := by
  have hirr : Irrational X ∨ Irrational Y := by
    rcases hXY with hX | hY
    · exact Or.inl fun ⟨p, hp⟩ => hX ⟨p, hp⟩
    · exact Or.inr fun ⟨q, hq⟩ => hY ⟨q, hq⟩
  have hS : (73728 : ℕ) = zfamSize (mainFamily.map Channel.toZ) := by decide
  have hcert : checkCertP (zfamPred (mainFamily.map Channel.toZ)) 73728
      mainLiveK mainRhoK mainOmegaK mainForcedK = true := by
    rw [zfamPred_map_toZ]
    exact main_cert_ok_kernel
  obtain ⟨ch, hch, hocc⟩ := signed_engine (mainFamily.map Channel.toZ) hS hcert X Y hirr
    (by decide) (by decide) (by decide)
  fin_cases hch
  · refine Or.inl ?_
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 2 (((1:ℤ):ℝ) * X + ((0:ℤ):ℝ) * Y) [0, 0] n := hocc
    rwa [show ((1:ℤ):ℝ) * X + ((0:ℤ):ℝ) * Y = X from by push_cast; ring] at h
  · refine Or.inr (Or.inl ?_)
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 2 (((0:ℤ):ℝ) * X + ((1:ℤ):ℝ) * Y) [0, 0, 1] n := hocc
    rwa [show ((0:ℤ):ℝ) * X + ((1:ℤ):ℝ) * Y = Y from by push_cast; ring] at h
  · refine Or.inr (Or.inr (Or.inl ?_))
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 2 (((1:ℤ):ℝ) * X + ((1:ℤ):ℝ) * Y) [1, 1] n := hocc
    rwa [show ((1:ℤ):ℝ) * X + ((1:ℤ):ℝ) * Y = X + Y from by push_cast; ring] at h
  · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 2 (((1:ℤ):ℝ) * X + ((2:ℤ):ℝ) * Y) [0, 0, 1] n := hocc
    rwa [show ((1:ℤ):ℝ) * X + ((2:ℤ):ℝ) * Y = X + 2 * Y from by push_cast; ring] at h
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 2 (((2:ℤ):ℝ) * X + ((1:ℤ):ℝ) * Y) [0, 1, 0] n := hocc
    rwa [show ((2:ℤ):ℝ) * X + ((1:ℤ):ℝ) * Y = 2 * X + Y from by push_cast; ring] at h
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 2 (((1:ℤ):ℝ) * X + ((3:ℤ):ℝ) * Y) [0, 0, 0] n := hocc
    rwa [show ((1:ℤ):ℝ) * X + ((3:ℤ):ℝ) * Y = X + 3 * Y from by push_cast; ring] at h

end NormalNumbers.Adder
