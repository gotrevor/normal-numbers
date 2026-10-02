/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-MD: what the distortion route actually pays — the crux constant is a MODULUS

The front (S7-FT/S7-CP) hides a tension that this module makes explicit and quantitative.

The only bound the transducer layer has on a state's pullback of a target of Gauss mass `G` is
`S7-PB`: `γ(s⁻¹ I_w) ≤ (2K/η)·G` on states of width `≥ η` — and the factor `1/η` is SHARP
(directive fact (β): a state whose image straddles a cylinder boundary at a scale below `|I_w|`
pulls `I_w` back to mass `≈ 1/2`).  The width floor `η` is not free either: S7-SK prices it, and
the price is `η = exp(−2S)` for a bad-time frequency `A/(cS)`.  So the per-word output of the whole
route is

    freq(w)  ≤  inf_{S>0} [ A/(c·S)  +  Cp·G·exp(2S) ]                 (`slotCount_le_of_modulus`)

and, at `S = ¼ log(1/G)`,

    freq(w)  ≤  4A/(c·log(1/G))  +  Cp·√G                              (`slotCount_le_modulus`).

**That is a modulus of continuity, not a constant multiple of `G`.**  The two terms cannot be
balanced better: driving the second to `O(G)` costs `S ≥ ½ log(1/G)`, which only ever buys
`O(1/log(1/G))` on the first.  Hence:

* the sharp form `freq(w) ≤ C·γ(I_w)` (`OrbitWordBound`) is **not** reachable from bounded
  distortion plus a first moment on the height — it would need an exponential moment
  (`Σ_{m<q} 1/width = O(q)`, i.e. `Σ d² = O(q)`), which is exactly the divergence
  `∫ dη/η` and is not expected to hold;
* but `freq(w) → 0 as γ(I_w) → 0` **is** reachable, and a modulus is all that absolute
  continuity of a limit point of the empirical measures requires — `ν ≪ γ` plus invariance
  already forces `ν = γ` (the unique-AC-invariant-measure form of the cited rigidity input).

So the route survives; what has to move is the *shape* of the cited ergodic input, from
"density ≤ C" to "absolutely continuous".  This module proves the modulus, unconditionally on
everything except the per-cell class-frequency hypothesis, whose constant is here carried in the
honest `η`-dependent form `Cp·G/η` that S7-PB + S7-MY deliver.
-/
import NormalNumbers.VandeheyS7Compose

namespace NormalNumbers.VandeheyS7

open Set Filter Finset NormalNumbers

namespace MapState

variable {Φ : MapState} {x : ℝ}

/-- **S7-MD, the tradeoff.**  For every `S > 0`: a width floor `exp(−2S)` costs `A/(cS)` in
bad-time frequency and buys a per-cell constant `Cp·G·exp(2S)`. -/
theorem slotCount_le_of_modulus (Φ : MapState) (x : ℝ) (w : List ℕ) {A c Cp G : ℝ}
    (hA : 0 ≤ A) (hc : 0 < c) (hCp : 0 ≤ Cp) (hG : 0 ≤ G)
    (hmean : ∀ᶠ q in atTop, ∑ m ∈ range q, slack Φ x m ≤ A * q)
    (hclin : ∀ᶠ q in atTop, c * q ≤ ((runClock Φ x (q + 2) : ℕ) : ℝ))
    (hCF : ∀ {η ρ : ℝ}, 0 < η → 0 < ρ → ∀ {M : ℕ} (net : StateNet Φ x η ρ M),
      ClassFreqBound net w (Cp * G / η))
    {S ε : ℝ} (hS : 0 < S) (hε : 0 < ε) :
    ∀ᶠ q in atTop, slotCount Φ x w (q + 2)
      ≤ (A / (c * S) + Cp * G * Real.exp (2 * S) + ε) * ((runClock Φ x (q + 2) : ℕ) : ℝ) := by
  classical
  set η : ℝ := Real.exp (-(2 * S)) with hηdef
  have hη : 0 < η := Real.exp_pos _
  set B : ℝ := Cp * G / η with hBdef
  have hBeq : B = Cp * G * Real.exp (2 * S) := by
    rw [hBdef, hηdef, Real.exp_neg]
    field_simp
  have hBnn : 0 ≤ B := by rw [hBeq]; positivity
  obtain ⟨M, ⟨net⟩⟩ := exists_stateNet Φ x hη (show (0:ℝ) < 1 by norm_num)
  set ε' := ε / 2 with hε'def
  have hε' : 0 < ε' := by positivity
  have hcells : ∀ᶠ q in atTop, ∀ i : Fin M,
      cellHitCount net w i q ≤ (B + ε') * cellCount net i q :=
    Filter.eventually_all.mpr
      (fun i => hCF hη (show (0:ℝ) < 1 by norm_num) net ε' hε' i)
  have hclockTop : Tendsto (fun q => ((runClock Φ x (q + 2) : ℕ) : ℝ)) atTop atTop := by
    refine tendsto_atTop_mono' _ hclin ?_
    exact Filter.Tendsto.const_mul_atTop hc tendsto_natCast_atTop_atTop
  have hbig : ∀ᶠ q in atTop, (2:ℝ) ≤ ε' * ((runClock Φ x (q + 2) : ℕ) : ℝ) := by
    have h := hclockTop.eventually_ge_atTop (2 / ε')
    filter_upwards [h] with q hq
    rw [div_le_iff₀ hε'] at hq
    linarith
  filter_upwards [hcells, hbig, hmean, hclin] with q hc' hb2 hm hcl
  -- the narrow times, priced by Chebyshev on the slack
  have hqnn : (0:ℝ) ≤ (q:ℝ) := by positivity
  have hwide : widthBadCount Φ x η q ≤ (A / (c * S)) * ((runClock Φ x (q + 2) : ℕ) : ℝ) := by
    have h1 : widthBadCount Φ x η q ≤ (1 / S) * ∑ m ∈ range q, slack Φ x m := by
      rw [hηdef]; exact widthBadCount_le_sum_slack Φ x hS q
    have h2 : (1 / S) * ∑ m ∈ range q, slack Φ x m ≤ (1 / S) * (A * q) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    have h3 : (A / (c * S)) * (c * q) = (1 / S) * (A * q) := by
      field_simp
    have h4 : (A / (c * S)) * (c * q)
        ≤ (A / (c * S)) * ((runClock Φ x (q + 2) : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hcl (by positivity)
    linarith
  -- the cells
  have hsplit := slotCount_le_split net w q
  have hsum : ∑ i : Fin M, cellHitCount net w i q
      ≤ (B + ε') * ∑ i : Fin M, cellCount net i q := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hc' i
  have hcc : ∑ i : Fin M, cellCount net i q ≤ ((runClock Φ x (q + 2) : ℕ) : ℝ) :=
    sum_cellCount_le_runClock net q
  have h3 : (B + ε') * ∑ i : Fin M, cellCount net i q
      ≤ (B + ε') * ((runClock Φ x (q + 2) : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hcc (by linarith)
  have hεsplit : ε = 2 * ε' := by rw [hε'def]; ring
  rw [hBeq] at h3
  nlinarith [hsplit, hsum, h3, hwide, hb2]

/-- **The modulus.**  At `S = ¼ log(1/G)` the tradeoff gives
`freq(w) ≤ 4A/(c·log(1/G)) + Cp·√G`: a modulus of continuity in the target's Gauss mass, with no
constant multiple of `G` anywhere. -/
theorem slotCount_le_modulus (Φ : MapState) (x : ℝ) (w : List ℕ) {A c Cp G : ℝ}
    (hA : 0 ≤ A) (hc : 0 < c) (hCp : 0 ≤ Cp) (hG : 0 < G) (hG1 : G < 1)
    (hmean : ∀ᶠ q in atTop, ∑ m ∈ range q, slack Φ x m ≤ A * q)
    (hclin : ∀ᶠ q in atTop, c * q ≤ ((runClock Φ x (q + 2) : ℕ) : ℝ))
    (hCF : ∀ {η ρ : ℝ}, 0 < η → 0 < ρ → ∀ {M : ℕ} (net : StateNet Φ x η ρ M),
      ClassFreqBound net w (Cp * G / η))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q in atTop, slotCount Φ x w (q + 2)
      ≤ (4 * A / (c * Real.log (1 / G)) + Cp * Real.sqrt G + ε)
          * ((runClock Φ x (q + 2) : ℕ) : ℝ) := by
  have hlog : 0 < Real.log (1 / G) := by
    refine Real.log_pos ?_
    rw [lt_div_iff₀ hG]; linarith
  set S : ℝ := Real.log (1 / G) / 4 with hSdef
  have hS : 0 < S := by rw [hSdef]; positivity
  set E : ℝ := Real.exp (Real.log (1 / G) / 2) with hEdef
  have hE : (0:ℝ) < E := Real.exp_pos _
  have hEE : E * E = 1 / G := by
    rw [hEdef, ← Real.exp_add, show Real.log (1 / G) / 2 + Real.log (1 / G) / 2
      = Real.log (1 / G) by ring]
    exact Real.exp_log (by positivity)
  have h2S : 2 * S = Real.log (1 / G) / 2 := by rw [hSdef]; ring
  have hGE : G * E * (G * E) = G := by
    have hEE' : E * E * G = 1 := by
      rw [hEE, one_div, inv_mul_cancel₀ hG.ne']
    nlinarith [hEE']
  have hsqrt : Real.sqrt G = G * E := by
    have h : Real.sqrt (G * E * (G * E)) = G * E := Real.sqrt_mul_self (by positivity)
    rw [hGE] at h; exact h
  have hkey : Cp * G * Real.exp (2 * S) = Cp * Real.sqrt G := by
    rw [h2S, hsqrt, ← hEdef]; ring
  have hSval : A / (c * S) = 4 * A / (c * Real.log (1 / G)) := by
    rw [hSdef]; field_simp
  have h := slotCount_le_of_modulus Φ x w hA hc hCp hG.le hmean hclin hCF hS hε
  rw [hSval, hkey] at h
  exact h

end MapState

section Audit

#print axioms MapState.slotCount_le_of_modulus
#print axioms MapState.slotCount_le_modulus

end Audit

end NormalNumbers.VandeheyS7
