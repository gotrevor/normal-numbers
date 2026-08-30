/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderCert

/-!
# The parametric certificate engine (meta-theorem core)

Brief: `BRIEF-adder-signed-engine.md` §Objective 2.

The certificate checker and the descent argument never look inside a
channel: they see only the backward-deterministic predecessor map
`fpred : ℕ → ℕ → ℕ → Option ℕ` (input bits `x y`, deeper state `s'` ↦
shallower state).  This module abstracts `famPred chs` out of
`AdderCert`/`AdderDescent`, so ANY family shape (unsigned channels,
signed/borrow channels, future k-track variants) that supplies an
`fpred` and a passing certificate inherits eventual periodicity of the
inputs (`inputP_eventually_periodic`).

`checkCertP (famPred chs) = checkCert chs` and
`HStepP (famPred chs) = HStep chs` definitionally
(`checkCert_eq_checkCertP`, `HStep_eq_HStepP`) — the unsigned pipeline
is the first instance.
-/

namespace NormalNumbers.Adder

/-- Abstract one-step relation: under input `σ = x + 2y`, the deeper state
`s'` legally follows `s` via the predecessor map. -/
def HStepP (fpred : ℕ → ℕ → ℕ → Option ℕ) (s σ s' : ℕ) : Prop :=
  fpred (σ % 2) (σ / 2) s' = some s

/-- Parametric edge sweep, the body of `checkEdges` with `famPred chs`
abstracted. -/
def checkEdgesP (fpred : ℕ → ℕ → ℕ → Option ℕ) (S : ℕ) (live : ℕ → Bool)
    (rho omega : ℕ → ℕ) (forced : ℕ → Option (ℕ × ℕ)) : Bool :=
  (List.range S).all fun s' =>
    (List.range 4).all fun σ =>
      match fpred (σ % 2) (σ / 2) s' with
      | none => true
      | some s =>
        if live s then
          !live s' || (decide (rho s' < rho s)
            || (decide (forced s = some (σ, s')) && decide (rho s' = rho s)))
        else
          !live s' && decide (omega s' < omega s)

/-- Parametric (C1') check. -/
def checkForcedP (fpred : ℕ → ℕ → ℕ → Option ℕ) (S : ℕ) (live : ℕ → Bool)
    (forced : ℕ → Option (ℕ × ℕ)) : Bool :=
  (List.range S).all fun s =>
    match forced s with
    | none => true
    | some (σ, s') =>
      decide (σ < 4) && decide (s' < S) && live s'
        && decide (fpred (σ % 2) (σ / 2) s' = some s)

/-- The full parametric certificate check. -/
def checkCertP (fpred : ℕ → ℕ → ℕ → Option ℕ) (S : ℕ) (live : ℕ → Bool)
    (rho omega : ℕ → ℕ) (forced : ℕ → Option (ℕ × ℕ)) : Bool :=
  checkEdgesP fpred S live rho omega forced && checkForcedP fpred S live forced

theorem checkCert_eq_checkCertP (chs : List Channel) (S : ℕ) (live : ℕ → Bool)
    (rho omega : ℕ → ℕ) (forced : ℕ → Option (ℕ × ℕ)) :
    checkCert chs S live rho omega forced
      = checkCertP (famPred chs) S live rho omega forced := rfl

theorem HStep_eq_HStepP (chs : List Channel) :
    HStep chs = HStepP (famPred chs) := rfl

/-! ## Semantic extraction (parametric) -/

section Extraction

variable {fpred : ℕ → ℕ → ℕ → Option ℕ} {S : ℕ} {live : ℕ → Bool}
  {rho omega : ℕ → ℕ} {forced : ℕ → Option (ℕ × ℕ)}

theorem checkEdgesP_c1 (h : checkEdgesP fpred S live rho omega forced = true)
    {s σ s' : ℕ} (hσ : σ < 4) (hs' : s' < S)
    (hstep : HStepP fpred s σ s') (hl : live s = true) (hl' : live s' = true) :
    rho s' < rho s ∨ (forced s = some (σ, s') ∧ rho s' = rho s) := by
  unfold checkEdgesP at h
  rw [List.all_eq_true] at h
  have h₁ := h s' (List.mem_range.2 hs')
  rw [List.all_eq_true] at h₁
  have h₂ := h₁ σ (List.mem_range.2 hσ)
  unfold HStepP at hstep
  rw [hstep] at h₂
  simp only [hl, hl', if_true, Bool.not_true, Bool.false_or, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq] at h₂
  tauto

theorem checkEdgesP_c3' (h : checkEdgesP fpred S live rho omega forced = true)
    {s σ s' : ℕ} (hσ : σ < 4) (hs' : s' < S)
    (hstep : HStepP fpred s σ s') (hl : live s = false) :
    live s' = false ∧ omega s' < omega s := by
  unfold checkEdgesP at h
  rw [List.all_eq_true] at h
  have h₁ := h s' (List.mem_range.2 hs')
  rw [List.all_eq_true] at h₁
  have h₂ := h₁ σ (List.mem_range.2 hσ)
  unfold HStepP at hstep
  rw [hstep] at h₂
  simp [hl] at h₂
  exact h₂

theorem checkForcedP_spec (h : checkForcedP fpred S live forced = true)
    {s σ s' : ℕ} (hs : s < S) (hf : forced s = some (σ, s')) :
    σ < 4 ∧ s' < S ∧ live s' = true ∧ HStepP fpred s σ s' := by
  unfold checkForcedP at h
  rw [List.all_eq_true] at h
  have h₁ := h s (List.mem_range.2 hs)
  rw [hf] at h₁
  simp only [Bool.and_eq_true, decide_eq_true_eq, HStepP] at h₁ ⊢
  tauto

theorem checkCertP_edges (h : checkCertP fpred S live rho omega forced = true) :
    checkEdgesP fpred S live rho omega forced = true := by
  simp only [checkCertP, Bool.and_eq_true] at h
  exact h.1

theorem checkCertP_forced (h : checkCertP fpred S live rho omega forced = true) :
    checkForcedP fpred S live forced = true := by
  simp only [checkCertP, Bool.and_eq_true] at h
  exact h.2

end Extraction

/-! ## Descent (parametric) -/

section Descent

variable {fpred : ℕ → ℕ → ℕ → Option ℕ} {S : ℕ} {live : ℕ → Bool}
  {rho omega : ℕ → ℕ} {forced : ℕ → Option (ℕ × ℕ)}
  {st σi : ℕ → ℕ}

/-- (C3') kills dead states: along the path every state is live. -/
theorem pathP_live (hcert : checkCertP fpred S live rho omega forced = true)
    (hσ : ∀ m, σi m < 4) (hst : ∀ m, st m < S)
    (hstep : ∀ m, HStepP fpred (st m) (σi m) (st (m + 1))) :
    ∀ m, live (st m) = true := by
  by_contra hdead
  push Not at hdead
  obtain ⟨m₀, hm₀⟩ := hdead
  have hm₀' : live (st m₀) = false := by
    cases h : live (st m₀) with
    | true => exact absurd h hm₀
    | false => rfl
  have key : ∀ k, live (st (m₀ + k)) = false ∧ omega (st (m₀ + k)) + k ≤ omega (st m₀) := by
    intro k
    induction k with
    | zero => simpa using hm₀'
    | succ n ih =>
      have hc := checkEdgesP_c3' (checkCertP_edges hcert) (hσ (m₀ + n))
        (hst (m₀ + n + 1)) (hstep (m₀ + n)) ih.1
      refine ⟨?_, ?_⟩
      · show live (st (m₀ + n + 1)) = false
        exact hc.1
      · show omega (st (m₀ + n + 1)) + (n + 1) ≤ omega (st m₀)
        omega
  have := (key (omega (st m₀) + 1)).2
  omega

/-- Along a live path, `rho` is non-increasing. -/
theorem pathP_rho_antitone (hcert : checkCertP fpred S live rho omega forced = true)
    (hσ : ∀ m, σi m < 4) (hst : ∀ m, st m < S)
    (hstep : ∀ m, HStepP fpred (st m) (σi m) (st (m + 1)))
    (hlive : ∀ m, live (st m) = true) (m : ℕ) :
    rho (st (m + 1)) ≤ rho (st m) := by
  rcases checkEdgesP_c1 (checkCertP_edges hcert) (hσ m) (hst (m + 1)) (hstep m)
    (hlive m) (hlive (m + 1)) with h | h
  · exact h.le
  · exact h.2.le

/-- Beyond the last `rho` drop, every step is the `forced` edge. -/
theorem pathP_forced (hcert : checkCertP fpred S live rho omega forced = true)
    (hσ : ∀ m, σi m < 4) (hst : ∀ m, st m < S)
    (hstep : ∀ m, HStepP fpred (st m) (σi m) (st (m + 1))) :
    ∃ N, ∀ m, N ≤ m → forced (st m) = some (σi m, st (m + 1)) := by
  have hlive := pathP_live hcert hσ hst hstep
  have hanti := pathP_rho_antitone hcert hσ hst hstep hlive
  set A : Set ℕ := {v | ∃ m, rho (st m) = v} with hA
  have hAne : A.Nonempty := ⟨rho (st 0), 0, rfl⟩
  obtain ⟨N, hN⟩ : ∃ m, rho (st m) = sInf A := Nat.sInf_mem hAne
  refine ⟨N, fun m hm => ?_⟩
  have hconst : ∀ k, rho (st (N + k)) = sInf A := by
    intro k
    induction k with
    | zero => simpa using hN
    | succ n ih =>
      have h₁ : rho (st (N + n + 1)) ≤ rho (st (N + n)) := hanti (N + n)
      have h₂ : sInf A ≤ rho (st (N + n + 1)) := Nat.sInf_le ⟨N + n + 1, rfl⟩
      have : N + (n + 1) = N + n + 1 := by omega
      rw [this]
      omega
  have hm₁ : rho (st m) = sInf A := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    exact hconst k
  have hm₂ : rho (st (m + 1)) = sInf A := by
    have := hconst (m + 1 - N)
    rwa [show N + (m + 1 - N) = m + 1 from by omega] at this
  rcases checkEdgesP_c1 (checkCertP_edges hcert) (hσ m) (hst (m + 1)) (hstep m)
    (hlive m) (hlive (m + 1)) with h | h
  · omega
  · exact h.1

/-- Determinism beyond `N`: equal states propagate. -/
theorem pathP_determined {N : ℕ}
    (hforced : ∀ m, N ≤ m → forced (st m) = some (σi m, st (m + 1)))
    {m₁ m₂ : ℕ} (h₁ : N ≤ m₁) (h₂ : N ≤ m₂) (heq : st m₁ = st m₂) :
    ∀ k, st (m₁ + k) = st (m₂ + k) ∧ σi (m₁ + k) = σi (m₂ + k) := by
  intro k
  induction k with
  | zero =>
    constructor
    · simpa using heq
    · have ha := hforced m₁ h₁
      have hb := hforced m₂ h₂
      rw [heq, hb] at ha
      simpa using (Prod.mk.inj (Option.some.inj ha)).1.symm
  | succ n ih =>
    have ha := hforced (m₁ + n) (by omega)
    have hb := hforced (m₂ + n) (by omega)
    rw [ih.1, hb] at ha
    have hnext := (Prod.mk.inj (Option.some.inj ha)).2.symm
    have hin : forced (st (m₁ + n + 1)) = some (σi (m₁ + n + 1), st (m₁ + n + 1 + 1)) :=
      hforced _ (by omega)
    have hin' : forced (st (m₂ + n + 1)) = some (σi (m₂ + n + 1), st (m₂ + n + 1 + 1)) :=
      hforced _ (by omega)
    rw [show m₁ + (n + 1) = m₁ + n + 1 from by omega,
      show m₂ + (n + 1) = m₂ + n + 1 from by omega]
    rw [hnext, hin'] at hin
    exact ⟨hnext, (Prod.mk.inj (Option.some.inj hin)).1.symm⟩

/-- **Parametric descent**: along any infinite certified walk the input
sequence is eventually periodic. -/
theorem inputP_eventually_periodic
    (hcert : checkCertP fpred S live rho omega forced = true)
    (hσ : ∀ m, σi m < 4) (hst : ∀ m, st m < S)
    (hstep : ∀ m, HStepP fpred (st m) (σi m) (st (m + 1))) :
    ∃ N p, 0 < p ∧ ∀ m, N ≤ m → σi (m + p) = σi m := by
  obtain ⟨N, hforced⟩ := pathP_forced hcert hσ hst hstep
  have hmap : ∀ i ∈ Finset.range (S + 1), st (N + i) ∈ Finset.range S :=
    fun i _ => Finset.mem_range.2 (hst (N + i))
  obtain ⟨i, hi, j, hj, hij, hstij⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (by simp) hmap
  rcases Nat.lt_or_ge i j with hlt | hge
  · refine ⟨N + i, j - i, by omega, fun m hm => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    have hdet := pathP_determined hforced (by omega : N ≤ N + i)
      (by omega : N ≤ N + j) hstij k
    have := hdet.2
    rw [show N + i + k + (j - i) = N + j + k from by omega]
    exact this.symm
  · have hlt' : j < i := by omega
    refine ⟨N + j, i - j, by omega, fun m hm => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    have hdet := pathP_determined hforced (by omega : N ≤ N + j)
      (by omega : N ≤ N + i) hstij.symm k
    have := hdet.2
    rw [show N + j + k + (i - j) = N + i + k from by omega]
    exact this.symm

end Descent

end NormalNumbers.Adder
