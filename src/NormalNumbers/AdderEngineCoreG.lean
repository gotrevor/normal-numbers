/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderCert

/-!
# The alphabet-generalized certificate engine (base-g support)

Brief: `BRIEF-adder-tower.md` phase B; dossier
`EVIDENCE-2026-08-29-tower-formalization.md` §1.3–1.4.

Like `AdderEngineCore`, but the input alphabet is an arbitrary `[0, A)`
(base-g families use `A = g²`, symbol `σ = x + g·y`) and the step map
consumes the packed symbol directly: `fstep σ s' = some s`.  The descent
argument (`inputA_eventually_periodic`) is verbatim the same — it never
looked at the alphabet.

Transpose note (dossier §1.4): our `fstep` is the backward-deterministic
deep→shallow predecessor form throughout (as in the base-2 pipeline), so
the certificate conditions sweep edges `s' → s` of the transpose graph
directly; there is no separate forward graph anywhere in the Lean
development, hence no transpose-invariance step to take on faith — the
walk produced by shadowing and the graph checked by the certificate are
the SAME orientation by construction.
-/

namespace NormalNumbers.Adder

/-- Abstract one-step relation on packed symbols. -/
def HStepA (fstep : ℕ → ℕ → Option ℕ) (s σ s' : ℕ) : Prop :=
  fstep σ s' = some s

/-- Edge sweep over alphabet `[0, A)` and states `[0, S)`. -/
def checkEdgesA (fstep : ℕ → ℕ → Option ℕ) (A S : ℕ) (live : ℕ → Bool)
    (rho omega : ℕ → ℕ) (forced : ℕ → Option (ℕ × ℕ)) : Bool :=
  (List.range S).all fun s' =>
    (List.range A).all fun σ =>
      match fstep σ s' with
      | none => true
      | some s =>
        if live s then
          !live s' || (decide (rho s' < rho s)
            || (decide (forced s = some (σ, s')) && decide (rho s' = rho s)))
        else
          !live s' && decide (omega s' < omega s)

/-- (C1') check over alphabet `[0, A)`. -/
def checkForcedA (fstep : ℕ → ℕ → Option ℕ) (A S : ℕ) (live : ℕ → Bool)
    (forced : ℕ → Option (ℕ × ℕ)) : Bool :=
  (List.range S).all fun s =>
    match forced s with
    | none => true
    | some (σ, s') =>
      decide (σ < A) && decide (s' < S) && live s'
        && decide (fstep σ s' = some s)

/-- The full alphabet-generalized certificate check. -/
def checkCertA (fstep : ℕ → ℕ → Option ℕ) (A S : ℕ) (live : ℕ → Bool)
    (rho omega : ℕ → ℕ) (forced : ℕ → Option (ℕ × ℕ)) : Bool :=
  checkEdgesA fstep A S live rho omega forced && checkForcedA fstep A S live forced

/-- Per-state edge check — definitionally the body of `checkEdgesA`. -/
def edgeOkA (fstep : ℕ → ℕ → Option ℕ) (A : ℕ) (live : ℕ → Bool)
    (rho omega : ℕ → ℕ) (forced : ℕ → Option (ℕ × ℕ)) (s' : ℕ) : Bool :=
  (List.range A).all fun σ =>
    match fstep σ s' with
    | none => true
    | some s =>
      if live s then
        !live s' || (decide (rho s' < rho s)
          || (decide (forced s = some (σ, s')) && decide (rho s' = rho s)))
      else
        !live s' && decide (omega s' < omega s)

/-- Chunked sweep over `[lo, lo + n)`. -/
def checkEdgesOnA (fstep : ℕ → ℕ → Option ℕ) (A : ℕ) (live : ℕ → Bool)
    (rho omega : ℕ → ℕ) (forced : ℕ → Option (ℕ × ℕ)) (lo n : ℕ) : Bool :=
  (List.range n).all fun i => edgeOkA fstep A live rho omega forced (lo + i)

section Extraction

variable {fstep : ℕ → ℕ → Option ℕ} {A S : ℕ} {live : ℕ → Bool}
  {rho omega : ℕ → ℕ} {forced : ℕ → Option (ℕ × ℕ)}

theorem checkEdgesOnA_spec {lo n : ℕ}
    (h : checkEdgesOnA fstep A live rho omega forced lo n = true) :
    ∀ i, i < n → edgeOkA fstep A live rho omega forced (lo + i) = true := by
  unfold checkEdgesOnA at h
  rw [List.all_eq_true] at h
  exact fun i hi => h i (List.mem_range.2 hi)

theorem checkEdgesA_of_edgeOkA
    (h : ∀ s', s' < S → edgeOkA fstep A live rho omega forced s' = true) :
    checkEdgesA fstep A S live rho omega forced = true := by
  unfold checkEdgesA
  rw [List.all_eq_true]
  intro s' hs'
  exact h s' (List.mem_range.1 hs')

theorem checkCertA_of_parts
    (h₁ : checkEdgesA fstep A S live rho omega forced = true)
    (h₂ : checkForcedA fstep A S live forced = true) :
    checkCertA fstep A S live rho omega forced = true := by
  unfold checkCertA
  rw [h₁, h₂]
  rfl

theorem checkEdgesA_c1 (h : checkEdgesA fstep A S live rho omega forced = true)
    {s σ s' : ℕ} (hσ : σ < A) (hs' : s' < S)
    (hstep : HStepA fstep s σ s') (hl : live s = true) (hl' : live s' = true) :
    rho s' < rho s ∨ (forced s = some (σ, s') ∧ rho s' = rho s) := by
  unfold checkEdgesA at h
  rw [List.all_eq_true] at h
  have h₁ := h s' (List.mem_range.2 hs')
  rw [List.all_eq_true] at h₁
  have h₂ := h₁ σ (List.mem_range.2 hσ)
  unfold HStepA at hstep
  rw [hstep] at h₂
  simp only [hl, hl', if_true, Bool.not_true, Bool.false_or, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq] at h₂
  tauto

theorem checkEdgesA_c3' (h : checkEdgesA fstep A S live rho omega forced = true)
    {s σ s' : ℕ} (hσ : σ < A) (hs' : s' < S)
    (hstep : HStepA fstep s σ s') (hl : live s = false) :
    live s' = false ∧ omega s' < omega s := by
  unfold checkEdgesA at h
  rw [List.all_eq_true] at h
  have h₁ := h s' (List.mem_range.2 hs')
  rw [List.all_eq_true] at h₁
  have h₂ := h₁ σ (List.mem_range.2 hσ)
  unfold HStepA at hstep
  rw [hstep] at h₂
  simp [hl] at h₂
  exact h₂

theorem checkForcedA_spec (h : checkForcedA fstep A S live forced = true)
    {s σ s' : ℕ} (hs : s < S) (hf : forced s = some (σ, s')) :
    σ < A ∧ s' < S ∧ live s' = true ∧ HStepA fstep s σ s' := by
  unfold checkForcedA at h
  rw [List.all_eq_true] at h
  have h₁ := h s (List.mem_range.2 hs)
  rw [hf] at h₁
  simp only [Bool.and_eq_true, decide_eq_true_eq, HStepA] at h₁ ⊢
  tauto

theorem checkCertA_edges (h : checkCertA fstep A S live rho omega forced = true) :
    checkEdgesA fstep A S live rho omega forced = true := by
  simp only [checkCertA, Bool.and_eq_true] at h
  exact h.1

theorem checkCertA_forced (h : checkCertA fstep A S live rho omega forced = true) :
    checkForcedA fstep A S live forced = true := by
  simp only [checkCertA, Bool.and_eq_true] at h
  exact h.2

end Extraction

/-! ## Descent -/

section Descent

variable {fstep : ℕ → ℕ → Option ℕ} {A S : ℕ} {live : ℕ → Bool}
  {rho omega : ℕ → ℕ} {forced : ℕ → Option (ℕ × ℕ)}
  {st σi : ℕ → ℕ}

theorem pathA_live (hcert : checkCertA fstep A S live rho omega forced = true)
    (hσ : ∀ m, σi m < A) (hst : ∀ m, st m < S)
    (hstep : ∀ m, HStepA fstep (st m) (σi m) (st (m + 1))) :
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
      have hc := checkEdgesA_c3' (checkCertA_edges hcert) (hσ (m₀ + n))
        (hst (m₀ + n + 1)) (hstep (m₀ + n)) ih.1
      refine ⟨?_, ?_⟩
      · show live (st (m₀ + n + 1)) = false
        exact hc.1
      · show omega (st (m₀ + n + 1)) + (n + 1) ≤ omega (st m₀)
        omega
  have := (key (omega (st m₀) + 1)).2
  omega

theorem pathA_rho_antitone (hcert : checkCertA fstep A S live rho omega forced = true)
    (hσ : ∀ m, σi m < A) (hst : ∀ m, st m < S)
    (hstep : ∀ m, HStepA fstep (st m) (σi m) (st (m + 1)))
    (hlive : ∀ m, live (st m) = true) (m : ℕ) :
    rho (st (m + 1)) ≤ rho (st m) := by
  rcases checkEdgesA_c1 (checkCertA_edges hcert) (hσ m) (hst (m + 1)) (hstep m)
    (hlive m) (hlive (m + 1)) with h | h
  · exact h.le
  · exact h.2.le

theorem pathA_forced (hcert : checkCertA fstep A S live rho omega forced = true)
    (hσ : ∀ m, σi m < A) (hst : ∀ m, st m < S)
    (hstep : ∀ m, HStepA fstep (st m) (σi m) (st (m + 1))) :
    ∃ N, ∀ m, N ≤ m → forced (st m) = some (σi m, st (m + 1)) := by
  have hlive := pathA_live hcert hσ hst hstep
  have hanti := pathA_rho_antitone hcert hσ hst hstep hlive
  set B : Set ℕ := {v | ∃ m, rho (st m) = v} with hB
  have hBne : B.Nonempty := ⟨rho (st 0), 0, rfl⟩
  obtain ⟨N, hN⟩ : ∃ m, rho (st m) = sInf B := Nat.sInf_mem hBne
  refine ⟨N, fun m hm => ?_⟩
  have hconst : ∀ k, rho (st (N + k)) = sInf B := by
    intro k
    induction k with
    | zero => simpa using hN
    | succ n ih =>
      have h₁ : rho (st (N + n + 1)) ≤ rho (st (N + n)) := hanti (N + n)
      have h₂ : sInf B ≤ rho (st (N + n + 1)) := Nat.sInf_le ⟨N + n + 1, rfl⟩
      have : N + (n + 1) = N + n + 1 := by omega
      rw [this]
      omega
  have hm₁ : rho (st m) = sInf B := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    exact hconst k
  have hm₂ : rho (st (m + 1)) = sInf B := by
    have := hconst (m + 1 - N)
    rwa [show N + (m + 1 - N) = m + 1 from by omega] at this
  rcases checkEdgesA_c1 (checkCertA_edges hcert) (hσ m) (hst (m + 1)) (hstep m)
    (hlive m) (hlive (m + 1)) with h | h
  · omega
  · exact h.1

theorem pathA_determined {N : ℕ}
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

/-- **Descent** (alphabet-generalized): along any infinite certified walk
the input sequence is eventually periodic. -/
theorem inputA_eventually_periodic
    (hcert : checkCertA fstep A S live rho omega forced = true)
    (hσ : ∀ m, σi m < A) (hst : ∀ m, st m < S)
    (hstep : ∀ m, HStepA fstep (st m) (σi m) (st (m + 1))) :
    ∃ N p, 0 < p ∧ ∀ m, N ≤ m → σi (m + p) = σi m := by
  obtain ⟨N, hforced⟩ := pathA_forced hcert hσ hst hstep
  have hmap : ∀ i ∈ Finset.range (S + 1), st (N + i) ∈ Finset.range S :=
    fun i _ => Finset.mem_range.2 (hst (N + i))
  obtain ⟨i, hi, j, hj, hij, hstij⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (by simp) hmap
  rcases Nat.lt_or_ge i j with hlt | hge
  · refine ⟨N + i, j - i, by omega, fun m hm => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    have hdet := pathA_determined hforced (by omega : N ≤ N + i)
      (by omega : N ≤ N + j) hstij k
    have := hdet.2
    rw [show N + i + k + (j - i) = N + j + k from by omega]
    exact this.symm
  · have hlt' : j < i := by omega
    refine ⟨N + j, i - j, by omega, fun m hm => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    have hdet := pathA_determined hforced (by omega : N ≤ N + j)
      (by omega : N ≤ N + i) hstij.symm k
    have := hdet.2
    rw [show N + j + k + (i - j) = N + i + k from by omega]
    exact this.symm

end Descent

end NormalNumbers.Adder
