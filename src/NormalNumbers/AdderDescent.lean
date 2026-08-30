/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderCert

/-!
# Descent: every infinite certified walk is eventually periodic (module 4)

Brief: `BRIEF-adder-disjunction-formalization.md` §"Descent glue".

From an infinite `HStep` path with all states `< S` and a certificate
passing `checkCert`:

* if any state were dead, (C3') would force an infinite strictly decreasing
  `omega` chain — impossible (`path_live`);
* so `rho` is non-increasing along the path (`C1`); it attains its infimum
  at some `N` and is constant beyond;
* beyond `N` every step must be the `forced` edge (the strict-drop branch of
  (C1) is unavailable), so both the successor state **and the input** are
  functions of the state (`path_forced`);
* pigeonhole on `[0, S)` yields a repeated state, and determinism propagates
  it: the input sequence is eventually periodic
  (`input_eventually_periodic`).

No König's lemma, no compactness — pure `Nat` bookkeeping.
-/

namespace NormalNumbers.Adder

variable {chs : List Channel} {S : ℕ} {live : ℕ → Bool}
  {rho omega : ℕ → ℕ} {forced : ℕ → Option (ℕ × ℕ)}
  {st σi : ℕ → ℕ}

/-- (C3') kills dead states: along the path every state is live. -/
theorem path_live (hcert : checkCert chs S live rho omega forced = true)
    (hσ : ∀ m, σi m < 4) (hst : ∀ m, st m < S)
    (hstep : ∀ m, HStep chs (st m) (σi m) (st (m + 1))) :
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
      have hc := checkEdges_c3' (checkCert_edges hcert) (hσ (m₀ + n))
        (hst (m₀ + n + 1)) (hstep (m₀ + n)) ih.1
      refine ⟨?_, ?_⟩
      · show live (st (m₀ + n + 1)) = false
        exact hc.1
      · show omega (st (m₀ + n + 1)) + (n + 1) ≤ omega (st m₀)
        omega
  have := (key (omega (st m₀) + 1)).2
  omega

/-- Along a live path, `rho` is non-increasing. -/
theorem path_rho_antitone (hcert : checkCert chs S live rho omega forced = true)
    (hσ : ∀ m, σi m < 4) (hst : ∀ m, st m < S)
    (hstep : ∀ m, HStep chs (st m) (σi m) (st (m + 1)))
    (hlive : ∀ m, live (st m) = true) (m : ℕ) :
    rho (st (m + 1)) ≤ rho (st m) := by
  rcases checkEdges_c1 (checkCert_edges hcert) (hσ m) (hst (m + 1)) (hstep m)
    (hlive m) (hlive (m + 1)) with h | h
  · exact h.le
  · exact h.2.le

/-- Beyond the last `rho` drop, every step is the `forced` edge: successor
state **and input** are functions of the state. -/
theorem path_forced (hcert : checkCert chs S live rho omega forced = true)
    (hσ : ∀ m, σi m < 4) (hst : ∀ m, st m < S)
    (hstep : ∀ m, HStep chs (st m) (σi m) (st (m + 1))) :
    ∃ N, ∀ m, N ≤ m → forced (st m) = some (σi m, st (m + 1)) := by
  have hlive := path_live hcert hσ hst hstep
  have hanti := path_rho_antitone hcert hσ hst hstep hlive
  -- the rho values attain their infimum at some N
  set A : Set ℕ := {v | ∃ m, rho (st m) = v} with hA
  have hAne : A.Nonempty := ⟨rho (st 0), 0, rfl⟩
  obtain ⟨N, hN⟩ : ∃ m, rho (st m) = sInf A := Nat.sInf_mem hAne
  refine ⟨N, fun m hm => ?_⟩
  -- rho is constant (= sInf A) from N on
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
  rcases checkEdges_c1 (checkCert_edges hcert) (hσ m) (hst (m + 1)) (hstep m)
    (hlive m) (hlive (m + 1)) with h | h
  · omega
  · exact h.1

/-- Determinism beyond `N`: equal states propagate. -/
theorem path_determined {N : ℕ}
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

/-- **Descent**: along any infinite certified walk the input sequence is
eventually periodic. -/
theorem input_eventually_periodic
    (hcert : checkCert chs S live rho omega forced = true)
    (hσ : ∀ m, σi m < 4) (hst : ∀ m, st m < S)
    (hstep : ∀ m, HStep chs (st m) (σi m) (st (m + 1))) :
    ∃ N p, 0 < p ∧ ∀ m, N ≤ m → σi (m + p) = σi m := by
  obtain ⟨N, hforced⟩ := path_forced hcert hσ hst hstep
  -- pigeonhole: two equal states among st (N), …, st (N + S)
  have hmap : ∀ i ∈ Finset.range (S + 1), st (N + i) ∈ Finset.range S :=
    fun i _ => Finset.mem_range.2 (hst (N + i))
  obtain ⟨i, hi, j, hj, hij, hstij⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (by simp) hmap
  -- normalize to i < j
  rcases Nat.lt_or_ge i j with hlt | hge
  · refine ⟨N + i, j - i, by omega, fun m hm => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    have hdet := path_determined hforced (by omega : N ≤ N + i)
      (by omega : N ≤ N + j) hstij k
    have := hdet.2
    rw [show N + i + k + (j - i) = N + j + k from by omega]
    exact this.symm
  · have hlt' : j < i := by omega
    refine ⟨N + j, i - j, by omega, fun m hm => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    have hdet := path_determined hforced (by omega : N ≤ N + j)
      (by omega : N ≤ N + i) hstij.symm k
    have := hdet.2
    rw [show N + j + k + (i - j) = N + i + k from by omega]
    exact this.symm

end NormalNumbers.Adder
