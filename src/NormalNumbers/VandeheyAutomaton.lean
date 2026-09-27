/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Headline

/-!
# The automaton transfer principle — a replacement for Vandehey's §3

Vandehey 2017 §3 establishes that for a CF-normal `x` and any transducer state `M`, the
skew-product orbit `(Tⁱx, Mᵢ)` equidistributes.  His proof runs through the
Pyatetskii-Shapiro criterion in the Moshchevitin–Shkredov form, which Airey–Mance
(arXiv:1912.10265) show is **false on non-compact spaces** such as the CF space; see
`LiteratureVandehey.lean` and `papers/vandehey-2017-open-problem-attack-map.md` §6.1.

This module builds a different engine, which needs no hot-spot criterion, no tightness
lemma, no ergodicity and no soft analysis — only CF-normality of `x` plus the repo's
mixing stack:

> **Automaton transfer.**  Let `δ : S → ℕ → S` be a deterministic automaton on a finite
> state set reading CF digits, and suppose some genuine word `z` is *synchronizing*
> (reading `z` lands in the same state whatever state you started in).  Then for every
> target state `t` and every genuine word `v`, the joint frequency
> `#{i < n : digits of x at i…i+|v|−1 spell v, and the state after i digits is t}/n`
> converges, to a limit independent of both the initial state and of **which** CF-normal
> `x` is used.

The mechanism is elementary and pathwise, not distributional: after a synchronizing word
the state forgets its past, so the state at time `i` is a function of the last `L` digits
alone — *provided* `z` occurs in that window.  The exceptional `i` (no `z` in the last `L`
digits) have frequency `→ γ(no z in L digits)` by CF-normality, and that tends to `0` in
`L` by mixing (`CFPsiPin` / `philipp_psi_mixing`).  So the joint count is, up to a
vanishing error, a *finite* sum of ordinary cylinder window counts — each of which
CF-normality pins to `γ` of a cylinder.  Hence the limit exists and is `x`-independent.

Status: the deterministic core (this section) is proved; the frequency assembly is the
open leaf `exists_jointFreq_limit`.
-/

namespace NormalNumbers

open Filter

namespace VandeheyAut

variable {S : Type*}

/-! ## Automata on CF digits -/

/-- Run a deterministic automaton `δ` from state `s` over a list of CF digits. -/
def runState (δ : S → ℕ → S) (s : S) (w : List ℕ) : S := w.foldl δ s

@[simp] lemma runState_nil (δ : S → ℕ → S) (s : S) : runState δ s [] = s := rfl

@[simp] lemma runState_cons (δ : S → ℕ → S) (s : S) (a : ℕ) (w : List ℕ) :
    runState δ s (a :: w) = runState δ (δ s a) w := rfl

lemma runState_append (δ : S → ℕ → S) (s : S) (u w : List ℕ) :
    runState δ s (u ++ w) = runState δ (runState δ s u) w := by
  simp [runState, List.foldl_append]

/-- `z` is **synchronizing** for `δ`: reading `z` erases the initial state. -/
def Synchronizing (δ : S → ℕ → S) (z : List ℕ) : Prop :=
  ∀ s s' : S, runState δ s z = runState δ s' z

/-- The state reached after reading a synchronizing word, from a reference state `s₁`. -/
def syncTarget (δ : S → ℕ → S) (s₁ : S) (z : List ℕ) : S := runState δ s₁ z

lemma runState_sync_append {δ : S → ℕ → S} {z : List ℕ} (hz : Synchronizing δ z)
    (s s₁ : S) (u r : List ℕ) :
    runState δ s (u ++ z ++ r) = runState δ (syncTarget δ s₁ z) r := by
  rw [List.append_assoc, runState_append, runState_append, hz _ s₁, syncTarget]

/-! ## CF digit words and windows -/

/-- The first `n` CF digits of `x`, as a list. -/
noncomputable def cfWord (x : ℝ) (n : ℕ) : List ℕ := (List.range n).map (cfDigit x)

/-- The CF digits of `x` at positions `m, …, m+ℓ−1`. -/
noncomputable def cfWindow (x : ℝ) (m ℓ : ℕ) : List ℕ :=
  (List.range ℓ).map (fun k => cfDigit x (m + k))

@[simp] lemma cfWindow_zero_length (x : ℝ) (m : ℕ) : cfWindow x m 0 = [] := by
  simp [cfWindow]

@[simp] lemma cfWindow_from_zero (x : ℝ) (ℓ : ℕ) : cfWindow x 0 ℓ = cfWord x ℓ := by
  simp [cfWindow, cfWord]

lemma cfWindow_length (x : ℝ) (m ℓ : ℕ) : (cfWindow x m ℓ).length = ℓ := by
  simp [cfWindow]

/-- The prefix splits at any point into a prefix and a window. -/
lemma cfWord_add (x : ℝ) (m ℓ : ℕ) :
    cfWord x (m + ℓ) = cfWord x m ++ cfWindow x m ℓ := by
  simp [cfWord, cfWindow, List.range_add, List.map_append, List.map_map,
    Function.comp_def]

/-- Windows concatenate. -/
lemma cfWindow_add (x : ℝ) (m ℓ₁ ℓ₂ : ℕ) :
    cfWindow x m (ℓ₁ + ℓ₂) = cfWindow x m ℓ₁ ++ cfWindow x (m + ℓ₁) ℓ₂ := by
  have hc : (fun k => cfDigit x (m + k)) ∘ (fun k => ℓ₁ + k)
      = fun k => cfDigit x (m + ℓ₁ + k) := by
    funext k
    show cfDigit x (m + (ℓ₁ + k)) = cfDigit x (m + ℓ₁ + k)
    rw [Nat.add_assoc]
  unfold cfWindow
  rw [List.range_add, List.map_append, List.map_map, hc]

/-! ## The state of the automaton along the CF expansion -/

/-- The automaton state after reading the first `i` CF digits of `x`. -/
noncomputable def stateAt (δ : S → ℕ → S) (s₀ : S) (x : ℝ) (i : ℕ) : S :=
  runState δ s₀ (cfWord x i)

/-- **The deterministic core.**  If a synchronizing word `z` occurs inside the window of
`L` digits ending at position `m + L`, then the state there is a function of that window
alone: it does not depend on the initial state, nor on anything before position `m`. -/
theorem stateAt_eq_of_window_sync {δ : S → ℕ → S} {z : List ℕ}
    (hz : Synchronizing δ z) (s₀ s₁ : S) (x : ℝ) (m L : ℕ) {u r : List ℕ}
    (hw : cfWindow x m L = u ++ z ++ r) :
    stateAt δ s₀ x (m + L) = runState δ (syncTarget δ s₁ z) r := by
  rw [stateAt, cfWord_add, hw, ← List.append_assoc, ← List.append_assoc,
    runState_sync_append hz]

/-- Corollary: the state is *independent of the initial state* as soon as a synchronizing
word has been read. -/
theorem stateAt_indep_of_init {δ : S → ℕ → S} {z : List ℕ}
    (hz : Synchronizing δ z) (s₀ s₀' : S) (x : ℝ) (m L : ℕ) {u r : List ℕ}
    (hw : cfWindow x m L = u ++ z ++ r) :
    stateAt δ s₀ x (m + L) = stateAt δ s₀' x (m + L) := by
  rw [stateAt_eq_of_window_sync hz s₀ s₀ x m L hw,
    stateAt_eq_of_window_sync hz s₀' s₀ x m L hw]

/-- Two points whose digit windows agree on a stretch containing a synchronizing word
have the same state at the end of that stretch — the *pathwise* merging that Vandehey's
§3 obtains only distributionally (and only through the defective criterion). -/
theorem stateAt_eq_of_window_eq {δ : S → ℕ → S} {z : List ℕ}
    (hz : Synchronizing δ z) (s₀ s₀' : S) (x y : ℝ) (m m' L : ℕ)
    (hxy : cfWindow x m L = cfWindow y m' L) {u r : List ℕ}
    (hw : cfWindow x m L = u ++ z ++ r) :
    stateAt δ s₀ x (m + L) = stateAt δ s₀' y (m' + L) := by
  rw [stateAt_eq_of_window_sync hz s₀ s₀ x m L hw,
    stateAt_eq_of_window_sync hz s₀' s₀ y m' L (hxy ▸ hw)]

/-! ## The joint count, and the transfer statement -/

/-- The joint count: indices `i < n` at which the digit window of length `v.length`
starting at `i` spells `v` **and** the automaton is in state `t` after `i` digits. -/
noncomputable def jointCount (δ : S → ℕ → S) [DecidableEq S] (s₀ : S) (t : S)
    (v : List ℕ) (x : ℝ) (n : ℕ) : ℕ :=
  ((Finset.range n).filter
    (fun i => cfWindow x i v.length = v ∧ stateAt δ s₀ x i = t)).card

/-- **The automaton transfer principle** (the replacement for Vandehey's Theorem 3.1).
For a finite-state automaton with a synchronizing genuine word, the joint
(window, state) frequency along a CF-normal `x` converges, to a limit that depends on
neither the initial state nor which CF-normal `x` was used.

Proof plan (see the module docstring): fix a lookback `L`.  Split the indices `i` by the
window `q = cfWindow x (i−L) L`.  For those `q` containing `z` the state is
`runState δ (syncTarget δ s₁ z) r`, a function of `q` alone, so the joint count is a
finite sum `Σ_{q ∈ Q_t} #{i : window of length L+|v| at i−L spells q ++ v}` — and each of
those is a plain window count, whose frequency CF-normality sends to `γ(I_{q ++ v})`.
The residue is `#{i < n : z does not occur in cfWindow x (i−L) L} + O(L)`, whose
frequency CF-normality sends to `γ(Z_L)`, `Z_L` = the `z`-free length-`L` cylinders; and
`γ(Z_L) → 0` in `L` by mixing.  A Cauchy argument in `L` then produces the limit,
manifestly as `lim_L Σ_{q ∈ Q_t} γ(I_{q ++ v})`, which mentions no `x`. -/
theorem exists_jointFreq_limit {S : Type*} [Fintype S] [DecidableEq S]
    (δ : S → ℕ → S) {z : List ℕ} (hzne : z ≠ []) (hzpos : ∀ a ∈ z, 1 ≤ a)
    (hz : Synchronizing δ z) (t : S) (v : List ℕ) (hvne : v ≠ [])
    (hvpos : ∀ a ∈ v, 1 ≤ a) :
    ∃ L : ℝ, ∀ (s₀ : S) (x : ℝ), IsCFNormal x →
      Tendsto (fun n => (jointCount δ s₀ t v x n : ℝ) / n) atTop (nhds L) := by
  sorry

end VandeheyAut

end NormalNumbers
