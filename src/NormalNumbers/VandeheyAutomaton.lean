/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Headline
import NormalNumbers.OccurrenceCountEquiv

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

## RETIRED 2026-09-28 — the `Synchronizing` hypothesis is unsatisfiable here

`probes/cf_transducer_sync.py` (`archive/probe/PROBE-2026-09-27-transducer-not-synchronizing.md`)
decided synchronizability for the det-`±D` CF transducer that Theorem 1.1 needs: it is NOT
synchronizing, for a structural reason no search bound is needed to see.  The reachable state
set fibres over `ℙ¹(ℤ/D)` by the row-lattice class of the state matrix, the class evolves by
`c ↦ c · B_a`, and every `B_a` acts **bijectively** on `ℙ¹(ℤ/D)`.  A bijective quotient never
forgets, so no input word can merge two states of different class — and there are `D + 1`
classes.

That obstruction is now a theorem here: `not_synchronizing_of_injective_quotient`.  Every
statement of this section carrying a `Synchronizing` hypothesis is therefore **vacuous for
the intended automaton**, and the frequency assembly that used to sit at the end of the file
as the sorried `exists_jointFreq_limit` is removed: its replacement is
`VandeheyCocycle.tendsto_jointCount_of_classEquidistribution`, which asks instead for
equidistribution of the `ℙ¹(ℤ/D)` cocycle — the crux the probe identified.  Maze row:
`hall_vandehey_synchronizing_transducer`.
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


/-! ## Uniform-length transitivity from a bounded diameter plus one self-loop

`VandeheyState.stateHorizonIntegral_pin_of_reach` (and the older pin) asks for a word of one
*fixed* length `M` joining every ordered pair of states — a Doeblin condition, not mere
connectivity.  Bare strong connectivity is not enough: a bipartite automaton is connected but
reaches half its states only at even times, and that is exactly what happens to the Raney
transducer read on balanced matrices of determinant `±D`, where a digit flips the sign of the
determinant.

The cheap repair is a **single self-loop**.  If some state `z` is fixed by some genuine digit
and the automaton has diameter `≤ r`, then for every `M ≥ 2r` and every pair `d, s` the word

  `(d → z)  ++  (the loop digit, repeated)  ++  (z → s)`

has length exactly `M`.  One loop kills every periodicity at once. -/

/-- **Uniform-length transitivity** from a diameter bound plus one self-loop. -/
theorem exists_uniform_reach_of_loop (δ : S → ℕ → S) {z : S} {a₀ : ℕ} (ha₀ : 1 ≤ a₀)
    (hz : δ z a₀ = z) {r : ℕ}
    (hconn : ∀ d s : S, ∃ w : List ℕ, w.length ≤ r ∧ (∀ a ∈ w, 1 ≤ a) ∧
      runState δ d w = s)
    {M : ℕ} (hM : 2 * r ≤ M) (d s : S) :
    ∃ w : List ℕ, w.length = M ∧ (∀ a ∈ w, 1 ≤ a) ∧ runState δ d w = s := by
  obtain ⟨u, hulen, hupos, hurun⟩ := hconn d z
  obtain ⟨v, hvlen, hvpos, hvrun⟩ := hconn z s
  have hloop : ∀ k : ℕ, runState δ z (List.replicate k a₀) = z := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [List.replicate_succ, runState_cons, hz, ih]
  refine ⟨u ++ List.replicate (M - u.length - v.length) a₀ ++ v, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_replicate]
    omega
  · intro a ha
    simp only [List.mem_append, List.mem_replicate] at ha
    rcases ha with (ha | ha) | ha
    · exact hupos a ha
    · exact ha.2 ▸ ha₀
    · exact hvpos a ha
  · rw [runState_append, runState_append, hurun, hloop, hvrun]

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

/-- The state after `i + k` digits is the automaton run over the length-`k` window at `i`,
started from the state at `i`.  No synchronization needed — this is the plain cocycle
identity, and it is what lets a *non*-synchronizing automaton still be handled. -/
theorem stateAt_add (δ : S → ℕ → S) (s₀ : S) (x : ℝ) (i k : ℕ) :
    stateAt δ s₀ x (i + k) = runState δ (stateAt δ s₀ x i) (cfWindow x i k) := by
  rw [stateAt, stateAt, cfWord_add, runState_append]

/-- Truncating a window on the right. -/
lemma cfWindow_take (x : ℝ) (i m k : ℕ) (h : k ≤ m) :
    (cfWindow x i m).take k = cfWindow x i k := by
  obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_le h
  subst hl
  rw [cfWindow_add]
  exact List.take_left' (cfWindow_length x i k)

/-- Truncating a window on the left. -/
lemma cfWindow_drop (x : ℝ) (i m k : ℕ) (h : k ≤ m) :
    (cfWindow x i m).drop k = cfWindow x (i + k) (m - k) := by
  obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_le h
  subst hl
  rw [cfWindow_add, List.drop_left' (cfWindow_length x i k)]
  congr 1
  omega

/-- A sub-window of a window is a window. -/
lemma cfWindow_drop_take (x : ℝ) (i m k l : ℕ) (h : k + l ≤ m) :
    ((cfWindow x i m).drop k).take l = cfWindow x (i + k) l := by
  rw [cfWindow_drop x i m k (by omega), cfWindow_take x (i + k) (m - k) l (by omega)]

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

/-- **The state is `runState` of the lookback window itself.**  No canonical choice of
occurrence is needed: if `z` occurs anywhere in the window, running the automaton over the
window *from any state at all* already gives the true state, because the run passes through
`z` and forgets where it started.  This is the exact form the counting argument wants — the
state is a function of the window, computed by the window. -/
theorem stateAt_eq_runState_window {δ : S → ℕ → S} {z : List ℕ}
    (hz : Synchronizing δ z) (s₀ s₁ : S) (x : ℝ) (m L : ℕ)
    (hfac : z <:+: cfWindow x m L) :
    stateAt δ s₀ x (m + L) = runState δ s₁ (cfWindow x m L) := by
  obtain ⟨u, r, hur⟩ := hfac
  rw [stateAt_eq_of_window_sync hz s₀ s₁ x m L hur.symm, ← hur,
    runState_sync_append hz s₁ s₁ u r]

/-! ## Windows and the repo's occurrence count -/

lemma cfWindow_eq_range' (x : ℝ) (m ℓ : ℕ) :
    cfWindow x m ℓ = (List.range' m ℓ).map (cfDigit x) :=
  (map_range'_eq (cfDigit x) ℓ m).symm

/-- `occStart` counts exactly the positions whose window spells `w`. -/
lemma occStart_eq_card_window (x : ℝ) (w : List ℕ) (n : ℕ) :
    occStart w (cfDigit x) n
      = ((Finset.range n).filter (fun i => w = cfWindow x i w.length)).card := by
  simp [occStart, cfWindow_eq_range']

/-- **CF-normality, restated on windows**: for CF-normal `x` the frequency of positions
`i < n` whose length-`|w|` window spells `w` tends to `γ(I_w)`.  (The repo's
`tendsto_occStart_iff` absorbs the `O(|w|)` right-edge discrepancy between the two
counting conventions.) -/
theorem tendsto_windowFreq {x : ℝ} (hx : IsCFNormal x) (w : List ℕ) (hne : w ≠ [])
    (hpos : ∀ a ∈ w, 1 ≤ a) :
    Tendsto (fun n => (((Finset.range n).filter
        (fun i => w = cfWindow x i w.length)).card : ℝ) / n) atTop
      (nhds (gaussMeasure (cfCylinder w)).toReal) := by
  have h := (tendsto_occStart_iff w hne (cfDigit x) _).2 (hx w hne hpos)
  simpa [occStart_eq_card_window] using h

/-! ## Bounded-digit words, and the exact count decomposition -/

/-- The words of length `n` with all digits in `[1, K]`.  Finite, unlike the set of all
length-`n` CF words: this is where the digit truncation (the elementary stand-in for
Airey–Mance tightness) enters. -/
def boundedWords (K : ℕ) : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | (n + 1) => (Finset.Icc 1 K).biUnion fun a => (boundedWords K n).image fun q => a :: q

lemma mem_boundedWords {K : ℕ} : ∀ (n : ℕ) (q : List ℕ),
    q ∈ boundedWords K n ↔ q.length = n ∧ ∀ a ∈ q, 1 ≤ a ∧ a ≤ K := by
  intro n
  induction n with
  | zero =>
    intro q
    simp only [boundedWords, Finset.mem_singleton]
    constructor
    · rintro rfl; simp
    · rintro ⟨h, -⟩; exact List.length_eq_zero_iff.mp h
  | succ n ih =>
    intro q
    simp only [boundedWords, Finset.mem_biUnion, Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨a, ⟨ha1, ha2⟩, q', hq', rfl⟩
      rw [ih] at hq'
      refine ⟨by simp [hq'.1], fun b hb => ?_⟩
      rcases List.mem_cons.mp hb with h | h
      · exact h ▸ ⟨ha1, ha2⟩
      · exact hq'.2 b h
    · rintro ⟨hlen, hall⟩
      cases q with
      | nil => simp at hlen
      | cons a q' =>
        refine ⟨a, ⟨(hall a (by simp)).1, (hall a (by simp)).2⟩, q', ?_, rfl⟩
        rw [ih]
        exact ⟨by simpa using hlen, fun b hb => hall b (by simp [hb])⟩

/-- The joint condition at a position whose lookback window contains `z`, rewritten as a
plain condition on the window of length `L + |v|`. -/
theorem joint_iff_window {δ : S → ℕ → S} {z : List ℕ} (hz : Synchronizing δ z)
    (s₀ s₁ : S) (t : S) (x : ℝ) (v : List ℕ) (L j : ℕ)
    (hfac : z <:+: cfWindow x j L) :
    (v = cfWindow x (j + L) v.length ∧ stateAt δ s₀ x (j + L) = t)
      ↔ (runState δ s₁ (cfWindow x j L) = t ∧
          cfWindow x j L ++ v = cfWindow x j (L + v.length)) := by
  rw [stateAt_eq_runState_window hz s₀ s₁ x j L hfac, cfWindow_add]
  constructor
  · rintro ⟨hv, hs⟩; exact ⟨hs, by rw [← hv]⟩
  · rintro ⟨hs, hq⟩
    exact ⟨List.append_cancel_left hq, hs⟩

/-- **The exact count decomposition.**  Among positions `j < n` whose lookback window has
all digits in `[1,K]` and contains the synchronizing word `z`, the joint (window, state)
condition is *equivalent* to a plain window condition, and the positions are partitioned by
their lookback window.  So the joint count is a **finite** sum of ordinary window counts —
no measure theory, no hot-spot criterion.  (`s₁` is an arbitrary reference state: the sum
does not depend on it, by `stateAt_eq_runState_window`.) -/
theorem card_joint_good_eq_sum {δ : S → ℕ → S} [DecidableEq S] {z : List ℕ}
    (hz : Synchronizing δ z) (s₀ s₁ : S) (t : S) (x : ℝ) (v : List ℕ) (K L n : ℕ) :
    ((Finset.range n).filter (fun j =>
        cfWindow x j L ∈ boundedWords K L ∧ z <:+: cfWindow x j L ∧
        v = cfWindow x (j + L) v.length ∧ stateAt δ s₀ x (j + L) = t)).card
      = ∑ q ∈ (boundedWords K L).filter (fun q => z <:+: q ∧ runState δ s₁ q = t),
          ((Finset.range n).filter (fun j => q ++ v = cfWindow x j (L + v.length))).card := by
  classical
  set T : Finset (List ℕ) :=
    (boundedWords K L).filter (fun q => z <:+: q ∧ runState δ s₁ q = t) with hT
  set S₀ : Finset ℕ := (Finset.range n).filter (fun j =>
      cfWindow x j L ∈ boundedWords K L ∧ z <:+: cfWindow x j L ∧
      v = cfWindow x (j + L) v.length ∧ stateAt δ s₀ x (j + L) = t) with hS₀
  have hmaps : ∀ j ∈ S₀, cfWindow x j L ∈ T := by
    intro j hj
    simp only [hS₀, Finset.mem_filter] at hj
    obtain ⟨-, hb, hfac, hv, hs⟩ := hj
    refine Finset.mem_filter.mpr ⟨hb, hfac, ?_⟩
    rw [← stateAt_eq_runState_window hz s₀ s₁ x j L hfac]
    exact hs
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun q hq => ?_
  congr 1
  simp only [hT, Finset.mem_filter] at hq
  obtain ⟨hqb, hqfac, hqs⟩ := hq
  have hqlen : q.length = L := ((mem_boundedWords L q).mp hqb).1
  ext j
  simp only [hS₀, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨⟨hjn, -, hfac, hv, hs⟩, hqeq⟩
    refine ⟨hjn, ?_⟩
    rw [← hqeq]
    exact ((joint_iff_window hz s₀ s₁ t x v L j hfac).mp ⟨hv, hs⟩).2
  · rintro ⟨hjn, hqv⟩
    have hwin : cfWindow x j L = q := by
      have h := hqv
      rw [cfWindow_add] at h
      have := (List.append_inj h (by rw [hqlen, cfWindow_length])).1
      exact this.symm
    have hfac : z <:+: cfWindow x j L := hwin ▸ hqfac
    have hjw := (joint_iff_window hz s₀ s₁ t x v L j hfac).mpr
      ⟨by rw [hwin]; exact hqs, by rw [hwin]; exact hqv⟩
    exact ⟨⟨hjn, hwin ▸ hqb, hfac, hjw.1, hjw.2⟩, hwin⟩

/-! ## The joint count, and the transfer statement -/

/-- The joint count: indices `i < n` at which the digit window of length `v.length`
starting at `i` spells `v` **and** the automaton is in state `t` after `i` digits. -/
noncomputable def jointSet (δ : S → ℕ → S) [DecidableEq S] (s₀ : S) (t : S)
    (v : List ℕ) (x : ℝ) (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter fun i => v = cfWindow x i v.length ∧ stateAt δ s₀ x i = t

lemma mem_jointSet {δ : S → ℕ → S} [DecidableEq S] {s₀ t : S} {v : List ℕ} {x : ℝ}
    {n i : ℕ} : i ∈ jointSet δ s₀ t v x n ↔
      i < n ∧ v = cfWindow x i v.length ∧ stateAt δ s₀ x i = t := by
  simp only [jointSet, Finset.mem_filter, Finset.mem_range]

noncomputable def jointCount (δ : S → ℕ → S) [DecidableEq S] (s₀ : S) (t : S)
    (v : List ℕ) (x : ℝ) (n : ℕ) : ℕ := (jointSet δ s₀ t v x n).card

lemma jointCount_eq_card (δ : S → ℕ → S) [DecidableEq S] (s₀ t : S) (v : List ℕ)
    (x : ℝ) (n : ℕ) : jointCount δ s₀ t v x n = (jointSet δ s₀ t v x n).card := rfl

/-! ## The digit tail -/

lemma cfWindow_one (x : ℝ) (i : ℕ) : cfWindow x i 1 = [cfDigit x i] := by
  simp [cfWindow]

lemma card_digit_eq_card_window (x : ℝ) (k n : ℕ) :
    ((Finset.range n).filter fun i => cfDigit x i = k).card
      = ((Finset.range n).filter fun i => [k] = cfWindow x i ([k].length)).card := by
  congr 1
  refine Finset.filter_congr fun i _ => ?_
  simp only [List.length_singleton, cfWindow_one, List.cons.injEq, and_true]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- Exact partition of the positions by digit: either the digit lies in `[1,K]`, in which
case it equals exactly one `k ∈ [1,K]`, or it does not. -/
lemma card_digitTail_add_sum (x : ℝ) (K n : ℕ) :
    ((Finset.range n).filter fun i => ¬ (1 ≤ cfDigit x i ∧ cfDigit x i ≤ K)).card
        + ∑ k ∈ Finset.Icc 1 K, ((Finset.range n).filter fun i => cfDigit x i = k).card
      = n := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.range n)
    (fun i => 1 ≤ cfDigit x i ∧ cfDigit x i ≤ K)
  have hmaps : ∀ i ∈ (Finset.range n).filter
      (fun i => 1 ≤ cfDigit x i ∧ cfDigit x i ≤ K), cfDigit x i ∈ Finset.Icc 1 K := by
    intro i hi
    obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_Icc.mpr ⟨h1, h2⟩
  have hfib : ((Finset.range n).filter
      fun i => 1 ≤ cfDigit x i ∧ cfDigit x i ≤ K).card
      = ∑ k ∈ Finset.Icc 1 K,
          ((Finset.range n).filter fun i => cfDigit x i = k).card := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
    congr 1
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun i _ => ?_
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h; exact ⟨⟨by omega, by omega⟩, h⟩
  rw [← hfib]
  simp only [Finset.card_range] at hsplit
  omega

/-- **The digit tail frequency** for a CF-normal point: an exact limit, equal to the Gauss
measure of the digit tail.  Gauss–Kuzmin makes it `O(1/K)`.  This is the elementary
replacement for the Airey–Mance tightness hypothesis: it is a *consequence* of
CF-normality, proved here, not an extra assumption. -/
theorem tendsto_digitTail_freq {x : ℝ} (hx : IsCFNormal x) (K : ℕ) :
    Tendsto (fun n => (((Finset.range n).filter
        fun i => ¬ (1 ≤ cfDigit x i ∧ cfDigit x i ≤ K)).card : ℝ) / n) atTop
      (nhds (1 - ∑ k ∈ Finset.Icc 1 K, (gaussMeasure (cfCylinder [k])).toReal)) := by
  classical
  have hone : ∀ k ∈ Finset.Icc 1 K,
      Tendsto (fun n => (((Finset.range n).filter
          fun i => cfDigit x i = k).card : ℝ) / n) atTop
        (nhds (gaussMeasure (cfCylinder [k])).toReal) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have h := tendsto_windowFreq hx [k] (by simp) (by simpa using hk1)
    refine h.congr fun n => ?_
    rw [card_digit_eq_card_window]
  have hsum : Tendsto (fun n => ∑ k ∈ Finset.Icc 1 K,
      (((Finset.range n).filter fun i => cfDigit x i = k).card : ℝ) / n) atTop
      (nhds (∑ k ∈ Finset.Icc 1 K, (gaussMeasure (cfCylinder [k])).toReal)) :=
    tendsto_finsetSum _ hone
  have htarget : Tendsto (fun n : ℕ => (1 : ℝ) - ∑ k ∈ Finset.Icc 1 K,
      (((Finset.range n).filter fun i => cfDigit x i = k).card : ℝ) / n) atTop
      (nhds (1 - ∑ k ∈ Finset.Icc 1 K, (gaussMeasure (cfCylinder [k])).toReal)) :=
    tendsto_const_nhds.sub hsum
  refine htarget.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hid := card_digitTail_add_sum x K n
  rw [← Finset.sum_div, sub_eq_iff_eq_add, ← add_div, eq_div_iff hnR, one_mul]
  exact_mod_cast hid.symm

/-! ## The residue: separating good positions from bad ones -/

variable (δ : S → ℕ → S)

/-- Positions whose lookback window is digit-bounded and contains `z`, and which carry the
joint (window, state) event. -/
noncomputable def goodSet [DecidableEq S] (s₀ t : S) (z v : List ℕ) (x : ℝ)
    (K L m : ℕ) : Finset ℕ :=
  (Finset.range m).filter fun j =>
    cfWindow x j L ∈ boundedWords K L ∧ z <:+: cfWindow x j L ∧
    v = cfWindow x (j + L) v.length ∧ stateAt δ s₀ x (j + L) = t

/-- Positions whose lookback window fails to be digit-bounded or fails to contain `z` —
the only places the finite-sum formula can miss. -/
noncomputable def badSet (z : List ℕ) (x : ℝ) (K L m : ℕ) : Finset ℕ :=
  (Finset.range m).filter fun j =>
    ¬ (cfWindow x j L ∈ boundedWords K L ∧ z <:+: cfWindow x j L)

/-- **Lower half of the sandwich**: every good position contributes to the joint count. -/
theorem goodSet_card_le_jointCount [DecidableEq S] (s₀ t : S) (z v : List ℕ)
    (x : ℝ) (K L n : ℕ) :
    (goodSet δ s₀ t z v x K L (n - L)).card ≤ jointCount δ s₀ t v x n := by
  classical
  rw [jointCount_eq_card]
  refine Finset.card_le_card_of_injOn (fun j => j + L) ?_ ?_
  · intro j hj
    obtain ⟨hjm', hrest⟩ := Finset.mem_filter.mp hj
    have hjm := Finset.mem_range.mp hjm'
    show (j + L) ∈ jointSet δ s₀ t v x n
    exact mem_jointSet.mpr ⟨by omega, hrest.2.2.1, hrest.2.2.2⟩
  · intro a _ b _ h; simpa using h

/-- **Upper half of the sandwich**: the joint count exceeds the good count by at most the
bad count plus the `L` initial positions. -/
theorem jointCount_le [DecidableEq S] (s₀ t : S) (z v : List ℕ)
    (x : ℝ) (K L n : ℕ) :
    jointCount δ s₀ t v x n
      ≤ L + (goodSet δ s₀ t z v x K L (n - L)).card + (badSet z x K L (n - L)).card := by
  classical
  set J : Finset ℕ := jointSet δ s₀ t v x n with hJ
  have hcard : (J.filter fun i => i < L).card + (J.filter fun i => ¬ i < L).card
      = J.card := Finset.card_filter_add_card_filter_not (fun i => i < L)
  have h1 : (J.filter fun i => i < L).card ≤ L := by
    refine le_trans (Finset.card_le_card ?_) (by simp : (Finset.range L).card ≤ L)
    intro i hi
    simp only [Finset.mem_filter] at hi
    exact Finset.mem_range.mpr hi.2
  have h2 : (J.filter fun i => ¬ i < L).card
      ≤ (goodSet δ s₀ t z v x K L (n - L) ∪ badSet z x K L (n - L)).card := by
    refine Finset.card_le_card_of_injOn (fun i => i - L) ?_ ?_
    · intro i hi
      obtain ⟨hiJ, hiL⟩ := Finset.mem_filter.mp hi
      obtain ⟨hin, hv, hs⟩ := mem_jointSet.mp hiJ
      have hiL' : L ≤ i := by omega
      have heq : i - L + L = i := by omega
      by_cases hb : cfWindow x (i - L) L ∈ boundedWords K L ∧ z <:+: cfWindow x (i - L) L
      · refine Finset.mem_union_left _ ?_
        simp only [goodSet, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hb.1, hb.2, by rw [heq]; exact hv, by rw [heq]; exact hs⟩
      · refine Finset.mem_union_right _ ?_
        simp only [badSet, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hb⟩
    · intro a ha b hb h
      have h' : a - L = b - L := h
      obtain ⟨-, haL⟩ := Finset.mem_filter.mp ha
      obtain ⟨-, hbL⟩ := Finset.mem_filter.mp hb
      simp only [not_lt] at haL hbL
      omega
  have h3 := Finset.card_union_le (goodSet δ s₀ t z v x K L (n - L))
    (badSet z x K L (n - L))
  calc jointCount δ s₀ t v x n = J.card := by rw [hJ, jointCount_eq_card]
    _ = (J.filter fun i => i < L).card + (J.filter fun i => ¬ i < L).card := hcard.symm
    _ ≤ L + (goodSet δ s₀ t z v x K L (n - L) ∪ badSet z x K L (n - L)).card := by
        exact Nat.add_le_add h1 h2
    _ ≤ L + ((goodSet δ s₀ t z v x K L (n - L)).card
            + (badSet z x K L (n - L)).card) := Nat.add_le_add_left h3 _
    _ = L + (goodSet δ s₀ t z v x K L (n - L)).card + (badSet z x K L (n - L)).card :=
        (Nat.add_assoc _ _ _).symm

/-- A window that is not digit-bounded contains an out-of-range digit, so unbounded windows
are charged to the digit tail, with multiplicity at most `L`. -/
theorem card_unbounded_window_le (x : ℝ) (K L m : ℕ) :
    ((Finset.range m).filter fun j => cfWindow x j L ∉ boundedWords K L).card
      ≤ L * ((Finset.range (m + L)).filter
              fun i => ¬ (1 ≤ cfDigit x i ∧ cfDigit x i ≤ K)).card := by
  classical
  set D : Finset ℕ := (Finset.range (m + L)).filter
    fun i => ¬ (1 ≤ cfDigit x i ∧ cfDigit x i ≤ K) with hD
  have hsub : ((Finset.range m).filter fun j => cfWindow x j L ∉ boundedWords K L)
      ⊆ (Finset.range L).biUnion fun k => (Finset.range m).filter
          fun j => ¬ (1 ≤ cfDigit x (j + k) ∧ cfDigit x (j + k) ≤ K) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hjm, hnb⟩ := hj
    rw [mem_boundedWords] at hnb
    have hex : ∃ a ∈ cfWindow x j L, ¬ (1 ≤ a ∧ a ≤ K) := by
      by_contra hc
      push_neg at hc
      exact hnb ⟨cfWindow_length x j L, fun a ha => hc a ha⟩
    obtain ⟨a, ha, hbad⟩ := hex
    simp only [cfWindow, List.mem_map, List.mem_range] at ha
    obtain ⟨k, hkL, hk⟩ := ha
    refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr hkL, ?_⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjm, ?_⟩
    show ¬ (1 ≤ cfDigit x (j + k) ∧ cfDigit x (j + k) ≤ K)
    rw [hk]; exact hbad
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_biUnion_le) ?_
  have hterm : ∀ k ∈ Finset.range L, ((Finset.range m).filter
      fun j => ¬ (1 ≤ cfDigit x (j + k) ∧ cfDigit x (j + k) ≤ K)).card ≤ D.card := by
    intro k hk
    refine Finset.card_le_card_of_injOn (fun j => j + k) ?_
      (fun a _ b _ h => by simpa using h)
    intro j hj
    obtain ⟨hjm', hjbad⟩ := Finset.mem_filter.mp hj
    have hjm := Finset.mem_range.mp hjm'
    have hkL := Finset.mem_range.mp hk
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hjbad⟩
    show j + k < m + L
    omega
  calc ∑ k ∈ Finset.range L, ((Finset.range m).filter
          fun j => ¬ (1 ≤ cfDigit x (j + k) ∧ cfDigit x (j + k) ≤ K)).card
      ≤ ∑ _k ∈ Finset.range L, D.card := Finset.sum_le_sum hterm
    _ = L * D.card := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- The bad set splits into "a digit in the window exceeds `K`" and "`z` is absent". -/
theorem badSet_card_le (z : List ℕ) (x : ℝ) (K L m : ℕ) :
    (badSet z x K L m).card
      ≤ L * ((Finset.range (m + L)).filter
              fun i => ¬ (1 ≤ cfDigit x i ∧ cfDigit x i ≤ K)).card
        + ((Finset.range m).filter fun j => ¬ z <:+: cfWindow x j L).card := by
  classical
  set D : Finset ℕ := (Finset.range (m + L)).filter
    fun i => ¬ (1 ≤ cfDigit x i ∧ cfDigit x i ≤ K) with hD
  -- unbounded windows
  have hunb := card_unbounded_window_le x K L m
  refine le_trans (Finset.card_le_card ?_) (le_trans (Finset.card_union_le _ _)
    (Nat.add_le_add hunb (le_refl _)))
  intro j hj
  simp only [badSet, Finset.mem_filter, Finset.mem_range] at hj
  obtain ⟨hjm, hnb⟩ := hj
  by_cases h : cfWindow x j L ∈ boundedWords K L
  · exact Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjm, fun hz => hnb ⟨h, hz⟩⟩)
  · exact Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjm, h⟩)

/-! ## Window counts against a finite family of words -/

/-- Positions whose length-`L` window lands in a finite family `F` of length-`L` words are
partitioned by that window. -/
theorem card_window_mem_eq_sum (x : ℝ) (F : Finset (List ℕ)) (L : ℕ)
    (hF : ∀ q ∈ F, q.length = L) (m : ℕ) :
    ((Finset.range m).filter fun j => cfWindow x j L ∈ F).card
      = ∑ q ∈ F, ((Finset.range m).filter fun j => q = cfWindow x j L).card := by
  classical
  have hmaps : ∀ j ∈ (Finset.range m).filter (fun j => cfWindow x j L ∈ F),
      cfWindow x j L ∈ F := fun j hj => (Finset.mem_filter.mp hj).2
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun q hq => ?_
  congr 1
  rw [Finset.filter_filter]
  refine Finset.filter_congr fun j _ => ?_
  constructor
  · rintro ⟨-, h⟩; exact h.symm
  · intro h; exact ⟨h ▸ hq, h.symm⟩

/-- The frequency of positions whose window lands in a finite family of genuine words is the
total Gauss mass of the corresponding cylinders. -/
theorem tendsto_window_mem_freq {x : ℝ} (hx : IsCFNormal x) (F : Finset (List ℕ)) (L : ℕ)
    (hL : 1 ≤ L) (hF : ∀ q ∈ F, q.length = L) (hFpos : ∀ q ∈ F, ∀ a ∈ q, 1 ≤ a) :
    Tendsto (fun m => (((Finset.range m).filter
        fun j => cfWindow x j L ∈ F).card : ℝ) / m) atTop
      (nhds (∑ q ∈ F, (gaussMeasure (cfCylinder q)).toReal)) := by
  classical
  have hterm : ∀ q ∈ F, Tendsto (fun m => (((Finset.range m).filter
      fun j => q = cfWindow x j L).card : ℝ) / m) atTop
      (nhds (gaussMeasure (cfCylinder q)).toReal) := by
    intro q hq
    have hlen := hF q hq
    have hne : q ≠ [] := by
      intro h; rw [h] at hlen; simp at hlen; omega
    have h := tendsto_windowFreq hx q hne (hFpos q hq)
    rw [hlen] at h
    exact h
  have hsum := tendsto_finsetSum (f := fun q m => (((Finset.range m).filter
      fun j => q = cfWindow x j L).card : ℝ) / m) F hterm
  refine hsum.congr fun m => ?_
  rw [← Finset.sum_div]
  congr 1
  rw [card_window_mem_eq_sum x F L hF m, Nat.cast_sum]

/-! ## The `Synchronizing` obstruction: a bijective quotient never forgets

The reason the intended CF transducer admits no synchronizing word, stated for any
automaton.  See the retirement note in the module docstring. -/

/-- Running the automaton commutes with a quotient that is equivariant for a letter action. -/
theorem quotient_runState {S C : Type*} {δ : S → ℕ → S} {φ : S → C} {ψ : ℕ → C → C}
    (hcomm : ∀ s a, φ (δ s a) = ψ a (φ s)) (s : S) (w : List ℕ) :
    φ (runState δ s w) = w.foldl (fun c a => ψ a c) (φ s) := by
  induction w generalizing s with
  | nil => rfl
  | cons a u ih => rw [runState_cons, List.foldl_cons, ih, hcomm]

/-- An iterated injective letter action stays injective. -/
theorem injective_foldl_of_injective {C : Type*} {ψ : ℕ → C → C}
    (hψ : ∀ a, Function.Injective (ψ a)) (w : List ℕ) :
    Function.Injective (fun c : C => w.foldl (fun c a => ψ a c) c) := by
  induction w with
  | nil => exact fun _ _ h => h
  | cons a u ih =>
    intro c c' h
    simp only [List.foldl_cons] at h
    exact hψ a (ih h)

/-- **The obstruction** (`PROBE-2026-09-27-transducer-not-synchronizing.md`): an automaton
with a quotient on which every letter acts **injectively** has NO synchronizing word, as
soon as the quotient separates two states.

For the det-`±D` CF transducer the quotient is the row-lattice class in `ℙ¹(ℤ/D)`, the letter
action is `c ↦ c · B_a` with `B_a ∈ GL₂(ℤ/D)`, and the `D + 1` classes are pairwise separated.
So every `Synchronizing`-hypothesis statement above is vacuous for that automaton, which is
why the frequency assembly moved to `VandeheyCocycle`. -/
theorem not_synchronizing_of_injective_quotient {S C : Type*} {δ : S → ℕ → S} {φ : S → C}
    {ψ : ℕ → C → C} (hψ : ∀ a, Function.Injective (ψ a))
    (hcomm : ∀ s a, φ (δ s a) = ψ a (φ s)) {s s' : S} (hne : φ s ≠ φ s') (z : List ℕ) :
    ¬ Synchronizing δ z := by
  intro hz
  apply hne
  refine injective_foldl_of_injective hψ z ?_
  show z.foldl (fun c a => ψ a c) (φ s) = z.foldl (fun c a => ψ a c) (φ s')
  rw [← quotient_runState hcomm, ← quotient_runState hcomm, hz s s']

/-- Content locator: the obstruction is not vacuous — a two-state automaton whose letters
all act as the identity on `Bool` has no synchronizing word. -/
theorem not_synchronizing_id (z : List ℕ) : ¬ Synchronizing (fun b : Bool => fun _ : ℕ => b) z :=
  not_synchronizing_of_injective_quotient (φ := (id : Bool → Bool))
    (ψ := fun _ => (id : Bool → Bool)) (fun _ => Function.injective_id) (fun _ _ => rfl)
    (s := false) (s' := true) (by simp) z

end VandeheyAut

end NormalNumbers
