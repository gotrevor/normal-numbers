/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-PN: the state family pinned as a FUNCTION — the repair S7-SA demands

S7-SA showed that pinning the coupling's sets to *some* family `s : ℕ → MobState` pins nothing: the
type interpolates the single pair of points the coupling evaluates.  The content of a transducer
hypothesis is the **recursion**, which determines `s n` from `x₁…xₙ` and forbids any dependence on
the image orbit.  This module states that recursion and proves that it *implies* the coupling.

    StatePin x Φ N s v :
      s 0 = Φ,   N 0 = 0,   N (n+1) = N n + |v n|,   N → ∞,   digits of v n ≥ 1,
      (s n).mob maps (0,1) into (0,1),
      cylState (v n) ∘ s (n+1) = s n ∘ readStateAt x n        -- the transducer step, as matrices

`readStateAt x n` is the input-digit map `t ↦ 1/(t + aₙ₊₁)` reconstructed from the orbit itself
(`readDigit x n = 1/Gⁿx − Gⁿ⁺¹x = ⌊1/Gⁿx⌋`), so no CF bookkeeping enters the statement.

The two outputs:

* `StatePin.realize` — `G^{N n} y = (s n).mob (Gⁿ x)` for all `n`, from `y = Φ.mob x` alone.  The
  induction is exactly the transducer's: read the next input digit (a right `comp`), then strip the
  emitted word off the image (a left `comp`, undone by `gaussMap^[|v n|]`).
* `StatePin.blockCouplingM` — hence the coupling, with the states now forced.

The clock is only monotone and unbounded, never strictly monotone: a transducer stalls, and
`v n = []` is allowed.  That is why the reduction goes through S7-C3's `freq_le_of_blockAverage_mono`
rather than S7-BD's `freq_le_of_blockAverage`.

So `PinnedData` (below) is a bundle whose only genuine freedom is the emitted words `v`, and the
cheap S7-SA witness is excluded: `lowState (Gⁿy/Gⁿx)` does not satisfy the recursion, because the
recursion never mentions `y`.
-/
import NormalNumbers.VandeheyS7Clock3
import NormalNumbers.VandeheyS7CylState
import NormalNumbers.VandeheyS7Emit2

namespace NormalNumbers.VandeheyS7

open Filter MeasureTheory NormalNumbers

namespace MobState

/-! ## The cylinder map strips its own word -/

lemma readState_mapsTo {a : ℝ} (ha : 1 ≤ a) :
    Set.MapsTo (readState a (lt_of_lt_of_le zero_lt_one ha)).mob (Set.Ioo (0:ℝ) 1)
      (Set.Ioo (0:ℝ) 1) := by
  intro t ht
  rw [readState_mob]
  have h1 : 0 < t + a := by linarith [ht.1]
  constructor
  · positivity
  · rw [div_lt_one h1]; linarith [ht.1]

/-- Reading a digit is inverted by one Gauss step. -/
lemma gaussMap_readState_mob {a : ℝ} (ha : 1 ≤ a) (han : ∃ m : ℤ, a = (m : ℝ)) {t : ℝ}
    (ht : t ∈ Set.Ioo (0:ℝ) 1) :
    gaussMap ((readState a (lt_of_lt_of_le zero_lt_one ha)).mob t) = t := by
  obtain ⟨m, rfl⟩ := han
  have h1 : 0 < t + (m : ℝ) := by linarith [ht.1]
  rw [readState_mob]
  have hne : (1:ℝ) / (t + (m : ℝ)) ≠ 0 := by positivity
  rw [gaussMap, if_neg hne, one_div, inv_inv, Int.fract_add_intCast,
    Int.fract_eq_self.2 ⟨ht.1.le, ht.2⟩]

/-- `cylState w` maps `(0,1)` into `(0,1)` when all digits are genuine. -/
lemma cylState_mapsTo : ∀ w : List ℕ, (∀ a ∈ w, 1 ≤ a) →
    Set.MapsTo (cylState w).mob (Set.Ioo (0:ℝ) 1) (Set.Ioo (0:ℝ) 1)
  | [], _ => by intro t ht; simpa [idState_mob] using ht
  | a :: w, hpos => by
      have ha : 0 < a := hpos a (by simp)
      have ha1 : (1:ℝ) ≤ (a : ℝ) := by exact_mod_cast hpos a (by simp)
      intro t ht
      rw [cylState_cons ha w, mob_comp _ _ ht.1.le]
      exact readState_mapsTo ha1 (cylState_mapsTo w (fun e he => hpos e (by simp [he])) ht)

/-- **The tail identity.**  `|w|` Gauss steps strip the word `w` off `cylState w`'s image. -/
theorem gaussMap_iterate_cylState_mob : ∀ (w : List ℕ), (∀ a ∈ w, 1 ≤ a) → ∀ {t : ℝ},
    t ∈ Set.Ioo (0:ℝ) 1 → gaussMap^[w.length] ((cylState w).mob t) = t
  | [], _, t, _ => by simp [idState_mob]
  | a :: w, hpos, t, ht => by
      have ha : 0 < a := hpos a (by simp)
      have ha1 : (1:ℝ) ≤ (a : ℝ) := by exact_mod_cast hpos a (by simp)
      have hw : ∀ e ∈ w, 1 ≤ e := fun e he => hpos e (by simp [he])
      have hmem := cylState_mapsTo w hw ht
      rw [cylState_cons ha w, mob_comp _ _ ht.1.le, List.length_cons,
        Function.iterate_succ_apply, gaussMap_readState_mob ha1 ⟨(a : ℤ), by push_cast; ring⟩ hmem]
      exact gaussMap_iterate_cylState_mob w hw ht

/-! ## The input digit, read off the orbit -/

/-- `⌊1/Gⁿx⌋`, written without CF bookkeeping. -/
noncomputable def readDigit (x : ℝ) (n : ℕ) : ℝ :=
  1 / gaussMap^[n] x - gaussMap^[n + 1] x

lemma one_le_readDigit {x : ℝ} (hx : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) (n : ℕ) :
    1 ≤ readDigit x n := by
  have h0 : gaussMap^[n] x ∈ Set.Ioo (0:ℝ) 1 := hx n
  have hstep : gaussMap^[n + 1] x = Int.fract (gaussMap^[n] x)⁻¹ := by
    rw [Function.iterate_succ_apply', gaussMap, if_neg h0.1.ne']
  have hone : (1:ℝ) < (gaussMap^[n] x)⁻¹ := by
    rw [lt_inv_comm₀ one_pos h0.1]; simpa using h0.2
  have hfl : (1:ℝ) ≤ (⌊(gaussMap^[n] x)⁻¹⌋ : ℝ) := by
    have : (1:ℤ) ≤ ⌊(gaussMap^[n] x)⁻¹⌋ := by
      rw [Int.le_floor]; exact_mod_cast hone.le
    exact_mod_cast this
  have : readDigit x n = (⌊(gaussMap^[n] x)⁻¹⌋ : ℝ) := by
    unfold readDigit
    rw [hstep, one_div, Int.self_sub_fract]
  rw [this]; exact hfl

/-- The read state at input time `n`, a total function of `x` and `n`. -/
noncomputable def readStateAt (x : ℝ) (n : ℕ) : MobState :=
  if h : 0 < readDigit x n then readState (readDigit x n) h else idState

/-- **The read identity**: the orbit point is the read image of its successor. -/
theorem readStateAt_mob {x : ℝ} (hx : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) (n : ℕ) :
    (readStateAt x n).mob (gaussMap^[n + 1] x) = gaussMap^[n] x := by
  have h1 := one_le_readDigit hx n
  have hpos : 0 < readDigit x n := lt_of_lt_of_le zero_lt_one h1
  rw [readStateAt, dif_pos hpos, readState_mob]
  have hsum : gaussMap^[n + 1] x + readDigit x n = 1 / gaussMap^[n] x := by
    unfold readDigit; ring
  rw [hsum, one_div, one_div, inv_inv]

/-- Two states with equal entries are equal (the remaining fields are `Prop`s). -/
theorem ext_entries {s t : MobState} (ha : s.a = t.a) (hb : s.b = t.b) (hc : s.c = t.c)
    (hd : s.d = t.d) : s = t := by
  cases s; cases t; simp_all

/-- **Left cancellation.**  An invertible left factor determines the right factor, so the
transducer step determines `s (n+1)` from `s n` and the emitted word. -/
theorem comp_left_cancel {A s t : MobState} (h : A.comp s = A.comp t) : s = t := by
  have hdet := A.hdet
  have hkey : ∀ p r : ℝ, A.a * p + A.b * r = 0 → A.c * p + A.d * r = 0 → p = 0 ∧ r = 0 := by
    intro p r h1 h2
    constructor
    · have : (A.a * A.d - A.b * A.c) * p = 0 := by linear_combination A.d * h1 - A.b * h2
      exact (mul_eq_zero.1 this).resolve_left hdet
    · have : (A.a * A.d - A.b * A.c) * r = 0 := by linear_combination A.a * h2 - A.c * h1
      exact (mul_eq_zero.1 this).resolve_left hdet
  have h1 : A.a * s.a + A.b * s.c = A.a * t.a + A.b * t.c := congrArg MobState.a h
  have h2 : A.c * s.a + A.d * s.c = A.c * t.a + A.d * t.c := congrArg MobState.c h
  have h3 : A.a * s.b + A.b * s.d = A.a * t.b + A.b * t.d := congrArg MobState.b h
  have h4 : A.c * s.b + A.d * s.d = A.c * t.b + A.d * t.d := congrArg MobState.d h
  obtain ⟨e1, e2⟩ := hkey (s.a - t.a) (s.c - t.c) (by linarith) (by linarith)
  obtain ⟨e3, e4⟩ := hkey (s.b - t.b) (s.d - t.d) (by linarith) (by linarith)
  exact ext_entries (by linarith) (by linarith) (by linarith) (by linarith)

end MobState

/-! ## The pinned bundle -/

open MobState

/-- **The transducer, as a pinned recursion.**  `s (n+1)` is determined by `s n`, the input digit
and the emitted word; nothing here mentions the image orbit, which is what S7-SA showed the
previous bundle lacked. -/
structure StatePin (x : ℝ) (Φ : MobState) (N : ℕ → ℕ) (s : ℕ → MobState) (v : ℕ → List ℕ) :
    Prop where
  init : s 0 = Φ
  clock0 : N 0 = 0
  clockStep : ∀ n, N (n + 1) = N n + (v n).length
  clockUnbounded : Tendsto N atTop atTop
  emitPos : ∀ n, ∀ a ∈ v n, 1 ≤ a
  reduced : ∀ n, Set.MapsTo (s n).mob (Set.Ioo (0:ℝ) 1) (Set.Ioo (0:ℝ) 1)
  step : ∀ n, (cylState (v n)).comp (s (n + 1)) = (s n).comp (readStateAt x n)

namespace StatePin

variable {x y : ℝ} {Φ : MobState} {N : ℕ → ℕ} {s : ℕ → MobState} {v : ℕ → List ℕ}

lemma mono (h : StatePin x Φ N s v) : Monotone N := by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [h.clockStep n]; omega

/-- **The realization identity.**  The image orbit at the clock time is the state's image of the
input orbit — proved, not assumed. -/
theorem realize (h : StatePin x Φ N s v)
    (hx : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) (hy : y = Φ.mob x) (n : ℕ) :
    gaussMap^[N n] y = (s n).mob (gaussMap^[n] x) := by
  induction n with
  | zero => simpa [h.clock0, h.init] using hy
  | succ n ih =>
      have hz : (s (n + 1)).mob (gaussMap^[n + 1] x) ∈ Set.Ioo (0:ℝ) 1 :=
        h.reduced (n + 1) (hx (n + 1))
      have hkey : (s n).mob (gaussMap^[n] x)
          = (cylState (v n)).mob ((s (n + 1)).mob (gaussMap^[n + 1] x)) := by
        rw [← mob_comp _ _ (hx (n + 1)).1.le, h.step n,
          mob_comp _ _ (hx (n + 1)).1.le, readStateAt_mob hx n]
      rw [h.clockStep n, Nat.add_comm, Function.iterate_add_apply, ih, hkey,
        gaussMap_iterate_cylState_mob (v n) (h.emitPos n) hz]

/-- **The coupling, forced.**  The S7-C3 coupling now follows from the recursion. -/
theorem blockCouplingM (h : StatePin x Φ N s v)
    (hx : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) (hy : y = Φ.mob x) (w : List ℕ) :
    BlockCouplingM (cfCylinder w) x y N (fun n j => stateBlockSet (s n) w j) where
  base := h.clock0
  mono := h.mono
  unbounded := h.clockUnbounded
  couple := by
    intro n j _
    have hz : (s n).mob (gaussMap^[n] x) ∈ Set.Ioo (0:ℝ) 1 := h.reduced n (hx n)
    have hr : gaussMap^[N n] y = (s n).mob (gaussMap^[n] x) := h.realize hx hy n
    have hiter : gaussMap^[N n + j] y = gaussMap^[j] ((s n).mob (gaussMap^[n] x)) := by
      rw [Nat.add_comm, Function.iterate_add_apply, hr]
    constructor
    · intro hmem
      exact ⟨⟨by rw [Set.mem_preimage]; rw [hiter] at hmem; exact hmem, hz⟩, hx n⟩
    · rintro ⟨⟨h1, -⟩, -⟩
      rw [hiter]
      exact h1

/-- **The recursion determines the run.**  Same input, same initial state, same emitted words ⟹
the same state family and the same clock.  This is what S7-SA's cheap witness cannot do: the data
`(Φ, v)` contains no information about the image orbit. -/
theorem eq_of_emit {N' : ℕ → ℕ} {s' : ℕ → MobState} (h : StatePin x Φ N s v)
    (h' : StatePin x Φ N' s' v) : ∀ n, s n = s' n ∧ N n = N' n := by
  intro n
  induction n with
  | zero => exact ⟨by rw [h.init, h'.init], by rw [h.clock0, h'.clock0]⟩
  | succ n ih =>
      refine ⟨MobState.comp_left_cancel (A := cylState (v n)) ?_, ?_⟩
      · rw [h.step n, h'.step n, ih.1]
      · rw [h.clockStep n, h'.clockStep n, ih.2]

end StatePin

/-- **The honest bundle.**  Everything existential is either the emitted words or the clock they
determine; the states are forced by the recursion. -/
def PinnedData (q r₀ C : ℝ) : Prop :=
  ∀ x : ℝ, IsCFNormal (Int.fract x) → ∀ w : List ℕ, (∀ e ∈ w, 1 ≤ e) →
    ∃ (Φ : MobState) (N : ℕ → ℕ) (s : ℕ → MobState) (v : ℕ → List ℕ),
      Int.fract (q * x + r₀) = Φ.mob (Int.fract x) ∧
      StatePin (Int.fract x) Φ N s v ∧
      Tendsto (fun n => ((N (n + 1) : ℝ)) / (N n : ℝ)) atTop (nhds 1) ∧
      BlockAverageBound (C * (gaussMeasure (cfCylinder w)).toReal) (Int.fract x) N
        (fun n j => stateBlockSet (s n) w j)

/-- **S7-PN.**  The pinned bundle gives the crux. -/
theorem orbitWordBound_of_pinnedData {q r₀ C : ℝ} (hC : 0 ≤ C)
    (h : PinnedData q r₀ C) : OrbitWordBound q r₀ C := by
  intro x hx w hw ε hε
  obtain ⟨Φ, N, s, v, hy, hpin, hratio, hBA⟩ := h x hx w hw
  have hx0 : Irrational x := Literature.irrational_of_isCFNormal_fract hx
  have hxirr : Irrational (Int.fract x) := (irrational_fract_mem hx0).1
  have hxmem : Int.fract x ∈ Set.Ioo (0:ℝ) 1 := (irrational_fract_mem hx0).2
  have hxo : ∀ k, gaussMap^[k] (Int.fract x) ∈ Set.Ioo (0:ℝ) 1 :=
    fun k => (irrational_orbit _ hxirr hxmem k).2
  have hB : 0 ≤ C * (gaussMeasure (cfCylinder w)).toReal :=
    mul_nonneg hC ENNReal.toReal_nonneg
  exact freq_le_of_blockAverage_mono (hpin.blockCouplingM hxo hy w) hratio hB hBA ε hε

section Audit

#print axioms MobState.gaussMap_iterate_cylState_mob
#print axioms StatePin.realize
#print axioms StatePin.blockCouplingM
#print axioms MobState.comp_left_cancel
#print axioms StatePin.eq_of_emit
#print axioms orbitWordBound_of_pinnedData

end Audit

end NormalNumbers.VandeheyS7
