/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderEscape
import NormalNumbers.AdderTowerDeductions

/-!
# The escape certificate: a finite automaton proves a Mahler lower bound 🧮

`AdderEscape.lean` established that the digits of `m·x` are read off by the
adder recursion once the **true carries** `⌊m·{gⁱx}⌋` are known.  This file
turns a finite *escape certificate* into a kernel-checked lower bound
`M(g,k) > M`:

* `EscapeCert g`: states `Fin n`, each emitting a digit `a s`, with successor
  lists `next s`; per state a rational **tail interval** `[lo s, hi s]` and
  per channel `m` a **carry** `c s m`.
* `EscapeCert.Valid C M w` (decidable): the interval inequalities
  `lo s ≤ (a s + lo s')/g`, `(a s + hi s')/g ≤ hi s` on every edge; the carry
  pinning `c s m ≤ m·lo s`, `m·hi s ≤ c s m + 1`; the adder recursion
  `c s m = (m·a s + c s' m)/g`; and the block `w` never appearing among the
  channel digits `(m·a s + c s' m) % g` along any path of length `|w|`.

Along an infinite path `σ` with digits `a ∘ σ`, the tails of
`x = realOfDigits g (a ∘ σ)` lie in the certified intervals
(`tail_mem`), and lie **strictly** below `hi` as soon as some later edge is
not `hi`-extremal (`tail_lt_hi`) — this is what excludes the rational
endpoints, where `m·x` could be an integer and the carry ambiguous.  Then the
true carries are the certificate's (`carry_eq`), the digits of `m·x` are the
channel digits (`digit_mul_eq`), and `w` never occurs in `m·x`
(`not_occursAt_of_path`).

Irrationality is by cardinality: two closed walks `u ≠ v` of the same
length from a common state, both containing a non-extremal edge and a digit
`≠ g − 1`, mixed according to `A : Set ℕ`, give `2^ℵ₀` distinct proper digit
sequences, hence an irrational witness (`exists_irrational_escape`).

The instance `M(7,2) ≥ 176` from the 10-state SCC is the next brick.
-/

namespace NormalNumbers.Adder

open NormalNumbers NormalNumbers.Mahler

/-- A finite escape certificate for base `g`. -/
structure EscapeCert (g : ℕ) where
  n : ℕ
  a : Fin n → ℕ
  next : Fin n → List (Fin n)
  lo : Fin n → ℚ
  hi : Fin n → ℚ
  c : Fin n → ℕ → ℕ

namespace EscapeCert

variable {g : ℕ} (C : EscapeCert g)

/-- The channel-`m` digit read on the edge `s → s'`. -/
def chDigit (m : ℕ) (s s' : Fin C.n) : ℕ := (m * C.a s + C.c s' m) % g

/-- An edge is `hi`-extremal when it attains the interval bound. -/
def HiMax (s s' : Fin C.n) : Prop := (C.a s + C.hi s') / g = C.hi s

/-- The finite validity check. -/
def Valid (M : ℕ) (w : List ℕ) : Prop :=
  (∀ s, C.a s < g) ∧
  (∀ s, 0 ≤ C.lo s ∧ C.lo s ≤ C.hi s ∧ C.hi s ≤ 1) ∧
  (∀ s, ∀ s' ∈ C.next s, C.lo s ≤ (C.a s + C.lo s') / g ∧ (C.a s + C.hi s') / g ≤ C.hi s) ∧
  (∀ m, m ≤ M → ∀ s, (C.c s m : ℚ) ≤ m * C.lo s ∧ m * C.hi s ≤ C.c s m + 1) ∧
  (∀ m, m ≤ M → ∀ s, ∀ s' ∈ C.next s, C.c s m = (m * C.a s + C.c s' m) / g) ∧
  (∀ m, 1 ≤ m → m ≤ M → ∀ σ : Fin (w.length + 1) → Fin C.n,
    (∀ i : Fin w.length, σ i.succ ∈ C.next (σ i.castSucc)) →
    List.ofFn (fun i : Fin w.length => C.chDigit m (σ i.castSucc) (σ i.succ)) ≠ w)

instance (M : ℕ) (w : List ℕ) : Decidable (C.Valid M w) := by
  unfold Valid; infer_instance

/-- A valid infinite path. -/
def IsPath (σ : ℕ → Fin C.n) : Prop := ∀ i, σ (i + 1) ∈ C.next (σ i)

/-- The digit sequence of a path. -/
def digits (σ : ℕ → Fin C.n) : ℕ → ℕ := fun i => C.a (σ i)

/-- The real number of a path. -/
noncomputable def real (σ : ℕ → Fin C.n) : ℝ := realOfDigits g (C.digits σ)

section path

variable {C} {M : ℕ} {w : List ℕ} (hV : C.Valid M w) (hg : 2 ≤ g)
  {σ : ℕ → Fin C.n} (hσ : C.IsPath σ) (hp : ProperDigits g (C.digits σ))

include hV hg hp in
theorem digit_real (i : ℕ) : digitOf g (Int.fract (C.real σ)) i = C.a (σ i) := by
  have hmem := realOfDigits_mem_Ico g hg (C.digits σ) (fun i => hV.1 _) hp
  have hfr : Int.fract (C.real σ) = C.real σ := Int.fract_eq_self.2 ⟨hmem.1, hmem.2⟩
  rw [hfr]
  exact congrFun (digitOf_realOfDigits g hg (C.digits σ) (fun i => hV.1 _) hp) i

include hV hg hp in
/-- The tail recursion `g · tail i = a (σ i) + tail (i+1)`. -/
theorem tail_split (i : ℕ) :
    (g : ℝ) * orbit g (C.real σ) i = (C.a (σ i) : ℝ) + orbit g (C.real σ) (i + 1) := by
  rw [orbit_split g hg, digit_real hV hg hp i]

include hV hg hσ hp in
/-- Approximate tail bounds at every depth `k` of the induction. -/
theorem tail_mem_approx (k : ℕ) (i : ℕ) :
    ((C.lo (σ i) : ℚ) : ℝ) - 1 / (g : ℝ) ^ k ≤ orbit g (C.real σ) i ∧
    orbit g (C.real σ) i ≤ ((C.hi (σ i) : ℚ) : ℝ) + 1 / (g : ℝ) ^ k := by
  induction k generalizing i with
  | zero =>
    have hmem := orbit_mem_Ico g (C.real σ) i
    obtain ⟨h0, h01, h1⟩ := hV.2.1 (σ i)
    have h0' : (0 : ℝ) ≤ ((C.lo (σ i) : ℚ) : ℝ) := by exact_mod_cast h0
    have h01' : ((C.lo (σ i) : ℚ) : ℝ) ≤ ((C.hi (σ i) : ℚ) : ℝ) := by exact_mod_cast h01
    have h1' : ((C.hi (σ i) : ℚ) : ℝ) ≤ 1 := by exact_mod_cast h1
    simp only [pow_zero, div_one]
    constructor <;> linarith [hmem.1, hmem.2]
  | succ k ih =>
    have hg0 : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
    obtain ⟨ih1, ih2⟩ := ih (i + 1)
    have hsplit := tail_split hV hg hp (σ := σ) i
    have hedge := hV.2.2.1 (σ i) (σ (i + 1)) (hσ i)
    have he1 : ((C.lo (σ i) : ℚ) : ℝ) ≤ ((C.a (σ i) : ℝ) + ((C.lo (σ (i + 1)) : ℚ) : ℝ)) / g := by
      have := hedge.1
      have h' : ((C.lo (σ i) : ℚ) : ℝ) ≤ (((C.a (σ i) : ℚ) + C.lo (σ (i + 1))) / (g : ℚ) : ℚ) := by
        exact_mod_cast this
      push_cast at h'; exact h'
    have he2 : ((C.a (σ i) : ℝ) + ((C.hi (σ (i + 1)) : ℚ) : ℝ)) / g ≤ ((C.hi (σ i) : ℚ) : ℝ) := by
      have := hedge.2
      have h' : (((C.a (σ i) : ℚ) + C.hi (σ (i + 1))) / (g : ℚ) : ℚ) ≤ ((C.hi (σ i) : ℚ) : ℝ) := by
        exact_mod_cast this
      push_cast at h'; exact h'
    have he1' := (le_div_iff₀ hg0).1 he1
    have he2' := (div_le_iff₀ hg0).1 he2
    have hpow : 1 / (g : ℝ) ^ (k + 1) = (1 / (g : ℝ) ^ k) / g := by
      rw [pow_succ]; field_simp
    have horb : orbit g (C.real σ) i = ((C.a (σ i) : ℝ) + orbit g (C.real σ) (i + 1)) / g := by
      rw [eq_div_iff hg0.ne', mul_comm]; exact hsplit
    rw [horb, hpow]
    constructor
    · rw [le_div_iff₀ hg0]
      have : (((C.lo (σ i) : ℚ) : ℝ) - 1 / (g : ℝ) ^ k / g) * g
          = ((C.lo (σ i) : ℚ) : ℝ) * g - 1 / (g : ℝ) ^ k := by field_simp
      rw [this]; linarith
    · rw [div_le_iff₀ hg0]
      have : (((C.hi (σ i) : ℚ) : ℝ) + 1 / (g : ℝ) ^ k / g) * g
          = ((C.hi (σ i) : ℚ) : ℝ) * g + 1 / (g : ℝ) ^ k := by field_simp
      rw [this]; linarith

include hV hg hσ hp in
/-- **Tail intervals.**  Every tail of the path's real lies in the certified
interval of its state. -/
theorem tail_mem (i : ℕ) :
    ((C.lo (σ i) : ℚ) : ℝ) ≤ orbit g (C.real σ) i ∧
    orbit g (C.real σ) i ≤ ((C.hi (σ i) : ℚ) : ℝ) := by
  have hg1 : (1 : ℝ) < g := by exact_mod_cast hg
  have hg0 : (0 : ℝ) < g := by linarith
  have hsmall : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, 1 / (g : ℝ) ^ k < ε := by
    intro ε hε
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hg1)
    exact ⟨k, by rwa [one_div, ← inv_pow]⟩
  constructor
  · apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨k, hk⟩ := hsmall ε hε
    have := (tail_mem_approx hV hg hσ hp k i).1
    linarith
  · apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨k, hk⟩ := hsmall ε hε
    have := (tail_mem_approx hV hg hσ hp k i).2
    linarith

include hV hg hσ hp in
/-- **Strictness.**  If some edge at or after `i` is not `hi`-extremal, the
tail at `i` is strictly below `hi`. -/
theorem tail_lt_hi (i j : ℕ) (hij : i ≤ j) (hne : ¬ C.HiMax (σ j) (σ (j + 1))) :
    orbit g (C.real σ) i < ((C.hi (σ i) : ℚ) : ℝ) := by
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  -- edge bound in ℝ, strict at `j`
  have hedgeR : ∀ t, ((C.a (σ t) : ℝ) + ((C.hi (σ (t + 1)) : ℚ) : ℝ)) / g ≤ ((C.hi (σ t) : ℚ) : ℝ) := by
    intro t
    have := (hV.2.2.1 (σ t) (σ (t + 1)) (hσ t)).2
    have h' : (((C.a (σ t) : ℚ) + C.hi (σ (t + 1))) / (g : ℚ) : ℚ) ≤ ((C.hi (σ t) : ℚ) : ℝ) := by
      exact_mod_cast this
    push_cast at h'; exact h'
  have hstrict : ((C.a (σ j) : ℝ) + ((C.hi (σ (j + 1)) : ℚ) : ℝ)) / g < ((C.hi (σ j) : ℚ) : ℝ) := by
    rcases lt_or_eq_of_le (hedgeR j) with h | h
    · exact h
    · exfalso; apply hne
      unfold HiMax
      have h' : (((C.a (σ j) : ℚ) + C.hi (σ (j + 1))) / (g : ℚ) : ℚ) = ((C.hi (σ j) : ℚ) : ℝ) := by
        push_cast; exact h
      exact_mod_cast h'
  have horb : ∀ t, orbit g (C.real σ) t = ((C.a (σ t) : ℝ) + orbit g (C.real σ) (t + 1)) / g := by
    intro t
    rw [eq_div_iff hg0.ne', mul_comm]; exact tail_split hV hg hp t
  -- strict at `j`
  have hj : orbit g (C.real σ) j < ((C.hi (σ j) : ℚ) : ℝ) := by
    rw [horb j]
    calc ((C.a (σ j) : ℝ) + orbit g (C.real σ) (j + 1)) / g
        ≤ ((C.a (σ j) : ℝ) + ((C.hi (σ (j + 1)) : ℚ) : ℝ)) / g := by
          gcongr; exact (tail_mem hV hg hσ hp (j + 1)).2
      _ < _ := hstrict
  -- propagate down to `i`
  have step : ∀ t, orbit g (C.real σ) (t + 1) < ((C.hi (σ (t + 1)) : ℚ) : ℝ) →
      orbit g (C.real σ) t < ((C.hi (σ t) : ℚ) : ℝ) := by
    intro t ht
    rw [horb t]
    calc ((C.a (σ t) : ℝ) + orbit g (C.real σ) (t + 1)) / g
        < ((C.a (σ t) : ℝ) + ((C.hi (σ (t + 1)) : ℚ) : ℝ)) / g := by gcongr
      _ ≤ _ := hedgeR t
  have descend : ∀ d i, orbit g (C.real σ) (i + d) < ((C.hi (σ (i + d)) : ℚ) : ℝ) →
      orbit g (C.real σ) i < ((C.hi (σ i) : ℚ) : ℝ) := by
    intro d
    induction d with
    | zero => intro i h; simpa using h
    | succ d ih =>
      intro i h
      exact ih i (step (i + d) h)
  exact descend (j - i) i (by rw [Nat.add_sub_cancel' hij]; exact hj)

/-- Paths with infinitely many non-`hi`-extremal edges. -/
def Mixing (σ : ℕ → Fin C.n) : Prop := ∀ i, ∃ j, i ≤ j ∧ ¬ C.HiMax (σ j) (σ (j + 1))

include hV hg hσ hp in
/-- **Carry soundness.**  Along a mixing path the true carries are the
certificate's. -/
theorem carry_eq (hmix : C.Mixing σ) (m : ℕ) (hm1 : 1 ≤ m) (hmM : m ≤ M) (i : ℕ) :
    carry g (C.real σ) m i = C.c (σ i) m := by
  obtain ⟨hlo, hhi⟩ := hV.2.2.2.1 m hmM (σ i)
  have hloR : (C.c (σ i) m : ℝ) ≤ (m : ℝ) * ((C.lo (σ i) : ℚ) : ℝ) := by
    have h' : ((C.c (σ i) m : ℚ) : ℝ) ≤ (((m : ℚ) * C.lo (σ i) : ℚ) : ℝ) := by exact_mod_cast hlo
    push_cast at h'; exact h'
  have hhiR : (m : ℝ) * ((C.hi (σ i) : ℚ) : ℝ) ≤ (C.c (σ i) m : ℝ) + 1 := by
    have h' : (((m : ℚ) * C.hi (σ i) : ℚ) : ℝ) ≤ (((C.c (σ i) m : ℚ) + 1 : ℚ) : ℝ) := by
      exact_mod_cast hhi
    push_cast at h'; exact h'
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  obtain ⟨j, hij, hne⟩ := hmix i
  have hlt := tail_lt_hi hV hg hσ hp i j hij hne
  have hge := (tail_mem hV hg hσ hp i).1
  have hfloor : ⌊(m : ℝ) * orbit g (C.real σ) i⌋ = C.c (σ i) m := by
    rw [Int.floor_eq_iff]
    push_cast
    constructor
    · calc (C.c (σ i) m : ℝ) ≤ (m : ℝ) * ((C.lo (σ i) : ℚ) : ℝ) := hloR
        _ ≤ (m : ℝ) * orbit g (C.real σ) i := by gcongr
    · calc (m : ℝ) * orbit g (C.real σ) i < (m : ℝ) * ((C.hi (σ i) : ℚ) : ℝ) := by gcongr
        _ ≤ _ := hhiR
  unfold carry
  rw [hfloor]
  rfl

include hV hg hσ hp in
/-- **The digits of `m·x` are the channel digits.** -/
theorem digit_mul_eq (hmix : C.Mixing σ) (m : ℕ) (hm1 : 1 ≤ m) (hmM : m ≤ M) (i : ℕ) :
    digitOf g (Int.fract ((m : ℝ) * C.real σ)) i = C.chDigit m (σ i) (σ (i + 1)) := by
  rw [digitOf_mul g hg, digit_real hV hg hp, carry_eq hV hg hσ hp hmix m hm1 hmM (i + 1)]
  rfl

include hV hg hσ hp in
/-- **Block avoidance.**  `w` never occurs in `m·x`, at any position. -/
theorem not_occursAt_of_path (hmix : C.Mixing σ) (m : ℕ) (hm1 : 1 ≤ m) (hmM : m ≤ M) (n : ℕ) :
    ¬ OccursAt g ((m : ℝ) * C.real σ) w n := by
  intro hocc
  let σ' : Fin (w.length + 1) → Fin C.n := fun i => σ (n + i)
  have hpath : ∀ i : Fin w.length, σ' i.succ ∈ C.next (σ' i.castSucc) := by
    intro i
    simp only [σ', Fin.val_succ, Fin.val_castSucc]
    rw [← Nat.add_assoc]
    exact hσ (n + i)
  apply hV.2.2.2.2.2 m hm1 hmM σ' hpath
  apply List.ext_getElem
  · simp
  · intro j hj1 hj2
    rw [List.getElem_ofFn]
    simp only [σ', Fin.val_castSucc, Fin.val_succ]
    have hjw : j < w.length := hj2
    have := hocc j hjw
    rw [digit_mul_eq hV hg hσ hp hmix m hm1 hmM (n + j)] at this
    rw [← this]
    rfl

end path

/-! ### Mixing two closed walks by a set of naturals -/

section mixing

variable {C}

open Classical in
/-- The path following `u` on blocks in `A` and `v` on blocks outside `A`. -/
noncomputable def mixPath (L : ℕ) (u v : Fin L → Fin C.n) (hL : 0 < L) (A : Set ℕ) :
    ℕ → Fin C.n := fun i =>
  if i / L ∈ A then u ⟨i % L, Nat.mod_lt _ hL⟩ else v ⟨i % L, Nat.mod_lt _ hL⟩

/-- A closed walk from `s₀`: starts at `s₀`, consecutive states are edges, and
the last state returns to `s₀`. -/
def IsClosedWalk (L : ℕ) (s₀ : Fin C.n) (hL : 0 < L) (u : Fin L → Fin C.n) : Prop :=
  u ⟨0, hL⟩ = s₀ ∧ (∀ j : Fin L, ∀ h : j.1 + 1 < L, u ⟨j.1 + 1, h⟩ ∈ C.next (u j)) ∧
  s₀ ∈ C.next (u ⟨L - 1, by omega⟩)

open Classical in
theorem mixPath_isPath (L : ℕ) (u v : Fin L → Fin C.n) (hL : 0 < L) (s₀ : Fin C.n)
    (hu : IsClosedWalk L s₀ hL u) (hv : IsClosedWalk L s₀ hL v) (A : Set ℕ) :
    C.IsPath (mixPath L u v hL A) := by
  intro i
  unfold mixPath
  have hmd := Nat.mod_add_div i L
  have hmlt := Nat.mod_lt i hL
  rcases Nat.lt_or_ge (i % L + 1) L with hin | hout
  · -- inside a block
    have hdm : (i + 1) / L = i / L ∧ (i + 1) % L = i % L + 1 :=
      (Nat.div_mod_unique hL).2 ⟨by omega, hin⟩
    have e : (⟨(i + 1) % L, Nat.mod_lt _ hL⟩ : Fin L) = ⟨i % L + 1, hin⟩ := Fin.ext hdm.2
    rw [hdm.1, e]
    split_ifs
    · exact hu.2.1 ⟨i % L, hmlt⟩ hin
    · exact hv.2.1 ⟨i % L, hmlt⟩ hin
  · -- block boundary: `i % L = L − 1`
    have hlast : i % L + 1 = L := by omega
    have hdm : (i + 1) / L = i / L + 1 ∧ (i + 1) % L = 0 :=
      (Nat.div_mod_unique hL).2 ⟨by rw [Nat.mul_succ]; omega, hL⟩
    have e : (⟨(i + 1) % L, Nat.mod_lt _ hL⟩ : Fin L) = ⟨0, hL⟩ := Fin.ext hdm.2
    rw [hdm.1, e]
    have hu0 : ∀ h : 0 < L, u ⟨0, h⟩ = s₀ := fun _ => hu.1
    have hv0 : ∀ h : 0 < L, v ⟨0, h⟩ = s₀ := fun _ => hv.1
    have hulast : ∀ h : i % L < L, s₀ ∈ C.next (u ⟨i % L, h⟩) := fun h => by
      have e : (⟨i % L, h⟩ : Fin L) = ⟨L - 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [e]; exact hu.2.2
    have hvlast : ∀ h : i % L < L, s₀ ∈ C.next (v ⟨i % L, h⟩) := fun h => by
      have e : (⟨i % L, h⟩ : Fin L) = ⟨L - 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [e]; exact hv.2.2
    split_ifs <;> simp only [hu0, hv0] <;> first | exact hulast _ | exact hvlast _

open Classical in
/-- Index bookkeeping: the position `t + L·j` sits in block `j` at offset `t`. -/
theorem mixPath_at (L : ℕ) (u v : Fin L → Fin C.n) (hL : 0 < L) (A : Set ℕ) (j : ℕ) (t : Fin L) :
    mixPath L u v hL A (t + L * j) = if j ∈ A then u t else v t := by
  unfold mixPath
  have h1 : (t + L * j) / L = j := by
    rw [Nat.add_mul_div_left _ _ hL, Nat.div_eq_of_lt t.2, zero_add]
  have h2 : (⟨(t + L * j) % L, Nat.mod_lt _ hL⟩ : Fin L) = t := by
    apply Fin.ext; simp only
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt t.2]
  rw [h2]
  simp only [h1]

open Classical in
/-- If both walks carry a digit `≠ g − 1`, every mixed path is proper. -/
theorem mixPath_proper (L : ℕ) (u v : Fin L → Fin C.n) (hL : 0 < L)
    (hu : ∃ t : Fin L, C.a (u t) ≠ g - 1) (hv : ∃ t : Fin L, C.a (v t) ≠ g - 1) (A : Set ℕ) :
    ProperDigits g (C.digits (mixPath L u v hL A)) := by
  intro N
  obtain ⟨tu, htu⟩ := hu
  obtain ⟨tv, htv⟩ := hv
  classical
  set j := N with hj
  by_cases hA : j ∈ A
  · refine ⟨tu + L * j, ?_, ?_⟩
    · nlinarith [tu.2]
    · show C.a (mixPath L u v hL A (tu + L * j)) ≠ g - 1
      rw [mixPath_at, if_pos hA]; exact htu
  · refine ⟨tv + L * j, ?_, ?_⟩
    · nlinarith [tv.2]
    · show C.a (mixPath L u v hL A (tv + L * j)) ≠ g - 1
      rw [mixPath_at, if_neg hA]; exact htv

/-- A walk has an internal non-`hi`-extremal edge. -/
def HasNonMax (L : ℕ) (u : Fin L → Fin C.n) : Prop :=
  ∃ t : Fin L, ∃ h : t.1 + 1 < L, ¬ C.HiMax (u t) (u ⟨t.1 + 1, h⟩)

open Classical in
/-- If both walks have an internal non-extremal edge, every mixed path is mixing. -/
theorem mixPath_mixing (L : ℕ) (u v : Fin L → Fin C.n) (hL : 0 < L)
    (hu : HasNonMax L u) (hv : HasNonMax L v) (A : Set ℕ) :
    C.Mixing (mixPath L u v hL A) := by
  intro i
  obtain ⟨tu, hu1, htu⟩ := hu
  obtain ⟨tv, hv1, htv⟩ := hv
  classical
  set j := i with hj
  by_cases hA : j ∈ A
  · refine ⟨tu + L * j, by nlinarith [tu.2], ?_⟩
    have e : tu + L * j + 1 = (⟨tu.1 + 1, hu1⟩ : Fin L) + L * j := by simp; ring
    rw [e, mixPath_at, mixPath_at, if_pos hA, if_pos hA]; exact htu
  · refine ⟨tv + L * j, by nlinarith [tv.2], ?_⟩
    have e : tv + L * j + 1 = (⟨tv.1 + 1, hv1⟩ : Fin L) + L * j := by simp; ring
    rw [e, mixPath_at, mixPath_at, if_neg hA, if_neg hA]; exact htv

open Classical in
/-- Distinct sets give distinct reals when the two walks differ in some digit. -/
theorem mixPath_real_injective (hg : 2 ≤ g) (L : ℕ) (u v : Fin L → Fin C.n) (hL : 0 < L)
    (hdig : ∀ s, C.a s < g)
    (hu : ∃ t : Fin L, C.a (u t) ≠ g - 1) (hv : ∃ t : Fin L, C.a (v t) ≠ g - 1)
    (hdiff : ∃ t : Fin L, C.a (u t) ≠ C.a (v t)) :
    Function.Injective (fun A : Set ℕ => C.real (mixPath L u v hL A)) := by
  intro A B hAB
  have hd : C.digits (mixPath L u v hL A) = C.digits (mixPath L u v hL B) := by
    have hA' := digitOf_realOfDigits g hg (C.digits (mixPath L u v hL A)) (fun _ => hdig _)
      (mixPath_proper L u v hL hu hv A)
    have hB' := digitOf_realOfDigits g hg (C.digits (mixPath L u v hL B)) (fun _ => hdig _)
      (mixPath_proper L u v hL hu hv B)
    rw [← hA', ← hB']
    exact congrArg (digitOf g) hAB
  obtain ⟨t, ht⟩ := hdiff
  ext j
  have := congrFun hd (t + L * j)
  simp only [digits] at this
  rw [mixPath_at, mixPath_at] at this
  constructor
  · intro hj
    by_contra hj'
    rw [if_pos hj, if_neg hj'] at this
    exact ht this
  · intro hj
    by_contra hj'
    rw [if_neg hj', if_pos hj] at this
    exact ht this.symm

open Classical in
/-- Some mixed path has an irrational real (`2^ℵ₀` paths, countably many rationals). -/
theorem exists_mixPath_irrational (hg : 2 ≤ g) (L : ℕ) (u v : Fin L → Fin C.n) (hL : 0 < L)
    (hdig : ∀ s, C.a s < g)
    (hu : ∃ t : Fin L, C.a (u t) ≠ g - 1) (hv : ∃ t : Fin L, C.a (v t) ≠ g - 1)
    (hdiff : ∃ t : Fin L, C.a (u t) ≠ C.a (v t)) :
    ∃ A : Set ℕ, Irrational (C.real (mixPath L u v hL A)) := by
  by_contra hcon
  push Not at hcon
  apply not_countable_set_nat
  rw [← Set.countable_univ_iff]
  have hpre : (fun A : Set ℕ => C.real (mixPath L u v hL A)) ⁻¹' (Set.range ((↑) : ℚ → ℝ))
      = Set.univ := by
    ext A; simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    have := hcon A
    unfold Irrational at this
    push Not at this
    exact this
  rw [← hpre]
  exact (Set.countable_range _).preimage_of_injOn
    (mixPath_real_injective hg L u v hL hdig hu hv hdiff).injOn

end mixing

/-- The data of a witness pair for a certificate, all decidable. -/
def WitnessPair (L : ℕ) (u v : Fin L → Fin C.n) (hL : 0 < L) (s₀ : Fin C.n) : Prop :=
  IsClosedWalk L s₀ hL u ∧ IsClosedWalk L s₀ hL v ∧
  (∃ t : Fin L, C.a (u t) ≠ g - 1) ∧ (∃ t : Fin L, C.a (v t) ≠ g - 1) ∧
  HasNonMax L u ∧ HasNonMax L v ∧ (∃ t : Fin L, C.a (u t) ≠ C.a (v t))

instance (L : ℕ) (u v : Fin L → Fin C.n) (hL : 0 < L) (s₀ : Fin C.n) :
    Decidable (C.WitnessPair L u v hL s₀) := by
  unfold WitnessPair IsClosedWalk HasNonMax HiMax; infer_instance

/-- **The escape theorem.**  A valid certificate with a witness pair yields an
irrational `x` such that no multiplier `1 ≤ m ≤ M` ever shows the block `w`
in `m·x` — at any position.  Hence `M(g, |w|) > M`. -/
theorem escape_lower_bound (hg : 2 ≤ g) (M : ℕ) (w : List ℕ) (hV : C.Valid M w)
    (L : ℕ) (u v : Fin L → Fin C.n) (hL : 0 < L) (s₀ : Fin C.n)
    (hW : C.WitnessPair L u v hL s₀) :
    ∃ x : ℝ, Irrational x ∧ ∀ m : ℕ, 1 ≤ m → m ≤ M → ∀ n, ¬ OccursAt g ((m : ℝ) * x) w n := by
  obtain ⟨hu, hv, hpu, hpv, hmu, hmv, hdiff⟩ := hW
  obtain ⟨A, hA⟩ := exists_mixPath_irrational hg L u v hL hV.1 hpu hpv hdiff
  refine ⟨C.real (mixPath L u v hL A), hA, fun m hm1 hmM n => ?_⟩
  exact not_occursAt_of_path hV hg (mixPath_isPath L u v hL s₀ hu hv A)
    (mixPath_proper L u v hL hpu hpv A) (mixPath_mixing L u v hL hmu hmv A) m hm1 hmM n

/-- The Mahler-form corollary: the lower-bound statement shape used across the
`Mahler*` files. -/
theorem escape_mahler_lower_bound (hg : 2 ≤ g) (M : ℕ) (w : List ℕ) (hV : C.Valid M w)
    (L : ℕ) (u v : Fin L → Fin C.n) (hL : 0 < L) (s₀ : Fin C.n)
    (hW : C.WitnessPair L u v hL s₀) :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ M →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt g ((m : ℝ) * α) w n := by
  obtain ⟨x, hx, h⟩ := escape_lower_bound C hg M w hV L u v hL s₀ hW
  exact ⟨x, hx, fun m hm1 hmM => ⟨0, fun n _ => h m hm1 hmM n⟩⟩

end EscapeCert

end NormalNumbers.Adder
