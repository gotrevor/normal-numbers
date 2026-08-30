/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderCarry
import NormalNumbers.AdderAutomaton

/-!
# The shadowing lemma (module 2½ of the adder wing)

Brief: `BRIEF-adder-disjunction-formalization.md` §"State, step relation".

The **true state** of the family at digit position `m` is built from the real
carries and digits: per channel, `chanCode = carry·winSize + window`, where
the window packs the `ℓ-1` digits of `z = a·X + b·Y` at positions
`m, …, m+ℓ-2` (LSB first); `famState` folds the channels exactly as
`famSize` (channel 0 least significant).

**Shadowing** (`famState_shadow` / `hstep_famState`): if no channel's word
occurs at position `m`, the true states at `m+1` and `m` are related by one
legal automaton step under the input digits `(x_m, y_m)`.  The proof per
channel is the column identity of `AdderCarry` plus the observation that the
freshly formed `ℓ`-bit window equals the word-value iff the word occurs at
`m` (bit-list value injectivity, `bitsVal_inj`).

Convention note: `winCode z m k` takes the digit **count** `k` directly
(so the channel window is `winCode z m (ch.ell - 1)`, and the formed
`ℓ`-bit window is `winCode z m ch.ell`).
-/

namespace NormalNumbers.Adder

open NormalNumbers

/-! ## Bit-list values -/

/-- The value of a bit list, LSB first (same fold as `Channel.wordVal`). -/
def bitsVal (l : List ℕ) : ℕ := l.foldr (fun d acc => d + 2 * acc) 0

@[simp] theorem bitsVal_nil : bitsVal [] = 0 := rfl

@[simp] theorem bitsVal_cons (d : ℕ) (l : List ℕ) :
    bitsVal (d :: l) = d + 2 * bitsVal l := rfl

theorem Channel.wordVal_eq_bitsVal (ch : Channel) : ch.wordVal = bitsVal ch.word := rfl

/-- Equal-length bit lists with equal values are equal. -/
theorem bitsVal_inj : ∀ (l₁ l₂ : List ℕ), (∀ d ∈ l₁, d ≤ 1) → (∀ d ∈ l₂, d ≤ 1) →
    l₁.length = l₂.length → bitsVal l₁ = bitsVal l₂ → l₁ = l₂
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, _, hlen, _ => by simp at hlen
  | d₁ :: t₁, d₂ :: t₂, h₁, h₂, hlen, hval => by
    have hd₁ : d₁ ≤ 1 := h₁ _ (by simp)
    have hd₂ : d₂ ≤ 1 := h₂ _ (by simp)
    simp only [bitsVal_cons] at hval
    have hd : d₁ = d₂ := by omega
    have ht : bitsVal t₁ = bitsVal t₂ := by omega
    have := bitsVal_inj t₁ t₂ (fun d hd => h₁ d (by simp [hd]))
      (fun d hd => h₂ d (by simp [hd])) (by simpa using hlen) ht
    rw [hd, this]

/-- `bitsVal` of a mapped range is the weighted digit sum. -/
theorem bitsVal_map_range (f : ℕ → ℕ) : ∀ k,
    bitsVal ((List.range k).map f) = ∑ j ∈ Finset.range k, f j * 2 ^ j := by
  intro k
  induction k generalizing f with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, bitsVal_cons,
      ih (f ∘ Nat.succ), Finset.sum_range_succ']
    simp only [Function.comp_apply]
    rw [Finset.mul_sum]
    have : ∀ j ∈ Finset.range n, 2 * (f (j + 1) * 2 ^ j) = f (j + 1) * 2 ^ (j + 1) := by
      intro j _; rw [pow_succ]; ring
    rw [Finset.sum_congr rfl this, pow_zero, mul_one]
    ring

/-! ## The true state -/

/-- The `k` digits of `z` at positions `m, …, m+k-1`, packed LSB first. -/
noncomputable def winCode (z : ℝ) (m k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range k, (rdigit z (m + j)).toNat * 2 ^ j

theorem rdigit_toNat_le_one (z : ℝ) (i : ℕ) : (rdigit z i).toNat ≤ 1 := by
  have h1 := rdigit_le_one z i
  have h0 := rdigit_nonneg z i
  omega

theorem winCode_lt (z : ℝ) (m : ℕ) : ∀ k, winCode z m k < 2 ^ k := by
  intro k
  induction k with
  | zero => simp [winCode]
  | succ n ih =>
    have hd : (rdigit z (m + n)).toNat * 2 ^ n ≤ 2 ^ n := by
      have := rdigit_toNat_le_one z (m + n)
      calc (rdigit z (m + n)).toNat * 2 ^ n ≤ 1 * 2 ^ n :=
            Nat.mul_le_mul_right _ this
        _ = 2 ^ n := one_mul _
    have hsum : winCode z m (n + 1) = winCode z m n + (rdigit z (m + n)).toNat * 2 ^ n := by
      unfold winCode; rw [Finset.sum_range_succ]
    have hp : (2:ℕ) ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ]; ring
    omega

/-- The formed `ℓ`-bit window equals the word list iff the word occurs at `m`
(word digits are bits; the word list is recovered digitwise). -/
theorem occursAt_iff_winList (z : ℝ) (w : List ℕ) (m : ℕ) :
    OccursAt 2 z w m ↔ (List.range w.length).map (fun j => (rdigit z (m + j)).toNat) = w := by
  have hdig : ∀ i, digitOf 2 (Int.fract z) i = (rdigit z i).toNat := by
    intro i
    have h := rdigit_eq_digitOf z i
    omega
  constructor
  · intro h
    apply List.ext_getElem (by simp)
    intro j hj₁ hj₂
    simp only [List.getElem_map, List.getElem_range]
    rw [← hdig (m + j)]
    exact h j (by simpa using hj₁)
  · intro h j hj
    rw [hdig (m + j)]
    have hj' : j < ((List.range w.length).map fun i => (rdigit z (m + i)).toNat).length := by
      simpa using hj
    calc (rdigit z (m + j)).toNat
        = ((List.range w.length).map fun i => (rdigit z (m + i)).toNat)[j]'hj' := by simp
      _ = w[j] := by simp only [h]

/-- The channel's true state at position `m`: carry `T(m)` (high part) and
the `ℓ-1` deeper digits of `z` at `m, …, m+ℓ-2` (low part). -/
noncomputable def chanCode (ch : Channel) (X Y : ℝ) (m : ℕ) : ℕ :=
  (carryT ch.a ch.b X Y m).toNat * ch.winSize
    + winCode (ch.a * X + ch.b * Y) m (ch.ell - 1)

theorem chanCode_lt (ch : Channel) (X Y : ℝ) (m : ℕ) (hab : 1 ≤ ch.a + ch.b) :
    chanCode ch X Y m < ch.size := by
  have hT0 := carryT_nonneg ch.a ch.b X Y m
  have hT1 := carryT_le ch.a ch.b X Y m hab
  have hcarry : (carryT ch.a ch.b X Y m).toNat < ch.carrySize := by
    have : ch.carrySize = ch.a + ch.b := by
      unfold Channel.carrySize; omega
    omega
  have hwin : winCode (ch.a * X + ch.b * Y) m (ch.ell - 1) < ch.winSize :=
    winCode_lt _ _ _
  calc chanCode ch X Y m
      < (carryT ch.a ch.b X Y m).toNat * ch.winSize + ch.winSize :=
        Nat.add_lt_add_left hwin _
    _ = ((carryT ch.a ch.b X Y m).toNat + 1) * ch.winSize := by ring
    _ ≤ ch.carrySize * ch.winSize := Nat.mul_le_mul_right _ (by omega)

/-- The family's true state: channels folded exactly as `famSize`. -/
noncomputable def famState : List Channel → ℝ → ℝ → ℕ → ℕ
  | [], _, _, _ => 0
  | ch :: rest, X, Y, m => chanCode ch X Y m + ch.size * famState rest X Y m

/-! ## The per-channel shadowing step -/

/-- **Per-channel shadowing**: if `ch`'s word does not occur at position `m`
in `z = a·X + b·Y`, then `Channel.pred` maps the true deeper state at `m+1`
to the true state at `m` under the input digits `(x_m, y_m)`. -/
theorem chan_shadow (ch : Channel) (X Y : ℝ) (m : ℕ)
    (_hab : 1 ≤ ch.a + ch.b) (hell : 1 ≤ ch.ell)
    (hword : ∀ d ∈ ch.word, d ≤ 1)
    (hnocc : ¬ OccursAt 2 (ch.a * X + ch.b * Y) ch.word m) :
    ch.pred (rdigit X m).toNat (rdigit Y m).toNat (chanCode ch X Y (m + 1))
      = some (chanCode ch X Y m) := by
  set z : ℝ := ch.a * X + ch.b * Y with hz
  have hwpos := ch.winSize_pos
  -- decompose the deeper code
  have hwlt : winCode z (m + 1) (ch.ell - 1) < ch.winSize := winCode_lt _ _ _
  have hdiv : chanCode ch X Y (m + 1) / ch.winSize
      = (carryT ch.a ch.b X Y (m + 1)).toNat := by
    unfold chanCode
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hwpos, Nat.div_eq_of_lt hwlt,
      Nat.zero_add]
  have hmod : chanCode ch X Y (m + 1) % ch.winSize = winCode z (m + 1) (ch.ell - 1) := by
    unfold chanCode
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hwlt]
  -- the ℕ column identity
  have hcol : ch.a * (rdigit X m).toNat + ch.b * (rdigit Y m).toNat
        + (carryT ch.a ch.b X Y (m + 1)).toNat
      = (rdigit z m).toNat + 2 * (carryT ch.a ch.b X Y m).toNat := by
    have hx := rdigit_nonneg X m
    have hy := rdigit_nonneg Y m
    have hzd := rdigit_nonneg z m
    have hT1 := carryT_nonneg ch.a ch.b X Y (m + 1)
    have hT0 := carryT_nonneg ch.a ch.b X Y m
    zify
    rw [Int.toNat_of_nonneg hx, Int.toNat_of_nonneg hy, Int.toNat_of_nonneg hzd,
      Int.toNat_of_nonneg hT1, Int.toNat_of_nonneg hT0]
    have := carry_column ch.a ch.b X Y m
    rw [hz]
    linarith
  set v : ℕ := ch.a * (rdigit X m).toNat + ch.b * (rdigit Y m).toNat
      + chanCode ch X Y (m + 1) / ch.winSize with hv
  have hdm : (rdigit z m).toNat ≤ 1 := rdigit_toNat_le_one z m
  have hvmod : v % 2 = (rdigit z m).toNat := by rw [hv, hdiv]; omega
  have hvdiv : v / 2 = (carryT ch.a ch.b X Y m).toNat := by rw [hv, hdiv]; omega
  -- the formed ℓ-bit window is the full window at m
  have hformed : v % 2 + 2 * (chanCode ch X Y (m + 1) % ch.winSize)
      = winCode z m ch.ell := by
    rw [hvmod, hmod]
    unfold winCode
    rw [show ch.ell = (ch.ell - 1) + 1 from by omega, Finset.sum_range_succ']
    rw [Finset.mul_sum]
    have : ∀ j ∈ Finset.range (ch.ell - 1),
        2 * ((rdigit z (m + 1 + j)).toNat * 2 ^ j)
          = (rdigit z (m + (j + 1))).toNat * 2 ^ (j + 1) := by
      intro j _
      rw [show m + (j + 1) = m + 1 + j from by omega, pow_succ]
      ring
    simp only [Nat.add_sub_cancel, Nat.add_zero, pow_zero, mul_one] at *
    rw [Finset.sum_congr rfl this]
    omega
  -- the formed window differs from the word (else the word occurs at m)
  have hne : v % 2 + 2 * (chanCode ch X Y (m + 1) % ch.winSize) ≠ ch.wordVal := by
    rw [hformed]
    intro heq
    apply hnocc
    rw [occursAt_iff_winList]
    refine bitsVal_inj _ ch.word ?_ hword (by simp) ?_
    · intro d hd
      simp only [List.mem_map, List.mem_range] at hd
      obtain ⟨j, _, rfl⟩ := hd
      exact rdigit_toNat_le_one z (m + j)
    · rw [bitsVal_map_range]
      rw [ch.wordVal_eq_bitsVal] at heq
      simpa [winCode, Channel.ell] using heq
  -- the emitted state is the true state at m
  have hmodwin : winCode z m ch.ell % ch.winSize = winCode z m (ch.ell - 1) := by
    have hsplit : winCode z m ch.ell
        = winCode z m (ch.ell - 1) + 2 ^ (ch.ell - 1) * (rdigit z (m + (ch.ell - 1))).toNat := by
      conv_lhs => rw [show ch.ell = (ch.ell - 1) + 1 from by omega]
      unfold winCode
      rw [Finset.sum_range_succ]
      ring
    rw [hsplit]
    unfold Channel.winSize
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (winCode_lt z m (ch.ell - 1))]
  -- assemble
  unfold Channel.pred
  rw [← hv, if_neg hne]
  congr 1
  rw [hvdiv, hformed, hmodwin]
  unfold chanCode
  rw [← hz]

/-! ## The family-level shadowing lemma -/

/-- **Shadowing**: if no channel's word occurs at position `m`, the family
predecessor maps the true state at `m+1` to the true state at `m` under the
input digits `(x_m, y_m)`. -/
theorem famState_shadow (chs : List Channel) (X Y : ℝ) (m : ℕ)
    (hab : ∀ ch ∈ chs, 1 ≤ ch.a + ch.b) (hell : ∀ ch ∈ chs, 1 ≤ ch.ell)
    (hword : ∀ ch ∈ chs, ∀ d ∈ ch.word, d ≤ 1)
    (hnocc : ∀ ch ∈ chs, ¬ OccursAt 2 (ch.a * X + ch.b * Y) ch.word m) :
    famPred chs (rdigit X m).toNat (rdigit Y m).toNat (famState chs X Y (m + 1))
      = some (famState chs X Y m) := by
  induction chs with
  | nil => rfl
  | cons ch rest ih =>
    have hab₀ : 1 ≤ ch.a + ch.b := hab ch (by simp)
    have hclt : chanCode ch X Y (m + 1) < ch.size := chanCode_lt ch X Y (m + 1) hab₀
    show famPred (ch :: rest) _ _ _ = _
    simp only [famPred, famState]
    have hmod : (chanCode ch X Y (m + 1) + ch.size * famState rest X Y (m + 1)) % ch.size
        = chanCode ch X Y (m + 1) := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hclt]
    have hdiv : (chanCode ch X Y (m + 1) + ch.size * famState rest X Y (m + 1)) / ch.size
        = famState rest X Y (m + 1) := by
      rw [Nat.add_mul_div_left _ _ ch.size_pos, Nat.div_eq_of_lt hclt, Nat.zero_add]
    rw [hmod, hdiv,
      chan_shadow ch X Y m hab₀ (hell ch (by simp)) (hword ch (by simp))
        (hnocc ch (by simp)),
      ih (fun c hc => hab c (by simp [hc])) (fun c hc => hell c (by simp [hc]))
        (fun c hc => hword c (by simp [hc])) (fun c hc => hnocc c (by simp [hc]))]

theorem famState_lt (chs : List Channel) (X Y : ℝ) (m : ℕ)
    (hab : ∀ ch ∈ chs, 1 ≤ ch.a + ch.b) :
    famState chs X Y m < famSize chs := by
  induction chs with
  | nil => simp [famState, famSize]
  | cons ch rest ih =>
    have h₀ : chanCode ch X Y m < ch.size := chanCode_lt ch X Y m (hab ch (by simp))
    have h₁ : famState rest X Y m < famSize rest :=
      ih (fun c hc => hab c (by simp [hc]))
    show chanCode ch X Y m + ch.size * famState rest X Y m < ch.size * famSize rest
    calc chanCode ch X Y m + ch.size * famState rest X Y m
        < ch.size + ch.size * famState rest X Y m := by omega
      _ = ch.size * (famState rest X Y m + 1) := by ring
      _ ≤ ch.size * famSize rest := Nat.mul_le_mul_left _ (by omega)

/-- Shadowing in `HStep` form, with the packed input `σ = x + 2y`. -/
theorem hstep_famState (chs : List Channel) (X Y : ℝ) (m : ℕ)
    (hab : ∀ ch ∈ chs, 1 ≤ ch.a + ch.b) (hell : ∀ ch ∈ chs, 1 ≤ ch.ell)
    (hword : ∀ ch ∈ chs, ∀ d ∈ ch.word, d ≤ 1)
    (hnocc : ∀ ch ∈ chs, ¬ OccursAt 2 (ch.a * X + ch.b * Y) ch.word m) :
    HStep chs (famState chs X Y m)
      ((rdigit X m).toNat + 2 * (rdigit Y m).toNat) (famState chs X Y (m + 1)) := by
  unfold HStep
  have hx : (rdigit X m).toNat ≤ 1 := rdigit_toNat_le_one X m
  have hy : (rdigit Y m).toNat ≤ 1 := rdigit_toNat_le_one Y m
  have h₁ : ((rdigit X m).toNat + 2 * (rdigit Y m).toNat) % 2 = (rdigit X m).toNat := by
    omega
  have h₂ : ((rdigit X m).toNat + 2 * (rdigit Y m).toNat) / 2 = (rdigit Y m).toNat := by
    omega
  rw [h₁, h₂]
  exact famState_shadow chs X Y m hab hell hword hnocc
