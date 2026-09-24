import NormalNumbers.CastingOut
import NormalNumbers.PowerBaseCount

/-!
# Swing at C3: `G4` is rich (every word at positive lower density)

`ConjC3` (frozen in `CastingOut.lean`).  Intermediate rung: positive UPPER density, `IsRichUpper`.
-/

open Finset Filter Topology NormalNumbers.PrimeLambert

namespace NormalNumbers.CastingOut

/-- Every word occurs at a set of positions of positive UPPER density. -/
noncomputable def IsRichUpper (b : ℕ) (x : ℝ) : Prop :=
  open Classical in
  ∀ w : List ℕ, (∀ d ∈ w, d < b) → ∃ c : ℝ, 0 < c ∧
    ∃ᶠ N in atTop, c * N ≤ (((range N).filter (fun n => OccursAt b x w n)).card : ℝ)

theorem isRichUpper_of_isRich (b : ℕ) (x : ℝ) (h : IsRich b x) : IsRichUpper b x := by
  intro w hw
  obtain ⟨c, hc, hev⟩ := h w hw
  exact ⟨c, hc, hev.frequently⟩


/-! ## The amplification lemma: effective disjunctivity ⇒ richness

`isDisjunctive_base` (`G4SchedBAssembly.lean`) is a proof *by contradiction from total
omission*: the omitted cylinder enters only through `exists_cover_of_omit`, which needs the
word to be missing at **every** position in order to place `orbitClosure` inside a Cantor set
of covering number `(bᵍ−1)^M`.  So the theorem as proved guarantees exactly **one** occurrence
and no density whatsoever.

The route from there to `ConjC3` is *effectivity*, not a new density argument.  If the first
occurrence of a length-`L` word is bounded by `C·b^L` then applying that bound to the `b^{L−ℓ}`
extensions `w ++ v` of a fixed length-`ℓ` word `w` produces `b^{L−ℓ}` **distinct** positions
below `C·b^L` at which `w` occurs, which is a positive proportion of `C·b^L`.  That is
`isRich_of_effDisjRate` below, and it reduces `ConjC3` to a purely effective statement.
-/

/-- **Effective disjunctivity at rate `C`**: every base-`b` word `u` occurs at some position
`< C · b^{|u|}`.  This is the optimal rate: there are `b^{|u|}` words to fit in, so no rate
below `b^{|u|}` is possible for all of them. -/
def EffDisjRate (b : ℕ) (x : ℝ) (C : ℕ) : Prop :=
  ∀ u : List ℕ, (∀ d ∈ u, d < b) → ∃ n < C * b ^ u.length, OccursAt b x u n

open PowerBase in
/-- The big-endian value of `wordOf b m k` is `k` (for `k < bᵐ`). -/
lemma blockNatVal_wordOf (b : ℕ) (hb : 0 < b) :
    ∀ (m k : ℕ), k < b ^ m → blockNatVal b (wordOf b m k) = k := by
  intro m
  induction m with
  | zero =>
      intro k hk
      have : k = 0 := by simpa using hk
      subst this; simp [blockNatVal]
  | succ m ih =>
      intro k hk
      have hq : k / b < b ^ m := by
        rw [Nat.div_lt_iff_lt_mul hb]
        calc k < b ^ (m + 1) := hk
          _ = b ^ m * b := by ring
      have hkey : k / b * b + k % b = k := Nat.div_add_mod' k b
      have := wordOf_append b m (k / b) (k % b) hb (Nat.mod_lt _ hb)
      rw [hkey] at this
      rw [this]
      simp only [blockNatVal, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [show (List.foldl (fun acc d => acc * b + d) 0 (wordOf b m (k / b)))
          = blockNatVal b (wordOf b m (k / b)) from rfl, ih _ hq, hkey]

open PowerBase in
lemma wordOf_injOn (b : ℕ) (hb : 0 < b) {m k k' : ℕ} (hk : k < b ^ m) (hk' : k' < b ^ m)
    (h : wordOf b m k = wordOf b m k') : k = k' := by
  have := blockNatVal_wordOf b hb m k hk
  rw [h, blockNatVal_wordOf b hb m k' hk'] at this
  exact this.symm

/-- Occurrence of `w ++ v` at `n` gives occurrence of `w` at `n`. -/
lemma occursAt_of_append {b : ℕ} {x : ℝ} {w v : List ℕ} {n : ℕ}
    (h : OccursAt b x (w ++ v) n) : OccursAt b x w n := by
  intro j hj
  have hj' : j < (w ++ v).length := by simp; omega
  have := h j hj'
  rwa [List.getElem_append_left hj] at this

/-- Two suffixes of the same length occurring at the same place agree. -/
lemma suffix_eq_of_occursAt {b : ℕ} {x : ℝ} {w v v' : List ℕ} {n : ℕ}
    (hlen : v.length = v'.length)
    (h : OccursAt b x (w ++ v) n) (h' : OccursAt b x (w ++ v') n) : v = v' := by
  refine List.ext_getElem hlen fun j hj hj' => ?_
  have hjw : j + w.length < (w ++ v).length := by simp; omega
  have hjw' : j + w.length < (w ++ v').length := by simp; omega
  have e1 := h (w.length + j) (by simp; omega)
  have e2 := h' (w.length + j) (by simp; omega)
  rw [List.getElem_append_right (by omega)] at e1 e2
  simp only [Nat.add_sub_cancel_left] at e1 e2
  rw [← e1, ← e2]

/-- **Amplification.**  An effective first-occurrence bound at the optimal rate `C·b^L`
upgrades one occurrence per word into positive *lower* density for every word: `IsRich`. -/
theorem isRich_of_effDisjRate (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (C : ℕ) (hC : 0 < C)
    (h : EffDisjRate b x C) : IsRich b x := by
  classical
  intro w hw
  set ℓ := w.length with hℓ
  refine ⟨1 / (C * (b : ℝ) ^ (ℓ + 1)), by positivity, ?_⟩
  have hb0 : 0 < b := by omega
  have hbR : (1 : ℝ) < b := by exact_mod_cast hb
  -- the extension count at scale `m`
  have key : ∀ m N : ℕ, C * b ^ (ℓ + m) ≤ N →
      b ^ m ≤ ((range N).filter (fun n => OccursAt b x w n)).card := by
    intro m N hN
    -- pick, for each `k < bᵐ`, an occurrence of `w ++ wordOf b m k`
    have hex : ∀ k : ℕ, ∃ n, n < C * b ^ (ℓ + m) ∧ OccursAt b x (w ++ PowerBase.wordOf b m k) n := by
      intro k
      have hdig : ∀ d ∈ w ++ PowerBase.wordOf b m k, d < b := by
        intro d hd
        rcases List.mem_append.1 hd with hd | hd
        · exact hw d hd
        · exact PowerBase.wordOf_lt b m k hb0 d hd
      obtain ⟨n, hn, hocc⟩ := h _ hdig
      exact ⟨n, by simpa [hℓ] using hn, hocc⟩
    choose f hf hfocc using hex
    refine le_trans (le_of_eq (card_range (b ^ m)).symm) ?_
    refine Finset.card_le_card_of_injOn f (fun k hk => ?_) (fun k hk k' hk' hkk => ?_)
    · refine mem_filter.2 ⟨mem_range.2 (lt_of_lt_of_le (hf k) hN), ?_⟩
      exact occursAt_of_append (hfocc k)
    · rw [coe_range, Set.mem_Iio] at hk hk'
      have h1 := hfocc k
      have h2 := hfocc k'
      rw [hkk] at h1
      have : PowerBase.wordOf b m k = PowerBase.wordOf b m k' :=
        suffix_eq_of_occursAt (by simp) h1 h2
      exact wordOf_injOn b hb0 hk hk' this
  -- for `N` large take the largest admissible `m`
  filter_upwards [eventually_ge_atTop (C * b ^ ℓ)] with N hN
  set P : ℕ → Prop := fun m => C * b ^ (ℓ + m) ≤ N with hP
  have hP0 : P 0 := by simpa [hP] using hN
  set m := Nat.findGreatest P N with hm
  have hPm : P m := Nat.findGreatest_spec (m := 0) (Nat.zero_le _) hP0
  have hmN : m ≤ N := Nat.findGreatest_le N
  -- `m + 1 ≤ N`, so `¬ P (m+1)`
  have hpow : ∀ j : ℕ, j < b ^ j := fun j =>
    lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_left hb j)
  have hm1N : m + 1 ≤ N := by
    have : b ^ m ≤ C * b ^ (ℓ + m) := by
      calc b ^ m ≤ b ^ (ℓ + m) := Nat.pow_le_pow_right hb0 (by omega)
        _ ≤ C * b ^ (ℓ + m) := Nat.le_mul_of_pos_left _ hC
    have := hpow m
    omega
  have hnot : ¬ P (m + 1) :=
    Nat.findGreatest_is_greatest (P := P) (n := N) (k := m + 1) (by rw [← hm]; omega) hm1N
  have hlt : N < C * b ^ (ℓ + m + 1) := by simpa [hP, Nat.add_assoc] using hnot
  have hcard := key m N hPm
  have hcardR : ((b : ℝ) ^ m) ≤ (((range N).filter (fun n => OccursAt b x w n)).card : ℝ) := by
    exact_mod_cast hcard
  refine le_trans ?_ hcardR
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  have hltR : (N : ℝ) < (C : ℝ) * (b : ℝ) ^ (ℓ + m + 1) := by exact_mod_cast hlt
  calc (N : ℝ) ≤ (C : ℝ) * (b : ℝ) ^ (ℓ + m + 1) := hltR.le
    _ = (b : ℝ) ^ m * ((C : ℝ) * (b : ℝ) ^ (ℓ + 1)) := by ring

/-! ## `ConjC3` reduced to an effective first-occurrence bound

`effDisjG4` is the crux after this lap.  It is *not* a density statement: it asks only that the
FIRST occurrence of a length-`L` base-`b` word in `∑ ω(n)/bⁿ` happen before `C_b · b^L`, the
optimal rate.  `isRich_of_effDisjRate` then supplies the density for free.

Distance to the existing proof.  `isDisjunctive_base` is run through the `ScheduleWitnessB`
schedule `k₄ = 8464·ℓ²·b^{2ℓ+2}`, `K = 4k₄`, `X = 2^K`, and the occurrence it produces sits
inside the sample window `Mx ≈ X = 2^{33856·ℓ²·b^{2ℓ+2}}`.  So the proof as written certifies
the rate `C·b^L` only with `C` doubly exponential in `L` — a first-occurrence bound
`N(b,ℓ) ≤ 2^{2^{O(ℓ)}}` where `effDisjG4` needs `N(b,ℓ) = O_b(b^ℓ)`.  The loss is not at a soft
step: `K` must be large for the determinant/Fourier budget `hbudget`, and `X = 2^K` is forced by
`hbig` (the row-`L¹`/`L²` bounds need `(apSample X P₀ b₀).card` comparable to `2^K`).  Any
attack on `effDisjG4` therefore needs a different mechanism from the §5 schedule — the natural
one being the Erdős–Kac normality heuristic: digit `n` of `∑ ω(n)/bⁿ` is `ω(n) + carry_n mod b`
with `ω(n)` asymptotically `N(log log n, log log n)`, whose mod-`b` discrepancy is
`≍ (log n)^{−2π²/b²}` — see `probes/g4_word_density.py`, which measures the base-4 digit
frequencies drifting `0.088 → 0.114 → 0.145` towards `1/4` for digit `1` as `N` runs
`2·10⁵ → 10⁶ → 5·10⁶`.  That heuristic predicts `N(b,ℓ) = b^{ℓ(1+o(1))}` — enough for
`IsRichUpper`-type rates but *not* obviously for the clean `O_b(b^ℓ)` of `effDisjG4`.
-/

/-- The effective form of the G4 disjunctivity theorem: for each base there is a constant `C_b`
with every length-`L` word occurring before position `C_b · b^L`. -/
def EffDisjG4 : Prop :=
  ∀ b, 3 ≤ b → ∃ C : ℕ, 0 < C ∧ EffDisjRate b (primeLambertAtBase b) C

/-- **The crux after the 2026-09-24 lap.**  Open.  See the module note above: the existing
`isDisjunctive_base` gives this with `C` doubly exponential in `L`, which is useless here. -/
theorem effDisjG4_holds : EffDisjG4 := by
  sorry

/-- **`ConjC3` from effectivity** — unconditional content of this lap. -/
theorem conjC3_of_effDisj (h : EffDisjG4) : ConjC3 := by
  intro b hb
  obtain ⟨C, hC, hrate⟩ := h b hb
  exact isRich_of_effDisjRate b (by omega) _ C hC hrate

theorem conjC3 : ConjC3 := conjC3_of_effDisj effDisjG4_holds

/-- Rung: `G4_b` is upper-rich. -/
theorem isRichUpper_primeLambertAtBase (b : ℕ) (hb : 3 ≤ b) :
    IsRichUpper b (primeLambertAtBase b) :=
  isRichUpper_of_isRich b _ (conjC3 b hb)

end NormalNumbers.CastingOut
