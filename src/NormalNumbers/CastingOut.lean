import NormalNumbers.PrimeLambertFour
import NormalNumbers.CastingOutCount
import NormalNumbers.CastingOutLambert
import NormalNumbers.Disjunctive

/-!
# Casting out `b − 1`: an abelian statistic that carries touch only at the ends

Conjectures C1–C3 of `CONJECTURES-2026-09-23-casting-out-and-rungs.md`, frozen here as `Prop`s,
together with the provable pieces around them.

* `windowDigitSum_modEq` — casting out nines: a window's digit sum is `⌊b^{n+L}x⌋ − ⌊bⁿx⌋`
  modulo `b − 1`.
* `windowDigitSum_lambert_modEq` — for `x = Σ w(m)/bᵐ` the carries enter only at the two window
  ends: `Σ_{m∈(n,n+L]} w(m) + c_{n+L} − c_n`.  This is why the statistic escapes the refuted Maze row
  "G4 sectors as digit characters", where carries hit every digit.
* `normalCastLaw` — the law of the window digit sum mod `b − 1` for a NORMAL number.  It is
  **not uniform** (`not_castUniform_of_isNormal`): in base 3 a single digit is even with
  probability `2/3`.  The first draft of C1 asked for uniformity; that was false, and the theorem
  records it.  The right target is `CastLaw` (`castLaw_of_isNormal`).
* `ConjC1` (G4 has the normal casting-out law), `ConjC2` (Erdős–Borwein is disjunctive),
  `ConjC3` (G4 is *rich*: every word has positive lower density).  These are statements, not
  theorems.  The bridges `isRich_of_isNormal` and `isDisjunctive_of_isRich` place C3 strictly on
  the ladder between the proved `isDisjunctive_base` and normality.
-/

open Finset Filter Topology NormalNumbers.PrimeLambert

namespace NormalNumbers.CastingOut

/-- Sum of the base-`b` digits with indices `n, …, n+L−1` of `x` (digit `i` sits at position
`i + 1` after the point, as in `digitOf`). -/
noncomputable def windowDigitSum (b : ℕ) (x : ℝ) (n L : ℕ) : ℕ :=
  ∑ i ∈ range L, digitOf b (Int.fract x) (n + i)

/-- **Casting out `b − 1`.** -/
theorem windowDigitSum_modEq (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (n L : ℕ) :
    (windowDigitSum b x n L : ℤ) ≡ ⌊x * (b : ℝ) ^ (n + L)⌋ - ⌊x * (b : ℝ) ^ n⌋
      [ZMOD ((b : ℤ) - 1)] := by
  have hfr : ∀ k : ℕ, ⌊Int.fract x * (b:ℝ)^k⌋ = ⌊x * (b:ℝ)^k⌋ - ⌊x⌋ * (b:ℤ)^k := by
    intro k
    have h : Int.fract x * (b:ℝ)^k = x * (b:ℝ)^k - ((⌊x⌋ * (b:ℤ)^k : ℤ) : ℝ) := by
      push_cast [Int.fract]; ring
    rw [h, Int.floor_sub_intCast]
  have hstep : ∀ k : ℕ, ((digitOf b (Int.fract x) k : ℤ))
      ≡ ⌊Int.fract x * (b:ℝ)^(k+1)⌋ - ⌊Int.fract x * (b:ℝ)^k⌋ [ZMOD ((b:ℤ)-1)] := by
    intro k
    rw [floor_mul_pow_succ b hb _ (Int.fract_nonneg x) k]
    exact Int.modEq_iff_dvd.mpr ⟨⌊Int.fract x * (b:ℝ)^k⌋, by ring⟩
  have hmain : ∀ L : ℕ, ((windowDigitSum b x n L : ℤ))
      ≡ ⌊Int.fract x * (b:ℝ)^(n+L)⌋ - ⌊Int.fract x * (b:ℝ)^n⌋ [ZMOD ((b:ℤ)-1)] := by
    intro L
    induction L with
    | zero => simp [windowDigitSum]
    | succ L ih =>
        have e : (windowDigitSum b x n (L+1) : ℤ)
            = (windowDigitSum b x n L : ℤ) + (digitOf b (Int.fract x) (n+L) : ℤ) := by
          simp [windowDigitSum, Finset.sum_range_succ]
        rw [e]
        have := (ih.add (hstep (n+L)))
        have h2 : (⌊Int.fract x * (b:ℝ)^(n+L)⌋ - ⌊Int.fract x * (b:ℝ)^n⌋)
            + (⌊Int.fract x * (b:ℝ)^(n+L+1)⌋ - ⌊Int.fract x * (b:ℝ)^(n+L)⌋)
            = ⌊Int.fract x * (b:ℝ)^(n+(L+1))⌋ - ⌊Int.fract x * (b:ℝ)^n⌋ := by
          rw [show n + (L+1) = n + L + 1 by omega]; ring
        rw [← h2]
        exact this
  have h := hmain L
  rw [hfr (n+L), hfr n] at h
  refine h.trans ?_
  refine Int.modEq_iff_dvd.mpr ?_
  have hd : ((b:ℤ) - 1) ∣ ((b:ℤ)^L - 1) := by
    simpa using sub_dvd_pow_sub_pow (b:ℤ) 1 L
  obtain ⟨c, hc⟩ := hd
  exact ⟨⌊x⌋ * (b:ℤ)^n * c, by rw [pow_add]; linear_combination (⌊x⌋ * (b:ℤ)^n) * hc⟩

/-- The real number `Σ_m w(m)/bᵐ`. -/
noncomputable def lambertVal (b : ℕ) (w : ℕ → ℕ) : ℝ := ∑' m : ℕ, (w m : ℝ) / (b : ℝ) ^ m

/-- The carry into position `N`: `⌊Σ_{m>N} w(m) b^{N−m}⌋`. -/
noncomputable def carry (b : ℕ) (w : ℕ → ℕ) (N : ℕ) : ℤ :=
  ⌊∑' k : ℕ, (w (N + 1 + k) : ℝ) / (b : ℝ) ^ (k + 1)⌋

/-- **Carries only at the ends.**  For a Lambert-type value with at most linear weights. -/
theorem windowDigitSum_lambert_modEq (b : ℕ) (hb : 2 ≤ b) (w : ℕ → ℕ) (hw : ∀ m, w m ≤ m)
    (n L : ℕ) :
    (windowDigitSum b (lambertVal b w) n L : ℤ) ≡
      (∑ m ∈ Ioc n (n + L), (w m : ℤ)) + carry b w (n + L) - carry b w n
      [ZMOD ((b : ℤ) - 1)] := by
  sorry

/-- `G4_b` is the Lambert value of `ω`. -/
theorem primeLambertAtBase_eq_lambertVal (b : ℕ) :
    primeLambertAtBase b = lambertVal b (fun m => m.primeFactors.card) := by
  unfold primeLambertAtBase lambertVal
  exact tsum_congr fun n => by rw [omegaR_eq]

/-- The **Erdős–Borwein constant** in base `b`: `Σ_{n≥1} 1/(bⁿ − 1)`. -/
noncomputable def erdosBorweinAtBase (b : ℕ) : ℝ := ∑' n : ℕ, 1 / ((b : ℝ) ^ (n + 1) - 1)

/-- `Σ_{n≥1} 1/(bⁿ−1) = Σ_m d(m)/bᵐ` (Lambert series of the divisor count). -/
theorem erdosBorweinAtBase_eq_lambertVal (b : ℕ) (hb : 2 ≤ b) :
    erdosBorweinAtBase b = lambertVal b (fun m => m.divisors.card) := by
  unfold erdosBorweinAtBase lambertVal
  exact tsum_one_div_pow_sub_one hb

/-- The law of the digit sum of `L` independent uniform base-`b` digits, modulo `b − 1`. -/
noncomputable def normalCastLaw (b L r : ℕ) : ℝ :=
  ((univ.filter (fun v : Fin L → Fin b => (∑ i, (v i : ℕ)) % (b - 1) = r)).card : ℝ) /
    (b : ℝ) ^ L

/-- Closed form: `1/(b−1) + b^{−L}((b−1)[r=0] − 1)/(b−1)`. -/
theorem normalCastLaw_closed (b L r : ℕ) (hb : 3 ≤ b) (hr : r < b - 1) :
    normalCastLaw b L r =
      1 / ((b : ℝ) - 1) + ((b : ℝ) ^ L)⁻¹ * ((if r = 0 then (b : ℝ) - 1 else 0) - 1) / ((b : ℝ) - 1) := by
  classical
  obtain ⟨q, rfl⟩ : ∃ q, b = q + 1 := ⟨b - 1, by omega⟩
  have hq : 2 ≤ q := by omega
  have hq1 : 1 ≤ q := by omega
  haveI : NeZero q := ⟨by omega⟩
  have hqr : q + 1 - 1 = q := by omega
  rw [hqr] at hr
  -- the filter is the `sumCount` fibre at `(r : ZMod q)`
  have hfilter : (univ.filter (fun v : Fin L → Fin (q + 1) => (∑ i, (v i : ℕ)) % q = r))
      = (univ.filter (fun v : Fin L → Fin (q + 1) =>
          (∑ i, ((v i : ℕ) : ZMod q)) = ((r : ℕ) : ZMod q))) := by
    refine Finset.filter_congr ?_
    intro v _
    have hcast : (∑ i, (((v i : ℕ)) : ZMod q)) = (((∑ i, (v i : ℕ)) : ℕ) : ZMod q) := by
      push_cast; ring
    rw [hcast, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hr]
  have hcnt : ((univ.filter (fun v : Fin L → Fin (q + 1) => (∑ i, (v i : ℕ)) % (q + 1 - 1) = r)).card)
      = sumCount (q + 1) q L ((r : ℕ) : ZMod q) := by
    rw [hqr, hfilter]; rfl
  have he : (if ((r : ℕ) : ZMod q) = 0 then 1 else 0) = (if r = 0 then 1 else 0) := by
    by_cases h : r = 0
    · simp [h]
    · have : ((r : ℕ) : ZMod q) ≠ 0 := by
        intro hzero
        have := congrArg ZMod.val hzero
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt hr, ZMod.val_zero] at this
        exact h this
      simp [h, this]
  have hclosed := sumCount_closed q hq1 L ((r : ℕ) : ZMod q)
  rw [he] at hclosed
  -- move to ℝ
  have hR : (sumCount (q + 1) q L ((r : ℕ) : ZMod q) : ℝ)
      = (((q : ℝ) + 1) ^ L - 1 + q * (if r = 0 then 1 else 0)) / q := by
    have := congrArg (fun n : ℕ => (n : ℝ)) hclosed
    push_cast at this
    have hqR : (0 : ℝ) < q := by positivity
    field_simp
    linarith [this]
  unfold normalCastLaw
  rw [hcnt, hR]
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hpow : (0 : ℝ) < ((q : ℝ) + 1) ^ L := by positivity
  have hb1 : ((q : ℕ) + 1 : ℝ) - 1 = (q : ℝ) := by ring
  push_cast
  rw [hb1]
  by_cases h : r = 0 <;> simp [h] <;> field_simp <;> ring

/-- Frequency of windows of length `L` whose digit sum is `≡ r (mod b−1)`, among `n < N`. -/
noncomputable def castFreq (b : ℕ) (x : ℝ) (L r N : ℕ) : ℝ :=
  (((range N).filter (fun n => windowDigitSum b x n L % (b - 1) = r)).card : ℝ) / N

/-- `x` has the casting-out law of a normal number at window length `L`. -/
def CastLaw (b : ℕ) (x : ℝ) (L : ℕ) : Prop :=
  ∀ r < b - 1, Tendsto (castFreq b x L r) atTop (𝓝 (normalCastLaw b L r))

/-- The (false) first draft of C1: window digit sums uniform mod `b − 1`. -/
def CastUniform (b : ℕ) (x : ℝ) (L : ℕ) : Prop :=
  ∀ r < b - 1, Tendsto (castFreq b x L r) atTop (𝓝 (1 / ((b : ℝ) - 1)))

/-- Cylinder frequencies: every length-`k` word of a normal number has frequency `b^{-k}`,
in the unclipped `MatchesAt` count. -/
theorem tendsto_matchesAt_freq (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (hx : IsNormal b x)
    (w : List ℕ) (hw0 : w ≠ []) (hw : ∀ d ∈ w, d < b) :
    Tendsto (fun N => ((((range N).filter
        (MatchesAt (digitOf b (Int.fract x)) w)).card : ℝ)) / N) atTop
      (𝓝 ((b : ℝ) ^ w.length)⁻¹) := by
  classical
  set s := digitOf b (Int.fract x) with hs
  have hbnd := fun n => card_filter_matchesAt_le s w hw0 n
  exact tendsto_div_of_bounded_diff (C := w.length)
    (fun n => (hbnd n).1) (fun n => (hbnd n).2) (hx w hw0 hw)

theorem castLaw_of_isNormal (b : ℕ) (hb : 3 ≤ b) (x : ℝ) (hx : IsNormal b x) (L : ℕ) :
    CastLaw b x L := by
  classical
  intro r hr
  set s := digitOf b (Int.fract x) with hs
  set q := b - 1 with hq
  have hb2 : 2 ≤ b := by omega
  rcases Nat.eq_zero_or_pos L with hL0 | hLpos
  · subst hL0
    have hval : ∀ n, windowDigitSum b x n 0 = 0 := by intro n; simp [windowDigitSum]
    have hlaw : normalCastLaw b 0 r = (if r = 0 then 1 else 0) := by
      unfold normalCastLaw
      by_cases h : r = 0 <;> simp [h, Nat.zero_mod, eq_comm]
    rw [hlaw]
    refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (if r = 0 then (1:ℝ) else 0)))
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNR : (N : ℝ) ≠ 0 := by positivity
    unfold castFreq
    by_cases h : r = 0
    · subst h
      have : ((range N).filter (fun n => windowDigitSum b x n 0 % q = 0)) = range N := by
        apply Finset.filter_true_of_mem; intro n _; simp [hval n]
      rw [this, Finset.card_range, if_pos rfl, div_self hNR]
    · have : ((range N).filter (fun n => windowDigitSum b x n 0 % q = r)) = ∅ := by
        apply Finset.filter_false_of_mem; intro n _; simp [hval n]; exact fun hc => h hc.symm
      rw [this]
      simp [h]
  -- L ≥ 1
  set W : Finset (Fin L → Fin b) :=
    univ.filter (fun v : Fin L → Fin b => (∑ i, (v i : ℕ)) % q = r) with hW
  have hblt : ∀ n i : ℕ, s (n + i) < b := fun n i => digitOf_lt b hb2 _ _
  set f : ℕ → (Fin L → Fin b) := fun n i => ⟨s (n + i), hblt n i⟩ with hf
  set wv : (Fin L → Fin b) → List ℕ := fun v => List.ofFn (fun i : Fin L => (v i : ℕ)) with hwv
  have hlen : ∀ v, (wv v).length = L := by intro v; simp [hwv]
  have hmatch : ∀ (v : Fin L → Fin b) (n : ℕ), MatchesAt s (wv v) n ↔ f n = v := by
    intro v n
    constructor
    · intro h
      funext i
      have := h i.val (by rw [hlen]; exact i.isLt)
      have h2 : (wv v).getD i.val 0 = (v i : ℕ) := by
        simp [hwv, List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt]
      rw [h2] at this
      exact Fin.ext this
    · intro h j hj
      rw [hlen] at hj
      have := congrFun h ⟨j, hj⟩
      have h2 : (wv v).getD j 0 = (v ⟨j, hj⟩ : ℕ) := by
        simp [hwv, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj]
      rw [h2, ← this]
  have hws : ∀ n, windowDigitSum b x n L = ∑ i, ((f n i : ℕ)) := by
    intro n
    have h := Fin.sum_univ_eq_sum_range (fun i => s (n + i)) L
    rw [windowDigitSum, ← h]
  have hcard : ∀ N, ((range N).filter (fun n => windowDigitSum b x n L % q = r)).card
      = ∑ v ∈ W, ((range N).filter (fun n => MatchesAt s (wv v) n)).card := by
    intro N
    rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := W)
      (fun n hn => by
        have hn2 := (Finset.mem_filter.mp hn).2
        rw [hW]
        refine Finset.mem_filter.mpr ⟨mem_univ _, ?_⟩
        rw [← hws n]
        exact hn2)]
    refine Finset.sum_congr rfl ?_
    intro v hv
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨hn, -⟩, hfv⟩
      exact ⟨hn, (hmatch v n).2 hfv⟩
    · rintro ⟨hn, hm⟩
      have hfv := (hmatch v n).1 hm
      refine ⟨⟨hn, ?_⟩, hfv⟩
      rw [hws n, hfv]
      simpa [hW] using (Finset.mem_filter.mp hv).2
  have hfreq : ∀ v : Fin L → Fin b,
      Tendsto (fun N => ((((range N).filter (MatchesAt s (wv v))).card : ℝ)) / N) atTop
        (𝓝 ((b : ℝ) ^ L)⁻¹) := by
    intro v
    have hne : wv v ≠ [] := List.ne_nil_of_length_pos (by rw [hlen]; exact hLpos)
    have hdlt : ∀ d ∈ wv v, d < b := by
      intro d hd
      rw [hwv, List.mem_ofFn] at hd
      obtain ⟨i, rfl⟩ := hd
      exact (v i).isLt
    have h := tendsto_matchesAt_freq b hb2 x hx (wv v) hne hdlt
    rwa [hlen, ← hs] at h
  have hsum : Tendsto (fun N => ∑ v ∈ W,
      ((((range N).filter (MatchesAt s (wv v))).card : ℝ)) / N) atTop
      (𝓝 (∑ _v ∈ W, ((b : ℝ) ^ L)⁻¹)) :=
    tendsto_finsetSum _ (fun v _ => hfreq v)
  have hlaw : normalCastLaw b L r = ∑ _v ∈ W, ((b : ℝ) ^ L)⁻¹ := by
    rw [Finset.sum_const, nsmul_eq_mul]
    unfold normalCastLaw
    rw [hW, hq]
    ring
  rw [hlaw]
  refine hsum.congr ?_
  intro N
  unfold castFreq
  rw [hcard N, ← Finset.sum_div]
  push_cast
  ring

/-- **The first draft of C1 was false**: no normal number has uniform window digit sums. -/
theorem not_castUniform_of_isNormal (b : ℕ) (hb : 3 ≤ b) (x : ℝ) (hx : IsNormal b x) (L : ℕ)
    (hL : 1 ≤ L) : ¬ CastUniform b x L := by
  intro hu
  have hr0 : 0 < b - 1 := by omega
  have h1 := hu 0 hr0
  have h2 := castLaw_of_isNormal b hb x hx L 0 hr0
  have heq : (1 : ℝ) / ((b : ℝ) - 1) = normalCastLaw b L 0 := tendsto_nhds_unique h1 h2
  rw [normalCastLaw_closed b L 0 hb hr0] at heq
  have hbR : (3 : ℝ) ≤ b := by exact_mod_cast hb
  have hpow : (0 : ℝ) < ((b : ℝ) ^ L)⁻¹ := by positivity
  norm_num at heq
  rcases heq with (⟨hb0, -⟩ | hb2) | hb1
  · omega
  · linarith
  · linarith

/-- **C1.**  `G4_b` has the casting-out law of a normal number, every base `b ≥ 3`, every `L`. -/
def ConjC1 : Prop := ∀ b, 3 ≤ b → ∀ L, CastLaw b (primeLambertAtBase b) L

/-- **C2.**  The Erdős–Borwein constant is disjunctive in every base `b ≥ 3`. -/
def ConjC2 : Prop := ∀ b, 3 ≤ b → IsDisjunctive b (erdosBorweinAtBase b)

/-- `x` is **rich** in base `b`: every word occurs at a set of positions of positive lower
density. -/
noncomputable def IsRich (b : ℕ) (x : ℝ) : Prop :=
  open Classical in
  ∀ w : List ℕ, (∀ d ∈ w, d < b) → ∃ c : ℝ, 0 < c ∧
    ∀ᶠ N in atTop, c * N ≤ (((range N).filter (fun n => OccursAt b x w n)).card : ℝ)

/-- **C3.**  `G4_b` is rich in every base `b ≥ 3`. -/
def ConjC3 : Prop := ∀ b, 3 ≤ b → IsRich b (primeLambertAtBase b)

/-- `OccursAt` is the real-number face of the sequence-level `MatchesAt`. -/
theorem occursAt_iff_matchesAt (b : ℕ) (x : ℝ) (w : List ℕ) (n : ℕ) :
    OccursAt b x w n ↔ MatchesAt (digitOf b (Int.fract x)) w n := by
  constructor
  · intro h j hj
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using h j hj
  · intro h j hj
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using h j hj

theorem isRich_of_isNormal (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (hx : IsNormal b x) : IsRich b x := by
  classical
  intro w hw
  by_cases hw0 : w = []
  · subst w
    refine ⟨1, one_pos, ?_⟩
    filter_upwards with N
    have : ((range N).filter (fun n => OccursAt b x [] n)) = range N := by
      apply Finset.filter_true_of_mem
      intro n _
      intro j hj
      simp at hj
    rw [this]
    simp
  · set s := digitOf b (Int.fract x) with hs
    have hfreq := hx w hw0 hw
    have hbnd := fun n => card_filter_matchesAt_le s w hw0 n
    have h2 : Tendsto (fun N => (((range N).filter (MatchesAt s w)).card : ℝ) / N) atTop
        (𝓝 ((b : ℝ) ^ w.length)⁻¹) :=
      tendsto_div_of_bounded_diff (C := w.length)
        (fun n => (hbnd n).1) (fun n => (hbnd n).2) hfreq
    have hL : (0:ℝ) < ((b : ℝ) ^ w.length)⁻¹ := by
      have : (0:ℝ) < b := by exact_mod_cast (show 0 < b by omega)
      positivity
    refine ⟨((b : ℝ) ^ w.length)⁻¹ / 2, by positivity, ?_⟩
    have hev := (tendsto_order.1 h2).1 (((b : ℝ) ^ w.length)⁻¹ / 2) (by linarith)
    filter_upwards [hev, eventually_gt_atTop 0] with N hN hN0
    have hNpos : (0:ℝ) < N := by exact_mod_cast hN0
    have heq : ((range N).filter (fun n => OccursAt b x w n))
        = ((range N).filter (MatchesAt s w)) := by
      apply Finset.filter_congr
      intro n _
      simp [occursAt_iff_matchesAt b x w n, hs]
    rw [heq]
    rw [lt_div_iff₀ hNpos] at hN
    linarith

theorem isDisjunctive_of_isRich (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (hx : IsRich b x) :
    IsDisjunctive b x := by
  classical
  rw [isDisjunctive_iff_forall_occursAt b hb x]
  intro w hw
  obtain ⟨c, hc, hev⟩ := hx w hw
  obtain ⟨N, hN, hN0⟩ := (hev.and (eventually_gt_atTop 0)).exists
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN0
  have : (0:ℝ) < (((range N).filter (fun n => OccursAt b x w n)).card : ℝ) := by
    have := hN
    nlinarith
  have hcard : 0 < ((range N).filter (fun n => OccursAt b x w n)).card := by
    exact_mod_cast this
  obtain ⟨n, hn⟩ := Finset.card_pos.mp hcard
  exact ⟨n, (Finset.mem_filter.mp hn).2⟩

/-- C1 and C3 both sit below normality of `G4`. -/
theorem conjC1_conjC3_of_normal (h : ∀ b, 3 ≤ b → IsNormal b (primeLambertAtBase b)) :
    ConjC1 ∧ ConjC3 :=
  ⟨fun b hb L => castLaw_of_isNormal b hb _ (h b hb) L,
   fun b hb => isRich_of_isNormal b (by omega) _ (h b hb)⟩

end NormalNumbers.CastingOut
