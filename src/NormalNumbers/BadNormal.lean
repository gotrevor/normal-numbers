/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.ComputableNormalB
import NormalNumbers.CFCylinder
import NormalNumbers.ExplicitOmegaK

/-!
# A computable absolutely normal number with partial quotients in `{1, 2}`

Audit: `docs/BAD-NORMAL-AUDIT-2026-10-03.md` (sweep `docs/OPEN-PROBLEMS-SWEEP-2026-10-03b.md` §1).

**Target.**  Montgomery, *Ten Lectures on the Interface between Analytic Number Theory and
Harmonic Analysis* (1994), p. 203, asks for "a normal number whose continued fraction coefficients
are bounded".  Bugeaud, *Distribution modulo one and Diophantine approximation* (2012), §7.7:
"No explicit example of such a number has been exhibited yet."  Queffélec, *Old and new results on
normality* (IMS LN 48, 2006; arXiv math/0608249) §4: "no explicit normal numbers in BAD have been
constructed yet."  Existence is Kaufman 1980 (`N ≥ 3`) + R. C. Baker's remark, Queffélec–Ramaré
2003 (`N = 2`), Jordan–Sahlsten 2016, Hochman–Shmerkin 2015.

**Mechanism.**  Fair coins `ω ↦ cfCoin ω = [0; 1+ω₀, 1+ω₁, …]`; the law is the Bernoulli(1/2)
measure on `E_{1,2}`.  Its polynomial Fourier decay is cited (`Literature.SahlstenStevensBernoulli12`);
the CF cylinder endpoints `cfVal w`, `cfVal (bumpLast w)` give exact rational lower approximations
within `1/(q_D(q_D+q_{D-1})) ≤ 2^{-D}` (`Abad_bounds`); then the proved all-bases derandomizer
`ComputableNormalB.exists_computable_absNormal` gives a computable coin sequence.

**Known-false siblings** (the mechanism must refuse them, and does):
* an atom (a single CF, e.g. the periodic `[0; 1, 1, …] = 1/φ`, or any quadratic irrational):
  the decay hypothesis fails for every Dirac measure (`not_decay_const`, proved), so the engine
  cannot be fed one (`not_decay_cfCoin_fixed`, proved);
* CF-normality of `cfCoin e`: false (all digits `≤ 2`); nothing here claims it.

⚠️ "Computable", not "explicit" in Queffélec's sense: the derandomizer is primitive recursive and
astronomically slow.
-/

open MeasureTheory Filter Topology

namespace NormalNumbers.BadNormal

open Derandomize DecayAeNormal ExplicitOmegaK

/-! ## The coin-to-CF map -/

/-- Coin `false ↦` partial quotient `1`, `true ↦ 2`. -/
def dig (b : Bool) : ℕ := if b then 2 else 1

/-- The CF word of a coin prefix. -/
def bWord (p : List Bool) : List ℕ := p.map dig

/-- **`[0; 1+ω₀, 1+ω₁, …]`**: the limit of the convergents `cfVal (bWord (pre ω n))`. -/
noncomputable def cfCoin (ω : ℕ → Bool) : ℝ :=
  limUnder atTop fun n : ℕ => ((cfVal (bWord (pre ω n)) : ℚ) : ℝ)

theorem dig_pos (b : Bool) : 1 ≤ dig b := by cases b <;> simp [dig]

theorem bWord_pos (p : List Bool) : ∀ a ∈ bWord p, 1 ≤ a := by
  intro a ha
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha
  exact dig_pos b

theorem cfVal_nonneg : ∀ l : List ℕ, 0 ≤ cfVal l
  | [] => by simp [cfVal]
  | a :: l => by
      have := cfVal_nonneg l
      simp only [cfVal]
      positivity

/-! ## Exact lower approximations for the engine -/

/-- Lower endpoint of the CF cylinder of the prefix `p`: the smaller of `[0; w]` and
`[0; w₁, …, w_D + 1]` (`w = bWord p`).  For `p = []` this is `min 0 1 = 0`. -/
noncomputable def Abad (p : List Bool) : ℝ :=
  min ((cfVal (bWord p) : ℚ) : ℝ) ((cfVal (bumpLast (bWord p)) : ℚ) : ℝ)

/-- Its base-`b` floors, read from the continuants (`cfVal w = cfP w / cfK w` for `w ≠ []`). -/
def PsiBad (b m : ℕ) (p : List Bool) : ℕ :=
  if p = [] then 0 else
    min (cfP (bWord p) * b ^ m / cfK (bWord p))
      (cfP (bumpLast (bWord p)) * b ^ m / cfK (bumpLast (bWord p)))

theorem Abad_nonneg (p : List Bool) : 0 ≤ Abad p := by
  unfold Abad
  exact le_min (by exact_mod_cast cfVal_nonneg _) (by exact_mod_cast cfVal_nonneg _)

/-! ## CF interval machinery for the leaves -/

/-- `[0; a₁, …, a_D + s]`-style tail evaluation: `gcf w s = [0; w, (tail of value s)]`. -/
noncomputable def gcf : List ℕ → ℝ → ℝ
  | [], s => s
  | a :: l, s => 1 / (a + gcf l s)

theorem cfVal_append_real (w u : List ℕ) :
    ((cfVal (w ++ u) : ℚ) : ℝ) = gcf w (cfVal u) := by
  induction w with
  | nil => simp [gcf]
  | cons a l ih => simp only [List.cons_append, cfVal, gcf]; push_cast; rw [ih]

theorem cfVal_append_one : ∀ w : List ℕ, cfVal (w ++ [1]) = cfVal (bumpLast w)
  | [] => by simp [bumpLast, cfVal]
  | [a] => by simp [bumpLast, cfVal]
  | a :: b :: l => by
      rw [bumpLast_cons (by simp), List.cons_append]
      simp only [cfVal]
      rw [cfVal_append_one (b :: l)]

theorem gcf_zero (w : List ℕ) : gcf w 0 = cfVal w := by
  have := (cfVal_append_real w []).symm
  rw [List.append_nil] at this
  simpa [cfVal] using this

theorem gcf_one (w : List ℕ) : gcf w 1 = cfVal (bumpLast w) := by
  rw [← cfVal_append_one, cfVal_append_real]; simp [cfVal]

theorem gcf_nonneg (w : List ℕ) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ gcf w s := by
  induction w with
  | nil => exact hs
  | cons a l ih => simp only [gcf]; positivity

theorem gcf_mem_uIcc (w : List ℕ) (hpos : ∀ a ∈ w, 1 ≤ a) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    gcf w s ∈ Set.uIcc (gcf w 0) (gcf w 1) := by
  induction w with
  | nil => simpa [gcf, Set.uIcc_of_le zero_le_one] using hs
  | cons a l ih =>
    have ha : (1 : ℝ) ≤ a := by exact_mod_cast hpos a (by simp)
    have h := ih fun x hx => hpos x (List.mem_cons_of_mem _ hx)
    have h0 := gcf_nonneg l (le_refl (0:ℝ))
    have h1 := gcf_nonneg l (zero_le_one' ℝ)
    have hx := gcf_nonneg l hs.1
    simp only [gcf]
    rw [Set.mem_uIcc] at h ⊢
    rcases h with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · right; constructor <;> apply one_div_le_one_div_of_le (by positivity) <;> linarith
    · left; constructor <;> apply one_div_le_one_div_of_le (by positivity) <;> linarith

theorem fib_mul_ge (n : ℕ) : 2 ^ n ≤ Nat.fib (n + 1) * Nat.fib (n + 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, show n + 1 + 2 = n + 3 by ring, show n + 1 + 1 = n + 2 by ring,
      Nat.fib_add_two (n := n + 1)]
    have : Nat.fib (n + 1) ≤ Nat.fib (n + 2) := Nat.fib_mono (by omega)
    nlinarith

theorem width_le (w : List ℕ) (hpos : ∀ a ∈ w, 1 ≤ a) :
    |((cfVal w : ℚ) : ℝ) - ((cfVal (bumpLast w) : ℚ) : ℝ)| ≤ (1 / 2 : ℝ) ^ w.length := by
  rcases eq_or_ne w [] with rfl | hw
  · simp [bumpLast, cfVal]
  have h := abs_cfVal_sub_bumpLast w hw hpos
  have hc : |((cfVal w : ℚ) : ℝ) - ((cfVal (bumpLast w) : ℚ) : ℝ)| =
      ((|cfVal w - cfVal (bumpLast w)| : ℚ) : ℝ) := by push_cast; ring_nf
  rw [hc, h, cfK_bumpLast hw]
  have hK := fib_le_cfK w hpos
  have hK' := fib_le_cfK w.dropLast fun a ha => hpos a (List.mem_of_mem_dropLast ha)
  obtain ⟨D, hD⟩ : ∃ D, w.length = D + 1 := ⟨w.length - 1, by
    have := List.length_pos_of_ne_nil hw; omega⟩
  rw [List.length_dropLast, hD] at hK'
  rw [hD] at hK ⊢
  simp only [Nat.add_sub_cancel] at hK'
  have hf := fib_mul_ge (D + 1)
  have hmul : 2 ^ (D + 1) ≤ cfK w * (cfK w + cfK w.dropLast) := by
    have e : Nat.fib (D + 1 + 2) = Nat.fib (D + 1) + Nat.fib (D + 1 + 1) := Nat.fib_add_two
    calc 2 ^ (D + 1) ≤ Nat.fib (D + 1 + 1) * (Nat.fib (D + 1) + Nat.fib (D + 1 + 1)) := by
          rw [← e]; exact hf
      _ ≤ cfK w * (cfK w + cfK w.dropLast) := by
          apply Nat.mul_le_mul hK; omega
  have hmR : ((2 : ℝ) ^ (D + 1)) ≤ (cfK w : ℝ) * ((cfK w : ℝ) + (cfK w.dropLast : ℝ)) := by
    exact_mod_cast hmul
  push_cast
  rw [one_div_pow]
  exact one_div_le_one_div_of_le (by positivity) hmR

/-- The `n`-th convergent of `cfCoin ω`. -/
noncomputable def conv (ω : ℕ → Bool) (n : ℕ) : ℝ := ((cfVal (bWord (pre ω n)) : ℚ) : ℝ)

theorem pre_add (ω : ℕ → Bool) (D k : ℕ) :
    pre ω (D + k) = pre ω D ++ (List.range k).map fun i => ω (D + i) := by
  simp [pre, List.range_add, List.map_map, Function.comp_def]

theorem conv_mem (ω : ℕ → Bool) {D n : ℕ} (h : D ≤ n) :
    conv ω n ∈ Set.uIcc ((cfVal (bWord (pre ω D)) : ℚ) : ℝ)
      ((cfVal (bumpLast (bWord (pre ω D))) : ℚ) : ℝ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  set u := bWord ((List.range k).map fun i => ω (D + i))
  have hu : cfVal u ∈ Set.Icc (0 : ℚ) 1 := cfVal_mem_Icc u (bWord_pos _)
  have e : bWord (pre ω (D + k)) = bWord (pre ω D) ++ u := by
    simp only [bWord, pre_add, List.map_append, u]
  unfold conv
  rw [e, cfVal_append_real, ← gcf_zero, ← gcf_one]
  refine gcf_mem_uIcc _ (bWord_pos _) ⟨?_, ?_⟩
  · exact_mod_cast hu.1
  · exact_mod_cast hu.2

theorem conv_dist (ω : ℕ → Bool) {D n m : ℕ} (hn : D ≤ n) (hm : D ≤ m) :
    |conv ω n - conv ω m| ≤ (1 / 2 : ℝ) ^ D := by
  have h := Set.abs_sub_le_of_uIcc_subset_uIcc
    (Set.uIcc_subset_uIcc (conv_mem ω hm) (conv_mem ω hn))
  refine h.trans ?_
  rw [abs_sub_comm]
  simpa [bWord, length_pre] using width_le (bWord (pre ω D)) (bWord_pos _)

theorem conv_tendsto (ω : ℕ → Bool) : Tendsto (conv ω) atTop (𝓝 (cfCoin ω)) := by
  have hc : CauchySeq (conv ω) := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨D, hD⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨D, fun n hn => ?_⟩
    rw [Real.dist_eq]
    exact (conv_dist ω hn le_rfl).trans_lt hD
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  have : cfCoin ω = L := hL.limUnder_eq
  rw [this]; exact hL

theorem Abad_bounds' (ω : ℕ → Bool) (D : ℕ) :
    Abad (pre ω D) ≤ cfCoin ω ∧ cfCoin ω ≤ Abad (pre ω D) + (1 / 2 : ℝ) ^ D := by
  have hmem : cfCoin ω ∈ Set.uIcc ((cfVal (bWord (pre ω D)) : ℚ) : ℝ)
      ((cfVal (bumpLast (bWord (pre ω D))) : ℚ) : ℝ) :=
    isClosed_Icc.mem_of_tendsto (conv_tendsto ω)
      (eventually_atTop.2 ⟨D, fun n hn => conv_mem ω hn⟩)
  have hw := width_le (bWord (pre ω D)) (bWord_pos _)
  rw [show (bWord (pre ω D)).length = D by simp [bWord, length_pre]] at hw
  rw [Set.mem_uIcc] at hmem
  unfold Abad
  constructor
  · rcases hmem with h | h
    · exact (min_le_left _ _).trans h.1
    · exact (min_le_right _ _).trans h.1
  · rcases hmem with h | h
    · rw [abs_le] at hw
      rcases le_total ((cfVal (bWord (pre ω D)) : ℚ) : ℝ)
        ((cfVal (bumpLast (bWord (pre ω D))) : ℚ) : ℝ) with hh | hh
      · rw [min_eq_left hh]; linarith [h.2]
      · rw [min_eq_right hh]; linarith [h.2]
    · rw [abs_le] at hw
      rcases le_total ((cfVal (bWord (pre ω D)) : ℚ) : ℝ)
        ((cfVal (bumpLast (bWord (pre ω D))) : ℚ) : ℝ) with hh | hh
      · rw [min_eq_left hh]; linarith [h.2]
      · rw [min_eq_right hh]; linarith [h.2]

theorem measurable_cfCoin' : Measurable cfCoin := by
  have hm : ∀ n, Measurable fun ω => conv ω n := by
    intro n
    have h : Measurable fun v : Fin n → Bool =>
        (((cfVal (bWord (List.ofFn v))) : ℚ) : ℝ) := measurable_of_countable _
    have h2 : Measurable fun ω : ℕ → Bool => fun i : Fin n => ω i :=
      measurable_pi_lambda _ fun i => measurable_pi_apply _
    convert h.comp h2 using 2 with ω
    simp only [Function.comp, conv, pre]
    congr 3
    apply List.ext_getElem <;> simp
  exact measurable_of_tendsto_metrizable hm (tendsto_pi_nhds.2 conv_tendsto)

/-- `cfK` and its "tail" companion, by one `foldr`. -/
def cfK' : List ℕ → ℕ
  | [] => 0
  | _ :: l => cfK l

theorem cfK_cons' (a : ℕ) (l : List ℕ) : cfK (a :: l) = a * cfK l + cfK' l := by
  cases l with
  | nil => simp [cfK, cfK']
  | cons b l => simp [cfK, cfK']

theorem foldr_cfK (l : List ℕ) :
    l.foldr (fun a q => (a * q.1 + q.2, q.1)) (1, 0) = (cfK l, cfK' l) := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.foldr_cons, ih, cfK_cons']; rfl

theorem primrec_cfK : Primrec cfK := by
  have h : Primrec fun l : List ℕ => l.foldr (fun a q => (a * q.1 + q.2, q.1)) (1, 0) :=
    Primrec.list_foldr Primrec.id (Primrec.const (1, 0))
      (Primrec.pair (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))).to₂
  exact (Primrec.fst.comp h).of_eq fun l => by rw [foldr_cfK]

theorem bumpLast_eq (w : List ℕ) : bumpLast w = w.reverse.tail.reverse ++ [w.reverse.headI + 1] := by
  unfold bumpLast
  congr 2
  · rw [List.tail_reverse, List.reverse_reverse]
  · cases w using List.reverseRecOn <;> simp

theorem primrec_bumpLast : Primrec bumpLast := by
  have h1 := Primrec.list_reverse.comp (Primrec.list_tail.comp (Primrec.list_reverse (α := ℕ)))
  have h2 := Primrec.succ.comp (Primrec.list_headI.comp (Primrec.list_reverse (α := ℕ)))
  exact (Primrec.list_append.comp h1 (Primrec.list_cons.comp h2 (Primrec.const []))).of_eq
    fun w => (bumpLast_eq w).symm

theorem primrec_PsiBad' : Primrec fun x : ℕ × ℕ × List Bool => PsiBad x.1 x.2.1 x.2.2 := by
  have hp := Primrec.snd.comp (Primrec.snd (α := ℕ) (β := ℕ × List Bool))
  have hw : Primrec fun x : ℕ × ℕ × List Bool => bWord x.2.2 :=
    Primrec.list_map hp ((Primrec.dom_bool dig).comp Primrec.snd).to₂
  have hw' := primrec_bumpLast.comp hw
  have hB := ComputableNormal.primrec_pow.comp (Primrec.fst (α := ℕ) (β := ℕ × List Bool))
    (Primrec.fst.comp Primrec.snd)
  have hq : ∀ {f : ℕ × ℕ × List Bool → List ℕ}, Primrec f →
      Primrec fun x => cfP (f x) * x.1 ^ x.2.1 / cfK (f x) := fun hf =>
    Primrec.nat_div.comp (Primrec.nat_mul.comp (primrec_cfK.comp
      (Primrec.list_drop.comp (Primrec.const 1) hf)) hB) (primrec_cfK.comp hf)
  exact (Primrec.ite (Primrec.eq.comp hp (Primrec.const [])) (Primrec.const 0)
    (Primrec.nat_min.comp (hq hw) (hq hw'))).of_eq fun x => rfl

theorem PsiBad_eq' (b m : ℕ) (p : List Bool) : PsiBad b m p = ⌊Abad p * (b : ℝ) ^ m⌋₊ := by
  unfold PsiBad Abad
  split_ifs with hp
  · subst hp; simp [bWord, bumpLast, cfVal]
  have hw : bWord p ≠ [] := by simpa [bWord] using hp
  have hpos := bWord_pos p
  have key : ∀ w : List ℕ, w ≠ [] → (∀ a ∈ w, 1 ≤ a) →
      ⌊((cfVal w : ℚ) : ℝ) * (b : ℝ) ^ m⌋₊ = cfP w * b ^ m / cfK w := by
    intro w hw hpos
    rw [cfVal_eq_div w hw hpos, ← Nat.floor_div_eq_div (K := ℝ)]
    congr 1; push_cast; ring
  rw [min_mul_of_nonneg _ _ (by positivity), Monotone.map_min Nat.floor_mono,
    key _ hw hpos, key _ (bumpLast_ne_nil _) (bumpLast_pos hpos)]

theorem pre_succ' (ω : ℕ → Bool) (k : ℕ) : pre ω (k + 1) = ω 0 :: pre (fun i => ω (i + 1)) k := by
  simp only [pre, List.range_succ_eq_map, List.map_cons, List.map_map, Function.comp_def]

theorem cfCoin_shift (ω : ℕ → Bool) :
    cfCoin ω = 1 / ((dig (ω 0) : ℝ) + cfCoin fun i => ω (i + 1)) := by
  set ω' : ℕ → Bool := fun i => ω (i + 1)
  have h1 : Tendsto (fun k => conv ω (k + 1)) atTop (𝓝 (cfCoin ω)) :=
    (conv_tendsto ω).comp (tendsto_add_atTop_nat 1)
  have hd : (1 : ℝ) ≤ dig (ω 0) := by exact_mod_cast dig_pos _
  have h0 : 0 ≤ cfCoin ω' := (Abad_nonneg _).trans (Abad_bounds' ω' 0).1
  have h2 : Tendsto (fun k => 1 / ((dig (ω 0) : ℝ) + conv ω' k)) atTop
      (𝓝 (1 / ((dig (ω 0) : ℝ) + cfCoin ω'))) :=
    tendsto_const_nhds.div (tendsto_const_nhds.add (conv_tendsto ω')) (by linarith : (0:ℝ) < _).ne'
  refine tendsto_nhds_unique h1 (h2.congr fun k => ?_)
  simp only [conv, pre_succ', bWord, List.map_cons, cfVal]
  push_cast; rfl

theorem cfCoin_nonneg (ω : ℕ → Bool) : 0 ≤ cfCoin ω :=
  (Abad_nonneg _).trans (Abad_bounds' ω 0).1

theorem cfCoin_le_one (ω : ℕ → Bool) : cfCoin ω ≤ 1 := by
  have := (Abad_bounds' ω 0).2
  have h0 : Abad (pre ω 0) = 0 := by simp [Abad, pre, bWord, bumpLast, cfVal]
  rw [h0] at this; simpa using this

theorem dig_le_two (b : Bool) : dig b ≤ 2 := by cases b <;> simp [dig]

theorem third_le_cfCoin (ω : ℕ → Bool) : 1 / 3 ≤ cfCoin ω := by
  rw [cfCoin_shift]
  have h := cfCoin_le_one (fun i => ω (i + 1))
  have h0 := cfCoin_nonneg (fun i => ω (i + 1))
  have hd : (dig (ω 0) : ℝ) ≤ 2 := by exact_mod_cast dig_le_two _
  have hd1 : (1 : ℝ) ≤ dig (ω 0) := by exact_mod_cast dig_pos _
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

theorem cfCoin_lt_one (ω : ℕ → Bool) : cfCoin ω < 1 := by
  rw [cfCoin_shift]
  have h := third_le_cfCoin (fun i => ω (i + 1))
  have hd1 : (1 : ℝ) ≤ dig (ω 0) := by exact_mod_cast dig_pos _
  rw [div_lt_one (by positivity)]; linarith

theorem cfDigit_cfCoin' (ω : ℕ → Bool) (n : ℕ) : cfDigit (cfCoin ω) n = dig (ω n) := by
  induction n generalizing ω with
  | zero =>
    have h := cfCoin_lt_one (fun i => ω (i + 1))
    have h0 := cfCoin_nonneg (fun i => ω (i + 1))
    rw [cfDigit_zero, cfCoin_shift, one_div, inv_inv, Nat.floor_eq_iff (by positivity)]
    constructor <;> linarith
  | succ n ih =>
    rw [cfDigit_succ]
    have hx : gaussMap (cfCoin ω) = cfCoin fun i => ω (i + 1) := by
      have hpos : cfCoin ω ≠ 0 := (lt_of_lt_of_le (by norm_num) (third_le_cfCoin ω)).ne'
      rw [gaussMap, if_neg hpos, cfCoin_shift ω, one_div, inv_inv, Int.fract_eq_iff]
      refine ⟨cfCoin_nonneg _, cfCoin_lt_one _, dig (ω 0), ?_⟩
      push_cast; ring
    rw [hx, ih]

theorem cfCoin_const_false' : cfCoin (fun _ => false) = (Real.sqrt 5 - 1) / 2 := by
  have h := cfCoin_shift (fun _ => false)
  set x := cfCoin fun _ => false
  have h0 : 0 ≤ x := cfCoin_nonneg _
  simp only [dig] at h
  push_cast at h
  have hx : x * (1 + x) = 1 := by
    have h' := h
    rwa [eq_div_iff (by linarith : (1 : ℝ) + x ≠ 0)] at h'
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hs0 := Real.sqrt_nonneg 5
  have hm : (2 * x + 1 - Real.sqrt 5) * (2 * x + 1 + Real.sqrt 5) = 0 := by nlinarith
  rcases mul_eq_zero.1 hm with h1 | h1
  · linarith
  · nlinarith

/-- **Leaf: the floors are exact.**

Confidence 90%.  Proof: for `p = []`, `Abad [] = min 0 1 = 0`.  Otherwise `w = bWord p ≠ []` and
`bumpLast w ≠ []` have positive digits, so `cfVal_eq_div` writes both endpoints as `P/K` with
`K = cfK ≥ 1` (`fib_le_cfK`); `⌊(P/K)·bᵐ⌋₊ = P·bᵐ / K` (`Nat.floor_div_eq_div`), and the floor of a
minimum is the minimum of the floors (monotone). -/
theorem PsiBad_eq (b m : ℕ) (p : List Bool) : PsiBad b m p = ⌊Abad p * (b : ℝ) ^ m⌋₊ := by
  exact PsiBad_eq' b m p

/-- **Leaf: the floors are primitive recursive.**

Confidence 85%.  Proof: `bWord` is a `List.map`; `bumpLast` is `dropLast ++ [getLastD + 1]`; `cfK`
is a two-step list recursion, primitive recursive via the pair `(cfK l, cfK (l.drop 1))` computed by
`List.foldr` (`cfK (a :: l) = a·cfK l + cfK (l.drop 1)`); then `nat_mul`, `primrec_pow`, `nat_div`,
`min`, and the `p = []` test. -/
theorem primrec_PsiBad : Primrec fun x : ℕ × ℕ × List Bool => PsiBad x.1 x.2.1 x.2.2 := by
  exact primrec_PsiBad'

/-- **Leaf: the coin map is measurable.**

Confidence 92%.  Proof: each convergent `ω ↦ cfVal (bWord (pre ω n))` depends on finitely many
coordinates, hence is measurable (`measurable_of_countable` on the finite prefix).  The limit exists
at every `ω` (the convergents are Cauchy: consecutive ones differ by `1/(q_n q_{n+1})`, and
`q_n ≥ F_{n+1}` by `fib_le_cfK`), so `cfCoin` is the pointwise limit and
`measurable_of_tendsto_metrizable` applies. -/
theorem measurable_cfCoin : Measurable cfCoin := by
  exact measurable_cfCoin'

/-- **Leaf: the approximation sandwich `A(pre ω D) ≤ cfCoin ω ≤ A(pre ω D) + 2^{-D}`.**

Confidence 85%.  Proof: `w = bWord (pre ω D)`.  Every later convergent `[0; w, u]` (`u` a word of
`1`s and `2`s) lies in the closed interval between `cfVal w` and `cfVal (bumpLast w)` (the CF
cylinder of `w` is contained in it, `cfCylinder_endpoints`; for `D = 0` the interval is `[0,1]`), so
the limit `cfCoin ω` does too.  The interval has length `1/(K(K+K'))` with `K = cfK w`,
`K' = cfK w.dropLast` (`abs_cfVal_sub_bumpLast`), and `K(K+K') ≥ F_{D+1}F_{D+2} ≥ 2^D`
(`fib_le_cfK`; `F_{D+1}F_{D+2}` is `1, 2, 6, 15, 40, …`, and the ratio exceeds `2` from `D = 1`). -/
theorem Abad_bounds (ω : ℕ → Bool) (D : ℕ) :
    Abad (pre ω D) ≤ cfCoin ω ∧ cfCoin ω ≤ Abad (pre ω D) + (1 / 2 : ℝ) ^ D := by
  exact Abad_bounds' ω D

/-- **Leaf (content locator): the partial quotients of `cfCoin ω` are exactly `dig (ω n)`.**

Confidence 85%.  Proof: `cfCoin ω` lies in the open interior of the CF cylinder of
`bWord (pre ω D)` for every `D` (it lies in the closed one by `Abad_bounds`; an endpoint is
rational, while `cfCoin ω` is irrational because it lies in nested cylinders whose lengths
`→ 0` and whose rational points are eventually excluded, as in `exists_irrational_mem_iInter_cfCylinder`).
Interior points of `cfCylinder w` have first `|w|` digits `w` (`cfCylinder_endpoints`, third
clause); take `D = n + 1`. -/
theorem cfDigit_cfCoin (ω : ℕ → Bool) (n : ℕ) : cfDigit (cfCoin ω) n = dig (ω n) := by
  exact cfDigit_cfCoin' ω n

/-! ## The cited decay input -/

namespace Literature

/-- **Cited input: polynomial Fourier decay of the Bernoulli(1/2) measure on `E_{1,2}`.**

**Primary source.**  T. Sahlsten, C. Stevens, *Fourier transform and expanding maps on Cantor
sets*, Amer. J. Math. **146** (2024), no. 4, 945–982 (arXiv 2009.01703), **Theorem 1.1(2)**
(`thm:nonlinear`): if `T : ⋃ I_a → [0,1]` is a totally non-linear uniformly expanding Markov map of
bounded distortions, conjugate to the full shift, with the `I_a` **disjoint** and the inverse
branches `f_a` **analytic**, and `μ` is a non-atomic equilibrium state of a potential with
exponentially vanishing variations, then `|μ̂(ξ)| = O(|ξ|^{-α})` for some `α > 0`
(their `μ̂(ξ) = ∫ e^{-2πiξx} dμ`, `ξ ∈ ℝ`, same modulus as `ee`).

**Hypothesis check** (instance: `f₁ t = 1/(1+t)`, `f₂ t = 1/(2+t)` on `J = [1/3, 3/4]`, conjugated
to `[0,1]` by the affine `J → [0,1]`, which changes `μ̂` by a phase and a rescaling of `ξ`):
* `f₁ J = [4/7, 3/4]`, `f₂ J = [4/11, 3/7]`: both inside `J` and disjoint (`3/7 < 4/7`);
  `T` maps each onto `J` (Markov, full shift); `E_{1,2} ⊂ [0.366, 0.733] ⊂ J`.
* Uniform expansion: `|f_a'| = (a+t)^{-2} ≤ 9/16` on `J`.  Distortion `T''/T' = -2/t`, bounded on `J`.
  Analytic: Möbius maps.
* Total non-linearity: a `C¹` coboundary relation `τ = ψ₀ + g∘T − g` makes periodic-orbit sums of
  `τ = log|T'|` additive in the letters.  The fixed points give `τ = 2 log φ` (word `1`) and
  `2 log(1+√2)` (word `2`); the period-2 orbit of `12` gives `S₂τ = 2 log(2+√3)`, the spectral
  radius of `[[0,1],[1,1]]·[[0,1],[1,2]] = [[1,2],[1,3]]` (trace 4).  `φ(1+√2) ≈ 3.906 ≠ 3.732 ≈ 2+√3`.
* `μ` = law of `cfCoin` = the uniform Bernoulli measure on the full shift `{1,2}^ℕ`: the
  equilibrium state of the constant potential `−log 2` (variations `0`), i.e. the measure of maximal
  entropy; non-atomic.
* `O(|ξ|^{-α})` as `|ξ| → ∞` plus `|μ̂| ≤ 1` gives the all-`ξ ≠ 0` form below (enlarge `C`).

**Independent cross-check.**  T. Jordan, T. Sahlsten, *Fourier transforms of Gibbs measures for the
Gauss map*, Math. Ann. **364** (2016), 983–1023 (arXiv 1312.3619), **Theorem 1.3(2)** in arXiv
numbering (`thm:main`): any Gibbs measure for the Gauss map restricted to `B(𝒜)`, `𝒜` finite, with
`dim μ > 1/2`, has polynomial decay; Bernoulli measures are Gibbs (their Remark `rmk:examples`(1)).
Here `dim μ = log 2 / λ`, `λ = 2·𝔼 log(a + x) ≈ 1.34602` (depth-20 exact cylinder average,
`probes/bad_bernoulli12_dimension.py`), so `dim μ ≈ 0.51496 > 1/2`: covered, with little margin.

**Faithful-or-weaker:** the statement below is the specialisation to `μ` = law of `cfCoin` under
`coins`.  Referee pass pending. -/
def SahlstenStevensBernoulli12 : Prop :=
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
    ∀ ξ : ℝ, ξ ≠ 0 → ‖∫ ω, ee (ξ * cfCoin ω) ∂coins‖ ≤ C * |ξ| ^ (-δ)

end Literature

/-! ## Headline -/

/-- **A computable absolutely normal number all of whose partial quotients lie in `{1, 2}`**:
a computable answer to Montgomery's question (Bugeaud 2012 §7.7, Queffélec 2006 §4: none
exhibited).  Since `cfDigit` returns the junk value `0` on rationals, "every digit is `1` or `2`"
also certifies that `cfCoin e` is irrational and badly approximable.

Wired from the cited decay, the proved engine, and the leaves above. -/
theorem exists_computable_absNormal_bad (h : Literature.SahlstenStevensBernoulli12) :
    ∃ e : ℕ → Bool, Computable e ∧ IsAbsNormal (cfCoin e) ∧
      ∀ n, cfDigit (cfCoin e) n ∈ ({1, 2} : Finset ℕ) := by
  obtain ⟨C, δ, hC, hδ, hdec⟩ := h
  obtain ⟨e, hce, hn⟩ := ComputableNormalB.exists_computable_absNormal PsiBad primrec_PsiBad Abad
    PsiBad_eq Abad_nonneg cfCoin measurable_cfCoin Abad_bounds hC hδ hdec
  refine ⟨e, hce, hn, fun n => ?_⟩
  rw [cfDigit_cfCoin]
  cases e n <;> simp [dig]

/-! ## Known-false siblings -/

/-- **Guard: no Dirac measure has polynomial Fourier decay.**  So the engine's decay hypothesis
can never be met by an atom (a single CF, e.g. a periodic one), and the derandomizer cannot
"certify" normality of a fixed quadratic irrational. -/
theorem not_decay_const (c : ℝ) :
    ¬ ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ ξ : ℝ, ξ ≠ 0 → ‖∫ _ω, ee (ξ * c) ∂coins‖ ≤ C * |ξ| ^ (-δ) := by
  rintro ⟨C, δ, hC, hδ, h⟩
  have : IsProbabilityMeasure coins := by unfold coins; infer_instance
  have hC1 : (0 : ℝ) < C + 1 := by linarith
  set ξ : ℝ := (C + 1) ^ (1 / δ) with hξdef
  have hξ : 0 < ξ := Real.rpow_pos_of_pos hC1 _
  have h1 := h ξ hξ.ne'
  rw [integral_const, probReal_univ, one_smul, norm_ee, abs_of_pos hξ, hξdef,
    ← Real.rpow_mul hC1.le, show 1 / δ * -δ = (-1 : ℝ) by field_simp, Real.rpow_neg_one] at h1
  have h2 : C * (C + 1)⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hC1]; linarith
  linarith

/-- **Guard, the one-letter and periodic siblings**: for any fixed coin sequence `ω₀` (constant,
periodic, …), the law of the constant map `ω ↦ cfCoin ω₀` is a Dirac and fails the decay
hypothesis.  The content of `Literature.SahlstenStevensBernoulli12` is the spread of `ω`. -/
theorem not_decay_cfCoin_fixed (ω₀ : ℕ → Bool) :
    ¬ ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ ξ : ℝ, ξ ≠ 0 → ‖∫ _ω, ee (ξ * cfCoin ω₀) ∂coins‖ ≤ C * |ξ| ^ (-δ) :=
  not_decay_const _

/-- **Non-vacuity anchor for `cfCoin`**: the all-`false` sequence is `[0; 1, 1, …] = (√5 − 1)/2`,
the golden-ratio conjugate (a quadratic irrational, where `not_decay_cfCoin_fixed` bites).

Confidence 85%.  Proof: `cfVal` of `n` ones is `F_n/F_{n+1}` (`cfVal_eq_div`, continuants of ones
are Fibonacci), which tends to `1/φ = (√5 − 1)/2`; `limUnder` of a convergent sequence is its
limit (`Tendsto.limUnder_eq`). -/
theorem cfCoin_const_false : cfCoin (fun _ => false) = (Real.sqrt 5 - 1) / 2 := by
  exact cfCoin_const_false'

end NormalNumbers.BadNormal
