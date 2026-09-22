import NormalNumbers.PrimeModelTheoremAGradedM

/-!
# The tier family of a geometric cutoff chain

Leaf **G5a** of the graded-state regrade.  `JointLaw.empLawG_lower_atom` takes an abstract tier
family `(tt, L, dd, uu, UU, yy)` and needs, besides the numeric conditions, two structural facts:
`hdpj` (each tier's primes have class count at most that tier's dimension) and `hcover` (the
dyadic blocks of the family exhaust the state's unassigned primes).  This file builds that family
from the *schedule alone* and discharges both.

The tiers are the **bands** of the cutoff chain: tier `b` is
`stateU ∩ (lo b, y b]` with `lo b = y_{b+1}` (and `lo = m` for the bottom tier), dimension
`dd b = b + 1` and cutoff `yy b = y b`.  Then:

* a prime in band `b` is seen by exactly the sites `0, …, b`, so its class count is `b + 1`
  (`classCount_le_of_mem_band`) — this is the whole point of grading, and it is what frees the
  tier dimensions from the constant `k` that the review lap refuted;
* each band sits inside its own tier's dyadic range `(y_b^{2^{−L}}, y_b]`
  (hypothesis `hcutlo`, which for a chain with `y_b ≤ y_{b+1}²` is automatic at any `L ≥ 1`), so
  the level blocks cover it (`band_cover`, via the telescoping `exists_level_mem`).  For the
  upper tiers the levels `l ≥ 1` are empty; `L` is set by the bottom tier alone.

Headline: `empLawG_lower_atom_bands`, the per-atom bound with the tier family eliminated — the
last input `KMT.window_bound_gradedGM` needs before the schedule is chosen.
-/

set_option linter.unusedSectionVars false

open Finset
open scoped BigOperators

namespace NormalNumbers.PrimeModel.BlockSieve

open NormalNumbers.PrimeModel.Radical NormalNumbers.PrimeModel.RadicalState
open NormalNumbers.PrimeModel.JointLaw NormalNumbers.PrimeModel.BrunGraded

/-! ## Telescoping a decreasing chain -/

/-- If `c` is decreasing and `c L < p ≤ c 0` then `p` lies in exactly one dyadic range. -/
theorem exists_level_mem {c : ℕ → ℝ} (hdec : ∀ l, c (l + 1) ≤ c l) (L : ℕ) {p : ℝ}
    (h0 : p ≤ c 0) (hL : c L < p) : ∃ l < L, c (l + 1) < p ∧ p ≤ c l := by
  by_contra hc
  push_neg at hc
  have key : ∀ l, l ≤ L → p ≤ c l := by
    intro l
    induction l with
    | zero => intro _; exact h0
    | succ n ih =>
        intro hn
        have hpn : p ≤ c n := ih (by omega)
        by_contra hlt
        push_neg at hlt
        exact absurd hpn (not_le.mpr (hc n (by omega) hlt))
  exact absurd (key L le_rfl) (not_le.mpr hL)

variable {κ : Type*} [DecidableEq κ]

@[simp] theorem cut_zero {y : κ → ℝ} (j : κ) : cut y j 0 = y j := by
  rw [cut]; norm_num

/-- **The level cover of one tier.**  If every prime of `U j` sits in the tier's dyadic range
then the level blocks `l < L` exhaust `U j`. -/
theorem tier_cover (U : κ → Finset ℕ) (y : κ → ℝ) (j : κ) (hy : 1 ≤ y j) (L : ℕ)
    (hlo : ∀ p ∈ U j, cut y j L < (p : ℝ)) (hhi : ∀ p ∈ U j, (p : ℝ) ≤ y j) :
    (Finset.range L).biUnion (fun l => gradedBlock U y (j, l)) = U j := by
  classical
  ext p
  simp only [Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨l, -, hp⟩
    exact gradedBlock_subset U y (j, l) hp
  · intro hp
    obtain ⟨l, hlL, h1, h2⟩ := exists_level_mem (c := fun l => cut y j l)
      (fun l => cut_antitone j hy (Nat.le_succ l)) L (by rw [cut_zero]; exact hhi p hp) (hlo p hp)
    exact ⟨l, hlL, Finset.mem_filter.mpr ⟨hp, h1, h2⟩⟩

/-- The blocks of the whole family exhaust `⋃_j U j`. -/
theorem family_cover (tt : Finset κ) (U : κ → Finset ℕ) (y : κ → ℝ) (L : ℕ)
    (hy : ∀ j, 1 ≤ y j)
    (hlo : ∀ j ∈ tt, ∀ p ∈ U j, cut y j L < (p : ℝ))
    (hhi : ∀ j ∈ tt, ∀ p ∈ U j, (p : ℝ) ≤ y j) :
    (tt ×ˢ Finset.range L).biUnion (gradedBlock U y) = tt.biUnion U := by
  classical
  ext p
  simp only [Finset.mem_biUnion, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨q, ⟨hq1, hq2⟩, hp⟩
    exact ⟨q.1, hq1, gradedBlock_subset U y q hp⟩
  · rintro ⟨j, hj, hp⟩
    have hcov := tier_cover U y j (hy j) L (hlo j hj) (hhi j hj)
    rw [← hcov] at hp
    obtain ⟨l, hlL, hpl⟩ := Finset.mem_biUnion.mp hp
    exact ⟨(j, l), ⟨hj, Finset.mem_range.mp hlL⟩, hpl⟩

/-! ## Degenerate atoms -/

/-- The graded model weight of a non-graded state vanishes. -/
theorem weightG_eq_zero_of_not_isGraded {k : ℕ} {P : Finset ℕ} {dp : ℕ → ℕ}
    {s : {q // q ∈ P} → Option (Fin k)} (hs : ¬ IsGraded dp s) (q : {q // q ∈ P} → ℝ) :
    weightG k (fun i : {q // q ∈ P} => dp (i : ℕ)) q s = 0 := by
  classical
  rw [IsGraded] at hs
  push_neg at hs
  obtain ⟨i, t, hst, hlt⟩ := hs
  rw [weightG]
  refine Finset.prod_eq_zero (Finset.mem_attach _ i) ?_
  rw [hst, localWeightG_some, if_neg (by omega)]

/-- The graded empirical law of a non-graded state vanishes. -/
theorem empLawG_eq_zero_of_not_isGraded {k : ℕ} {P : Finset ℕ} {Q x : ℕ} {dp : ℕ → ℕ}
    {s : {q // q ∈ P} → Option (Fin k)} (hs : ¬ IsGraded dp s) (r : Fin Q) :
    empLawG P Q x k dp (r, s) = 0 := by
  classical
  unfold empLawG
  have hempty : ((range x).filter
      (fun n => n % Q = r.val ∧ actualStateG k dp P n = s)) = ∅ := by
    refine Finset.filter_false_of_mem fun n _ hn => ?_
    exact hs (hn.2 ▸ isGraded_actualStateG k dp P n)
  rw [hempty]
  simp

/-! ## The per-atom bound with the tier family eliminated -/

/-- **G5a, the per-atom lower bound at the band tiers.**  The tier family is the band
decomposition of the cutoff chain: tier `b` is `stateU ∩ (lo b, y b]`, dimension `b + 1`, cutoff
`y b`.  Every structural hypothesis of `JointLaw.empLawG_lower_atom` is discharged from the
schedule; what remains for the caller is purely numeric. -/
theorem empLawG_lower_atom_bands {k m L : ℕ} (hk : 1 ≤ k) (hm : 2 * k ≤ m)
    (y : Fin k → ℕ) (hmy : ∀ j, m ≤ y j)
    (hmono : ∀ i j : Fin k, i ≤ j → y j ≤ y i)
    (lo : Fin k → ℕ)
    (hloin : ∀ (b : Fin k) (hb : (b : ℕ) + 1 < k), lo b = y ⟨(b : ℕ) + 1, hb⟩)
    (hlotop : ∀ b : Fin k, (b : ℕ) + 1 = k → lo b = m)
    (hcutlo : ∀ b : Fin k, cut (fun b : Fin k => ((y b : ℕ) : ℝ)) b L ≤ (lo b : ℝ))
    (hcut2 : ∀ b : Fin k, 2 ≤ cut (fun b : Fin k => ((y b : ℕ) : ℝ)) b L)
    {P : Finset ℕ} (hPk : ∀ q ∈ P, m < q) (hPY : ∀ q ∈ P, q ≤ y ⟨0, hk⟩)
    (hPprime : ∀ q ∈ P, Nat.Prime q)
    (dp : ℕ → ℕ) (hdp2 : ∀ p, 2 * dp p ≤ p) (hdpk : ∀ q, dp q ≤ k)
    (hdpP : ∀ q ∈ P, ∀ j : Fin k, q ≤ y j ↔ (j : ℕ) < dp q)
    (uu : Fin k → ℕ) (hT1 : ∑ b : Fin k, Real.exp (-(uu b : ℝ)) ≤ 1)
    {Q x : ℕ} (hQ : 0 < Q) (hx : 0 < x) (hQcop : ∀ p ∈ P, Nat.Coprime Q p)
    (t : JointState k P Q) :
    (1 - 0.3 * ∑ b : Fin k, Real.exp (-(uu b : ℝ)))
          * jointModelG (Fin Q) k (fun i : {q // q ∈ P} => dp (i : ℕ))
              (primeRecip (primeOf P)) t
        - (gradedLevel Finset.univ (fun b : Fin k => (b : ℕ) + 1) uu
            (fun b : Fin k => ((y b : ℕ) : ℝ))) ^ 2 / x
      ≤ empLawG P Q x k dp t := by
  classical
  obtain ⟨r, s⟩ := t
  set yy : Fin k → ℝ := fun b => ((y b : ℕ) : ℝ) with hyy
  set Rlev : ℝ := gradedLevel Finset.univ (fun b : Fin k => (b : ℕ) + 1) uu yy with hRlev
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hy1 : ∀ b : Fin k, 1 ≤ yy b := by
    intro b
    have h1 : 1 ≤ y b := le_trans (by omega) (hmy b)
    show (1:ℝ) ≤ ((y b : ℕ) : ℝ)
    exact_mod_cast h1
  by_cases hs : IsGraded dp s
  · -- the tier family
    set UU : Fin k → Finset ℕ :=
      fun b => (stateU P s).filter (fun p => lo b < p ∧ p ≤ y b) with hUU
    have hUsub : ∀ b, ∀ p ∈ UU b, p ∈ stateU P s := by
      intro b p hp; exact (Finset.mem_filter.mp hp).1
    have hUP : ∀ b, ∀ p ∈ UU b, p ∈ P := fun b p hp => stateU_subset (hUsub b p hp)
    have hUdisj : ∀ b b' : Fin k, b ≠ b' → Disjoint (UU b) (UU b') := by
      have hkey : ∀ b b' : Fin k, b < b' → ∀ p ∈ UU b, p ∉ UU b' := by
        intro b b' hbb p hp hp'
        obtain ⟨-, hlop, -⟩ := Finset.mem_filter.mp hp
        obtain ⟨-, -, hhi⟩ := Finset.mem_filter.mp hp'
        have hb1 : (b : ℕ) + 1 < k := lt_of_le_of_lt hbb (b'.isLt)
        have hlb : lo b = y ⟨(b : ℕ) + 1, hb1⟩ := hloin b hb1
        have : y b' ≤ y ⟨(b : ℕ) + 1, hb1⟩ := hmono _ _ (by exact hbb)
        omega
      intro b b' hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact Finset.disjoint_left.mpr (fun p hp => hkey b b' hlt p hp)
      · exact (Finset.disjoint_left.mpr (fun p hp => hkey b' b hlt p hp)).symm
    have hUprime : ∀ b, ∀ p ∈ UU b, Nat.Prime p := fun b p hp => hPprime p (hUP b p hp)
    have hcut : ∀ b ∈ (Finset.univ : Finset (Fin k)), ∀ l < L, 2 ≤ cut yy b (l + 1) := by
      intro b _ l hl
      exact le_trans (hcut2 b) (cut_antitone b (hy1 b) (by omega))
    have hdpj : ∀ b : Fin k, ∀ p ∈ UU b, dp p ≤ (b : ℕ) + 1 := by
      intro b p hp
      obtain ⟨-, hlop, -⟩ := Finset.mem_filter.mp hp
      by_contra hc
      push_neg at hc
      have hb1 : (b : ℕ) + 1 < k := lt_of_lt_of_le hc (hdpk p)
      have hsee : p ≤ y ⟨(b : ℕ) + 1, hb1⟩ :=
        (hdpP p (hUP b p hp) ⟨(b : ℕ) + 1, hb1⟩).2 hc
      rw [hloin b hb1] at hlop
      omega
    have hcover : ((Finset.univ : Finset (Fin k)) ×ˢ Finset.range L).biUnion
        (gradedBlock UU yy) = stateU P s := by
      rw [family_cover Finset.univ UU yy L hy1
        (fun b _ p hp => by
          refine lt_of_le_of_lt (hcutlo b) ?_
          have := (Finset.mem_filter.mp hp).2.1
          exact_mod_cast this)
        (fun b _ p hp => by
          have h2 := (Finset.mem_filter.mp hp).2.2
          show ((p : ℕ) : ℝ) ≤ ((y b : ℕ) : ℝ)
          exact_mod_cast h2)]
      ext p
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨b, hp⟩; exact hUsub b p hp
      · intro hp
        have hpP : p ∈ P := stateU_subset hp
        have h0 : (0 : ℕ) < dp p := (hdpP p hpP ⟨0, hk⟩).1 (hPY p hpP)
        have hdk : dp p ≤ k := hdpk p
        set b : Fin k := ⟨dp p - 1, by omega⟩ with hb
        have hbv : (b : ℕ) = dp p - 1 := rfl
        refine ⟨b, Finset.mem_filter.mpr ⟨hp, ?_, ?_⟩⟩
        · by_cases hlt : dp p < k
          · have hb1 : (b : ℕ) + 1 < k := by rw [hbv]; omega
            rw [hloin b hb1]
            have hnot : ¬ (p ≤ y ⟨(b : ℕ) + 1, hb1⟩) := fun hle => by
              have h2 := (hdpP p hpP ⟨(b : ℕ) + 1, hb1⟩).1 hle
              simp only [hbv] at h2
              omega
            omega
          · rw [hlotop b (by rw [hbv]; omega)]
            exact hPk p hpP
        · exact (hdpP p hpP b).2 (by rw [hbv]; omega)
    have hmain := empLawG_lower_atom (k := k) hk (P := P) (Q := Q) (x := x)
      dp hdp2 (fun q hq => hdpk q) (fun q hq => lt_of_le_of_lt (by omega) (hPk q hq))
      hPprime hQ hx hQcop r s hs
      (Finset.univ : Finset (Fin k)) L (fun b : Fin k => (b : ℕ) + 1) uu (fun b => by omega)
      UU yy hy1 hUdisj hUprime hcut (by simpa using hT1) hdpj hcover
    exact hmain
  · -- a non-graded state carries no model mass and no empirical mass
    have hz : jointModelG (Fin Q) k (fun i : {q // q ∈ P} => dp (i : ℕ))
        (primeRecip (primeOf P)) (r, s) = 0 := by
      unfold jointModelG
      rw [weightG_eq_zero_of_not_isGraded hs]
      simp
    rw [hz, empLawG_eq_zero_of_not_isGraded hs r]
    have : (0 : ℝ) ≤ Rlev ^ 2 / x := by positivity
    linarith

end NormalNumbers.PrimeModel.BlockSieve

#print axioms NormalNumbers.PrimeModel.BlockSieve.empLawG_lower_atom_bands
