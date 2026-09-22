import NormalNumbers.PrimeModelJointLawGraded
import NormalNumbers.PrimeModelRadicalTailGraded
import NormalNumbers.PrimeModelGradedLemmaB

/-!
# The graded joint state and its per-atom lower bound

Leaf **G3** of the graded-state regrade (`PENDING_WORK.md`, 2026-09-22 route correction).  This
is where the *first* wall closes.

`BlockSieve.empLaw_lower_atom_graded` instantiates Lemma B at the **constant** class count
`dpK k`, and `graded_brun_lower`'s hypothesis `hdpj : ∀ j, ∀ p ∈ U j, dp p ≤ d j` then forces
`d_j ≥ k` in *every* tier — including the top one, which carries the largest `log y`.  The
support level is therefore `log R ≥ 128 k log y₀`, which pins the top cutoff exponent at
`a ≤ 1/(2048 J)` and makes the transfer term `≍ ρ_N log J ≍ ρ_N L₄N`.  That is not controlled by
`ρ_N → 0`.

The fix is to let the class count be the **band-dependent** `d_p = #{j : p ≤ y_j}`.  Then the
sifted condition only forbids the shifts `t < d_p` at `p`, so the arithmetic filter is a fibre of
the *truncated* state

    truncState d s i = (s i).bind (fun j => if j < d i then some j else none),

and the model atom is `∏_{p unassigned} (1 − d_p/p)` — exactly `graded_brun_lower`'s main term.

* `truncState`, `IsGraded`, `actualStateG` — the graded state, on the same state type as the
  ungraded one, so `retainedBoxG_card_le` and friends are reused verbatim;
* `actual_stateG_sifted_iff` — the graded twin of `RadicalState.actual_state_sifted_iff`;
* `state_model_densityG` — the graded twin of `RadicalState.state_model_density`;
* `empLawG`, `jointModelG` with mass one, nonnegativity and the box tail;
* **`empLawG_lower_atom`** — the per-atom estimate at a band-dependent `dp`, off
  `BlockSieve.graded_brun_lower`.  Nothing forces `d_j ≥ k` any more: the tier dimensions are
  free, so the geometric schedule's `d_b = b` is admissible and the level collapses to
  `a(270 + 4u)`.
-/

set_option linter.unusedSectionVars false

open Finset
open scoped BigOperators

namespace NormalNumbers.PrimeModel.RadicalState

open NormalNumbers.PrimeModel.Radical

variable {k : ℕ}

/-! ## The truncated (graded) state -/

/-- Truncate a state to each prime's own class count: a prime assigned to a shift it does not
reach is recorded as unassigned. -/
def truncState (k : ℕ) (dp : ℕ → ℕ) (P : Finset ℕ) (s : {q // q ∈ P} → Option (Fin k)) :
    {q // q ∈ P} → Option (Fin k) :=
  fun i => (s i).bind (fun j => if (j : ℕ) < dp (i : ℕ) then some j else none)

/-- A state is *graded* for `dp` when every assignment is to a live shift. -/
def IsGraded (dp : ℕ → ℕ) {P : Finset ℕ} (s : {q // q ∈ P} → Option (Fin k)) : Prop :=
  ∀ (i : {q // q ∈ P}) (t : Fin k), s i = some t → (t : ℕ) < dp (i : ℕ)

variable {dp : ℕ → ℕ} {P : Finset ℕ} {s : {q // q ∈ P} → Option (Fin k)}

lemma truncState_eq_some_iff {i : {q // q ∈ P}} {t : Fin k} :
    truncState k dp P s i = some t ↔ (s i = some t ∧ (t : ℕ) < dp (i : ℕ)) := by
  unfold truncState
  rcases hsi : s i with _ | u
  · simp
  · by_cases hu : (u : ℕ) < dp (i : ℕ)
    · simp only [Option.bind_some, if_pos hu, Option.some.injEq]
      constructor
      · rintro rfl; exact ⟨rfl, hu⟩
      · rintro ⟨h1, -⟩; exact h1
    · simp only [Option.bind_some, if_neg hu]
      constructor
      · intro hc; exact absurd hc (by simp)
      · rintro ⟨h1, h2⟩
        rw [← Option.some.inj h1] at h2
        exact absurd h2 hu

lemma truncState_eq_none_iff {i : {q // q ∈ P}} :
    truncState k dp P s i = none ↔ ∀ t : Fin k, s i = some t → dp (i : ℕ) ≤ (t : ℕ) := by
  unfold truncState
  rcases hsi : s i with _ | u
  · simp
  · by_cases hu : (u : ℕ) < dp (i : ℕ)
    · simp only [Option.bind_some, if_pos hu]
      constructor
      · intro hc; exact absurd hc (by simp)
      · intro hc; exact absurd (hc u rfl) (by omega)
    · simp only [Option.bind_some, if_neg hu]
      constructor
      · intro _ t ht
        rw [← Option.some.inj ht]
        omega
      · intro _; trivial

/-- The truncation of any state is graded. -/
lemma isGraded_truncState : IsGraded dp (truncState k dp P s) := by
  intro i t ht
  exact (truncState_eq_some_iff.mp ht).2

/-- Truncation fixes graded states. -/
lemma truncState_of_isGraded (hs : IsGraded dp s) : truncState k dp P s = s := by
  funext i
  cases h : s i with
  | none => rw [truncState]; simp [h]
  | some t => exact truncState_eq_some_iff.mpr ⟨h, hs i t h⟩

/-- The state actually realised by `n`, graded by `dp`. -/
def actualStateG (k : ℕ) (dp : ℕ → ℕ) (P : Finset ℕ) (n : ℕ) : {q // q ∈ P} → Option (Fin k) :=
  truncState k dp P (actualState k P n)

lemma isGraded_actualStateG (k : ℕ) (dp : ℕ → ℕ) (P : Finset ℕ) (n : ℕ) :
    IsGraded dp (actualStateG k dp P n) := isGraded_truncState

/-! ## The graded state identification -/

/-- **G3a, the graded state identification.**  Being in residue class `r` mod `Q` and realising
exactly the *graded* state `s` is the same as the graded arithmetic sifted condition
`SiftedCondD`, whose sieve clause at `p` runs only over the shifts `t < d_p`. -/
theorem actual_stateG_sifted_iff (hk : 0 < k) (hdpk : ∀ q ∈ P, dp q ≤ k)
    (hP : ∀ q ∈ P, k < q) (hs : IsGraded dp s) (Q r n : ℕ) :
    (n % Q = r ∧ actualStateG k dp P n = s)
      ↔ BrunGraded.SiftedCondD (stateA P s) (stateU P s) dp
          (fun q => ((stateShift P s hk q : Fin k) : ℕ)) Q r n := by
  constructor
  · rintro ⟨hr, hst⟩
    refine ⟨hr, ?_, ?_⟩
    · intro q hq
      obtain ⟨h, hsome⟩ := mem_stateA.mp hq
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hsome
      have hG : actualStateG k dp P n ⟨q, h⟩ = some t := by rw [hst]; exact ht
      have hact := (truncState_eq_some_iff (dp := dp) (s := actualState k P n)).mp hG
      have hdvd := (hitShift_eq_some_iff (hP q h) t).mp hact.1
      show q ∣ n + ((stateShift P s hk q : Fin k) : ℕ) + 1
      rw [stateShift_of_some h ht]
      exact hdvd
    · intro q hq t htlt hdvd
      obtain ⟨h, hnone⟩ := mem_stateU.mp hq
      have hsn : s ⟨q, h⟩ = none := by
        cases hh : s ⟨q, h⟩ with
        | none => rfl
        | some u => exact absurd (by simp [hh]) hnone
      have hG : actualStateG k dp P n ⟨q, h⟩ = none := by rw [hst]; exact hsn
      have htk : t < k := lt_of_lt_of_le htlt (hdpk q h)
      have hhit : actualState k P n ⟨q, h⟩ = some ⟨t, htk⟩ :=
        (hitShift_eq_some_iff (hP q h) ⟨t, htk⟩).mpr hdvd
      have hle : dp q ≤ t := by
        have hx := (truncState_eq_none_iff (dp := dp) (s := actualState k P n)).mp hG
          ⟨t, htk⟩ hhit
        simpa using hx
      omega
  · rintro ⟨hr, hA, hU⟩
    refine ⟨hr, ?_⟩
    funext i
    obtain ⟨q, hq⟩ := i
    cases hs' : s ⟨q, hq⟩ with
    | none =>
        refine (truncState_eq_none_iff (dp := dp) (s := actualState k P n)).mpr ?_
        intro t hts
        show dp q ≤ (t : ℕ)
        by_contra hlt
        have hlt' : (t : ℕ) < dp q := by omega
        have hmem : q ∈ stateU P s := mem_stateU.mpr ⟨hq, by simp [hs']⟩
        exact hU q hmem (t : ℕ) hlt' ((hitShift_eq_some_iff (hP q hq) t).mp hts)
    | some t =>
        refine (truncState_eq_some_iff (dp := dp) (s := actualState k P n)).mpr ⟨?_, ?_⟩
        · refine (hitShift_eq_some_iff (hP q hq) t).mpr ?_
          have hmem : q ∈ stateA P s := mem_stateA.mpr ⟨hq, by simp [hs']⟩
          have hdvd : q ∣ n + ((stateShift P s hk q : Fin k) : ℕ) + 1 := hA q hmem
          rwa [stateShift_of_some hq hs'] at hdvd
        · exact hs ⟨q, hq⟩ t hs'

/-! ## The graded state density -/

/-- **G3b, the graded state density.**  The graded model weight of a graded state is one factor
`1/q` per assigned prime and one factor `1 − d_q/q` per unassigned prime — exactly the main term
of `BlockSieve.graded_brun_lower`. -/
theorem state_model_densityG (hs : IsGraded dp s) :
    Radical.weightG k (fun i : {q // q ∈ P} => dp (i : ℕ))
        (Radical.primeRecip (fun i : {q // q ∈ P} => (i : ℕ))) s
      = (1 / ∏ q ∈ stateA P s, (q : ℝ)) * ∏ q ∈ stateU P s, (1 - (dp q : ℝ) / q) := by
  classical
  have hval : Function.Injective (Subtype.val : {q // q ∈ P} → ℕ) := Subtype.val_injective
  have hsplit :
      (∏ i ∈ P.attach.filter (fun i => (s i).isSome),
          Radical.localWeightG k (dp (i : ℕ))
            (Radical.primeRecip (fun i : {q // q ∈ P} => (i : ℕ)) i) (s i)) *
      (∏ i ∈ P.attach.filter (fun i => ¬ (s i).isSome),
          Radical.localWeightG k (dp (i : ℕ))
            (Radical.primeRecip (fun i : {q // q ∈ P} => (i : ℕ)) i) (s i))
        = Radical.weightG k (fun i : {q // q ∈ P} => dp (i : ℕ))
            (Radical.primeRecip (fun i : {q // q ∈ P} => (i : ℕ))) s := by
    rw [Radical.weightG, Finset.prod_filter_mul_prod_filter_not]
    exact Finset.prod_congr (by simp [Finset.attach]) fun i _ => rfl
  rw [← hsplit]
  congr 1
  · rw [stateA, Finset.prod_image (fun a _ b _ h => hval h)]
    rw [one_div, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun i hi => ?_
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (Finset.mem_filter.mp hi).2
    rw [ht, Radical.localWeightG_some, if_pos (hs i t ht), Radical.primeRecip]
  · rw [stateU, Finset.prod_image (fun a _ b _ h => hval h)]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hnone : s i = none := by
      cases hh : s i with
      | none => rfl
      | some t => exact absurd (by simp [hh]) (Finset.mem_filter.mp hi).2
    rw [hnone, Radical.localWeightG_none, Radical.primeRecip, div_eq_mul_inv]

end NormalNumbers.PrimeModel.RadicalState

namespace NormalNumbers.PrimeModel.JointLaw

open NormalNumbers.PrimeModel.Radical NormalNumbers.PrimeModel.RadicalState
open NormalNumbers.PrimeModel.BrunGraded NormalNumbers.PrimeModel.BlockSieve

variable {k : ℕ} (P : Finset ℕ) (Q x : ℕ)

/-! ## The graded empirical law -/

/-- The empirical joint law of `(n mod Q, actualStateG k dp P n)` for `n < x`. -/
noncomputable def empLawG (k : ℕ) (dp : ℕ → ℕ) (t : JointState k P Q) : ℝ :=
  (((range x).filter
      (fun n => n % Q = t.1.val ∧ actualStateG k dp P n = t.2)).card : ℝ) / x

lemma empLawG_nonneg (k : ℕ) (dp : ℕ → ℕ) (t : JointState k P Q) :
    0 ≤ empLawG P Q x k dp t := by
  unfold empLawG
  positivity

private lemma fibreG_eq (k : ℕ) (dp : ℕ → ℕ) (hQ : 0 < Q) (t : JointState k P Q) :
    ((range x).filter
        (fun n => ((⟨n % Q, Nat.mod_lt n hQ⟩ : Fin Q), actualStateG k dp P n) = t))
      = ((range x).filter (fun n => n % Q = t.1.val ∧ actualStateG k dp P n = t.2)) := by
  refine Finset.filter_congr fun n _ => ?_
  simp [Prod.ext_iff, Fin.ext_iff]

theorem empLawG_mass_one (k : ℕ) (dp : ℕ → ℕ) (hQ : 0 < Q) (hx : 0 < x) :
    ∑ t : JointState k P Q, empLawG P Q x k dp t = 1 := by
  classical
  have hfib := Finset.card_eq_sum_card_fiberwise
    (f := fun n => ((⟨n % Q, Nat.mod_lt n hQ⟩ : Fin Q), actualStateG k dp P n))
    (s := range x) (t := (Finset.univ : Finset (JointState k P Q)))
    (fun n _ => Finset.mem_univ _)
  have hsum : ∑ t : JointState k P Q,
      ((range x).filter (fun n => n % Q = t.1.val ∧ actualStateG k dp P n = t.2)).card = x := by
    rw [← Finset.sum_congr rfl (fun t _ => congrArg Finset.card (fibreG_eq P Q x k dp hQ t)),
      ← hfib, Finset.card_range]
  have hx0 : (x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hx.ne'
  unfold empLawG
  rw [← Finset.sum_div, ← Nat.cast_sum, hsum]
  exact div_self hx0

/-! ## The graded joint model -/

/-- The graded joint model: the graded radical law tensored with the uniform residue law. -/
noncomputable def jointModelG {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Type*) [Fintype R] (k : ℕ) (dp : ι → ℕ) (q : ι → ℝ)
    (z : R × (ι → Option (Fin k))) : ℝ :=
  weightG k dp q z.2 / (Fintype.card R)

lemma jointModelG_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [Fintype R] {k : ℕ} {p dp : ι → ℕ}
    (hp : ∀ i, 0 < p i) (hdp : ∀ i, dp i ≤ p i)
    (z : R × (ι → Option (Fin k))) : 0 ≤ jointModelG R k dp (primeRecip p) z := by
  have := weightG_nonneg_prime hp hdp z.2
  unfold jointModelG
  positivity

lemma jointModelG_mass_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Type*) [Fintype R] [Nonempty R] (k : ℕ) (dp : ι → ℕ) (hdk : ∀ i, dp i ≤ k)
    (p : ι → ℕ) :
    ∑ z : R × (ι → Option (Fin k)), jointModelG R k dp (primeRecip p) z = 1 := by
  have hcard : (0:ℝ) < (Fintype.card R : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := R)
  have hinner : ∀ _r : R, (∑ s : ι → Option (Fin k),
      weightG k dp (primeRecip p) s / (Fintype.card R : ℝ)) = 1 / (Fintype.card R : ℝ) := by
    intro _
    rw [← Finset.sum_div, radical_mass_oneG_prime k dp hdk]
  rw [Fintype.sum_prod_type]
  simp only [jointModelG]
  rw [Finset.sum_congr rfl (fun r _ => hinner r), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  field_simp

open scoped Classical in
/-- The graded joint tail outside `R × B(T⃗)` is the state-only tail. -/
lemma jointModelG_tailG {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Type*) [Fintype R] [Nonempty R] (k : ℕ) (dp : ι → ℕ) (p : ι → ℕ) (T : Fin k → ℝ) :
    (∑ z ∈ (Finset.univ ×ˢ retainedBoxG k p T)ᶜ, jointModelG R k dp (primeRecip p) z)
      = ∑ s ∈ (retainedBoxG k p T)ᶜ, weightG k dp (primeRecip p) s := by
  classical
  have hcard : (0:ℝ) < (Fintype.card R : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := R)
  have hcompl : ((Finset.univ : Finset R) ×ˢ retainedBoxG k p T)ᶜ
      = (Finset.univ : Finset R) ×ˢ (retainedBoxG k p T)ᶜ := by
    ext z
    simp [Finset.mem_compl, Finset.mem_product]
  rw [hcompl, Finset.sum_product]
  simp only [jointModelG]
  rw [Finset.sum_congr rfl (fun r _ => (Finset.sum_div _ _ _).symm), Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  field_simp

/-! ## The per-atom lower bound at a band-dependent class count -/

/-- **G3, the graded per-atom lower bound.**  The tier dimensions `dd` are now constrained only
by `dp p ≤ dd j` on each tier's own primes, so the geometric schedule's `d_b = b` is admissible
and the support level is `a(270 + 4u)` rather than `128 k a`.  This is the estimate the constant
class count of `BlockSieve.empLaw_lower_atom_graded` cannot give. -/
theorem empLawG_lower_atom {k : ℕ} (hk : 1 ≤ k) {P : Finset ℕ} {Q x : ℕ}
    (dp : ℕ → ℕ) (hdp2 : ∀ p, 2 * dp p ≤ p) (hdpk : ∀ q ∈ P, dp q ≤ k)
    (hPk : ∀ q ∈ P, k < q) (hPprime : ∀ q ∈ P, Nat.Prime q)
    (hQ : 0 < Q) (hx : 0 < x) (hQcop : ∀ p ∈ P, Nat.Coprime Q p)
    (r : Fin Q) (s : {q // q ∈ P} → Option (Fin k)) (hs : IsGraded dp s)
    {κ : Type*} [DecidableEq κ] (tt : Finset κ) (L : ℕ) (dd uu : κ → ℕ) (hdd : ∀ j, 1 ≤ dd j)
    (UU : κ → Finset ℕ) (yy : κ → ℝ) (hy : ∀ j, 1 ≤ yy j)
    (hUdisj : ∀ j j', j ≠ j' → Disjoint (UU j) (UU j'))
    (hUprime : ∀ j, ∀ p ∈ UU j, Nat.Prime p)
    (hcut : ∀ j ∈ tt, ∀ l < L, 2 ≤ cut yy j (l + 1))
    (hT1 : ∑ j ∈ tt, Real.exp (-(uu j : ℝ)) ≤ 1)
    (hdpj : ∀ j, ∀ p ∈ UU j, dp p ≤ dd j)
    (hcover : (tt ×ˢ Finset.range L).biUnion (gradedBlock UU yy) = stateU P s) :
    (1 - 0.3 * ∑ j ∈ tt, Real.exp (-(uu j : ℝ)))
          * jointModelG (Fin Q) k (fun i : {q // q ∈ P} => dp (i : ℕ))
              (primeRecip (primeOf P)) (r, s)
        - (gradedLevel tt dd uu yy) ^ 2 / x
      ≤ empLawG P Q x k dp (r, s) := by
  classical
  have hk' : 0 < k := hk
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hAP : ∀ p ∈ stateA P s, p ∈ P := fun p hp => stateA_subset hp
  have hUP : ∀ p ∈ stateU P s, p ∈ P := fun p hp => stateU_subset hp
  -- the arithmetic filter is the graded joint-state fibre
  have hfilter : (range x).filter (SiftedCondD (stateA P s) (stateU P s) dp
        (fun q => ((stateShift P s hk' q : Fin k) : ℕ)) Q r.val)
      = (range x).filter (fun n => n % Q = r.val ∧ actualStateG k dp P n = s) := by
    refine Finset.filter_congr fun n _ => ?_
    exact (actual_stateG_sifted_iff hk' hdpk hPk hs Q r.val n).symm
  -- the graded sieve lower bound, at the band-dependent class count
  have hbrun := graded_brun_lower tt L dd uu hdd UU yy hy hUdisj hUprime hcut hT1
    dp (fun q => ((stateShift P s hk' q : Fin k) : ℕ)) hdp2 hdpj (stateA P s) Q r.val x
    (fun p hp => hPprime p (hAP p hp))
    (fun p hp => by
      show ((stateShift P s hk' p : Fin k) : ℕ) < p
      exact lt_of_lt_of_le (Fin.is_lt _) (le_of_lt (hPk p (hAP p hp))))
    (by rw [hcover]; exact stateA_disjoint_stateU)
    hQ r.isLt
    (fun p hp => by
      rcases Finset.mem_union.1 hp with h | h
      · exact hQcop p (hAP p h)
      · rw [hcover] at h; exact hQcop p (hUP p h))
  rw [hcover, hfilter] at hbrun
  -- the model atom
  have hprodA : ((∏ p ∈ stateA P s, p : ℕ) : ℝ) = ∏ q ∈ stateA P s, (q : ℝ) :=
    Nat.cast_prod _ _
  have hprodA0 : ((∏ p ∈ stateA P s, p : ℕ) : ℝ) ≠ 0 := by
    rw [hprodA]
    refine Finset.prod_ne_zero_iff.mpr fun q hq => ?_
    have := (hPprime q (hAP q hq)).pos
    positivity
  have hQ0 : ((Q : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hQ.ne'
  have hmodel : jointModelG (Fin Q) k (fun i : {q // q ∈ P} => dp (i : ℕ))
        (primeRecip (primeOf P)) (r, s)
      = ((1 / ((∏ p ∈ stateA P s, p : ℕ) : ℝ))
          * ∏ q ∈ stateU P s, (1 - (dp q : ℝ) / q)) / (Q : ℝ) := by
    unfold jointModelG
    rw [Fintype.card_fin]
    congr 1
    rw [show (primeRecip (primeOf P)) = Radical.primeRecip (fun i : {q // q ∈ P} => (i : ℕ)) from
      rfl, state_model_densityG hs, hprodA]
  have hgoal : (1 - 0.3 * ∑ j ∈ tt, Real.exp (-(uu j : ℝ)))
          * jointModelG (Fin Q) k (fun i : {q // q ∈ P} => dp (i : ℕ))
              (primeRecip (primeOf P)) (r, s)
        - (gradedLevel tt dd uu yy) ^ 2 / x
      = ((x : ℝ) / ((Q : ℝ) * ((∏ p ∈ stateA P s, p : ℕ) : ℝ))
            * ((1 - 0.3 * ∑ j ∈ tt, Real.exp (-(uu j : ℝ)))
              * ∏ q ∈ stateU P s, (1 - (dp q : ℝ) / q))
          - (gradedLevel tt dd uu yy) ^ 2) / x := by
    rw [hmodel]
    field_simp
  rw [hgoal, empLawG, div_le_div_iff_of_pos_right hxpos]
  exact hbrun

end NormalNumbers.PrimeModel.JointLaw

#print axioms NormalNumbers.PrimeModel.RadicalState.actual_stateG_sifted_iff
#print axioms NormalNumbers.PrimeModel.RadicalState.state_model_densityG
#print axioms NormalNumbers.PrimeModel.JointLaw.empLawG_lower_atom
