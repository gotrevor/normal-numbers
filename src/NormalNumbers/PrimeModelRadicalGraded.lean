import NormalNumbers.PrimeModelRadical

/-!
# The graded radical model: a per-prime class count

Leaf **G1** of the graded-state regrade (`PENDING_WORK.md`, 2026-09-22 route correction).

In the multicutoff argument site `j` carries its own cutoff `y_j`, and the schedule is
decreasing, so a prime `p` is *seen* by an initial segment of the sites: exactly
`d_p = #{j : p ≤ y_j}` of them.  The ungraded model of `PrimeModelRadical` gives every prime all
`k` shifts with mass `1/p` each; the graded model gives it only its own `d_p`:

* `none   ↦ 1 − d_p q`,
* `some j ↦ q` for `j < d_p`, and `0` for `j ≥ d_p`.

Keeping the *same* state type `ι → Option (Fin k)` and zeroing the dead shifts (rather than
introducing a dependent state type `∀ i, Option (Fin (d i))`) means every structural lemma that
is stated for the full type — `sum_pi_prod`, `retainedBox_card_le`, `retainedBoxG_card_le` — is
reused verbatim.

Two identities are the point of the file.

* `radical_site_momentG` : the single-site moment at shift `j₀` is
  `∏_{i : j₀ < d_i} (1 + q_i (t_i − 1))` — **the product runs only over the primes that site
  `j₀` sees**.  This is the sharp E4a of Fable §2 / Astra (8.4); the ungraded moment runs over
  the whole prime range and, as the route correction records, makes the discarded-radical sum
  diverge like `J e^{20}`.
* `radical_phase_productG_eq` : when the site phases are trivial off the live range
  (`z i j = 1` for `j ≥ d_i` — exactly what `zSee` does above the cutoff), the graded and
  ungraded phase expectations are **equal**.  So the graded model is the pushforward of the
  ungraded one as far as the test function can see, and `PrimeModelKMTGradedModel`'s leg E5 is
  reusable with no change.
-/

set_option linter.unusedSectionVars false

open scoped BigOperators

namespace NormalNumbers.PrimeModel.Radical

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}

/-! ## The live sites of a prime -/

/-- The shifts a prime with class count `d` is allowed to occupy. -/
def liveSites (k d : ℕ) : Finset (Fin k) := Finset.univ.filter (fun j : Fin k => (j : ℕ) < d)

@[simp] lemma mem_liveSites {k d : ℕ} {j : Fin k} : j ∈ liveSites k d ↔ (j : ℕ) < d := by
  simp [liveSites]

/-- With `d ≤ k` the live range has exactly `d` sites. -/
lemma card_liveSites {k d : ℕ} (hd : d ≤ k) : (liveSites k d).card = d := by
  classical
  have h : (liveSites k d).card = ((Finset.range k).filter (fun j => j < d)).card := by
    rw [liveSites, ← Finset.card_map ⟨Fin.val, Fin.val_injective⟩]
    congr 1
    ext j
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk, Finset.mem_range]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ⟨a.isLt, ha⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨j, h1⟩, h2, rfl⟩
  rw [h, show (Finset.range k).filter (fun j => j < d) = Finset.range d by
    ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega, Finset.card_range]

/-- The **graded local expectation identity**, over an arbitrary commutative ring: the `none`
mass `1 − d q` plus the live-shift masses reassembles into `1 + q ∑_{j < d}(v j − 1)`. -/
private lemma sum_option_graded {R : Type*} [CommRing R] (k d : ℕ) (hd : d ≤ k)
    (q : R) (v : Fin k → R) :
    ((1 : R) - (d : R) * q) + ∑ j : Fin k, (if (j : ℕ) < d then q else 0) * v j
      = 1 + q * ∑ j ∈ liveSites k d, (v j - 1) := by
  classical
  have h1 : ∑ j : Fin k, (if (j : ℕ) < d then q else 0) * v j
      = ∑ j ∈ liveSites k d, q * v j := by
    rw [liveSites, Finset.sum_filter]
    exact Finset.sum_congr rfl fun j _ => by split <;> simp
  have h2 : ∑ j ∈ liveSites k d, (v j - 1) = (∑ j ∈ liveSites k d, v j) - (d : R) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, card_liveSites hd, nsmul_eq_mul, mul_one]
  rw [h1, ← Finset.mul_sum, h2]
  ring

/-! ## The graded local weight -/

/-- Graded local mass at a site with class count `d` and reciprocal probability `q`: the dead
shifts `j ≥ d` carry mass `0`, so only `d` of the `k` shifts are live. -/
def localWeightG (k d : ℕ) (q : ℝ) : Option (Fin k) → ℝ
  | none => 1 - d * q
  | some j => if (j : ℕ) < d then q else 0

@[simp] lemma localWeightG_none (k d : ℕ) (q : ℝ) :
    localWeightG k d q none = 1 - d * q := rfl

@[simp] lemma localWeightG_some (k d : ℕ) (q : ℝ) (j : Fin k) :
    localWeightG k d q (some j) = if (j : ℕ) < d then q else 0 := rfl

/-- At the full class count the graded local weight is the ungraded one. -/
lemma localWeightG_eq_localWeight (k : ℕ) (q : ℝ) (a : Option (Fin k)) :
    localWeightG k k q a = localWeight k q a := by
  cases a with
  | none => rfl
  | some j => simp [localWeightG, localWeight, j.isLt]

/-- Graded local weights are nonnegative under the model constraint `d q ≤ 1`. -/
lemma localWeightG_nonneg {d : ℕ} {q : ℝ} (hq : 0 ≤ q) (hd : (d : ℝ) * q ≤ 1) :
    ∀ a : Option (Fin k), 0 ≤ localWeightG k d q a := by
  intro a
  cases a with
  | none => simpa using sub_nonneg.mpr hd
  | some j => dsimp [localWeightG]; split <;> simp [hq]

/-- Graded local weights sum to one (this is where `d ≤ k` is needed). -/
lemma localWeightG_sum (k d : ℕ) (hd : d ≤ k) (q : ℝ) :
    ∑ a : Option (Fin k), localWeightG k d q a = 1 := by
  rw [Fintype.sum_option]
  have := sum_option_graded (R := ℝ) k d hd q (fun _ => 1)
  simp only [sub_self, Finset.sum_const_zero, mul_zero, add_zero, mul_one] at this
  simpa [localWeightG] using this

/-! ## The graded product law -/

/-- The graded product law: prime `i` occupies only its own `d i` shifts. -/
def weightG (k : ℕ) (dp : ι → ℕ) (q : ι → ℝ) (s : ι → Option (Fin k)) : ℝ :=
  ∏ i, localWeightG k (dp i) (q i) (s i)

/-- At the full class count the graded law is the ungraded one. -/
lemma weightG_eq_weight (k : ℕ) (q : ι → ℝ) (s : ι → Option (Fin k)) :
    weightG k (fun _ => k) q s = weight k q s :=
  Finset.prod_congr rfl fun i _ => localWeightG_eq_localWeight k (q i) (s i)

theorem weightG_nonneg {dp : ι → ℕ} {q : ι → ℝ} (hq : ∀ i, 0 ≤ q i)
    (hd : ∀ i, (dp i : ℝ) * q i ≤ 1) (s : ι → Option (Fin k)) :
    0 ≤ weightG k dp q s :=
  Finset.prod_nonneg fun i _ => localWeightG_nonneg (hq i) (hd i) (s i)

theorem radical_mass_oneG (k : ℕ) (dp : ι → ℕ) (hd : ∀ i, dp i ≤ k) (q : ι → ℝ) :
    ∑ s : ι → Option (Fin k), weightG k dp q s = 1 := by
  have h : ∀ s : ι → Option (Fin k),
      weightG k dp q s = ∏ i, localWeightG k (dp i) (q i) (s i) := fun _ => rfl
  simp only [h]
  rw [sum_pi_prod (fun i a => localWeightG k (dp i) (q i) a)]
  exact Finset.prod_eq_one fun i _ => localWeightG_sum k (dp i) (hd i) (q i)

/-! ## Graded phase expectations -/

/-- **G1, the graded phase product.**  The local factor collects only the live shifts. -/
theorem radical_phase_productG (k : ℕ) (dp : ι → ℕ) (hd : ∀ i, dp i ≤ k) (q : ι → ℝ)
    (z : ι → Fin k → ℂ) :
    ∑ s : ι → Option (Fin k),
        (weightG k dp q s : ℂ) * ∏ i, localPhase k (z i) (s i)
      = ∏ i, (1 + (q i : ℂ) * ∑ j ∈ liveSites k (dp i), (z i j - 1)) := by
  classical
  have h : ∀ s : ι → Option (Fin k),
      (weightG k dp q s : ℂ) * ∏ i, localPhase k (z i) (s i)
        = ∏ i, ((localWeightG k (dp i) (q i) (s i) : ℂ) * localPhase k (z i) (s i)) := by
    intro s
    rw [Finset.prod_mul_distrib, weightG, Complex.ofReal_prod]
  simp only [h]
  rw [sum_pi_prod (fun i a => (localWeightG k (dp i) (q i) a : ℂ) * localPhase k (z i) a)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.sum_option]
  have hcast : ∀ j : Fin k,
      ((localWeightG k (dp i) (q i) (some j) : ℝ) : ℂ)
        = if (j : ℕ) < dp i then (q i : ℂ) else 0 := by
    intro j
    dsimp [localWeightG]
    split <;> simp
  simp only [localWeightG_none, localPhase_none, localPhase_some, mul_one, hcast,
    Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_natCast]
  exact sum_option_graded (R := ℂ) k (dp i) (hd i) (q i) (z i)

/-- **The bridge to the ungraded model.**  If the site phases are trivial above each prime's
class count — which is exactly what `zSee` does above the cutoff — then the graded and ungraded
phase expectations agree.  So grading the model does not move the model expectation, and leg E5
transfers with no change. -/
theorem radical_phase_productG_eq (k : ℕ) (dp : ι → ℕ) (hd : ∀ i, dp i ≤ k) (q : ι → ℝ)
    (z : ι → Fin k → ℂ) (hz : ∀ i, ∀ j : Fin k, dp i ≤ (j : ℕ) → z i j = 1) :
    ∑ s : ι → Option (Fin k),
        (weightG k dp q s : ℂ) * ∏ i, localPhase k (z i) (s i)
      = ∑ s : ι → Option (Fin k),
        (weight k q s : ℂ) * ∏ i, localPhase k (z i) (s i) := by
  classical
  rw [radical_phase_productG k dp hd q z, radical_phase_product k q z]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1
  congr 1
  rw [liveSites, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : (j : ℕ) < dp i
  · simp [hj]
  · simp [hj, hz i j (by omega)]

/-! ## Graded moment identities -/

/-- The graded real moment identity with arbitrary per-site, per-shift multipliers. -/
theorem radical_mult_productG (k : ℕ) (dp : ι → ℕ) (hd : ∀ i, dp i ≤ k) (q : ι → ℝ)
    (t : ι → Fin k → ℝ) :
    ∑ s : ι → Option (Fin k), weightG k dp q s * ∏ i, localMult k (t i) (s i)
      = ∏ i, (1 + q i * ∑ j ∈ liveSites k (dp i), (t i j - 1)) := by
  classical
  have h : ∀ s : ι → Option (Fin k),
      weightG k dp q s * ∏ i, localMult k (t i) (s i)
        = ∏ i, (localWeightG k (dp i) (q i) (s i) * localMult k (t i) (s i)) := by
    intro s; rw [Finset.prod_mul_distrib, weightG]
  simp only [h]
  rw [sum_pi_prod (fun i a => localWeightG k (dp i) (q i) a * localMult k (t i) a)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.sum_option]
  have hcast : ∀ j : Fin k,
      localWeightG k (dp i) (q i) (some j) * localMult k (t i) (some j)
        = (if (j : ℕ) < dp i then q i else 0) * t i j := fun _ => rfl
  simp only [localWeightG_none, localMult_none, mul_one, hcast]
  exact sum_option_graded (R := ℝ) k (dp i) (hd i) (q i) (t i)

/-- **G1, the graded single-site moment.**  A multiplier acting on the event "`p` occupies shift
`j₀`" has expectation `∏_{i : j₀ < d_i} (1 + q_i (t_i − 1))`: **the primes that do not reach site
`j₀` contribute the factor `1`**.  This is the per-shift Markov range of Fable §2 / Astra (8.4),
and it is what the ungraded `radical_site_moment` cannot supply. -/
theorem radical_site_momentG (k : ℕ) (dp : ι → ℕ) (hd : ∀ i, dp i ≤ k) (q : ι → ℝ)
    (j₀ : Fin k) (t : ι → ℝ) :
    ∑ s : ι → Option (Fin k),
        weightG k dp q s * ∏ i, (if s i = some j₀ then t i else 1)
      = ∏ i, (if (j₀ : ℕ) < dp i then 1 + q i * (t i - 1) else 1) := by
  classical
  have hrw : ∀ (i : ι) (a : Option (Fin k)),
      (if a = some j₀ then t i else 1)
        = localMult k (fun j => if j = j₀ then t i else 1) a := by
    intro i a
    cases a with
    | none => simp
    | some j => by_cases hj : j = j₀ <;> simp [hj]
  simp only [hrw]
  rw [radical_mult_productG k dp hd q (fun i j => if j = j₀ then t i else 1)]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hj : ∀ j : Fin k, ((if j = j₀ then t i else 1) - 1)
      = (if j = j₀ then t i - 1 else 0) := by
    intro j; by_cases h : j = j₀ <;> simp [h]
  simp only [hj]
  by_cases hlive : (j₀ : ℕ) < dp i
  · rw [if_pos hlive, Finset.sum_ite_eq' (liveSites k (dp i)) j₀ (fun _ => t i - 1),
      if_pos (mem_liveSites.mpr hlive)]
  · rw [if_neg hlive, Finset.sum_ite_eq' (liveSites k (dp i)) j₀ (fun _ => t i - 1),
      if_neg (fun hmem => hlive (mem_liveSites.mp hmem))]
    ring

/-! ## Prime specialisation -/

/-- Admissibility of a graded prime site: `d ≤ p` gives `d * (1/p) ≤ 1`. -/
lemma primeRecipG_mul_le_one {p : ι → ℕ} {dp : ι → ℕ} (hp : ∀ i, 0 < p i)
    (hd : ∀ i, dp i ≤ p i) (i : ι) : (dp i : ℝ) * primeRecip p i ≤ 1 := by
  have hpos : (0 : ℝ) < (p i : ℝ) := by exact_mod_cast hp i
  rw [primeRecip, mul_inv_le_iff₀ hpos, one_mul]
  exact_mod_cast hd i

theorem weightG_nonneg_prime {p : ι → ℕ} {dp : ι → ℕ} (hp : ∀ i, 0 < p i)
    (hd : ∀ i, dp i ≤ p i) (s : ι → Option (Fin k)) :
    0 ≤ weightG k dp (primeRecip p) s :=
  weightG_nonneg (primeRecip_nonneg p) (primeRecipG_mul_le_one hp hd) s

theorem radical_mass_oneG_prime (k : ℕ) (dp : ι → ℕ) (hd : ∀ i, dp i ≤ k) (p : ι → ℕ) :
    ∑ s : ι → Option (Fin k), weightG k dp (primeRecip p) s = 1 :=
  radical_mass_oneG k dp hd _

/-- **(G1, prime form)** the graded single-site moment at `q_i = 1/p_i`. -/
theorem radical_site_momentG_prime (k : ℕ) (dp : ι → ℕ) (hd : ∀ i, dp i ≤ k) (p : ι → ℕ)
    (j₀ : Fin k) (t : ι → ℝ) :
    ∑ s : ι → Option (Fin k),
        weightG k dp (primeRecip p) s * ∏ i, (if s i = some j₀ then t i else 1)
      = ∏ i, (if (j₀ : ℕ) < dp i then 1 + (t i - 1) / (p i : ℝ) else 1) := by
  rw [radical_site_momentG k dp hd (primeRecip p) j₀ t]
  refine Finset.prod_congr rfl fun i _ => ?_
  split
  · rw [primeRecip, div_eq_inv_mul]
  · rfl

end NormalNumbers.PrimeModel.Radical
