import NormalNumbers.ElliottGenericGraphCRT
import ErdosProblems.Erdos67b.PrimeGraphDecoupling

/-!
# Entropy decoupling for the generic-edge prime graph

The rung above `NormalNumbers.ElliottGenericGraphCRT`, and the last structural obstacle between the
proved lower-bound chain and the `a`-dilated graph of the Elliott crux.

Two widenings relative to `NormalNumbers.ElliottTwistedGraphDecoupling`, both identified as free in
laps 27–28:

* **Generic edge** (lap 27).  The CRT/concentration layer is proved for an arbitrary family
  `E : ℕ → Fin H → ℂ` with `‖E p j‖ ≤ B²`.
* **Block-level decode at a dilated length** (lap 28).  The proved port builds its two graph blocks
  pointwise from the alphabet block (`d₁ ∘ b`).  The dilated graph's blocks have length `a` times
  the entropy block length, so the edge family is produced by an arbitrary map

  ```
  mkE : (m : ℕ) → (Fin m → α) → ℕ → Fin (a * m) → ℂ.
  ```

  This is legitimate because `Erdos67b.logProb_block_rare_event_le` takes an **arbitrary** rare
  event family over an **arbitrary** finite alphabet, and (lap 28)
  `affineBlock f a n (a*m) = finiteSequenceBlock f (a*m) (a*(n+1) - 1)` is a function of the
  ordinary block of the `a`-grouped sequence at the ordinary base point `n`.

The prime-dependent residue shift the dilated graph needs is *not* a parameter here: by CRT the
family of per-prime shifts `(d_p)_p` is a single element of `ZMod (primeGraphModulus H)`, so the
caller applies it to the residue variable and the rare-event family absorbs it.

The only place the dilation costs anything is a constant: the entropy budget is stated at the
block length `m` while the graph lives at `a*m`, and `m / log m ≤ 2 · (a m) / log (a m)` for
`m ≥ a`, so the dependency's `τ = cκ/2` becomes `τ = cκ/4`.

Never edit dependency files; everything here is a new statement in `src/`.
-/

open scoped BigOperators ComplexConjugate NNReal
open Finset Filter

namespace NormalNumbers.ElliottGenericGraph

open Erdos67b
open Erdos67b.FiniteEntropy

noncomputable section

/-- The centred generic graph observable, at an arbitrary residue. -/
def genDiscrepancyAt {H : ℕ} (w : ℕ → ℂ) (E : ℕ → Fin H → ℂ) (s : Finset ℕ)
    (z : ZMod (primeGraphModulus H)) : ℂ :=
  genSum w E s z - genMeanCRT w E s

theorem norm_genDiscrepancyAt_le {H : ℕ} (w : ℕ → ℂ) (E : ℕ → Fin H → ℂ) (s : Finset ℕ)
    {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hw : ∀ p ∈ s, ‖w p‖ ≤ 1)
    (hE : ∀ p, ∀ j, ‖E p j‖ ≤ B ^ 2) (hs : ∀ p ∈ s, δ * H ≤ p)
    (z : ZMod (primeGraphModulus H)) :
    ‖genDiscrepancyAt w E s z‖ ≤ 2 * (Nat.primeCounting H : ℝ) * primeGraphRadius B δ := by
  have hsum := norm_genSum_le w E s hB hδ hw hE hs z
  have hmean := norm_genMeanCRT_le w E s hB hδ hw hE hs
  exact (norm_sub_le _ _).trans (by linarith)

/-- A convenience comparison: at block length `m ≥ max 2 a` the graph length `a*m` has
`m / log m ≤ 2 · (a m) / log (a m)`.  This is the *only* place the dilation costs anything in the
entropy layer, and it costs a factor `2`. -/
theorem entropy_scale_ratio {a m : ℕ} (ha : 0 < a) (ham : a ≤ m) (hm : 2 ≤ m) :
    (m : ℝ) / Real.log m ≤ 2 * ((a * m : ℕ) : ℝ) / Real.log ((a * m : ℕ) : ℝ) := by
  have hmr : (1 : ℝ) < m := by exact_mod_cast hm
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos hmr
  have har : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hamr : ((a * m : ℕ) : ℝ) = (a : ℝ) * m := by push_cast; ring
  have hloga : Real.log (a : ℝ) ≤ Real.log (m : ℝ) :=
    Real.log_le_log (by linarith) (by exact_mod_cast ham)
  have hlogam : Real.log ((a * m : ℕ) : ℝ) ≤ 2 * Real.log (m : ℝ) := by
    rw [hamr, Real.log_mul (by linarith) (by linarith)]
    linarith
  have hlogampos : 0 < Real.log ((a * m : ℕ) : ℝ) := by
    rw [hamr, Real.log_mul (by linarith) (by linarith)]
    have : 0 ≤ Real.log (a : ℝ) := Real.log_nonneg har
    linarith
  have hm0 : (0 : ℝ) < m := by linarith
  rw [div_le_div_iff₀ hlogm hlogampos]
  calc (m : ℝ) * Real.log ((a * m : ℕ) : ℝ) ≤ (m : ℝ) * (2 * Real.log (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogam hm0.le
    _ ≤ 2 * ((a * m : ℕ) : ℝ) * Real.log (m : ℝ) := by
        rw [hamr]
        nlinarith [mul_nonneg (mul_nonneg (show (0:ℝ) ≤ (a:ℝ) - 1 by linarith) hm0.le) hlogm.le]

/-- **Port of `NormalNumbers.ElliottTwistedGraph.exists_logProb_pairTwisted_small_tail` to a
generic edge family at the dilated length `a * m`.**  The scale `j` is selected from the
finite-alphabet sequence alone; the twist `w` and the active primes `s` are chosen afterwards. -/
theorem exists_logProb_gen_small_tail
    {α : Type*} [Finite α] [Nonempty α] {a : ℕ} (ha : 0 < a)
    (mkE : (m : ℕ) → (Fin m → α) → ℕ → Fin (a * m) → ℂ)
    {B δ ρ κ : ℝ} (hB : 0 < B) (hδ : 0 < δ) (hρ : 0 < ρ) (hκ : 0 < κ)
    (hE : ∀ m b p j, ‖mkE m b p j‖ ≤ B ^ 2) (Hmin : ℕ) :
    ∃ H₀ J L₀ : ℕ, Hmin ≤ H₀ ∧ 2 ≤ H₀ ∧ a ≤ H₀ ∧ 0 < J ∧ 0 < L₀ ∧
      ∀ (L U : ℕ) (hL : 0 < L) (hU : 2 * L ≤ U), L₀ ≤ L →
      ∀ F : ℕ → α, ∃ j < J, ∀ (w : ℕ → ℂ) (s : Finset ℕ),
        (∀ p ∈ s, ‖w p‖ ≤ 1) → (∀ p ∈ s, δ * (a * entropyScale H₀ j : ℕ) ≤ p) →
        finiteEventMass (logProbFiniteLaw L U hL (by omega))
          {n | ρ * (a * entropyScale H₀ j : ℕ) / Real.log ((a * entropyScale H₀ j : ℕ) : ℝ) ≤
            ‖genDiscrepancyAt w
                (mkE (entropyScale H₀ j) (finiteSequenceBlock F (entropyScale H₀ j) n.1)) s
                (n.1 : ZMod (primeGraphModulus (a * entropyScale H₀ j)))‖} ≤ κ := by
  classical
  let _ := Fintype.ofFinite α
  obtain ⟨c, hc, H₁, hH₁, htail⟩ := exists_gen_exponential_tail hB hδ hρ
  obtain ⟨H₂, hH₂⟩ := eventually_atTop.mp (eventually_four_le_mul_nat_div_log (mul_pos hc hκ))
  let H₀ := max (max Hmin a) (max (max H₁ H₂) 2)
  have hH₀min : Hmin ≤ H₀ := (le_max_left _ _).trans (le_max_left _ _)
  have hH₀a : a ≤ H₀ := (le_max_right _ _).trans (le_max_left _ _)
  have hH₀one : H₁ ≤ H₀ := ((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_right _ _)
  have hH₀two : H₂ ≤ H₀ := ((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_right _ _)
  have hH₀ : 2 ≤ H₀ := (le_max_right _ _).trans (le_max_right _ _)
  let τ := c * κ / 4
  have hτ : 0 < τ := by dsimp [τ]; positivity
  let P : ℕ → ℕ := fun j ↦ primeGraphModulus (a * entropyScale H₀ j)
  let _ : ∀ j, NeZero (P j) := fun j ↦ instNeZeroPrimeGraphModulus _
  have hP (j : ℕ) : Real.log (P j) ≤ (Real.log 4 * a) * entropyScale H₀ j := by
    have h1 : Real.log (P j) ≤ Real.log 4 * (a * entropyScale H₀ j : ℕ) := by
      rw [show P j = primorial (a * entropyScale H₀ j) from primeGraphModulus_eq_primorial _]
      exact log_primorial_le_log_four_mul _
    have h2 : ((a * entropyScale H₀ j : ℕ) : ℝ) = (a : ℝ) * entropyScale H₀ j := by
      push_cast; ring
    rw [h2] at h1
    linarith [h1]
  obtain ⟨J, L₀, hJ, hL₀, hselect⟩ := exists_logProb_block_entropy_control (α := α)
    hH₀ hτ (by positivity : (0:ℝ) ≤ Real.log 4 * a) P hP
  refine ⟨H₀, J, L₀, hH₀min, hH₀, hH₀a, hJ, hL₀, ?_⟩
  intro L U hL hU hLL F
  obtain ⟨j, hj, hinfo, hdef⟩ := hselect L U hL hU hLL F
  refine ⟨j, hj, ?_⟩
  intro w s hw hs
  set m := entropyScale H₀ j with hmdef
  have hmH₀ : H₀ ≤ m := le_entropyScale H₀ j
  have hm2 : 2 ≤ m := hH₀.trans hmH₀
  have hma : a ≤ m := hH₀a.trans hmH₀
  set H := a * m with hHdef
  have hmH : m ≤ H := Nat.le_mul_of_pos_left m ha
  have hHH₁ : H₁ ≤ H := (hH₀one.trans hmH₀).trans hmH
  have hHH₂ : H₂ ≤ H := (hH₀two.trans hmH₀).trans hmH
  have hHpos : (0 : ℝ) < H := by
    have : 0 < H := by rw [hHdef]; positivity
    exact_mod_cast this
  have hlog : 0 < Real.log (H : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < H by omega))
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  let E : (Fin m → α) → Finset (ZMod (primeGraphModulus H)) := fun b ↦
    Finset.univ.filter fun z ↦ ρ * H / Real.log (H : ℝ) ≤
      ‖genDiscrepancyAt w (mkE m b) s z‖
  have hrare : ∀ b, ((E b).card : ℝ) * Real.exp (c * H / Real.log H) ≤ primeGraphModulus H := by
    intro b
    exact htail H hHH₁ w (mkE m b) s hw (fun p jj ↦ hE m b p jj) hs
  have hprob := logProb_block_rare_event_le hL (by omega : L ≤ U) F E
    (show 0 < c * H / Real.log H by positivity) hrare hinfo hdef
  have hratio : (m : ℝ) / Real.log m ≤ 2 * (H : ℝ) / Real.log (H : ℝ) :=
    entropy_scale_ratio ha hma hm2
  have hsmall : (τ * m / Real.log m + 2) / (c * H / Real.log H) ≤ κ := by
    apply (div_le_iff₀ (show 0 < c * H / Real.log H by positivity)).mpr
    have hlarge := hH₂ H hHH₂
    set X : ℝ := (H : ℝ) / Real.log (H : ℝ) with hX
    have h1 : τ * ((m : ℝ) / Real.log m) ≤ τ * (2 * X) := by
      refine mul_le_mul_of_nonneg_left ?_ hτ.le
      rw [hX]
      simpa only [mul_div_assoc] using hratio
    have h2 : (4 : ℝ) ≤ c * κ * X := by
      rw [hX]; simpa only [mul_div_assoc] using hH₂ H hHH₂
    have hgoal : τ * ((m : ℝ) / Real.log m) + 2 ≤ κ * (c * X) := by
      have hτv : τ = c * κ / 4 := rfl
      rw [hτv] at h1
      nlinarith [h1, h2, hc, hκ]
    simpa only [mul_div_assoc] using hgoal
  have hfinal := hprob.trans hsmall
  have hset : {n : LogProbIndex L U | (n.1 : ZMod (primeGraphModulus H)) ∈
      E (finiteSequenceBlock F m n.1)} =
      {n : LogProbIndex L U | ρ * (H : ℕ) / Real.log ((H : ℕ) : ℝ) ≤
        ‖genDiscrepancyAt w (mkE m (finiteSequenceBlock F m n.1)) s
          (n.1 : ZMod (primeGraphModulus H))‖} := by
    ext n
    change ((n.1 : ZMod (primeGraphModulus H)) ∈ E (finiteSequenceBlock F m n.1)) ↔ _
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  rw [hset] at hfinal
  exact hfinal

end

end NormalNumbers.ElliottGenericGraph

#print axioms NormalNumbers.ElliottGenericGraph.exists_logProb_gen_small_tail
