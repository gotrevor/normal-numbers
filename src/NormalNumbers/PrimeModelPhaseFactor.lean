import NormalNumbers.PrimeModelPhaseAlgebra
import NormalNumbers.PrimeModelRadicalState

/-!
# Prime model, assembly part B: factorising the window phase

`papers/prime-model-assembly-2026-09-22.md`, "Decomposition", "E1" and "Phase factorisation".

The window term `e(h · truncTailS S k n) = ∏_{j<k} z_j^{ω_S(n+j+1)}` with `z_j = e(h/4^{j+1})`.
Split `ω_S(m) = ω_{≤y}(m) + ω_{>y}(m)` at the sieve cutoff `y`:

* **E1** (`windowMean_sub_windowMeanLe_le`): dropping the primes above `y` costs at most
  `4k · recipSumIoc S y x + 2k²/x` in the window mean (each `p ∈ (y, x]` divides at most
  `x/p + 1 ≤ 2x/p` of the `n+j+1 < x + k`, and there are at most `k` primes in `(x, x+k]`).
* **Phase factorisation** (`phase_factorisation`): for `p ≤ k` the indicator `[p ∣ n+j+1]`
  depends only on `n mod k#`; for `k < p ≤ y` at most one `j` hits, recorded by `hitShift`.
  So the `y`-truncated term is `residuePhase (n mod k#) · statePhase (actualState k P n)`,
  `P` the `S`-primes in `(k, y]`.

Shift convention `n + j + 1` throughout, matching `truncTailS` and `hitShift`.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.PrimeModel.PhaseFactor

open NormalNumbers.PrimeLambert NormalNumbers.G4 NormalNumbers.G4Sparse
open NormalNumbers.PrimeModel.Radical NormalNumbers.PrimeModel.RadicalState
open NormalNumbers.PrimeModel.PhaseAlgebra

variable (S : ℕ → Prop) [DecidablePred S]

/-- `#{p ∈ S prime : p ≤ y, p ∣ m}`. -/
def omegaLe (y m : ℕ) : ℕ := ((m.primeFactors.filter S).filter (fun p => p ≤ y)).card

/-- `#{p ∈ S prime : y < p, p ∣ m}`. -/
def omegaGt (y m : ℕ) : ℕ := ((m.primeFactors.filter S).filter (fun p => y < p)).card

lemma omegaSN_eq_omegaLe_add_omegaGt (y m : ℕ) :
    omegaSN S m = omegaLe S y m + omegaGt S y m := by
  sorry

/-- The window term as a product of site phases raised to `ω_S`. -/
theorem window_term_eq (k : ℕ) (h : ℤ) (n : ℕ) :
    ePhase ((h : ℝ) * truncTailS S k n)
      = ∏ j : Fin k, zPhase h k j ^ omegaSN S (n + j.val + 1) := by
  sorry

/-- The window mean with the primes above `y` removed from every `ω_S`. -/
noncomputable def windowMeanLe (y k : ℕ) (h : ℤ) (x : ℕ) : ℂ :=
  prefixMean (fun n => ∏ j : Fin k, zPhase h k j ^ omegaLe S y (n + j.val + 1)) x

/-- **E1.**  `‖W − W_y‖ ≤ 4k · ∑_{y<p≤x, p∈S} 1/p + 2k²/x`. -/
theorem windowMean_sub_windowMeanLe_le (y k : ℕ) (h : ℤ) (x : ℕ) (hx : 1 ≤ x) :
    ‖windowMeanS S k h x - windowMeanLe S y k h x‖
      ≤ 4 * k * recipSumIoc S y x + 2 * (k : ℝ) ^ 2 / x := by
  sorry

/-- The `S`-primes in `(k, y]`: the index set of the radical model. -/
def midPrimes (k y : ℕ) : Finset ℕ := (Finset.Iic y).filter (fun p => p.Prime ∧ S p ∧ k < p)

/-- The `S`-primes `≤ k`, handled by the residue modulo `k#`. -/
def smallPrimes (k : ℕ) : Finset ℕ := (Finset.Iic k).filter (fun p => p.Prime ∧ S p)

lemma mem_midPrimes {k y p : ℕ} : p ∈ midPrimes S k y ↔ p.Prime ∧ S p ∧ k < p ∧ p ≤ y := by
  sorry

/-- The residue factor: the phase contribution of the `S`-primes `≤ k`, a function of `n mod k#`. -/
noncomputable def residuePhase (k : ℕ) (h : ℤ) (r : ℕ) : ℂ :=
  ∏ p ∈ smallPrimes S k, ∏ j : Fin k, if p ∣ r + j.val + 1 then zPhase h k j else 1

lemma norm_residuePhase_le (k : ℕ) (h : ℤ) (r : ℕ) : ‖residuePhase S k h r‖ ≤ 1 := by
  sorry

/-- The state factor: `∏_{p ∈ P} localPhase (state p)`. -/
noncomputable def statePhase (k y : ℕ) (h : ℤ)
    (s : {q // q ∈ midPrimes S k y} → Option (Fin k)) : ℂ :=
  ∏ i, localPhase k (zPhase h k) (s i)

lemma norm_statePhase_le (k y : ℕ) (h : ℤ) (s : {q // q ∈ midPrimes S k y} → Option (Fin k)) :
    ‖statePhase S k y h s‖ ≤ 1 := by
  sorry

/-- **Phase factorisation.**  The `y`-truncated window term is the residue factor at `n mod k#`
times the state factor at the actual radical state. -/
theorem phase_factorisation (k y : ℕ) (hk : 1 ≤ k) (h : ℤ) (n : ℕ) :
    ∏ j : Fin k, zPhase h k j ^ omegaLe S y (n + j.val + 1)
      = residuePhase S k h (n % primorial k)
          * statePhase S k y h (actualState k (midPrimes S k y) n) := by
  sorry

/-- The `S`-reciprocal sum up to `y` is the `midPrimes` sum plus at most `k` (one term `≤ 1/2`
per small prime, and there are at most `k` of them). -/
theorem recipSumLe_le_sum_midPrimes (k y : ℕ) :
    recipSumLe S y ≤ (∑ i : {q // q ∈ midPrimes S k y}, (1 : ℝ) / ((i : ℕ) : ℝ)) + k := by
  sorry

end NormalNumbers.PrimeModel.PhaseFactor
