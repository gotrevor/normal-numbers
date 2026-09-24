import NormalNumbers.SwingC1Weyl

/-!
# Leaf (D) isolated: `PairDecorr = (proved model) + (named decoupling defect)`

`conjC1_of_delange_katai` (`SwingC1Weyl.lean`) leaves `PairDecorr b t` as the only open input.
This file splits `PairDecorr` along the model/decoupling decomposition of `SwingC1CRT.lean` and
discharges the model half from the unconditional result of `SwingC1Pair.lean`.

Fix a prime cut `P` and put `Q = Π_{r ≤ P} r`.  Then

`e(t(θ_{pn} − θ_{qn})) = A(n) · B(n)`,
`A(n) = e(t·truncPairTail b P p q n)` exactly `Q`-periodic,
`B(n) = e(t·pairRemainder b P p q n)` carried by the primes `> P`,

and `norm_fullMean_mul_le_periodMean_add_defect` gives

`‖mean_{n<QR} A B‖ ≤ ‖periodMean A Q‖ + pairDefect b P p q t R`.

The first term is `‖Π_{r ≤ P} pairLocalFactor b t r p q‖`, which tends to `0` as `P → ∞` —
**a theorem** (`prod_pairLocalFactor_tendsto_zero`, lap 32, unconditional).  So the entire
remaining content of the swing is the second term:

`PairDecouple b p q t` : for every cut `P`, the large-prime remainder equidistributes in
progressions to the small-prime modulus `Q`.

`pairDecorr_of_pairDecouple` is the resulting reduction.  Sorry-free.

⚠️ What this does NOT do: `PairDecouple` is not easier than `PairDecorr` by fiat — it is the same
difficulty, relocated.  Its value is that it names EXACTLY the gap and proves everything else,
and that the obstruction is now visible as a single quantity: the primorial `Q = e^{(1+o(1))P}`
must be `≤ N`, so the usable cut is `P ≤ log N`, where the discarded mass is still `≍ log log N`
(`OBSTRUCTION-2026-09-24-periodic-approximant.md`).  `PairDecouple` is precisely the assertion
that the discarded mass nonetheless does not conspire with the residues mod `Q`.
-/

open Finset Filter Topology NormalNumbers.PrimeLambert

namespace NormalNumbers.CastingOut

/-- The pair difference of the orbit at multiplicatively shifted indices. -/
noncomputable def pairTail (b p q n : ℕ) : ℝ := omegaTail b (p * n) - omegaTail b (q * n)

/-- The large-prime remainder of the pair difference at cut `P`. -/
noncomputable def pairRemainder (b P p q n : ℕ) : ℝ :=
  pairTail b p q n - truncPairTail b P p q n

lemma truncPairTail_add_pairRemainder (b P p q n : ℕ) :
    truncPairTail b P p q n + pairRemainder b P p q n = pairTail b p q n := by
  rw [pairRemainder]; ring

/-- The small-prime part is exactly `primorialLe P`-periodic. -/
lemma truncPairTail_add_mul_primorial (b P p q c r : ℕ) :
    truncPairTail b P p q (c + r * primorialLe P) = truncPairTail b P p q c := by
  rw [truncPairTail, truncPairTail]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hdvd : s ∣ primorialLe P := dvd_primorialLe hs
  have hmod : ∀ k : ℕ, (k * (c + r * primorialLe P)) % s = (k * c) % s := by
    intro k
    obtain ⟨d, hd⟩ := hdvd
    rw [show k * (c + r * primorialLe P) = k * c + (k * r * d) * s by rw [hd]; ring,
      Nat.add_mul_mod_self_right]
  rw [primePeriodicTerm, primePeriodicTerm, primePeriodicTerm, primePeriodicTerm,
    hmod p, hmod q]

/-! ### The defect -/

/-- The decoupling defect of the pair remainder at cut `P` over `Q·R` terms. -/
noncomputable def pairDefect (b P p q : ℕ) (t : ℝ) (R : ℕ) : ℝ :=
  (∑ c ∈ range (primorialLe P),
      ‖progMean (fun n => phase (t * pairRemainder b P p q n)) (primorialLe P) R c
        - fullMean (fun n => phase (t * pairRemainder b P p q n)) (primorialLe P * R)‖)
    / primorialLe P

/-- **LEAF (D), isolated.**  For every prime cut `P`, the large-prime remainder of the pair
difference equidistributes in progressions to the small-prime modulus `Q = Π_{r ≤ P} r`. -/
def PairDecouple (b p q : ℕ) (t : ℝ) : Prop :=
  ∀ P : ℕ, Tendsto (fun R => pairDefect b P p q t R) atTop (𝓝 0)

/-! ### Ragged `N` -/

/-- A Cesàro mean over `N` terms is controlled by the mean over the largest multiple of `Q`. -/
lemma norm_fullMean_le_of_mul (f : ℕ → ℂ) (hf : ∀ m, ‖f m‖ ≤ 1) (Q N : ℕ)
    (hQ : 0 < Q) (hN : 0 < N) :
    ‖fullMean f N‖ ≤ ‖fullMean f (Q * (N / Q))‖ + (Q : ℝ) / N := by
  have h1 : Q * (N / Q) + N % Q = N := Nat.div_add_mod N Q
  have h2 : N % Q < Q := Nat.mod_lt N hQ
  set R := N / Q with hR
  have hle' : Q * R ≤ N := by omega
  have hgt : N < Q * R + Q := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsplit : ∑ m ∈ range N, f m
      = (∑ m ∈ range (Q * R), f m) + ∑ m ∈ Finset.Ico (Q * R) N, f m := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le (Q * R)) hle',
      Finset.range_eq_Ico]
  have hrest : ‖∑ m ∈ Finset.Ico (Q * R) N, f m‖ ≤ (Q : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ m ∈ Finset.Ico (Q * R) N, ‖f m‖
        ≤ ∑ _m ∈ Finset.Ico (Q * R) N, (1 : ℝ) := Finset.sum_le_sum fun m _ => hf m
      _ = ((N - Q * R : ℕ) : ℝ) := by simp
      _ ≤ (Q : ℝ) := by
          have : N - Q * R ≤ Q := by omega
          exact_mod_cast this
  have hmain : ‖∑ m ∈ range (Q * R), f m‖ ≤ ‖fullMean f (Q * R)‖ * (N : ℝ) := by
    rcases Nat.eq_zero_or_pos (Q * R) with h0 | h0
    · rw [h0]; simp; positivity
    · have hQR : (0 : ℝ) < (Q * R : ℕ) := by exact_mod_cast h0
      have : ‖fullMean f (Q * R)‖ = ‖∑ m ∈ range (Q * R), f m‖ / ((Q * R : ℕ) : ℝ) := by
        rw [fullMean, norm_div, Complex.norm_natCast]
      rw [this, div_mul_eq_mul_div, le_div_iff₀ hQR]
      have hQRN : ((Q * R : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hle'
      nlinarith [norm_nonneg (∑ m ∈ range (Q * R), f m)]
  rw [fullMean, norm_div, Complex.norm_natCast, div_le_iff₀ hNR, hsplit]
  refine (norm_add_le _ _).trans ?_
  have : (‖fullMean f (Q * R)‖ + (Q : ℝ) / N) * N
      = ‖fullMean f (Q * R)‖ * N + (Q : ℝ) := by field_simp
  rw [this]
  linarith

/-! ### The reduction -/

set_option maxHeartbeats 1000000 in
/-- **Leaf (D) is the whole remaining content.**  The model half is proved; granted
`PairDecouple`, `PairDecorr` follows. -/
theorem pairDecorr_of_pairDecouple (b : ℕ) (hb : 2 ≤ b) (t : ℝ) (ht : t ≠ 0)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hdec : PairDecouple b p q t) :
    Tendsto (fun N => fullMean (fun n => phase (t * pairTail b p q n)) N) atTop (𝓝 0) := by
  classical
  set f : ℕ → ℂ := fun n => phase (t * pairTail b p q n) with hf
  have hfnorm : ∀ m, ‖f m‖ ≤ 1 := fun m => le_of_eq (norm_phase _)
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  -- choose the cut `P`
  obtain ⟨P, hP⟩ := Filter.eventually_atTop.mp
    ((NormedAddGroup.tendsto_nhds_zero.mp
      (prod_pairLocalFactor_tendsto_zero b hb t ht p q hp hq hpq)) (ε / 4) (by linarith))
  have hmodel : ‖(‖∏ r ∈ primesLe P, pairLocalFactor b t r p q‖ : ℝ)‖ < ε / 4 := hP P le_rfl
  have hmodel' : ‖∏ r ∈ primesLe P, pairLocalFactor b t r p q‖ < ε / 4 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hmodel
  set Q : ℕ := primorialLe P with hQdef
  have hQ : 0 < Q := primorialLe_pos P
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  set A : ℕ → ℂ := fun n => phase (t * truncPairTail b P p q n) with hA
  set B : ℕ → ℂ := fun n => phase (t * pairRemainder b P p q n) with hB
  have hAB : ∀ n, f n = A n * B n := by
    intro n
    rw [hf, hA, hB, ← phase_add, ← mul_add, truncPairTail_add_pairRemainder]
  have hper : ∀ c r : ℕ, A (c + r * Q) = A c := by
    intro c r
    show phase (t * truncPairTail b P p q (c + r * Q)) = phase (t * truncPairTail b P p q c)
    rw [hQdef, truncPairTail_add_mul_primorial]
  have hAnorm : ∀ m, ‖A m‖ ≤ 1 := fun m => le_of_eq (norm_phase _)
  have hBnorm : ∀ m, ‖B m‖ ≤ 1 := fun m => le_of_eq (norm_phase _)
  have hperiodMean : ‖periodMean A Q‖ < ε / 4 := by
    rw [hA, hQdef, periodMean_phase_truncPairTail]
    exact hmodel'
  -- choose `R₀`
  obtain ⟨R₀, hR₀⟩ := Filter.eventually_atTop.mp
    ((NormedAddGroup.tendsto_nhds_zero.mp (hdec P)) (ε / 4) (by linarith))
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (4 * (Q : ℝ) / ε)
  refine Filter.eventually_atTop.mpr ⟨max (Q * (R₀ + 1) + Q) (N₁ + 1), fun N hN => ?_⟩
  have hNpos : 0 < N := by
    have := le_trans (le_max_right _ _) hN
    omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  set R : ℕ := N / Q with hRdef
  have hRge1 : R₀ + 1 ≤ R := by
    have hb1 : Q * (R₀ + 1) + Q ≤ N := le_trans (le_max_left _ _) hN
    have hb2 : Q * (R₀ + 1) ≤ N := by omega
    have hb3 : (Q * (R₀ + 1)) / Q ≤ N / Q := Nat.div_le_div_right hb2
    rw [Nat.mul_div_cancel_left _ hQ] at hb3
    rw [hRdef]
    omega
  have hRge : R₀ ≤ R := by omega
  have hRpos : 0 < R := by omega
  -- the tail term
  have htail : (Q : ℝ) / N < ε / 4 := by
    have hN1 : (N₁ : ℝ) < (N : ℝ) := by
      have := le_trans (le_max_right _ _) hN
      exact_mod_cast (by omega : N₁ < N)
    have : 4 * (Q : ℝ) / ε < (N : ℝ) := lt_trans hN₁ hN1
    rw [div_lt_iff₀ hNR]
    rw [div_lt_iff₀ hε] at this
    linarith
  -- assemble
  have hsplit := norm_fullMean_le_of_mul f hfnorm Q N hQ hNpos
  have hcore : ‖fullMean f (Q * R)‖
      ≤ ‖periodMean A Q‖ + (∑ c ∈ range Q, ‖progMean B Q R c - fullMean B (Q * R)‖) / Q := by
    have hmain := norm_fullMean_mul_le_periodMean_add_defect A B Q R hQ hRpos hper hAnorm hBnorm
    have heq : fullMean f (Q * R) = fullMean (fun m => A m * B m) (Q * R) := by
      rw [fullMean, fullMean, Finset.sum_congr rfl (fun n _ => hAB n)]
    rw [heq]
    exact hmain
  have hdefect : (∑ c ∈ range Q, ‖progMean B Q R c - fullMean B (Q * R)‖) / Q
      = pairDefect b P p q t R := by
    rw [pairDefect, hB, hQdef]
  have hdlt : pairDefect b P p q t R < ε / 4 := by
    have := hR₀ R hRge
    simpa [Real.norm_eq_abs, abs_of_nonneg (by
      rw [pairDefect]
      positivity : (0:ℝ) ≤ pairDefect b P p q t R)] using this
  rw [hdefect] at hcore
  rw [← hRdef] at hsplit
  calc ‖fullMean f N‖ ≤ ‖fullMean f (Q * R)‖ + (Q : ℝ) / N := hsplit
    _ ≤ (‖periodMean A Q‖ + pairDefect b P p q t R) + (Q : ℝ) / N := by linarith
    _ < ε := by linarith

/-- **`PairDecorr` from `PairDecouple`.** -/
theorem pairDecorr_of_decouple (b : ℕ) (hb : 2 ≤ b) (t : ℝ) (ht : t ≠ 0)
    (hdec : ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → PairDecouple b p q t) :
    PairDecorr b t := by
  intro p q hp hq hpq
  exact pairDecorr_of_pairDecouple b hb t ht p q hp hq hpq (hdec p q hp hq hpq)

/-- **THE SWING, with leaf (D) fully isolated.**  `ConjC1` follows from the two KNOWN theorems
`KataiOrthogonality` and `DelangeMean`, plus `PairDecouple` — the assertion that the
large-prime remainder of the pair difference equidistributes in progressions to the small-prime
modulus.  Every other ingredient, including the model term `Π_{r≤P} pairLocalFactor → 0`
(Mertens + the separation bound), is a proved theorem of this development. -/
theorem conjC1_of_delange_katai_decouple (hDK : KataiOrthogonality)
    (hD : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) → DelangeMean (((m : ℤ) : ℝ) / b))
    (hDc : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
      ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → PairDecouple b p q (((m : ℤ) : ℝ) / b)) :
    ConjC1 := by
  refine conjC1_of_delange_katai hDK hD (fun b hb m hm hdvd => ?_)
  have hbpos : (0 : ℝ) < (b : ℝ) := by
    have : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  have hmR : ((m : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
  exact pairDecorr_of_decouple b (by omega) (((m : ℤ) : ℝ) / b)
    (div_ne_zero hmR (ne_of_gt hbpos)) (hDc b hb m hm hdvd)

end NormalNumbers.CastingOut
