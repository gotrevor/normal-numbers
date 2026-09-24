import NormalNumbers.PairDecoupleAttacks

/-!
# The CRT half of `PairDecouple`, PROVED

`DIRECTION.md`'s finding: since `PairDecouple` fixes the cut `P` (hence the modulus
`Q = primorialLe P`) *before* letting `R → ∞`, every **bounded** prime band is reachable by CRT
and only the primes `r ≍ N` are not.  This file proves exactly that, so the crux is decomposed:

> `pairRemainder b P p q n = bandPairTail b P y p q n + pairRemainder b y p q n`   (`P ≤ y`)

with the first summand's class deviation **provably** `≤ 4·bandModulus P y / R`
(`classDeviation_bandPairTail_le`) — it tends to `0` for every fixed `y`.  So

**any counterexample to `PairDecouple` must be produced by the tail beyond every fixed `y`.**

## The mechanism, in one line

`bandPairTail b P y p q ·` is periodic with modulus `bandModulus P y = ∏_{P < r ≤ y} r`, and that
modulus is **coprime** to `Q = ∏_{r ≤ P} r`.  A `M`-periodic function with `gcd(Q, M) = 1` has all
its class sums over `ℤ/Q` *equal*: `H c = ∑_{s<M} B (c + sQ)` is both `Q`-periodic (telescoping,
using `B (c + MQ) = B c`) and `M`-periodic (termwise), hence `1`-periodic, hence constant
(`sum_class_period_const`).  That is the whole CRT content, with no arithmetic in it.

The abstract statement is `classDeviation_le_of_periodic_coprime`; the quantitative rate `4M/R`
matches the band probe's measured `O(y/R)` (`probes/data-2026-09-24-pair-defect-bands.txt`).
-/

open Finset Filter Topology NormalNumbers.PrimeLambert

namespace NormalNumbers.CastingOut

/-! ### Iterating a period -/

lemma iterate_period {α : Type*} (F : ℕ → α) (M : ℕ) (h : ∀ x, F (x + M) = F x) :
    ∀ x k : ℕ, F (x + M * k) = F x := by
  intro x k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show M * (k + 1) = M * k + M by ring, ← Nat.add_assoc, h, ih]

/-! ### The mean of a periodic function -/

lemma sum_range_mul_of_periodicR (g : ℕ → ℂ) (M k : ℕ) (hper : ∀ n, g (n + M) = g n) :
    ∑ r ∈ range (M * k), g r = (k : ℂ) * ∑ s ∈ range M, g s := by
  rw [sum_range_mul_split g M k]
  have hin : ∀ c ∈ range M, ∑ r ∈ range k, g (c + r * M) = (k : ℂ) * g c := by
    intro c _
    have : ∀ r ∈ range k, g (c + r * M) = g c := fun r _ => by
      rw [Nat.mul_comm r M]; exact iterate_period g M hper c r
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [Finset.sum_congr rfl hin, ← Finset.mul_sum]

lemma norm_sum_range_sub_periodic (g : ℕ → ℂ) (M R : ℕ) (hM : 0 < M)
    (hper : ∀ n, g (n + M) = g n) (hg : ∀ n, ‖g n‖ ≤ 1) :
    ‖(∑ r ∈ range R, g r) - ((R / M : ℕ) : ℂ) * ∑ s ∈ range M, g s‖ ≤ (R % M : ℕ) := by
  have hdm : M * (R / M) + R % M = R := Nat.div_add_mod R M
  have hrlt : R % M < M := Nat.mod_lt _ hM
  have hle' : M * (R / M) ≤ R := by omega
  have hsplit : ∑ r ∈ range R, g r
      = (∑ r ∈ range (M * (R / M)), g r) + ∑ r ∈ Finset.Ico (M * (R / M)) R, g r := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le _) hle',
      Finset.range_eq_Ico]
  rw [hsplit, sum_range_mul_of_periodicR g M (R / M) hper,
    show ((R / M : ℕ) : ℂ) * (∑ s ∈ range M, g s)
        + (∑ r ∈ Finset.Ico (M * (R / M)) R, g r)
        - ((R / M : ℕ) : ℂ) * ∑ s ∈ range M, g s
      = ∑ r ∈ Finset.Ico (M * (R / M)) R, g r from by ring]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ r ∈ Finset.Ico (M * (R / M)) R, ‖g r‖
      ≤ ∑ _r ∈ Finset.Ico (M * (R / M)) R, (1 : ℝ) := Finset.sum_le_sum fun r _ => hg r
    _ = ((R - M * (R / M) : ℕ) : ℝ) := by simp
    _ = ((R % M : ℕ) : ℝ) := by exact_mod_cast (by omega : R - M * (R / M) = R % M)

lemma norm_mean_sub_periodMean_le (g : ℕ → ℂ) (M R : ℕ) (hM : 0 < M) (hR : 0 < R)
    (hper : ∀ n, g (n + M) = g n) (hg : ∀ n, ‖g n‖ ≤ 1) :
    ‖(∑ r ∈ range R, g r) / R - (∑ s ∈ range M, g s) / M‖ ≤ 2 * (R % M : ℕ) / R := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hRr : (0 : ℝ) < R := by exact_mod_cast hR
  have hMc : ((M : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hRc : ((R : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  set S : ℂ := ∑ s ∈ range M, g s with hS
  set T : ℂ := ∑ r ∈ range R, g r with hT
  set k : ℕ := R / M with hk
  set ρ : ℕ := R % M with hρ
  have hRdec : M * k + ρ = R := Nat.div_add_mod R M
  have hρlt : ρ < M := Nat.mod_lt _ hM
  have hE : ‖T - (k : ℂ) * S‖ ≤ (ρ : ℝ) := norm_sum_range_sub_periodic g M R hM hper hg
  have hSnorm : ‖S‖ ≤ M := by
    rw [hS]
    calc ‖∑ s ∈ range M, g s‖ ≤ ∑ s ∈ range M, ‖g s‖ := norm_sum_le _ _
      _ ≤ ∑ _s ∈ range M, (1 : ℝ) := Finset.sum_le_sum fun s _ => hg s
      _ = M := by simp
  have hid : T / R - S / M = ((M : ℂ) * (T - (k : ℂ) * S) - (ρ : ℂ) * S) / ((R : ℂ) * M) := by
    have hRcast : ((R : ℂ)) = (M : ℂ) * k + ρ := by
      rw [← hRdec]; push_cast; ring
    field_simp
    rw [hRcast]
    ring
  rw [hid, norm_div]
  have hden : ‖(R : ℂ) * M‖ = (R : ℝ) * M := by
    rw [norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  rw [hden]
  have hnum : ‖(M : ℂ) * (T - (k : ℂ) * S) - (ρ : ℂ) * S‖ ≤ 2 * M * (ρ : ℝ) := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    have hρr : (0 : ℝ) ≤ (ρ : ℝ) := Nat.cast_nonneg ρ
    nlinarith [norm_nonneg (T - (k : ℂ) * S), norm_nonneg S, hMr, hE, hSnorm]
  rw [div_le_div_iff₀ (by positivity) hRr]
  nlinarith [hnum, hMr, hRr]

/-! ### Coprime period ⇒ the class sums are all equal -/

/-! ### Two coprime periods force constancy -/

lemma const_of_period_one {α : Type*} (F : ℕ → α) (h : ∀ x, F (x + 1) = F x) :
    ∀ x, F x = F 0 := by
  intro x
  induction x with
  | zero => rfl
  | succ n ih => rw [h n]; exact ih

/-- A function with two coprime periods is constant. -/
lemma const_of_coprime_periods {α : Type*} (F : ℕ → α) (Q M : ℕ) (hM : 0 < M)
    (hcop : Nat.Coprime Q M) (hFQ : ∀ x, F (x + Q) = F x) (hFM : ∀ x, F (x + M) = F x) :
    ∀ x, F x = F 0 := by
  refine const_of_period_one F fun x => ?_
  rcases Nat.lt_or_ge M 2 with hM1 | hM2
  · have hM1' : M = 1 := by omega
    subst hM1'
    simpa using hFM x
  · haveI : NeZero M := ⟨by omega⟩
    set a : ℕ := ((Q : ZMod M)⁻¹).val with hadef
    have hav : ((a : ℕ) : ZMod M) = (Q : ZMod M)⁻¹ := by rw [hadef]; simp
    have hQa : ((Q * a : ℕ) : ZMod M) = ((1 : ℕ) : ZMod M) := by
      push_cast
      rw [hav]
      simpa using ZMod.coe_mul_inv_eq_one Q hcop
    have hmod : Q * a ≡ 1 [MOD M] := (ZMod.natCast_eq_natCast_iff _ _ _).mp hQa
    have h1 : (Q * a) % M = 1 := by
      rw [Nat.ModEq] at hmod
      rw [hmod, Nat.mod_eq_of_lt (by omega)]
    have hdm : Q * a = M * (Q * a / M) + 1 := by
      have := Nat.div_add_mod (Q * a) M
      omega
    calc F (x + 1) = F (x + 1 + M * (Q * a / M)) :=
          (iterate_period F M hFM (x + 1) (Q * a / M)).symm
      _ = F (x + Q * a) := by congr 1; omega
      _ = F x := iterate_period F Q hFQ x a

/-- **The CRT core, arithmetic-free.**  If `B` is `M`-periodic and `gcd(Q, M) = 1`, then the sum
of `B` along the class `c mod Q` over one full period does not depend on `c`. -/
theorem sum_class_period_const (B : ℕ → ℂ) (Q M : ℕ) (hQ : 0 < Q) (hM : 0 < M)
    (hcop : Nat.Coprime Q M) (hper : ∀ n, B (n + M) = B n) (c : ℕ) :
    ∑ s ∈ range M, B (c + s * Q) = ∑ s ∈ range M, B (0 + s * Q) := by
  have hHQ : ∀ x : ℕ, (∑ s ∈ range M, B (x + Q + s * Q)) = ∑ s ∈ range M, B (x + s * Q) := by
    intro x
    have hshift : ∀ s ∈ range M, B (x + Q + s * Q) = B (x + (s + 1) * Q) := by
      intro s _; congr 1; ring
    have hsucc : ∑ s ∈ range (M + 1), B (x + s * Q)
        = (∑ s ∈ range M, B (x + (s + 1) * Q)) + B (x + 0 * Q) :=
      Finset.sum_range_succ' (fun s => B (x + s * Q)) M
    have hsucc2 : ∑ s ∈ range (M + 1), B (x + s * Q)
        = (∑ s ∈ range M, B (x + s * Q)) + B (x + M * Q) :=
      Finset.sum_range_succ (fun s => B (x + s * Q)) M
    have hend : B (x + M * Q) = B (x + 0 * Q) := by
      rw [Nat.zero_mul, Nat.add_zero]
      exact iterate_period B M hper x Q
    rw [Finset.sum_congr rfl hshift]
    have hcomb := hsucc.symm.trans hsucc2
    rw [hend] at hcomb
    linear_combination hcomb
  have hHM : ∀ x : ℕ, (∑ s ∈ range M, B (x + M + s * Q)) = ∑ s ∈ range M, B (x + s * Q) := by
    intro x
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [show x + M + s * Q = x + s * Q + M by ring, hper]
  exact const_of_coprime_periods (fun x => ∑ s ∈ range M, B (x + s * Q)) Q M hM hcop hHQ hHM c

/-- **A periodic factor with coprime modulus has vanishing class deviation.** -/
theorem classDeviation_le_of_periodic_coprime (B : ℕ → ℂ) (Q M R : ℕ)
    (hQ : 0 < Q) (hM : 0 < M) (hR : 0 < R) (hcop : Nat.Coprime Q M)
    (hper : ∀ n, B (n + M) = B n) (hB : ∀ n, ‖B n‖ ≤ 1) :
    classDeviation B Q R ≤ 4 * (R % M : ℕ) / R := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hRr : (0 : ℝ) < R := by exact_mod_cast hR
  set V : ℂ := (∑ s ∈ range M, B (0 + s * Q)) / M with hV
  have hclose : ∀ c, ‖progMean B Q R c - V‖ ≤ 2 * (R % M : ℕ) / R := by
    intro c
    have hgper : ∀ n, B (c + (n + M) * Q) = B (c + n * Q) := by
      intro n
      rw [show c + (n + M) * Q = (c + n * Q) + M * Q by ring]
      exact iterate_period B M hper (c + n * Q) Q
    have hsum : ∑ s ∈ range M, B (c + s * Q) = ∑ s ∈ range M, B (0 + s * Q) :=
      sum_class_period_const B Q M hQ hM hcop hper c
    have hkey := norm_mean_sub_periodMean_le (fun r => B (c + r * Q)) M R hM hR hgper
      (fun n => hB _)
    rw [progMean, hV, ← hsum]
    simpa using hkey
  have hfullclose : ‖fullMean B (Q * R) - V‖ ≤ 2 * (R % M : ℕ) / R := by
    rw [fullMean_eq_periodMean_progMean B Q R hQ hR, periodMean]
    have hQc : ((Q : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hid : (∑ c ∈ range Q, progMean B Q R c) / Q - V
        = (∑ c ∈ range Q, (progMean B Q R c - V)) / Q := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, sub_div,
        mul_div_cancel_left₀ _ hQc]
    rw [hid, norm_div, Complex.norm_natCast, div_le_iff₀ hQr]
    calc ‖∑ c ∈ range Q, (progMean B Q R c - V)‖
        ≤ ∑ c ∈ range Q, ‖progMean B Q R c - V‖ := norm_sum_le _ _
      _ ≤ ∑ _c ∈ range Q, (2 * ((R % M : ℕ) : ℝ) / (R : ℝ)) :=
          Finset.sum_le_sum fun c _ => hclose c
      _ = 2 * ((R % M : ℕ) : ℝ) / (R : ℝ) * Q := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  rw [classDeviation, div_le_iff₀ hQr]
  calc ∑ c ∈ range Q, ‖progMean B Q R c - fullMean B (Q * R)‖
      ≤ ∑ _c ∈ range Q,
          (2 * ((R % M : ℕ) : ℝ) / (R : ℝ) + 2 * ((R % M : ℕ) : ℝ) / (R : ℝ)) := by
        refine Finset.sum_le_sum fun c _ => ?_
        calc ‖progMean B Q R c - fullMean B (Q * R)‖
            = ‖(progMean B Q R c - V) - (fullMean B (Q * R) - V)‖ := by congr 1; ring
          _ ≤ ‖progMean B Q R c - V‖ + ‖fullMean B (Q * R) - V‖ := norm_sub_le _ _
          _ ≤ 2 * ((R % M : ℕ) : ℝ) / (R : ℝ) + 2 * ((R % M : ℕ) : ℝ) / (R : ℝ) :=
              add_le_add (hclose c) hfullclose
    _ = 4 * ((R % M : ℕ) : ℝ) / (R : ℝ) * Q := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-! ### The prime band -/

/-- The primes in `(P, y]`. -/
def primesIocR (P y : ℕ) : Finset ℕ := primesLe y \ primesLe P

lemma prime_of_mem_primesIocR {P y r : ℕ} (hr : r ∈ primesIocR P y) : r.Prime :=
  prime_of_mem_primesLe (Finset.mem_sdiff.mp hr).1

/-- The band modulus `∏_{P < r ≤ y} r`. -/
def bandModulus (P y : ℕ) : ℕ := ∏ r ∈ primesIocR P y, r

lemma bandModulus_pos (P y : ℕ) : 0 < bandModulus P y :=
  Finset.prod_pos fun r hr => (prime_of_mem_primesIocR hr).pos

lemma dvd_bandModulus {P y r : ℕ} (hr : r ∈ primesIocR P y) : r ∣ bandModulus P y :=
  Finset.dvd_prod_of_mem _ hr

/-- The small-prime modulus and the band modulus are coprime: disjoint sets of primes. -/
lemma coprime_primorialLe_bandModulus (P y : ℕ) :
    Nat.Coprime (primorialLe P) (bandModulus P y) := by
  rw [primorialLe, bandModulus]
  refine Nat.Coprime.prod_left (fun r hr => Nat.Coprime.prod_right fun s hs => ?_)
  have hrp : r.Prime := prime_of_mem_primesLe hr
  have hsp : s.Prime := prime_of_mem_primesIocR hs
  have hne : r ≠ s := fun h => (Finset.mem_sdiff.mp hs).2 (h ▸ hr)
  exact (Nat.coprime_primes hrp hsp).mpr hne

/-- The pair difference carried by the primes in `(P, y]`. -/
noncomputable def bandPairTail (b P y p q n : ℕ) : ℝ :=
  ∑ r ∈ primesIocR P y, (primePeriodicTerm b r (p * n) - primePeriodicTerm b r (q * n))

lemma bandPairTail_add_bandModulus (b P y p q n : ℕ) :
    bandPairTail b P y p q (n + bandModulus P y) = bandPairTail b P y p q n := by
  rw [bandPairTail, bandPairTail]
  refine Finset.sum_congr rfl fun r hr => ?_
  obtain ⟨d, hd⟩ := dvd_bandModulus hr
  have hmod : ∀ k : ℕ, (k * (n + bandModulus P y)) % r = (k * n) % r := by
    intro k
    rw [show k * (n + bandModulus P y) = k * n + (k * d) * r by rw [hd]; ring,
      Nat.add_mul_mod_self_right]
  rw [primePeriodicTerm, primePeriodicTerm, primePeriodicTerm, primePeriodicTerm, hmod p, hmod q]

/-! ### The band is decoupled — the CRT half of `PairDecouple`, PROVED -/

/-- **For every bounded prime band the class deviation provably vanishes**, at the sharp rate
`4·(R mod M)/R` with `M = bandModulus P y` — in particular EXACTLY `0` whenever `M ∣ R`. -/
theorem classDeviation_bandPairTail_le (b P y p q : ℕ) (t : ℝ) (R : ℕ) (hR : 0 < R) :
    classDeviation (fun n => phase (t * bandPairTail b P y p q n)) (primorialLe P) R
      ≤ 4 * ((R % bandModulus P y : ℕ) : ℝ) / R :=
  classDeviation_le_of_periodic_coprime _ (primorialLe P) (bandModulus P y) R
    (primorialLe_pos P) (bandModulus_pos P y) hR (coprime_primorialLe_bandModulus P y)
    (fun n => by
      show phase (t * bandPairTail b P y p q (n + bandModulus P y))
        = phase (t * bandPairTail b P y p q n)
      rw [bandPairTail_add_bandModulus])
    (fun n => le_of_eq (norm_phase _))

/-- **The band's class deviation is EXACTLY `0` when the band modulus divides `R`.**  This is the
exact CRT statement, and it is what `probes/data-2026-09-24-pair-defect-bands.txt` measures as a
row of clean zeros (e.g. `p=5, q=11, P=3, y=5`: the band is the single prime `5` and `5 ∣ R`). -/
theorem classDeviation_bandPairTail_eq_zero (b P y p q : ℕ) (t : ℝ) (R : ℕ) (hR : 0 < R)
    (hdvd : bandModulus P y ∣ R) :
    classDeviation (fun n => phase (t * bandPairTail b P y p q n)) (primorialLe P) R = 0 := by
  have hmod : R % bandModulus P y = 0 := by obtain ⟨d, hd⟩ := hdvd; subst hd; simp
  have hle := classDeviation_bandPairTail_le b P y p q t R hR
  have hnn := classDeviation_nonneg (fun n => phase (t * bandPairTail b P y p q n))
    (primorialLe P) R
  rw [hmod] at hle
  simp only [Nat.cast_zero, mul_zero, zero_div] at hle
  linarith

theorem classDeviation_bandPairTail_le_modulus (b P y p q : ℕ) (t : ℝ) (R : ℕ) (hR : 0 < R) :
    classDeviation (fun n => phase (t * bandPairTail b P y p q n)) (primorialLe P) R
      ≤ 4 * (bandModulus P y : ℝ) / R := by
  refine le_trans (classDeviation_bandPairTail_le b P y p q t R hR) ?_
  have hRr : (0 : ℝ) < R := by exact_mod_cast hR
  have hle : ((R % bandModulus P y : ℕ) : ℝ) ≤ (bandModulus P y : ℝ) := by
    exact_mod_cast (Nat.mod_lt R (bandModulus_pos P y)).le
  rw [div_le_div_iff_of_pos_right hRr]
  linarith

theorem classDeviation_bandPairTail_tendsto_zero (b P y p q : ℕ) (t : ℝ) :
    Tendsto (fun R => classDeviation (fun n => phase (t * bandPairTail b P y p q n))
      (primorialLe P) R) atTop (𝓝 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨R₀, hR₀⟩ := exists_nat_gt (4 * (bandModulus P y : ℝ) / ε)
  refine Filter.eventually_atTop.mpr ⟨max 1 R₀, fun R hR => ?_⟩
  have hRpos : 0 < R := by have := le_trans (le_max_left 1 R₀) hR; omega
  have hRr : (0 : ℝ) < R := by exact_mod_cast hRpos
  have hbound := classDeviation_bandPairTail_le_modulus b P y p q t R hRpos
  have hnn := classDeviation_nonneg (fun n => phase (t * bandPairTail b P y p q n))
    (primorialLe P) R
  have hlt : 4 * (bandModulus P y : ℝ) / R < ε := by
    have h1 : (R₀ : ℝ) ≤ R := by
      have := le_trans (le_max_right 1 R₀) hR
      exact_mod_cast this
    have : 4 * (bandModulus P y : ℝ) / ε < R := lt_of_lt_of_le hR₀ h1
    rw [div_lt_iff₀ hRr]
    rw [div_lt_iff₀ hε] at this
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  linarith

/-! ### The decomposition of the crux -/

lemma primesLe_subsetR {P y : ℕ} (h : P ≤ y) : primesLe P ⊆ primesLe y := by
  intro r hr
  rw [primesLe, Finset.mem_filter, Finset.mem_range] at hr ⊢
  exact ⟨by omega, hr.2⟩

/-- `truncPairTail` at the higher cut splits as the lower cut plus the band. -/
lemma truncPairTail_eq_add_band (b P y p q n : ℕ) (h : P ≤ y) :
    truncPairTail b y p q n = truncPairTail b P p q n + bandPairTail b P y p q n := by
  rw [truncPairTail, truncPairTail, bandPairTail, primesIocR, add_comm]
  exact (Finset.sum_sdiff (primesLe_subsetR h)).symm

/-- **The crux, decomposed.**  At any cut `P ≤ y`, the remainder at `P` is the band `(P, y]` —
whose class deviation provably tends to `0` — plus the remainder at `y`.  So a counterexample to
`PairDecouple` must be produced by the tail beyond EVERY fixed `y`. -/
theorem pairRemainder_eq_band_add (b P y p q n : ℕ) (h : P ≤ y) :
    pairRemainder b P p q n = bandPairTail b P y p q n + pairRemainder b y p q n := by
  rw [pairRemainder, pairRemainder, truncPairTail_eq_add_band b P y p q n h]
  ring

/-- The phase factorisation matching `pairRemainder_eq_band_add`: the frozen statement's `B` at
cut `P` is (band factor) × (`B` at cut `y`). -/
theorem phase_pairRemainder_eq (b P y p q : ℕ) (t : ℝ) (n : ℕ) (h : P ≤ y) :
    phase (t * pairRemainder b P p q n)
      = phase (t * bandPairTail b P y p q n) * phase (t * pairRemainder b y p q n) := by
  rw [pairRemainder_eq_band_add b P y p q n h, mul_add, phase_add]

end NormalNumbers.CastingOut
