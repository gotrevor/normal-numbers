import NormalNumbers.SwingC1Decouple

/-!
# Splitting the prime range inside leaf (D)

`PairDecouple b p q t` (`SwingC1Decouple.lean`) asks, for every prime cut `P` with
`Q = Π_{r ≤ P} r`, that the large-prime remainder `B(n) = e(t · pairRemainder b P p q n)`
have the same mean along every progression `c mod Q` as over all of `[0, QR)`.

This file splits the primes `> P` at a second cut `y`:

`pairRemainder b P = midPairTail b P y + pairRemainder b y`,
`B = B_mid · B_top`,  `B_mid` exactly `M`-periodic with `M = Π_{P < r ≤ y} r`.

Two consequences, both proved here:

* **The middle range is unconditional.**  `B_mid` is `M`-periodic and `gcd(M, Q) = 1`, so its
  progression means agree with its period mean to within `2M/R` — `midDefect_le`.  No sieve, no
  arithmetic input: exact CRT.  (The cost is that `M` must be `o(R)`, i.e. `y ≲ log N`.)
* **Hence the whole defect is carried by the top range**:
  `pairDefect b P p q t R ≤ midDefect + 2 · topMass y`, where `topMass` is the mean of
  `‖e(t · pairRemainder b y p q n) − 1‖` (`pairDefect_le`).

and two reductions of `PairDecouple` to a single named leaf, with no `P` left in it:

* `pairDecouple_of_topMass` — from `TopMassVanishing` (the top range contributes little mass);
* `pairDecouple_of_largeDecay` — from `LargeDecay` (the top range's phase *equidistributes*
  along each progression).

⚠️ Recorded: `TopMassVanishing` is heuristically FALSE.  For fixed `y`, `pairRemainder b y p q n`
has typical size `≍ (log log N − log log y)/b` — the divergent Mertens sum — so the mass does not
vanish; it is `→ 4/π`.  That divergence is not an obstruction but the *engine*: it is exactly why
`LargeDecay` should hold.  `LargeDecay` is therefore the honest successor crux.
-/

open Finset Filter Topology NormalNumbers.PrimeLambert

namespace NormalNumbers.CastingOut

/-! ### Means of a periodic function -/

lemma periodic_add_mul {M : Type*} (g : ℕ → M) (T : ℕ) (hper : ∀ n, g (n + T) = g n) :
    ∀ k n : ℕ, g (n + T * k) = g n := by
  intro k
  induction k with
  | zero => intro n; simp
  | succ k ih =>
      intro n
      rw [show T * (k + 1) = T * k + T by ring, ← Nat.add_assoc, hper, ih]

/-- A `T`-periodic sum over a whole number of periods. -/
lemma sum_range_mul_of_periodic {M : Type*} [AddCommMonoid M] (g : ℕ → M) (T : ℕ)
    (hper : ∀ n, g (n + T) = g n) (S : ℕ) :
    ∑ n ∈ range (T * S), g n = S • ∑ d ∈ range T, g d := by
  induction S with
  | zero => simp
  | succ S ih =>
      have hIco : ∑ n ∈ Finset.Ico (T * S) (T * S + T), g n = ∑ d ∈ range T, g d := by
        rw [Finset.sum_Ico_eq_sum_range]
        simp only [Nat.add_sub_cancel_left]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [show T * S + d = d + T * S by ring, periodic_add_mul g T hper]
      rw [show T * (S + 1) = T * S + T by ring, Finset.range_eq_Ico,
        ← Finset.sum_Ico_consecutive _ (Nat.zero_le (T * S)) (Nat.le_add_right (T * S) T),
        ← Finset.range_eq_Ico, ih, hIco, succ_nsmul]

private lemma mean_algebra (Sg tail : ℂ) (S T N : ℕ) (hN : ((N:ℂ)) ≠ 0) (hT : ((T:ℂ)) ≠ 0) :
    ((S : ℂ) * Sg + tail) / N - Sg / T
      = (((S : ℂ) * T - N) / ((N : ℂ) * T)) * Sg + tail / N := by
  field_simp; ring

/-- **The Cesàro mean of a periodic function is its period mean, to within `2T/N`.** -/
lemma norm_fullMean_sub_periodMean_le (g : ℕ → ℂ) (T N : ℕ) (hT : 0 < T) (hN : 0 < N)
    (hper : ∀ n, g (n + T) = g n) (hg : ∀ n, ‖g n‖ ≤ 1) :
    ‖fullMean g N - periodMean g T‖ ≤ 2 * T / N := by
  set S := N / T with hS
  set r := N % T with hr
  have hNsplit : T * S + r = N := Nat.div_add_mod N T
  have hrT : r < T := Nat.mod_lt _ hT
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hNc : ((N : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hTc : ((T : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hSgle : ‖∑ d ∈ range T, g d‖ ≤ (T : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ d ∈ range T, ‖g d‖ ≤ ∑ _d ∈ range T, (1 : ℝ) := Finset.sum_le_sum fun d _ => hg d
      _ = T := by simp
  have hsplit : ∑ n ∈ range N, g n
      = (S : ℂ) * (∑ d ∈ range T, g d) + ∑ i ∈ Finset.Ico (T * S) N, g i := by
    have hle : T * S ≤ N := by omega
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le (T * S)) hle,
      ← Finset.range_eq_Ico, sum_range_mul_of_periodic g T hper S, nsmul_eq_mul]
  have htail : ‖∑ i ∈ Finset.Ico (T * S) N, g i‖ ≤ (r : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i ∈ Finset.Ico (T * S) N, ‖g i‖
        ≤ ∑ _i ∈ Finset.Ico (T * S) N, (1 : ℝ) := Finset.sum_le_sum fun i _ => hg i
      _ = ((N - T * S : ℕ) : ℝ) := by simp
      _ = (r : ℝ) := by congr 1; omega
  have hid : fullMean g N - periodMean g T
      = (((S : ℂ) * T - N) / ((N : ℂ) * T)) * (∑ d ∈ range T, g d)
        + (∑ i ∈ Finset.Ico (T * S) N, g i) / N := by
    rw [fullMean, periodMean, hsplit]
    exact mean_algebra _ _ S T N hNc hTc
  have hcoef : ‖((S : ℂ) * T - N) / ((N : ℂ) * T)‖ = (r : ℝ) / ((N : ℝ) * T) := by
    have hc : ((S : ℂ) * T - N) = -(r : ℂ) := by
      have hh : (T : ℂ) * S + r = N := by exact_mod_cast congrArg (fun k : ℕ => (k : ℂ)) hNsplit
      linear_combination hh
    rw [hc, norm_div, norm_neg, Complex.norm_natCast, norm_mul, Complex.norm_natCast,
      Complex.norm_natCast]
  rw [hid]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, hcoef, norm_div, Complex.norm_natCast]
  have h1 : (r : ℝ) / ((N : ℝ) * T) * ‖∑ d ∈ range T, g d‖ ≤ (r : ℝ) / (N : ℝ) := by
    have hnn : (0:ℝ) ≤ (r:ℝ)/((N:ℝ)*T) := by positivity
    calc (r : ℝ) / ((N : ℝ) * T) * ‖∑ d ∈ range T, g d‖
        ≤ (r : ℝ) / ((N : ℝ) * T) * T := mul_le_mul_of_nonneg_left hSgle hnn
      _ = (r : ℝ) / N := by field_simp
  have h2 : ‖∑ i ∈ Finset.Ico (T * S) N, g i‖ / (N : ℝ) ≤ (r : ℝ) / N := by gcongr
  have h3 : (r : ℝ) ≤ (T : ℝ) := by exact_mod_cast hrT.le
  have h4 : (r : ℝ) / N + (r : ℝ) / N ≤ 2 * T / N := by
    have he : (r:ℝ)/N + (r:ℝ)/N = 2*r/N := by ring
    rw [he]; gcongr
  linarith

/-- A `T`-periodic function only sees the residue. -/
lemma periodic_mod {M : Type*} (g : ℕ → M) (T : ℕ) (hT : 0 < T) (hper : ∀ n, g (n + T) = g n)
    (n : ℕ) : g (n % T) = g n := by
  conv_rhs => rw [← Nat.mod_add_div n T]
  rw [periodic_add_mul g T hper]

/-- **CRT shift.**  For `T`-periodic `g` and `Q` coprime to `T`, one period of the progression
`c, c+Q, c+2Q, …` sees every residue exactly once. -/
lemma sum_range_shift_coprime (g : ℕ → ℂ) (T Q c : ℕ) (hT : 0 < T)
    (hcop : Nat.Coprime Q T) (hper : ∀ n, g (n + T) = g n) :
    ∑ i ∈ range T, g (c + i * Q) = ∑ d ∈ range T, g d := by
  classical
  set f : ℕ → ℕ := fun i => (c + i * Q) % T with hf
  have hmaps : ∀ i ∈ range T, f i ∈ range T := fun i _ =>
    Finset.mem_range.mpr (Nat.mod_lt _ hT)
  have hinj : ∀ x ∈ range T, ∀ y ∈ range T, f x = f y → x = y := by
    intro x hx y hy hxy
    rw [Finset.mem_range] at hx hy
    have h1 : (c + x * Q) ≡ (c + y * Q) [MOD T] := hxy
    have h2 : x * Q ≡ y * Q [MOD T] := (Nat.ModEq.add_left_cancel' c h1)
    have h3 : x ≡ y [MOD T] := Nat.ModEq.cancel_right_of_coprime hcop.symm.gcd_eq_one h2
    have := h3
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this
  have himg : (range T).image f = range T := by
    refine Finset.eq_of_subset_of_card_le (fun d hd => ?_) ?_
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd
      exact hmaps i hi
    · rw [Finset.card_image_of_injOn (fun x hx y hy h => hinj x hx y hy h)]
  calc ∑ i ∈ range T, g (c + i * Q)
      = ∑ i ∈ range T, g (f i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hf]; exact (periodic_mod g T hT hper _).symm
    _ = ∑ d ∈ (range T).image f, g d := (Finset.sum_image hinj).symm
    _ = ∑ d ∈ range T, g d := by rw [himg]

/-- **The progression mean of a periodic function, for a coprime modulus.** -/
lemma norm_progMean_sub_periodMean_le (g : ℕ → ℂ) (T Q R c : ℕ) (hT : 0 < T) (hR : 0 < R)
    (hcop : Nat.Coprime Q T) (hper : ∀ n, g (n + T) = g n) (hg : ∀ n, ‖g n‖ ≤ 1) :
    ‖progMean g Q R c - periodMean g T‖ ≤ 2 * T / R := by
  set h : ℕ → ℂ := fun i => g (c + i * Q) with hh
  have hhper : ∀ i, h (i + T) = h i := by
    intro i
    show g (c + (i + T) * Q) = g (c + i * Q)
    rw [show c + (i + T) * Q = (c + i * Q) + T * Q by ring, periodic_add_mul g T hper]
  have hhnorm : ∀ i, ‖h i‖ ≤ 1 := fun i => hg _
  have h1 : progMean g Q R c = fullMean h R := by rw [progMean, fullMean]
  have h2 : periodMean h T = periodMean g T := by
    rw [periodMean, periodMean, sum_range_shift_coprime g T Q c hT hcop hper]
  rw [h1, ← h2]
  exact norm_fullMean_sub_periodMean_le h T R hT hR hhper hhnorm

/-! ### The second cut -/

/-- The primes in `(P, y]`. -/
def primesIoc (P y : ℕ) : Finset ℕ := primesLe y \ primesLe P

lemma prime_of_mem_primesIoc {P y r : ℕ} (hr : r ∈ primesIoc P y) : r.Prime :=
  prime_of_mem_primesLe (Finset.mem_sdiff.mp hr).1

lemma primesIoc_disjoint (P y : ℕ) : Disjoint (primesLe P) (primesIoc P y) :=
  Finset.disjoint_sdiff

/-- The middle range's contribution to the pair difference. -/
noncomputable def midPairTail (b P y p q n : ℕ) : ℝ :=
  ∑ r ∈ primesIoc P y, (primePeriodicTerm b r (p * n) - primePeriodicTerm b r (q * n))

/-- `Π_{P < r ≤ y} r`. -/
def midModulus (P y : ℕ) : ℕ := ∏ r ∈ primesIoc P y, r

lemma midModulus_pos (P y : ℕ) : 0 < midModulus P y :=
  Finset.prod_pos fun r hr => (prime_of_mem_primesIoc hr).pos

lemma primesLe_subset {P y : ℕ} (h : P ≤ y) : primesLe P ⊆ primesLe y := by
  intro r hr
  rw [primesLe, Finset.mem_filter, Finset.mem_range] at hr ⊢
  exact ⟨by omega, hr.2⟩

/-- **The range split.**  `pairRemainder` at the low cut is the middle range plus the
`pairRemainder` at the high cut. -/
lemma pairRemainder_split (b P y p q n : ℕ) (hPy : P ≤ y) :
    pairRemainder b P p q n = midPairTail b P y p q n + pairRemainder b y p q n := by
  have hsum : midPairTail b P y p q n + truncPairTail b P p q n = truncPairTail b y p q n := by
    rw [truncPairTail, midPairTail, primesIoc, truncPairTail]
    exact Finset.sum_sdiff (primesLe_subset hPy)
  rw [pairRemainder, pairRemainder]
  linarith [hsum]

/-- The middle range is exactly `midModulus`-periodic. -/
lemma midPairTail_add_modulus (b P y p q n : ℕ) :
    midPairTail b P y p q (n + midModulus P y) = midPairTail b P y p q n := by
  refine Finset.sum_congr rfl fun r hr => ?_
  have hdvd : r ∣ midModulus P y := Finset.dvd_prod_of_mem (fun x => x) hr
  obtain ⟨d, hd⟩ := hdvd
  have hmod : ∀ k : ℕ, (k * (n + midModulus P y)) % r = (k * n) % r := by
    intro k
    rw [show k * (n + midModulus P y) = k * n + (k * d) * r by rw [hd]; ring,
      Nat.add_mul_mod_self_right]
  unfold primePeriodicTerm
  rw [hmod p, hmod q]

/-- `Q = Π_{r ≤ P} r` and `M = Π_{P < r ≤ y} r` are coprime. -/
lemma coprime_primorial_midModulus (P y : ℕ) : Nat.Coprime (primorialLe P) (midModulus P y) := by
  refine Nat.Coprime.prod_left (fun a ha => Nat.Coprime.prod_right fun c hc => ?_)
  have hac : a ≠ c := by
    intro h
    exact (Finset.disjoint_left.mp (primesIoc_disjoint P y) ha) (h ▸ hc)
  exact (Nat.coprime_primes (prime_of_mem_primesLe ha) (prime_of_mem_primesIoc hc)).mpr hac

/-! ### The two frozen leaves -/

/-- The decoupling defect of the MIDDLE range alone. -/
noncomputable def midDefect (b P y p q : ℕ) (t : ℝ) (R : ℕ) : ℝ :=
  (∑ c ∈ range (primorialLe P),
      ‖progMean (fun n => phase (t * midPairTail b P y p q n)) (primorialLe P) R c
        - fullMean (fun n => phase (t * midPairTail b P y p q n)) (primorialLe P * R)‖)
    / primorialLe P

/-- The phase mass of the TOP range: the mean of `‖e(t·pairRemainder_y) − 1‖`. -/
noncomputable def topMass (b y p q : ℕ) (t : ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ range N, ‖phase (t * pairRemainder b y p q n) - 1‖) / N

lemma topMass_nonneg (b y p q : ℕ) (t : ℝ) (N : ℕ) : 0 ≤ topMass b y p q t N := by
  rw [topMass]; positivity

/-- **The middle range is unconditional.**  Exact CRT: its defect is `O(M/R)`. -/
theorem midDefect_le (b P y p q : ℕ) (t : ℝ) (R : ℕ) (hR : 0 < R) :
    midDefect b P y p q t R ≤ 4 * midModulus P y / R := by
  classical
  set Q := primorialLe P with hQdef
  have hQ : 0 < Q := primorialLe_pos P
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  set M := midModulus P y with hMdef
  have hM : 0 < M := midModulus_pos P y
  have hRR : (0 : ℝ) < R := by exact_mod_cast hR
  set g : ℕ → ℂ := fun n => phase (t * midPairTail b P y p q n) with hg
  have hgper : ∀ n, g (n + M) = g n := by
    intro n
    show phase (t * midPairTail b P y p q (n + M)) = _
    rw [hMdef, midPairTail_add_modulus]
  have hgnorm : ∀ n, ‖g n‖ ≤ 1 := fun n => le_of_eq (norm_phase _)
  have hcop : Nat.Coprime Q M := coprime_primorial_midModulus P y
  have hterm : ∀ c ∈ range Q,
      ‖progMean g Q R c - fullMean g (Q * R)‖ ≤ 4 * M / R := by
    intro c _
    have h1 : ‖progMean g Q R c - periodMean g M‖ ≤ 2 * M / R :=
      norm_progMean_sub_periodMean_le g M Q R c hM hR hcop hgper hgnorm
    have h2 : ‖fullMean g (Q * R) - periodMean g M‖ ≤ 2 * (M:ℝ) / ((Q:ℝ) * R) := by
      have := norm_fullMean_sub_periodMean_le g M (Q * R) hM (Nat.mul_pos hQ hR) hgper hgnorm
      rwa [Nat.cast_mul] at this
    have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    have hMnn : (0:ℝ) ≤ 2 * (M:ℝ) := by positivity
    have hle : (R:ℝ) ≤ (Q:ℝ) * R := by nlinarith
    have h3 : (2 : ℝ) * M / ((Q:ℝ) * R) ≤ 2 * M / R :=
      div_le_div_of_nonneg_left hMnn hRR hle
    have htri : ‖progMean g Q R c - fullMean g (Q * R)‖
        ≤ ‖progMean g Q R c - periodMean g M‖ + ‖fullMean g (Q * R) - periodMean g M‖ := by
      have he : progMean g Q R c - fullMean g (Q * R)
          = (progMean g Q R c - periodMean g M) + -(fullMean g (Q * R) - periodMean g M) := by
        ring
      rw [he]
      exact (norm_add_le _ _).trans (by rw [norm_neg])
    have h4 : (4:ℝ) * M / R = 2 * M / R + 2 * M / R := by ring
    rw [h4]
    linarith
  have hsum : (∑ c ∈ range Q, ‖progMean g Q R c - fullMean g (Q * R)‖)
      ≤ (Q : ℝ) * (4 * M / R) := by
    calc (∑ c ∈ range Q, ‖progMean g Q R c - fullMean g (Q * R)‖)
        ≤ ∑ _c ∈ range Q, (4 * (M:ℝ) / R) := Finset.sum_le_sum hterm
      _ = (Q : ℝ) * (4 * M / R) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [midDefect, ← hQdef, ← hg, div_le_iff₀ hQR]
  linarith [hsum]

/-! ### The splitting inequality -/

private lemma norm_sum_mul_sub_div (u v : ℕ → ℂ) (s : Finset ℕ) (D : ℕ) (hD : 0 < D)
    (hu : ∀ n, ‖u n‖ ≤ 1) :
    ‖(∑ n ∈ s, u n * v n) / (D : ℂ) - (∑ n ∈ s, u n) / (D : ℂ)‖
      ≤ (∑ n ∈ s, ‖v n - 1‖) / (D : ℝ) := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  rw [div_sub_div_same, ← Finset.sum_sub_distrib, norm_div, Complex.norm_natCast]
  have hnum : ‖∑ n ∈ s, (u n * v n - u n)‖ ≤ ∑ n ∈ s, ‖v n - 1‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    rw [show u n * v n - u n = u n * (v n - 1) by ring, norm_mul]
    nlinarith [norm_nonneg (v n - 1), hu n, norm_nonneg (u n)]
  gcongr

/-- **The prime range splits the defect.**  At the low cut `P`, the decoupling defect is at most
the MIDDLE range's defect (which is `O(M/R)`, `midDefect_le`) plus twice the TOP range's phase
mass.  Both cuts are free; the tension between them is the content of leaf (D). -/
theorem pairDefect_le (b P y p q : ℕ) (t : ℝ) (R : ℕ) (hPy : P ≤ y) (hR : 0 < R) :
    pairDefect b P p q t R
      ≤ midDefect b P y p q t R + 2 * topMass b y p q t (primorialLe P * R) := by
  classical
  set Q := primorialLe P with hQdef
  have hQ : 0 < Q := primorialLe_pos P
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hRR : (0 : ℝ) < R := by exact_mod_cast hR
  have hQRpos : 0 < Q * R := Nat.mul_pos hQ hR
  have hQRR : (0 : ℝ) < ((Q * R : ℕ) : ℝ) := by exact_mod_cast hQRpos
  set Bm : ℕ → ℂ := fun n => phase (t * midPairTail b P y p q n) with hBm
  set Bt : ℕ → ℂ := fun n => phase (t * pairRemainder b y p q n) with hBt
  set B : ℕ → ℂ := fun n => phase (t * pairRemainder b P p q n) with hB
  set w : ℕ → ℝ := fun n => ‖Bt n - 1‖ with hw
  have hBmnorm : ∀ n, ‖Bm n‖ ≤ 1 := fun n => le_of_eq (norm_phase _)
  have hsplit : ∀ n, B n = Bm n * Bt n := by
    intro n
    show phase (t * pairRemainder b P p q n) = _
    rw [pairRemainder_split b P y p q n hPy, mul_add, phase_add]
  set T : ℝ := topMass b y p q t (Q * R) with hT
  have hTeq : T = (∑ n ∈ range (Q * R), w n) / ((Q * R : ℕ) : ℝ) := by rw [hT, topMass]
  -- progression comparison
  have hprog : ∀ c, ‖progMean B Q R c - progMean Bm Q R c‖
      ≤ (∑ i ∈ range R, w (c + i * Q)) / (R : ℝ) := by
    intro c
    have := norm_sum_mul_sub_div (fun i => Bm (c + i * Q)) (fun i => Bt (c + i * Q))
      (range R) R hR (fun i => hBmnorm _)
    rw [progMean, progMean]
    calc ‖(∑ i ∈ range R, B (c + i * Q)) / (R:ℂ) - (∑ i ∈ range R, Bm (c + i * Q)) / (R:ℂ)‖
        = ‖(∑ i ∈ range R, Bm (c + i * Q) * Bt (c + i * Q)) / (R:ℂ)
            - (∑ i ∈ range R, Bm (c + i * Q)) / (R:ℂ)‖ := by
          rw [Finset.sum_congr rfl (fun i _ => hsplit (c + i * Q))]
      _ ≤ _ := this
  -- full comparison
  have hfull : ‖fullMean B (Q * R) - fullMean Bm (Q * R)‖ ≤ T := by
    have := norm_sum_mul_sub_div Bm Bt (range (Q * R)) (Q * R) hQRpos hBmnorm
    rw [fullMean, fullMean, hTeq]
    calc ‖(∑ n ∈ range (Q*R), B n) / ((Q*R : ℕ):ℂ) - (∑ n ∈ range (Q*R), Bm n) / ((Q*R : ℕ):ℂ)‖
        = ‖(∑ n ∈ range (Q*R), Bm n * Bt n) / ((Q*R : ℕ):ℂ)
            - (∑ n ∈ range (Q*R), Bm n) / ((Q*R : ℕ):ℂ)‖ := by
          rw [Finset.sum_congr rfl (fun n _ => hsplit n)]
      _ ≤ _ := this
  -- termwise
  have hterm : ∀ c, ‖progMean B Q R c - fullMean B (Q * R)‖
      ≤ ‖progMean Bm Q R c - fullMean Bm (Q * R)‖
        + (∑ i ∈ range R, w (c + i * Q)) / (R : ℝ) + T := by
    intro c
    have he : progMean B Q R c - fullMean B (Q * R)
        = (progMean B Q R c - progMean Bm Q R c)
          + (progMean Bm Q R c - fullMean Bm (Q * R))
          + (fullMean Bm (Q * R) - fullMean B (Q * R)) := by ring
    have h3 : ‖fullMean Bm (Q * R) - fullMean B (Q * R)‖ ≤ T := by
      rw [show fullMean Bm (Q*R) - fullMean B (Q*R) = -(fullMean B (Q*R) - fullMean Bm (Q*R)) by
        ring, norm_neg]
      exact hfull
    rw [he]
    have := (norm_add_le ((progMean B Q R c - progMean Bm Q R c)
      + (progMean Bm Q R c - fullMean Bm (Q * R))) (fullMean Bm (Q * R) - fullMean B (Q * R)))
    have h12 := norm_add_le (progMean B Q R c - progMean Bm Q R c)
      (progMean Bm Q R c - fullMean Bm (Q * R))
    linarith [hprog c]
  -- average over c
  have havg : (∑ c ∈ range Q, (∑ i ∈ range R, w (c + i * Q)) / (R : ℝ)) = (Q : ℝ) * T := by
    rw [← Finset.sum_div, ← sum_range_mul_split w Q R, hTeq]
    push_cast
    field_simp
  have hsum : (∑ c ∈ range Q, ‖progMean B Q R c - fullMean B (Q * R)‖)
      ≤ (∑ c ∈ range Q, ‖progMean Bm Q R c - fullMean Bm (Q * R)‖) + (Q : ℝ) * T + (Q : ℝ) * T := by
    calc (∑ c ∈ range Q, ‖progMean B Q R c - fullMean B (Q * R)‖)
        ≤ ∑ c ∈ range Q, (‖progMean Bm Q R c - fullMean Bm (Q * R)‖
            + (∑ i ∈ range R, w (c + i * Q)) / (R : ℝ) + T) :=
          Finset.sum_le_sum fun c _ => hterm c
      _ = (∑ c ∈ range Q, ‖progMean Bm Q R c - fullMean Bm (Q * R)‖)
            + (∑ c ∈ range Q, (∑ i ∈ range R, w (c + i * Q)) / (R : ℝ))
            + (Q : ℝ) * T := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_range, nsmul_eq_mul]
      _ = _ := by rw [havg]
  rw [pairDefect, midDefect, ← hQdef, ← hB, ← hBm, div_add' _ _ _ (ne_of_gt hQR),
    div_le_div_iff_of_pos_right hQR]
  linarith [hsum]

/-! ### The middle range's own model: CRT factorisation and Mertens decay

The `midDefect` bound above is `O(M/R)` and so is useless once `y` grows with `R`.  The two
theorems here give the *other* handle on the middle range — the one that survives growing `y`:
its period mean factorises over the primes of `(P, y]`, and that product tends to `0` as
`y → ∞` with `P` FIXED.  This is what makes a progression-level attack on `LargeDecay`
quantitative: the model factor is `exp(−c·Σ_{P<r≤y} 1/r)`, and `Σ_{P<r≤y} 1/r → ∞`. -/

/-- **CRT factorisation of the middle range.** -/
theorem periodMean_phase_midPairTail (b P y p q : ℕ) (t : ℝ) :
    periodMean (fun n => phase (t * midPairTail b P y p q n)) (midModulus P y)
      = ∏ r ∈ primesIoc P y, pairLocalFactor b t r p q := by
  classical
  have hA : ∀ n : ℕ, phase (t * midPairTail b P y p q n)
      = ∏ r ∈ primesIoc P y,
          phase (t * (primePeriodicTerm b r (p * (n % r))
            - primePeriodicTerm b r (q * (n % r)))) := by
    intro n
    rw [midPairTail, Finset.mul_sum, phase_sum]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [primePeriodicTerm_mul_mod b r p n, primePeriodicTerm_mul_mod b r q n]
  have hcop : ((primesIoc P y : Finset ℕ) : Set ℕ).Pairwise Nat.Coprime := by
    intro x hx y' hy hne
    exact (Nat.coprime_primes (prime_of_mem_primesIoc hx) (prime_of_mem_primesIoc hy)).mpr hne
  have hpos : ∀ r ∈ primesIoc P y, 0 < r := fun r hr => (prime_of_mem_primesIoc hr).pos
  rw [periodMean, midModulus, Finset.sum_congr rfl (fun n _ => hA n),
    sum_range_prod_mod
      (fun r s => phase (t * (primePeriodicTerm b r (p * s) - primePeriodicTerm b r (q * s))))
      (primesIoc P y) hpos hcop,
    Nat.cast_prod, ← Finset.prod_div_distrib]
  rfl

/-- **Mertens over a half-infinite range.**  With the low cut `P` FIXED, the product of pair
local factors over `(P, y]` still tends to `0` as `y → ∞`: deleting finitely many primes does
not affect the divergence of `Σ 1/r`. -/
theorem prod_pairLocalFactor_Ioc_tendsto_zero (b : ℕ) (hb : 2 ≤ b) (t : ℝ) (ht : t ≠ 0)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (P : ℕ) :
    Tendsto (fun y => ‖∏ r ∈ primesIoc P y, pairLocalFactor b t r p q‖) atTop (𝓝 0) := by
  classical
  obtain ⟨c, hc, hev⟩ := norm_pairLocalFactor_le b hb t ht p q hp hq hpq
  set F : ℕ → ℂ := fun r => if P < r then pairLocalFactor b t r p q else 1 with hF
  have hF1 : ∀ r : ℕ, 0 < r → ‖F r‖ ≤ 1 := by
    intro r hr
    rw [hF]
    by_cases h : P < r
    · simp only [if_pos h]; exact norm_pairLocalFactor_le_one b t r p q hr
    · simp [h]
  have hFev : ∀ᶠ r : ℕ in atTop, r.Prime → ‖F r‖ ≤ 1 - c / r := by
    filter_upwards [hev, Filter.eventually_gt_atTop P] with r hr hrP hrp
    rw [hF]; simp only [if_pos hrP]; exact hr hrp
  have hmain := prod_tendsto_zero_of_norm_le F hF1 hc hFev
  refine (hmain.congr' ?_)
  filter_upwards [Filter.eventually_ge_atTop P] with y hy
  congr 1
  have hsub : primesLe P ⊆ primesLe y := primesLe_subset hy
  rw [← Finset.prod_sdiff hsub]
  have h1 : ∏ r ∈ primesLe y \ primesLe P, F r = ∏ r ∈ primesIoc P y, pairLocalFactor b t r p q := by
    rw [primesIoc]
    refine Finset.prod_congr rfl fun r hr => ?_
    have hrP : P < r := by
      rw [Finset.mem_sdiff, primesLe, Finset.mem_filter, Finset.mem_range] at hr
      by_contra hcon
      exact hr.2 (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hr.1.2⟩)
    rw [hF]; simp [hrP]
  have h2 : ∏ r ∈ primesLe P, F r = 1 := by
    refine Finset.prod_eq_one fun r hr => ?_
    have hrP : ¬ P < r := by
      rw [primesLe, Finset.mem_filter, Finset.mem_range] at hr
      omega
    rw [hF]; simp [hrP]
  rw [h1, h2, mul_one]

/-! ### The progression-level model bound — the attack on `LargeDecay`

Everything above is assembled here.  Along a FIXED progression `c mod Q` to the small-prime
modulus, split the primes `> P` at `y`: the middle range is again an exactly periodic factor
(period `M`, and `gcd(Q, M) = 1`, so the progression still sweeps every residue mod `M`), and
its period mean is the CRT product `Π_{P<r≤y} pairLocalFactor`, which tends to `0` as `y → ∞`
with `P` fixed.  Hence

`‖progMean B Q (M·S) c‖ ≤ ‖Π_{P<r≤y} pairLocalFactor‖ + topDefect_y(c, S)`,

with the first term `≤ exp(−c·Σ_{P<r≤y} 1/r) → 0`.  The whole of `LargeDecay` — and therefore
of `PairDecouple`, and therefore of the C1 swing — is now the single quantity `topDefect`. -/

/-- The top range, restricted to the progression `c mod Q`. -/
noncomputable def topProg (b P y p q : ℕ) (t : ℝ) (c : ℕ) : ℕ → ℂ :=
  fun i => phase (t * pairRemainder b y p q (c + i * primorialLe P))

/-- The level-2 decoupling defect: the top range against the MIDDLE-prime modulus `M`, inside
one progression to the small-prime modulus `Q`. -/
noncomputable def topDefect (b P y p q : ℕ) (t : ℝ) (c S : ℕ) : ℝ :=
  (∑ d ∈ range (midModulus P y),
      ‖progMean (topProg b P y p q t c) (midModulus P y) S d
        - fullMean (topProg b P y p q t c) (midModulus P y * S)‖) / midModulus P y

/-- **The progression-level model bound.**  The iterated split, one level up. -/
theorem norm_progMean_le_model_add_topDefect (b P y p q : ℕ) (t : ℝ) (c S : ℕ)
    (hPy : P ≤ y) (hS : 0 < S) :
    ‖progMean (fun n => phase (t * pairRemainder b P p q n)) (primorialLe P)
        (midModulus P y * S) c‖
      ≤ ‖∏ r ∈ primesIoc P y, pairLocalFactor b t r p q‖ + topDefect b P y p q t c S := by
  classical
  set Q := primorialLe P with hQdef
  have hQ : 0 < Q := primorialLe_pos P
  set M := midModulus P y with hMdef
  have hM : 0 < M := midModulus_pos P y
  set gm : ℕ → ℂ := fun n => phase (t * midPairTail b P y p q n) with hgm
  have hgmper : ∀ n, gm (n + M) = gm n := by
    intro n
    show phase (t * midPairTail b P y p q (n + M)) = _
    rw [hMdef, midPairTail_add_modulus]
  set A' : ℕ → ℂ := fun i => gm (c + i * Q) with hA'
  set Bt' : ℕ → ℂ := topProg b P y p q t c with hBt'
  have hA'per : ∀ d r : ℕ, A' (d + r * M) = A' d := by
    intro d r
    show gm (c + (d + r * M) * Q) = gm (c + d * Q)
    rw [show c + (d + r * M) * Q = (c + d * Q) + M * (r * Q) by ring,
      periodic_add_mul gm M hgmper]
  have hA'norm : ∀ i, ‖A' i‖ ≤ 1 := fun i => le_of_eq (norm_phase _)
  have hBt'norm : ∀ i, ‖Bt' i‖ ≤ 1 := fun i => le_of_eq (norm_phase _)
  have hmul : ∀ i : ℕ, phase (t * pairRemainder b P p q (c + i * Q)) = A' i * Bt' i := by
    intro i
    rw [pairRemainder_split b P y p q (c + i * Q) hPy, mul_add, phase_add]
    rfl
  have heq : progMean (fun n => phase (t * pairRemainder b P p q n)) Q (M * S) c
      = fullMean (fun i => A' i * Bt' i) (M * S) := by
    rw [progMean, fullMean]
    exact congrArg (fun z => z / ((M * S : ℕ) : ℂ)) (Finset.sum_congr rfl fun i _ => hmul i)
  rw [heq]
  refine (norm_fullMean_mul_le_periodMean_add_defect A' Bt' M S hM hS hA'per hA'norm
    hBt'norm).trans ?_
  have hmodel : periodMean A' M = ∏ r ∈ primesIoc P y, pairLocalFactor b t r p q := by
    rw [periodMean, hA']
    rw [sum_range_shift_coprime gm M Q c hM (coprime_primorial_midModulus P y) hgmper]
    rw [← periodMean, hMdef, hgm, periodMean_phase_midPairTail]
  rw [hmodel]
  have : (∑ d ∈ range M, ‖progMean Bt' M S d - fullMean Bt' (M * S)‖) / M
      = topDefect b P y p q t c S := by rw [topDefect, hBt', hMdef]
  rw [this]

/-! ### Into the second moment

**Probe 1 (iterating the split) is REFUTED as a closure route.**  The level-`k` bound has the
shape `‖mean‖ ≤ model_k + defect_k` and `defect_k ≤ 2·‖mean‖_{k+1}` (a defect is a mean of
differences of means, and the triangle inequality costs a factor `2`).  Unrolling gives
`N_P ≤ Σ_{j<k} 2^j·model_j + 2^k·N_{y_k}`.  The models are free — `Σ_{y_j<r≤y_{j+1}} 1/r` may be
made as large as one likes, so `2^j·model_j` is summable — but the residual `2^k·N_{y_k}` is only
bounded by `2^k`, and nothing in the iteration makes `N` small.  The iteration converts a mean
into a mean of sub-means and never gains absolute smallness.  The factor `2` is exactly the
triangle inequality, so the fix is to leave the `L¹` world.

That is what this section sets up: `topDefect` is dominated by the square root of a **variance**,
where the loss disappears and the large sieve / Turán machinery applies. -/

private lemma mean_le_sqrt_mean_sq (a : ℕ → ℝ) (M : ℕ) (hM : 0 < M) (ha : ∀ d, 0 ≤ a d) :
    (∑ d ∈ range M, a d) / M ≤ Real.sqrt ((∑ d ∈ range M, (a d) ^ 2) / M) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hnn : 0 ≤ (∑ d ∈ range M, a d) / M := by
    have : 0 ≤ ∑ d ∈ range M, a d := Finset.sum_nonneg fun d _ => ha d
    positivity
  have h := sq_sum_le_card_mul_sum_sq (s := range M) (f := a)
  rw [Finset.card_range] at h
  have key : ((∑ d ∈ range M, a d) / M) ^ 2 ≤ (∑ d ∈ range M, (a d) ^ 2) / M := by
    rw [div_pow, div_le_div_iff₀ (by positivity) hMR]
    nlinarith [h]
  calc (∑ d ∈ range M, a d) / M
      = Real.sqrt (((∑ d ∈ range M, a d) / M) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ _ := Real.sqrt_le_sqrt key

/-- The `L²` form of the level-2 defect: the VARIANCE of the top range's progression means
around their common mean. -/
noncomputable def topDefectL2 (b P y p q : ℕ) (t : ℝ) (c S : ℕ) : ℝ :=
  (∑ d ∈ range (midModulus P y),
      ‖progMean (topProg b P y p q t c) (midModulus P y) S d
        - fullMean (topProg b P y p q t c) (midModulus P y * S)‖ ^ 2) / midModulus P y

lemma topDefectL2_nonneg (b P y p q : ℕ) (t : ℝ) (c S : ℕ) :
    0 ≤ topDefectL2 b P y p q t c S := by rw [topDefectL2]; positivity

/-- **Cauchy–Schwarz: the defect is at most the root of the variance.** -/
theorem topDefect_le_sqrt_topDefectL2 (b P y p q : ℕ) (t : ℝ) (c S : ℕ) :
    topDefect b P y p q t c S ≤ Real.sqrt (topDefectL2 b P y p q t c S) := by
  rw [topDefect, topDefectL2]
  exact mean_le_sqrt_mean_sq _ (midModulus P y) (midModulus_pos P y) (fun d => norm_nonneg _)

/-! ### Two reductions of leaf (D), with the cut `P` eliminated -/

/-- **Leaf (T), the mass form.**  At arbitrarily large cuts `y`, the top range's phase
displacement has small mean.  ⚠️ Heuristically FALSE: for fixed `y` the remainder has typical
size `≍ (log log N − log log y)/b`, so this mass tends to `4/π`, not to `0`.  Recorded because
it is the exact content of the prime-range split, and its failure is the Mertens divergence. -/
def TopMassVanishing (b p q : ℕ) (t : ℝ) : Prop :=
  ∀ ε > 0, ∀ Y : ℕ, ∃ y ≥ Y, ∀ᶠ N in atTop, topMass b y p q t N < ε

/-- **Leaf (L), the decay form.**  The large-prime remainder's phase equidistributes along
*each* progression to the small-prime modulus.  Strictly stronger than `PairDecouple` (which
asks only that the progressions agree with each other), but it is the statement the CRT/Mertens
heuristic actually predicts — the divergence of `Σ_{r > P} 1/r` is its engine. -/
def LargeDecay (b p q : ℕ) (t : ℝ) : Prop :=
  ∀ P c : ℕ, Tendsto (fun R => progMean (fun n => phase (t * pairRemainder b P p q n))
    (primorialLe P) R c) atTop (𝓝 0)

lemma pairDefect_nonneg (b P p q : ℕ) (t : ℝ) (R : ℕ) : 0 ≤ pairDefect b P p q t R := by
  rw [pairDefect]; positivity

theorem pairDecouple_of_topMass (b p q : ℕ) (t : ℝ) (h : TopMassVanishing b p q t) :
    PairDecouple b p q t := by
  intro P
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨y, hyP, hy⟩ := h (ε / 4) (by linarith) P
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hy
  set Q := primorialLe P with hQdef
  have hQ : 0 < Q := primorialLe_pos P
  set M := midModulus P y with hMdef
  obtain ⟨R₁, hR₁⟩ := exists_nat_gt (8 * (M : ℝ) / ε)
  refine Filter.eventually_atTop.mpr ⟨max (max 1 (R₁ + 1)) N₀, fun R hR => ?_⟩
  have hR1 : 1 ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
  have hRpos : 0 < R := hR1
  have hRR : (0 : ℝ) < R := by exact_mod_cast hRpos
  have hRN₀ : N₀ ≤ R := le_trans (le_max_right _ _) hR
  have hRR₁ : (R₁ : ℝ) < (R : ℝ) := by
    have : R₁ < R := by
      have := le_trans (le_max_right 1 (R₁ + 1)) (le_trans (le_max_left _ _) hR)
      omega
    exact_mod_cast this
  have hmid : midDefect b P y p q t R < ε / 2 := by
    have h1 := midDefect_le b P y p q t R hRpos
    have h2 : 4 * (M : ℝ) / R < ε / 2 := by
      rw [div_lt_iff₀ hRR]
      have : 8 * (M : ℝ) / ε < R := lt_trans hR₁ hRR₁
      rw [div_lt_iff₀ hε] at this
      linarith
    linarith
  have htop : topMass b y p q t (Q * R) < ε / 4 := by
    refine hN₀ (Q * R) ?_
    calc N₀ ≤ R := hRN₀
      _ ≤ Q * R := Nat.le_mul_of_pos_left R hQ
  have hle := pairDefect_le b P y p q t R hyP hRpos
  rw [← hQdef] at hle
  have hnn := pairDefect_nonneg b P p q t R
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  linarith

theorem pairDecouple_of_largeDecay (b p q : ℕ) (t : ℝ) (h : LargeDecay b p q t) :
    PairDecouple b p q t := by
  intro P
  set Q := primorialLe P with hQdef
  have hQ : 0 < Q := primorialLe_pos P
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  set B : ℕ → ℂ := fun n => phase (t * pairRemainder b P p q n) with hB
  have hsum : Tendsto (fun R => (∑ c ∈ range Q, progMean B Q R c) / (Q : ℂ)) atTop (𝓝 0) := by
    have hs : Tendsto (fun R => ∑ c ∈ range Q, progMean B Q R c) atTop (𝓝 0) := by
      have := tendsto_finsetSum (range Q) (fun c (_ : c ∈ range Q) => h P c)
      simpa using this
    simpa using hs.div_const ((Q : ℂ))
  have hfull : Tendsto (fun R => fullMean B (Q * R)) atTop (𝓝 0) := by
    refine hsum.congr' ?_
    refine Filter.eventually_atTop.mpr ⟨1, fun R hR => ?_⟩
    show (∑ c ∈ range Q, progMean B Q R c) / (Q:ℂ) = fullMean B (Q * R)
    rw [fullMean_eq_periodMean_progMean B Q R hQ hR, periodMean]
  have hterm : ∀ c ∈ range Q,
      Tendsto (fun R => ‖progMean B Q R c - fullMean B (Q * R)‖) atTop (𝓝 0) := by
    intro c _
    have := ((h P c).sub hfull).norm
    simpa using this
  have : Tendsto (fun R => (∑ c ∈ range Q, ‖progMean B Q R c - fullMean B (Q * R)‖) / (Q : ℝ))
      atTop (𝓝 0) := by
    have hs := tendsto_finsetSum (range Q) hterm
    simp only [Finset.sum_const_zero] at hs
    simpa using hs.div_const ((Q : ℝ))
  simpa [pairDefect, hB, hQdef] using this

/-- **`LargeDecay` is exactly the vanishing of `topDefect`.**  If, for every low cut `P` and
every progression `c`, the level-2 defect can be made small at arbitrarily large middle cuts `y`,
then the large-prime phase decays along every progression — hence `PairDecouple` by
`pairDecouple_of_largeDecay`, hence the C1 swing.

This is the sharpest available restatement of the crux: no small primes remain in the integrand,
the model factor is explicit and quantitative (`exp(−c·Σ_{P<r≤y} 1/r)`), and `topDefect` is a
mean over one middle-prime period of the deviation of the TOP range's progression means. -/
theorem largeDecay_of_topDefect (b p q : ℕ) (t : ℝ) (hb : 2 ≤ b) (ht : t ≠ 0)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (h : ∀ P c : ℕ, ∀ ε > 0, ∀ Y : ℕ, ∃ y ≥ Y, ∀ᶠ S in atTop, topDefect b P y p q t c S < ε) :
    LargeDecay b p q t := by
  intro P c
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  set Q := primorialLe P with hQdef
  set f : ℕ → ℂ := fun i => phase (t * pairRemainder b P p q (c + i * Q)) with hf
  have hfnorm : ∀ i, ‖f i‖ ≤ 1 := fun i => le_of_eq (norm_phase _)
  have hprogf : ∀ R, progMean (fun n => phase (t * pairRemainder b P p q n)) Q R c
      = fullMean f R := fun R => rfl
  -- the model factor at all large middle cuts
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.mp
    ((NormedAddGroup.tendsto_nhds_zero.mp
      (prod_pairLocalFactor_Ioc_tendsto_zero b hb t ht p q hp hq hpq P)) (ε / 4) (by linarith))
  obtain ⟨y, hyY, hy⟩ := h P c (ε / 4) (by linarith) (max P Y₀)
  have hyP : P ≤ y := le_trans (le_max_left _ _) hyY
  have hmodel : ‖∏ r ∈ primesIoc P y, pairLocalFactor b t r p q‖ < ε / 4 := by
    have h0 := hY₀ y (le_trans (le_max_right _ _) hyY)
    rw [Real.norm_eq_abs] at h0
    exact lt_of_abs_lt h0
  obtain ⟨S₀, hS₀⟩ := Filter.eventually_atTop.mp hy
  set M := midModulus P y with hMdef
  have hM : 0 < M := midModulus_pos P y
  obtain ⟨R₁, hR₁⟩ := exists_nat_gt (4 * (M : ℝ) / ε)
  refine Filter.eventually_atTop.mpr ⟨max (M * (S₀ + 1) + M) (R₁ + 1), fun R hR => ?_⟩
  have hRpos : 0 < R := by
    have := le_trans (le_max_left _ _) hR
    have : 0 < M * (S₀ + 1) + M := by positivity
    omega
  have hRR : (0 : ℝ) < R := by exact_mod_cast hRpos
  set S := R / M with hSdef
  have hSge : S₀ ≤ S := by
    have hb1 : M * (S₀ + 1) + M ≤ R := le_trans (le_max_left _ _) hR
    have hb3 : (M * (S₀ + 1)) / M ≤ R / M := Nat.div_le_div_right (by omega)
    rw [Nat.mul_div_cancel_left _ hM] at hb3
    omega
  have hSpos : 0 < S := by
    have hb1 : M * (S₀ + 1) + M ≤ R := le_trans (le_max_left _ _) hR
    have hb3 : (M * (S₀ + 1)) / M ≤ R / M := Nat.div_le_div_right (by omega)
    rw [Nat.mul_div_cancel_left _ hM] at hb3
    omega
  have htail : (M : ℝ) / R < ε / 4 := by
    have hR1 : (R₁ : ℝ) < (R : ℝ) := by
      have := le_trans (le_max_right _ _) hR
      exact_mod_cast (by omega : R₁ < R)
    have hlt : 4 * (M : ℝ) / ε < (R : ℝ) := lt_trans hR₁ hR1
    rw [div_lt_iff₀ hRR]
    rw [div_lt_iff₀ hε] at hlt
    linarith
  have hsplit := norm_fullMean_le_of_mul f hfnorm M R hM hRpos
  have hcore : ‖fullMean f (M * S)‖ < ε / 2 := by
    have h1 := norm_progMean_le_model_add_topDefect b P y p q t c S hyP hSpos
    rw [hprogf (M * S)] at h1
    have h2 : topDefect b P y p q t c S < ε / 4 := hS₀ S hSge
    linarith
  rw [hprogf R]
  rw [← hSdef] at hsplit
  linarith

/-- **Bias–variance.**  The variance of a family about its own mean is the mean of the squares
minus the square of the mean.  This is the form the large sieve attacks: `topDefectL2` is
`mean_d ‖progMean_d‖² − ‖fullMean‖²`, so the whole crux becomes an upper bound for the mean
square of the top range's progression means. -/
theorem sum_norm_sub_mean_sq (z : ℕ → ℂ) (M : ℕ) (hM : 0 < M) :
    (∑ d ∈ range M, ‖z d - (∑ e ∈ range M, z e) / (M : ℂ)‖ ^ 2) / M
      = (∑ d ∈ range M, ‖z d‖ ^ 2) / M - ‖(∑ e ∈ range M, z e) / (M : ℂ)‖ ^ 2 := by
  have hMc : ((M : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  set m : ℂ := (∑ e ∈ range M, z e) / (M : ℂ) with hm
  have hsum : ∑ e ∈ range M, z e = (M : ℂ) * m := by rw [hm]; field_simp
  have hexp : ∑ d ∈ range M, ‖z d - m‖ ^ 2
      = (∑ d ∈ range M, ‖z d‖ ^ 2) + (M : ℝ) * ‖m‖ ^ 2
        - 2 * (((∑ d ∈ range M, z d) * (starRingEnd ℂ) m).re) := by
    have hstep : ∀ d ∈ range M, ‖z d - m‖ ^ 2
        = ‖z d‖ ^ 2 + ‖m‖ ^ 2 - 2 * ((z d * (starRingEnd ℂ) m).re) := by
      intro d _
      rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub]
    rw [Finset.sum_congr rfl hstep]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, ← Finset.mul_sum, ← Complex.re_sum, ← Finset.sum_mul]
  have hre : (((∑ d ∈ range M, z d) * (starRingEnd ℂ) m).re) = (M : ℝ) * ‖m‖ ^ 2 := by
    rw [hsum, mul_assoc, Complex.mul_conj, Complex.sq_norm]
    simp
  rw [hexp, hre]
  field_simp
  ring

/-- **The crux as a mean square.**  `topDefectL2` is the mean square of the top range's
progression means minus the square of their mean.  Since the second term is `≥ 0`, it suffices
to bound `mean_d ‖progMean_d‖²` — a pair-correlation sum over the top range. -/
theorem topDefectL2_eq (b P y p q : ℕ) (t : ℝ) (c S : ℕ) (hS : 0 < S) :
    topDefectL2 b P y p q t c S
      = (∑ d ∈ range (midModulus P y),
          ‖progMean (topProg b P y p q t c) (midModulus P y) S d‖ ^ 2) / midModulus P y
        - ‖fullMean (topProg b P y p q t c) (midModulus P y * S)‖ ^ 2 := by
  set M := midModulus P y with hMdef
  have hM : 0 < M := midModulus_pos P y
  set Z : ℕ → ℂ := fun d => progMean (topProg b P y p q t c) M S d with hZ
  have hfull : fullMean (topProg b P y p q t c) (M * S) = (∑ e ∈ range M, Z e) / (M : ℂ) := by
    rw [fullMean_eq_periodMean_progMean _ M S hM hS, periodMean]
  rw [topDefectL2, ← hMdef, hfull]
  exact sum_norm_sub_mean_sq Z M hM

/-! ### Diagonal + off-diagonal: the crux as a shifted correlation

Expanding the mean square of the progression means, the diagonal contributes exactly `1/S` and
everything else is a sum of **correlations at a shift**,
`C(s,s') = Σ_{d<M} W(d+sM)·conj W(d+s'M)`.  This is the classical shape: the crux has become a
bilinear/correlation statement about the large-prime phase, which is the regime where Kátai's
criterion and Bourgain–Sarnak–Ziegler operate — and there is no triangle-inequality loss. -/

private lemma norm_sq_re (u : ℂ) : ‖u‖ ^ 2 = (u * (starRingEnd ℂ) u).re := by
  rw [Complex.sq_norm, Complex.mul_conj]; simp

/-- The off-diagonal correlation sum of `W` at scale `M` over `S` blocks. -/
noncomputable def offDiagCorr (W : ℕ → ℂ) (M S : ℕ) : ℝ :=
  ∑ s ∈ range S, ∑ s' ∈ range S,
    if s = s' then 0
    else ‖∑ d ∈ range M, W (d + s * M) * (starRingEnd ℂ) (W (d + s' * M))‖

lemma offDiagCorr_nonneg (W : ℕ → ℂ) (M S : ℕ) : 0 ≤ offDiagCorr W M S := by
  rw [offDiagCorr]
  refine Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun s' _ => ?_
  by_cases h : s = s' <;> simp [h]

/-- **Diagonal + off-diagonal.**  The mean square of the progression means is `1/S` plus the
normalised off-diagonal correlation. -/
theorem meanSq_progMean_le (W : ℕ → ℂ) (M S : ℕ) (hM : 0 < M) (hS : 0 < S)
    (hW : ∀ n, ‖W n‖ ≤ 1) :
    (∑ d ∈ range M, ‖progMean W M S d‖ ^ 2) / M
      ≤ 1 / S + offDiagCorr W M S / ((M : ℝ) * S ^ 2) := by
  classical
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hSR : (0 : ℝ) < S := by exact_mod_cast hS
  set U : ℕ → ℂ := fun d => ∑ s ∈ range S, W (d + s * M) with hU
  set C : ℕ → ℕ → ℂ := fun s s' => ∑ d ∈ range M,
    W (d + s * M) * (starRingEnd ℂ) (W (d + s' * M)) with hC
  have hexp : ∀ d, ‖U d‖ ^ 2
      = ∑ s ∈ range S, ∑ s' ∈ range S, (W (d + s * M) * (starRingEnd ℂ) (W (d + s' * M))).re := by
    intro d
    rw [norm_sq_re, hU]
    simp only [map_sum]
    rw [Finset.sum_mul_sum, Complex.re_sum]
    exact Finset.sum_congr rfl fun s _ => Complex.re_sum _ _
  have hsum : ∑ d ∈ range M, ‖U d‖ ^ 2
      = ∑ s ∈ range S, ∑ s' ∈ range S, (C s s').re := by
    rw [Finset.sum_congr rfl (fun d _ => hexp d)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s' _ => ?_
    rw [hC, Complex.re_sum]
  have hCnorm : ∀ s s', ‖C s s'‖ ≤ (M : ℝ) := by
    intro s s'
    rw [hC]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ d ∈ range M, ‖W (d + s * M) * (starRingEnd ℂ) (W (d + s' * M))‖
        ≤ ∑ _d ∈ range M, (1 : ℝ) := by
          refine Finset.sum_le_sum fun d _ => ?_
          rw [norm_mul, RCLike.norm_conj]
          nlinarith [hW (d + s * M), hW (d + s' * M), norm_nonneg (W (d + s * M)),
            norm_nonneg (W (d + s' * M))]
      _ = M := by simp
  have hbound : ∀ s ∈ range S, ∀ s' ∈ range S,
      (C s s').re ≤ (if s = s' then (M : ℝ) else 0)
        + (if s = s' then 0 else ‖C s s'‖) := by
    intro s _ s' _
    by_cases h : s = s'
    · simp only [if_pos h, add_zero]
      exact le_trans (Complex.re_le_norm _) (hCnorm s s')
    · simp only [if_neg h, zero_add]
      exact Complex.re_le_norm _
  have hfin : ∑ s ∈ range S, ∑ s' ∈ range S, (C s s').re ≤ (S : ℝ) * M + offDiagCorr W M S := by
    calc ∑ s ∈ range S, ∑ s' ∈ range S, (C s s').re
        ≤ ∑ s ∈ range S, ∑ s' ∈ range S,
            ((if s = s' then (M : ℝ) else 0) + (if s = s' then 0 else ‖C s s'‖)) :=
          Finset.sum_le_sum fun s hs => Finset.sum_le_sum fun s' hs' => hbound s hs s' hs'
      _ = (S : ℝ) * M + offDiagCorr W M S := by
          rw [offDiagCorr]
          simp only [Finset.sum_add_distrib]
          have hd : ∑ x ∈ range S, ∑ x' ∈ range S, (if x = x' then (M : ℝ) else 0)
              = (S : ℝ) * M := by
            rw [Finset.sum_congr rfl
              (fun s _ => Finset.sum_ite_eq (range S) s (fun _ => (M : ℝ)))]
            rw [Finset.sum_congr rfl (fun x hx => if_pos hx)]
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          rw [hd, hC]
  have hmain : ∑ d ∈ range M, ‖progMean W M S d‖ ^ 2
      = (∑ d ∈ range M, ‖U d‖ ^ 2) / (S : ℝ) ^ 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [progMean, norm_div, Complex.norm_natCast, div_pow]
  rw [hmain, div_div]
  rw [div_le_iff₀ (by positivity)]
  have h1 : (1 / (S:ℝ) + offDiagCorr W M S / ((M : ℝ) * S ^ 2)) * ((S:ℝ) ^ 2 * M)
      = (S : ℝ) * M + offDiagCorr W M S := by field_simp
  rw [h1, hsum]
  exact hfin

/-- **The crux as a correlation bound.**  Combining `topDefectL2_eq` with the diagonal split. -/
theorem topDefectL2_le (b P y p q : ℕ) (t : ℝ) (c S : ℕ) (hS : 0 < S) :
    topDefectL2 b P y p q t c S
      ≤ 1 / S + offDiagCorr (topProg b P y p q t c) (midModulus P y) S
          / ((midModulus P y : ℝ) * S ^ 2) := by
  have hM : 0 < midModulus P y := midModulus_pos P y
  have h1 := topDefectL2_eq b P y p q t c S hS
  have h2 := meanSq_progMean_le (topProg b P y p q t c) (midModulus P y) S hM hS
    (fun n => le_of_eq (norm_phase _))
  have h3 : (0:ℝ) ≤ ‖fullMean (topProg b P y p q t c) (midModulus P y * S)‖ ^ 2 := by positivity
  rw [h1]
  linarith

/-- **LEAF (C): the off-diagonal correlation.**  At arbitrarily large middle cuts `y`, the
large-prime phase along a progression has small correlation with its own shifts by multiples of
`M = Π_{P<r≤y} r`.

This is the final named form of the C1 swing's only open input.  It is a genuinely bilinear
statement — no triangle-inequality loss, and `M` is a free parameter which may be taken far
below the sample size `M·S`.  Both features were unavailable at every earlier stage. -/
def TopCorrSmall (b p q : ℕ) (t : ℝ) : Prop :=
  ∀ P c : ℕ, ∀ ε > 0, ∀ Y : ℕ, ∃ y ≥ Y, ∀ᶠ S in atTop,
    offDiagCorr (topProg b P y p q t c) (midModulus P y) S
      < ε * (midModulus P y : ℝ) * S ^ 2

/-- **`LargeDecay` from the variance.**  The `L²` entry point: it suffices that the top range's
progression means have small variance about their mean. -/
theorem largeDecay_of_topDefectL2 (b p q : ℕ) (t : ℝ) (hb : 2 ≤ b) (ht : t ≠ 0)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (h : ∀ P c : ℕ, ∀ ε > 0, ∀ Y : ℕ, ∃ y ≥ Y, ∀ᶠ S in atTop, topDefectL2 b P y p q t c S < ε) :
    LargeDecay b p q t := by
  refine largeDecay_of_topDefect b p q t hb ht hp hq hpq (fun P c ε hε Y => ?_)
  obtain ⟨y, hyY, hy⟩ := h P c (ε ^ 2) (by positivity) Y
  refine ⟨y, hyY, ?_⟩
  filter_upwards [hy] with S hS
  have h1 := topDefect_le_sqrt_topDefectL2 b P y p q t c S
  have h2 : Real.sqrt (topDefectL2 b P y p q t c S) < Real.sqrt (ε ^ 2) :=
    Real.sqrt_lt_sqrt (topDefectL2_nonneg _ _ _ _ _ _ _ _) hS
  rw [Real.sqrt_sq hε.le] at h2
  linarith

theorem largeDecay_of_topCorr (b p q : ℕ) (t : ℝ) (hb : 2 ≤ b) (ht : t ≠ 0)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (h : TopCorrSmall b p q t) :
    LargeDecay b p q t := by
  refine largeDecay_of_topDefectL2 b p q t hb ht hp hq hpq (fun P c ε hε Y => ?_)
  obtain ⟨y, hyY, hy⟩ := h P c (ε / 2) (by linarith) Y
  refine ⟨y, hyY, ?_⟩
  have hM : 0 < midModulus P y := midModulus_pos P y
  have hMR : (0:ℝ) < midModulus P y := by exact_mod_cast hM
  obtain ⟨S₁, hS₁⟩ := exists_nat_gt (2 / ε)
  filter_upwards [hy, Filter.eventually_gt_atTop S₁, Filter.eventually_gt_atTop 0]
    with S hS hS1 hSpos
  have hSR : (0:ℝ) < S := by exact_mod_cast hSpos
  have hdiag : 1 / (S:ℝ) < ε / 2 := by
    have : (2:ℝ) / ε < (S:ℝ) := lt_trans hS₁ (by exact_mod_cast hS1)
    rw [div_lt_iff₀ hSR]
    rw [div_lt_iff₀ hε] at this
    linarith
  have hoff : offDiagCorr (topProg b P y p q t c) (midModulus P y) S
      / ((midModulus P y : ℝ) * S ^ 2) < ε / 2 := by
    rw [div_lt_iff₀ (by positivity)]
    calc offDiagCorr (topProg b P y p q t c) (midModulus P y) S
        < ε / 2 * (midModulus P y : ℝ) * S ^ 2 := hS
      _ = ε / 2 * ((midModulus P y : ℝ) * S ^ 2) := by ring
  have := topDefectL2_le b P y p q t c S hSpos
  linarith

end NormalNumbers.CastingOut
