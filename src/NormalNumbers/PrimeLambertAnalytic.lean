import NormalNumbers.PrimeLambertOscillation

/-!
# The analytic chain behind `PhaseOscillation`, as separate exact obligations

Draft §5 proves `PhaseOscillation` by splitting the signed tail `F_N(n) = phaseSum c K n` as

  `F = (F − F_J) + ∑_{p bad} X_p + ∑_{p small} X_p + ∑_{p large} X_p`,

where `F_J = truncPhase c K J n` is the finite tail `K < j ≤ J`, and for a prime `p`

  `X_p(n) = primePart c K J p n = ∑_a c(a) ∑_{K<j≤J} 2^{-j} 1[p ∣ n + j d_a − s_a]`.

The identity `F_J = ∑_p X_p` over any finite set of primes covering all prime factors of the
arguments is exact (`truncPhase_eq_sum_primePart`).  The four analytic obligations are stated as
separate `def … : Prop` with explicit quantifiers:

* `TailTruncation` — `sup_{n∈P_N} |F − F_J| → 0` (draft (20));
* `LargePrimeNegligible` — `sup_{n∈P_N} |∑_{p large} X_p| → 0` (draft (19));
* `BadPrimeFrozen` — `∑_{p bad} X_p` is constant on `P_N` (draft §5.2; exact, no bound needed);
* `SmallPrimeDecay q` — `‖𝔼_{n∈P_N} e(q ∑_{p small} X_p(n))‖ → 0` (draft §5.3–5.4, the sieve
  characteristic-function estimate).

`phaseOscillation_of_chain` is the **proved** wiring: these four, for configurations cancelling
at `1..K_N`, imply `PhaseOscillation`.  None of the four is proved here; `SmallPrimeDecay` is the
deep step (independent model + CRT moments + even-moment transfer).
-/

open Filter Topology Finset
open scoped BigOperators

namespace NormalNumbers.PrimeLambert

/-- The finite tail `∑_a c(a) ∑_{K<j≤J} 2^{-j} ω(n + j d − s)` (index `j = i+1`, `i ∈ [K, J)`). -/
noncomputable def truncPhase (c : TConfig) (K J : ℕ) (n : ℤ) : ℝ :=
  c.sum fun a w => (w : ℝ) * ∑ i ∈ Ico K J, omegaZ (n + ((i : ℤ) + 1) * a.1 - a.2) / 2 ^ (i + 1)

/-- The contribution of one prime `p` to the finite tail. -/
noncomputable def primePart (c : TConfig) (K J : ℕ) (p : ℕ) (n : ℤ) : ℝ :=
  c.sum fun a w => (w : ℝ) * ∑ i ∈ Ico K J,
    (if (p : ℤ) ∣ n + ((i : ℤ) + 1) * a.1 - a.2 then 1 / 2 ^ (i + 1) else 0)

/-- `ω(m) = ∑_{p ∈ Ps} 1[p ∣ m]` for any finite set of primes `Ps ⊇ primeFactors m`, `m ≠ 0`. -/
lemma omegaR_eq_sum_indicator (Ps : Finset ℕ) (hP : ∀ p ∈ Ps, p.Prime) (m : ℕ) (hm : m ≠ 0)
    (hcov : m.primeFactors ⊆ Ps) :
    omegaR m = ∑ p ∈ Ps, (if p ∣ m then (1 : ℝ) else 0) := by
  rw [omegaR_eq, Finset.sum_boole]
  congr 2
  ext p
  simp only [Nat.mem_primeFactors, Finset.mem_filter]
  constructor
  · rintro ⟨hp, hd, _⟩; exact ⟨hcov (Nat.mem_primeFactors.mpr ⟨hp, hd, hm⟩), hd⟩
  · rintro ⟨hp, hd⟩; exact ⟨hP p hp, hd, hm⟩

lemma omegaZ_eq_sum_indicator (Ps : Finset ℕ) (hP : ∀ p ∈ Ps, p.Prime) (m : ℤ) (hm : m ≠ 0)
    (hcov : m.natAbs.primeFactors ⊆ Ps) :
    omegaZ m = ∑ p ∈ Ps, (if (p : ℤ) ∣ m then (1 : ℝ) else 0) := by
  unfold omegaZ
  rw [omegaR_eq_sum_indicator Ps hP m.natAbs (Int.natAbs_ne_zero.mpr hm) hcov]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  simp only [Int.natCast_dvd]

/-- Per-atom form of the additive decomposition. -/
lemma tail_atom_eq_sum (K J : ℕ) (arg : ℕ → ℤ) (Ps : Finset ℕ) (hP : ∀ p ∈ Ps, p.Prime)
    (hne : ∀ i ∈ Ico K J, arg i ≠ 0)
    (hcov : ∀ i ∈ Ico K J, (arg i).natAbs.primeFactors ⊆ Ps) :
    ∑ i ∈ Ico K J, omegaZ (arg i) / 2 ^ (i + 1)
      = ∑ p ∈ Ps, ∑ i ∈ Ico K J, (if (p : ℤ) ∣ arg i then (1 : ℝ) / 2 ^ (i + 1) else 0) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [omegaZ_eq_sum_indicator Ps hP _ (hne i hi) (hcov i hi), Finset.sum_div]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  split_ifs <;> simp

/-- **Exact additive decomposition** of the finite tail over a covering set of primes. -/
theorem truncPhase_eq_sum_primePart (c : TConfig) (K J : ℕ) (n : ℤ) (Ps : Finset ℕ)
    (hP : ∀ p ∈ Ps, p.Prime)
    (hne : ∀ a ∈ c.support, ∀ i ∈ Ico K J, n + ((i : ℤ) + 1) * a.1 - a.2 ≠ 0)
    (hcov : ∀ a ∈ c.support, ∀ i ∈ Ico K J,
      (n + ((i : ℤ) + 1) * a.1 - a.2).natAbs.primeFactors ⊆ Ps) :
    truncPhase c K J n = ∑ p ∈ Ps, primePart c K J p n := by
  unfold truncPhase primePart Finsupp.sum
  have h : ∀ a ∈ c.support, (c a : ℝ) * ∑ i ∈ Ico K J, omegaZ (n + ((i : ℤ) + 1) * a.1 - a.2) / 2 ^ (i + 1)
      = ∑ p ∈ Ps, (c a : ℝ) * ∑ i ∈ Ico K J,
          (if (p : ℤ) ∣ n + ((i : ℤ) + 1) * a.1 - a.2 then (1 : ℝ) / 2 ^ (i + 1) else 0) := by
    intro a ha
    rw [tail_atom_eq_sum K J (fun i => n + ((i : ℤ) + 1) * a.1 - a.2) Ps hP (hne a ha) (hcov a ha),
      Finset.mul_sum]
  rw [Finset.sum_congr rfl h, Finset.sum_comm]

/-! ### The sieve data and the four obligations -/

/-- Sieve bookkeeping attached to one configuration and progression sample. -/
structure SieveData (c : TConfig) (K : ℕ) (D : ProgressionFamily c) where
  /-- finite tail cutoff -/
  J : ℕ
  /-- frozen ("bad") primes -/
  bad : Finset ℕ
  /-- good primes up to the sieve cutoff -/
  small : Finset ℕ
  /-- good primes above the cutoff that can occur -/
  large : Finset ℕ
  prime_bad : ∀ p ∈ bad, p.Prime
  prime_small : ∀ p ∈ small, p.Prime
  prime_large : ∀ p ∈ large, p.Prime
  disj_bs : Disjoint bad small
  disj_bl : Disjoint bad large
  disj_sl : Disjoint small large
  /-- arguments are nonzero on the sample -/
  arg_ne : ∀ n ∈ D.P, ∀ a ∈ c.support, ∀ i ∈ Ico K J, n + ((i : ℤ) + 1) * a.1 - a.2 ≠ 0
  /-- the three classes cover every prime factor of every argument -/
  cover : ∀ n ∈ D.P, ∀ a ∈ c.support, ∀ i ∈ Ico K J,
    (n + ((i : ℤ) + 1) * a.1 - a.2).natAbs.primeFactors ⊆ bad ∪ small ∪ large

/-- Sum of prime parts over a class. -/
noncomputable def classSum (c : TConfig) (K J : ℕ) (S : Finset ℕ) (n : ℤ) : ℝ :=
  ∑ p ∈ S, primePart c K J p n

/-- The finite tail splits exactly into bad, small, and large classes on the sample. -/
theorem truncPhase_split {c : TConfig} {K : ℕ} {D : ProgressionFamily c} (S : SieveData c K D)
    (n : ℤ) (hn : n ∈ D.P) :
    truncPhase c K S.J n =
      classSum c K S.J S.bad n + classSum c K S.J S.small n + classSum c K S.J S.large n := by
  unfold classSum
  rw [truncPhase_eq_sum_primePart c K S.J n (S.bad ∪ S.small ∪ S.large)
    (fun p hp => by
      rcases Finset.mem_union.mp hp with h | h
      · rcases Finset.mem_union.mp h with h | h
        · exact S.prime_bad p h
        · exact S.prime_small p h
      · exact S.prime_large p h)
    (S.arg_ne n hn) (S.cover n hn)]
  rw [Finset.sum_union (Finset.disjoint_union_left.mpr ⟨S.disj_bl, S.disj_sl⟩),
    Finset.sum_union S.disj_bs]

/-- A family of sieve data indexed by `N`. -/
structure Chain (q : ℤ) where
  c : ℕ → TConfig
  K : ℕ → ℕ
  D : ∀ N, ProgressionFamily (c N)
  S : ∀ N, SieveData (c N) (K N) (D N)
  cancel : ∀ N j, 1 ≤ j → j ≤ K N → CancelsAt (c N) j

/-- (20): the infinite binary tail beyond `J` is uniformly negligible on the sample. -/
def TailTruncation {q : ℤ} (C : Chain q) : Prop :=
  ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
    ∀ N, ∀ n ∈ (C.D N).P, |phaseSum (C.c N) (C.K N) n - truncPhase (C.c N) (C.K N) (C.S N).J n| ≤ ε N

/-- (19): good primes above the sieve cutoff are uniformly negligible on the sample. -/
def LargePrimeNegligible {q : ℤ} (C : Chain q) : Prop :=
  ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
    ∀ N, ∀ n ∈ (C.D N).P, |classSum (C.c N) (C.K N) (C.S N).J (C.S N).large n| ≤ ε N

/-- §5.2: the bad-prime contribution is a deterministic constant on the sample. -/
def BadPrimeFrozen {q : ℤ} (C : Chain q) : Prop :=
  ∀ N, ∀ n ∈ (C.D N).P, ∀ n' ∈ (C.D N).P,
    classSum (C.c N) (C.K N) (C.S N).J (C.S N).bad n
      = classSum (C.c N) (C.K N) (C.S N).J (C.S N).bad n'

/-- §5.3–5.4: the good small-prime signed sum equidistributes: its `q`-th phase average on the
sample tends to zero.  This is the finite-sieve characteristic-function estimate. -/
def SmallPrimeDecay {q : ℤ} (C : Chain q) : Prop :=
  Tendsto (fun N => ‖(∑ n ∈ (C.D N).P,
      e (q * classSum (C.c N) (C.K N) (C.S N).J (C.S N).small n)) / (C.D N).P.card‖)
    atTop (𝓝 0)

/-! ### Wiring -/

lemma e_mul (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e; rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- `‖e(x) − 1‖ ≤ 4π|x|`. -/
lemma norm_e_sub_one_le (x : ℝ) : ‖e x - 1‖ ≤ 4 * Real.pi * |x| := by
  have hpi := Real.pi_pos
  by_cases h : |2 * Real.pi * x| ≤ 1
  · have h1 : ‖(((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]; exact h
    have := Complex.norm_exp_sub_one_le h1
    unfold e
    refine this.trans ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_mul, abs_of_pos hpi, abs_two]
    nlinarith [abs_nonneg x]
  · push Not at h
    have h2 : ‖e x - 1‖ ≤ 2 := by
      calc ‖e x - 1‖ ≤ ‖e x‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_e, norm_one]; norm_num
    have : 1 < 2 * Real.pi * |x| := by
      rw [abs_mul, abs_mul, abs_of_pos hpi, abs_two] at h; linarith
    nlinarith

/-- Averages of unimodular phases: shifting by a uniformly small perturbation moves the average
by at most `4π|q|·ε`. -/
lemma norm_avg_le {P : Finset ℤ} (hP : P.Nonempty) (g δ : ℤ → ℝ) (ε : ℝ)
    (hδ : ∀ n ∈ P, |δ n| ≤ ε) :
    ‖(∑ n ∈ P, e (g n + δ n)) / P.card‖ ≤ ‖(∑ n ∈ P, e (g n)) / P.card‖ + 4 * Real.pi * ε := by
  have hcard : (0 : ℝ) < P.card := by exact_mod_cast Finset.card_pos.mpr hP
  have hsplit : ∑ n ∈ P, e (g n + δ n) = ∑ n ∈ P, e (g n) + ∑ n ∈ P, e (g n) * (e (δ n) - 1) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [e_mul]; ring
  rw [hsplit, add_div, norm_div, Complex.norm_natCast]
  refine (norm_add_le _ _).trans ?_
  rw [norm_div, Complex.norm_natCast]
  gcongr
  rw [norm_div, Complex.norm_natCast, div_le_iff₀ hcard]
  calc ‖∑ n ∈ P, e (g n) * (e (δ n) - 1)‖ ≤ ∑ n ∈ P, ‖e (g n) * (e (δ n) - 1)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ P, 4 * Real.pi * ε := by
        refine Finset.sum_le_sum (fun n hn => ?_)
        rw [norm_mul, norm_e, one_mul]
        refine (norm_e_sub_one_le _).trans ?_
        have := hδ n hn
        have hpi := Real.pi_pos
        nlinarith
    _ = 4 * Real.pi * ε * P.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **Wiring.**  The four obligations, for a chain of cancelling configurations, give the phase
oscillation at frequency `q`. -/
theorem phaseOscillation_at_of_chain {q : ℤ} (C : Chain q)
    (h1 : TailTruncation C) (h2 : LargePrimeNegligible C) (h3 : BadPrimeFrozen C)
    (h4 : SmallPrimeDecay C) :
    Tendsto (fun N => ‖phaseAverage (C.c N) (C.K N) (C.D N).P q‖) atTop (𝓝 0) := by
  obtain ⟨ε₁, hε₁, hb₁⟩ := h1
  obtain ⟨ε₂, hε₂, hb₂⟩ := h2
  -- pointwise bound
  have hpt : ∀ N, ‖phaseAverage (C.c N) (C.K N) (C.D N).P q‖ ≤
      ‖(∑ n ∈ (C.D N).P, e (q * classSum (C.c N) (C.K N) (C.S N).J (C.S N).small n))
        / (C.D N).P.card‖ + 4 * Real.pi * (|q| * (ε₁ N + ε₂ N)) := by
    intro N
    obtain ⟨n₀, hn₀⟩ := (C.D N).nonempty
    set B := classSum (C.c N) (C.K N) (C.S N).J (C.S N).bad n₀
    -- F(n) = small(n) + B + δ(n) with |δ| ≤ ε₁ + ε₂
    have hdec : ∀ n ∈ (C.D N).P, (q : ℝ) * phaseSum (C.c N) (C.K N) n
        = (q * classSum (C.c N) (C.K N) (C.S N).J (C.S N).small n + q * B)
          + q * (phaseSum (C.c N) (C.K N) n - truncPhase (C.c N) (C.K N) (C.S N).J n
              + classSum (C.c N) (C.K N) (C.S N).J (C.S N).large n) := by
      intro n hn
      have := truncPhase_split (C.S N) n hn
      have hB := h3 N n hn n₀ hn₀
      simp only [B]
      linear_combination (q : ℝ) * this + (q : ℝ) * hB
    have hδ : ∀ n ∈ (C.D N).P,
        |(q : ℝ) * (phaseSum (C.c N) (C.K N) n - truncPhase (C.c N) (C.K N) (C.S N).J n
              + classSum (C.c N) (C.K N) (C.S N).J (C.S N).large n)| ≤ |q| * (ε₁ N + ε₂ N) := by
      intro n hn
      rw [abs_mul]
      have hq : (|(q : ℝ)|) = ((|q| : ℤ) : ℝ) := by push_cast; rfl
      rw [hq]
      gcongr
      exact (abs_add_le _ _).trans (add_le_add (hb₁ N n hn) (hb₂ N n hn))
    unfold phaseAverage
    rw [Finset.sum_congr rfl (fun n hn => by rw [hdec n hn])]
    refine (norm_avg_le (C.D N).nonempty _ _ _ hδ).trans ?_
    have hsplit : ∑ n ∈ (C.D N).P,
        e (q * classSum (C.c N) (C.K N) (C.S N).J (C.S N).small n + q * B)
        = (∑ n ∈ (C.D N).P, e (q * classSum (C.c N) (C.K N) (C.S N).J (C.S N).small n)) * e (q * B) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun n _ => by rw [e_mul])
    rw [hsplit, mul_div_right_comm, norm_mul, norm_e, mul_one]
  -- squeeze
  have hlim : Tendsto (fun N => ‖(∑ n ∈ (C.D N).P,
      e (q * classSum (C.c N) (C.K N) (C.S N).J (C.S N).small n)) / (C.D N).P.card‖
        + 4 * Real.pi * (|q| * (ε₁ N + ε₂ N))) atTop (𝓝 0) := by
    have := h4.add (((hε₁.add hε₂).const_mul (|q| : ℝ)).const_mul (4 * Real.pi))
    simpa using this
  exact squeeze_zero (fun N => norm_nonneg _) hpt hlim

/-- **Conditional wiring of the whole chain**: if for every `q ≠ 0` a chain with the four
obligations exists, then `PhaseOscillation` holds (and hence, by
`irrational_of_phaseOscillation`, `primeLambert` is irrational). -/
theorem phaseOscillation_of_chain
    (h : ∀ q : ℤ, q ≠ 0 → ∃ C : Chain q,
      TailTruncation C ∧ LargePrimeNegligible C ∧ BadPrimeFrozen C ∧ SmallPrimeDecay C) :
    PhaseOscillation := by
  intro q hq
  obtain ⟨C, h1, h2, h3, h4⟩ := h q hq
  exact ⟨C.c, C.K, C.D, C.cancel, phaseOscillation_at_of_chain C h1 h2 h3 h4⟩

/-- The remaining open obligation, as a research-map Prop: for every `q ≠ 0` a chain of
cancelling configurations exists satisfying the four analytic conditions.  Draft §5.1 proposes
the hexagon tensor with `K ~ (6/5) log log log N`, `J = ⌈2 log₂ log N⌉`, `M ~ (log log N)^{1/12}`
even, `R = N^{1/(20M)}`. -/
def ChainExists : Prop :=
  ∀ q : ℤ, q ≠ 0 → ∃ C : Chain q,
    TailTruncation C ∧ LargePrimeNegligible C ∧ BadPrimeFrozen C ∧ SmallPrimeDecay C

theorem phaseOscillation_of_chainExists (h : ChainExists) : PhaseOscillation :=
  phaseOscillation_of_chain h

/-- `ChainExists → Irrational primeLambert`, with every step above it machine-checked. -/
theorem irrational_of_chainExists (h : ChainExists) : Irrational primeLambert :=
  irrational_of_phaseOscillation (phaseOscillation_of_chainExists h)

end NormalNumbers.PrimeLambert
