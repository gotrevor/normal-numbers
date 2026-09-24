import NormalNumbers.DelangeSlotIdentity
import PNTPort.MediumPNT

/-!
# L4's engine: the quantitative PNT, summed over the hyperbola

The one step of the Levin–Fainleib chain where a *quantitative* prime number theorem is
unavoidable (`DESIGN-2026-09-24-delange-route.md`): we need

    ∑_{k ≤ N} |ψ(⌊N/k⌋) − ⌊N/k⌋|  ≤  C · N,

with an absolute `C`.  Plain PNT (`Δ = o(x)`) does not suffice — the `k ≤ √N` range needs
`|Δ(x)| ≪ x/log x`, and the range `k > √N` needs `∫ δ(y) dy/y < ∞`.

Three ingredients:

* `abs_psi_sub_le` — `|ψ(x) − x| ≤ C₀ x / (log x)²` for large `x`.  The saving in
  `PNTPort.MediumPNT` is `exp(−c (log x)^{1/10})`, and we convert it to a power of `log` with the
  **explicit** inequality `y^{20}/20! ≤ e^y` (no limit argument): with `y = c (log x)^{1/10}` this
  reads `(log x)² e^{−y} ≤ 20!/c^{20}`.
* `telescope_sum` — the discrete tail `∑_{k ≤ K} 1/(k v_k²) ≤ 2/v_K + 1/(K v_K²)` for any
  positive antitone `v` with `v_k − v_{k+1} ≥ 1/(k+1)`.  Instantiated at `v_k = log (N/k)` it is
  the discrete form of `∫ du/u² < ∞`, and it is what makes the `O(N)` budget close.
* `sum_abs_deltaN_le` — the splice, splitting `Ioc 0 N` at `k = ⌊N/n₁⌋`.
-/

open Finset ArithmeticFunction Filter Topology

namespace NormalNumbers.DelangeSlot

/-- `ψ x = ∑_{d ≤ x} Λ d`, as a function of a natural cutoff. -/
noncomputable def psiN (x : ℕ) : ℝ := ∑ d ∈ Ioc 0 x, Λ d

lemma psiN_nonneg (n : ℕ) : 0 ≤ psiN n :=
  Finset.sum_nonneg fun d _ ↦ vonMangoldt_nonneg

lemma psiN_mono {m n : ℕ} (h : m ≤ n) : psiN m ≤ psiN n :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_right h)
    (fun d _ _ ↦ vonMangoldt_nonneg)

lemma psiN_eq_chebyshev (n : ℕ) : psiN n = Chebyshev.psi (n : ℝ) := by
  simp [psiN, Chebyshev.psi]

/-- `Δ n = ψ(n) − n`, the error in the prime number theorem at a natural cutoff. -/
noncomputable def deltaN (n : ℕ) : ℝ := psiN n - n

/-- The explicit conversion from the `exp(−c (log x)^{1/10})` saving to a power of `log`:
`y^{20}/20! ≤ e^y` at `y = c (log x)^{1/10}`. -/
lemma log_sq_mul_exp_le {c : ℝ} (hc : 0 < c) {x : ℝ} (hx : 1 ≤ x) :
    (Real.log x) ^ 2 * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))
      ≤ (Nat.factorial 20 : ℝ) / c ^ 20 := by
  set t : ℝ := Real.log x with ht
  have ht0 : 0 ≤ t := Real.log_nonneg hx
  rcases eq_or_lt_of_le ht0 with h | htpos
  · -- `t = 0`: the left side is `0`
    rw [← h]
    have : (0:ℝ) < (Nat.factorial 20 : ℝ) / c ^ 20 := by positivity
    simpa using this.le
  · set y : ℝ := c * t ^ ((1 : ℝ) / 10) with hy
    have hrpow : (0:ℝ) < t ^ ((1 : ℝ) / 10) := Real.rpow_pos_of_pos htpos _
    have hy0 : 0 < y := by rw [hy]; positivity
    have hy20 : y ^ 20 = c ^ 20 * t ^ 2 := by
      rw [hy, mul_pow]
      congr 1
      rw [← Real.rpow_natCast (t ^ ((1 : ℝ) / 10)) 20, ← Real.rpow_mul ht0]
      norm_num
    have hkey : y ^ 20 / (Nat.factorial 20 : ℝ) ≤ Real.exp y :=
      Real.pow_div_factorial_le_exp (x := y) hy0.le 20
    have hexp : Real.exp (-y) ≤ (Nat.factorial 20 : ℝ) / y ^ 20 := by
      rw [Real.exp_neg]
      rw [inv_le_iff_one_le_mul₀ (Real.exp_pos y)]
      have h20 : (0:ℝ) < y ^ 20 := by positivity
      have hfac : (0:ℝ) < (Nat.factorial 20 : ℝ) := by positivity
      rw [div_mul_eq_mul_div, le_div_iff₀ h20]
      calc (1:ℝ) * y ^ 20 = y ^ 20 := one_mul _
        _ = (Nat.factorial 20 : ℝ) * (y ^ 20 / (Nat.factorial 20 : ℝ)) := by
            field_simp
        _ ≤ (Nat.factorial 20 : ℝ) * Real.exp y := by
            exact mul_le_mul_of_nonneg_left hkey hfac.le
  -- combine
    have hneg : -c * t ^ ((1 : ℝ) / 10) = -y := by rw [hy]; ring
    rw [hneg]
    calc t ^ 2 * Real.exp (-y) ≤ t ^ 2 * ((Nat.factorial 20 : ℝ) / y ^ 20) := by
          exact mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = (Nat.factorial 20 : ℝ) / c ^ 20 := by
          rw [hy20]
          field_simp

/-- **Step (a).**  The quantitative prime number theorem in the shape the hyperbola sum needs:
`|ψ(x) − x| ≤ C₀ x / (log x)²` for all large `x`.  Consumes `PNTPort.MediumPNT`. -/
theorem exists_abs_psi_sub_le :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      |Chebyshev.psi x - x| ≤ C₀ * x / (Real.log x) ^ 2 := by
  obtain ⟨c, hc, hO⟩ := MediumPNT
  rw [Asymptotics.isBigO_iff] at hO
  obtain ⟨C, hC⟩ := hO
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.1 hC
  set K : ℝ := (Nat.factorial 20 : ℝ) / c ^ 20 with hK
  have hK0 : 0 < K := by rw [hK]; positivity
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  refine ⟨max (C' * K) 1, lt_of_lt_of_le one_pos (le_max_right _ _),
    max x₁ 2, le_max_right _ _, ?_⟩
  intro x hx
  have hx2 : (2:ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hx1 : (1:ℝ) ≤ x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hb := hx₁ x (le_trans (le_max_left _ _) hx)
  simp only [Pi.sub_apply, id_eq, Real.norm_eq_abs] at hb
  have hnorm : |x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))|
      = x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)) :=
    abs_of_nonneg (by positivity)
  rw [hnorm] at hb
  have hb2 : |Chebyshev.psi x - x| ≤ C' * (x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) :=
    hb.trans (by
      have : (0:ℝ) ≤ x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)) := by positivity
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) this)
  have hexpbd : Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)) ≤ K / (Real.log x) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have := log_sq_mul_exp_le hc hx1
    linarith [this]
  calc |Chebyshev.psi x - x|
      ≤ C' * (x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) := hb2
    _ ≤ C' * (x * (K / (Real.log x) ^ 2)) := by
        have hxx : (0:ℝ) ≤ x := by linarith
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hexpbd hxx) hC'0
    _ = (C' * K) * x / (Real.log x) ^ 2 := by ring
    _ ≤ max (C' * K) 1 * x / (Real.log x) ^ 2 := by
        have hxx : (0:ℝ) ≤ x := by linarith
        gcongr
        exact le_max_left _ _

/-- The one-step inequality behind the telescoping: `1/(K a²) ≤ 2/b − 2/a` whenever
`0 < b ≤ a`, `a − b ≥ 1/(K+1)` and `K ≥ 1`. -/
lemma telescope_step {a b : ℝ} {K : ℕ} (hK : 1 ≤ K) (hb : 0 < b) (hba : b ≤ a)
    (hgap : 1 / ((K : ℝ) + 1) ≤ a - b) :
    2 / a + 1 / ((K : ℝ) * a ^ 2) ≤ 2 / b := by
  have ha : 0 < a := lt_of_lt_of_le hb hba
  have hK1 : (1:ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hKp : (0:ℝ) < (K : ℝ) + 1 := by linarith
  have hgap' : 1 ≤ (a - b) * ((K : ℝ) + 1) := by
    rw [div_le_iff₀ hKp] at hgap; linarith
  have step1 : 2 * a * (K : ℝ) ≤ 2 * a * (K : ℝ) * ((a - b) * ((K : ℝ) + 1)) := by
    nlinarith [mul_pos ha (lt_of_lt_of_le one_pos hK1)]
  have step2 : a * ((K : ℝ) + 1) ≤ 2 * a * (K : ℝ) := by nlinarith
  have step3 : b * ((K : ℝ) + 1) ≤ a * ((K : ℝ) + 1) := by nlinarith
  have step4 : b ≤ 2 * a * (K : ℝ) * (a - b) := by
    nlinarith [step1, step2, step3]
  have hfin : 2 * a * b * (K : ℝ) + b ≤ 2 * a ^ 2 * (K : ℝ) := by nlinarith [step4]
  have e1 : 2 / a + 1 / ((K : ℝ) * a ^ 2) = (2 * a * (K : ℝ) + 1) / ((K : ℝ) * a ^ 2) := by
    field_simp
  rw [e1, div_le_div_iff₀ (by positivity) hb]
  nlinarith [hfin]

/-- **Step (c).**  The discrete form of `∫_{v_K}^{∞} du/u² < ∞`: for a positive antitone `v`
whose gaps dominate `1/(k+1)` (which `log` gaps do),
`∑_{k ≤ K} 1/(k v_k²) ≤ 2/v_K + 1/(K v_K²)`. -/
lemma telescope_sum (v : ℕ → ℝ) : ∀ K : ℕ, 1 ≤ K →
    (∀ k, 1 ≤ k → k ≤ K → 0 < v k) →
    (∀ k, 1 ≤ k → k + 1 ≤ K → v (k + 1) ≤ v k) →
    (∀ k, 1 ≤ k → k + 1 ≤ K → 1 / ((k : ℝ) + 1) ≤ v k - v (k + 1)) →
    ∑ k ∈ Ioc 0 K, 1 / ((k : ℝ) * (v k) ^ 2) ≤ 2 / v K + 1 / ((K : ℝ) * (v K) ^ 2) := by
  intro K
  induction K with
  | zero => intro h; exact absurd h (by norm_num)
  | succ K ih =>
    intro _ hpos hanti hgap
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le _)]
    rcases Nat.eq_zero_or_pos K with rfl | hK1
    · have h1 : 0 < v 1 := hpos 1 le_rfl le_rfl
      simp only [Finset.Ioc_self, Finset.sum_empty, zero_add]
      have : (0:ℝ) ≤ 2 / v 1 := by positivity
      norm_num
      linarith
    · have ihc := ih hK1 (fun k h1 h2 => hpos k h1 (by omega))
        (fun k h1 h2 => hanti k h1 (by omega)) (fun k h1 h2 => hgap k h1 (by omega))
      have hposK : 0 < v K := hpos K hK1 (by omega)
      have hposK1 : 0 < v (K + 1) := hpos (K + 1) (by omega) le_rfl
      have hanti' : v (K + 1) ≤ v K := hanti K hK1 le_rfl
      have hgap' : 1 / ((K : ℝ) + 1) ≤ v K - v (K + 1) := hgap K hK1 le_rfl
      have hstep := telescope_step hK1 hposK1 hanti' hgap'
      have hcast : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      linarith [ihc, hstep]


/-- `log(k+1) − log k ≥ 1/(k+1)`: the gap hypothesis of `telescope_sum` for `v_k = log(N/k)`. -/
lemma one_div_succ_le_log_sub {k : ℕ} (hk : 1 ≤ k) :
    1 / ((k : ℝ) + 1) ≤ Real.log ((k : ℝ) + 1) - Real.log k := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hk1 : (0:ℝ) < (k : ℝ) + 1 := by linarith
  have h := Real.log_le_sub_one_of_pos (x := (k : ℝ) / ((k : ℝ) + 1)) (by positivity)
  rw [Real.log_div hk0.ne' hk1.ne'] at h
  have he : (k : ℝ) / ((k : ℝ) + 1) - 1 = -(1 / ((k : ℝ) + 1)) := by
    field_simp; ring
  rw [he] at h
  linarith

lemma log_eight_eq : Real.log 8 = 3 * Real.log 2 := by
  rw [show (8:ℝ) = 2 ^ (3:ℕ) by norm_num, Real.log_pow]
  push_cast; ring

/-- `2 < log 8`, the numerical slack that lets `⌊N/k⌋` replace `N/k` inside the logarithm. -/
lemma two_lt_log_eight : (2:ℝ) < Real.log 8 := by
  rw [log_eight_eq]
  linarith [Real.log_two_gt_d9]

/-- `N/k ≤ 2⌊N/k⌋` once the quotient is at least one: floors lose at most a factor two. -/
lemma cast_div_le_two_mul {N k : ℕ} (hk : 0 < k) (hm : 1 ≤ N / k) :
    (N : ℝ) / (k : ℝ) ≤ 2 * ((N / k : ℕ) : ℝ) := by
  have hlt : N < (N / k + 1) * k := (Nat.div_lt_iff_lt_mul hk).1 (Nat.lt_succ_self _)
  have hk0R : (0:ℝ) < k := by exact_mod_cast hk
  have h1 : (N : ℝ) < (((N / k : ℕ) : ℝ) + 1) * k := by exact_mod_cast hlt
  have h2 : (1:ℝ) ≤ ((N / k : ℕ) : ℝ) := by exact_mod_cast hm
  rw [div_le_iff₀ hk0R]
  nlinarith


/-- **Step (d), the splice.**  The prime-number-theorem error, summed over the hyperbola, is
`O(N)`.  This is the whole analytic content of L4. -/
theorem exists_sum_abs_deltaN_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ∑ k ∈ Ioc 0 N, |deltaN (N / k)| ≤ C * N := by
  obtain ⟨C₀, hC₀pos, x₀, hx₀2, hpnt⟩ := exists_abs_psi_sub_le
  classical
  set n₁ : ℕ := max 8 ⌈x₀⌉₊ with hn₁def
  have hn₁8 : 8 ≤ n₁ := le_max_left _ _
  have hn₁pos : 0 < n₁ := by omega
  have hn₁x : x₀ ≤ (n₁ : ℝ) :=
    le_trans (Nat.le_ceil x₀) (by exact_mod_cast le_max_right 8 ⌈x₀⌉₊)
  -- the large range: the quantitative PNT
  have hlarge : ∀ n : ℕ, n₁ ≤ n → |deltaN n| ≤ C₀ * n / (Real.log n) ^ 2 := by
    intro n hn
    have hxn : x₀ ≤ (n : ℝ) := le_trans hn₁x (by exact_mod_cast hn)
    have h := hpnt (n : ℝ) hxn
    rwa [deltaN, psiN_eq_chebyshev]
  -- the small range: monotonicity of `ψ`, no maximum needed
  set B : ℝ := psiN n₁ + n₁ with hBdef
  have hB0 : 0 ≤ B := by
    have := psiN_nonneg n₁
    have : (0:ℝ) ≤ (n₁ : ℝ) := Nat.cast_nonneg _
    rw [hBdef]; positivity
  have hsmall : ∀ n : ℕ, n ≤ n₁ → |deltaN n| ≤ B := by
    intro n hn
    have h1 : psiN n ≤ psiN n₁ := psiN_mono hn
    have h2 : (n : ℝ) ≤ (n₁ : ℝ) := by exact_mod_cast hn
    have h3 : 0 ≤ psiN n := psiN_nonneg n
    have h4 : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    have h5 : (0:ℝ) ≤ psiN n₁ := psiN_nonneg n₁
    rw [deltaN, abs_le, hBdef]
    constructor <;> linarith
  refine ⟨B + 3 * C₀, by linarith, ?_⟩
  intro N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  set K : ℕ := N / n₁ with hKdef
  have hKN : K ≤ N := Nat.div_le_self _ _
  have hsub : Ioc 0 K ⊆ Ioc 0 N := Finset.Ioc_subset_Ioc_right hKN
  rw [← Finset.sum_sdiff hsub]
  -- Part A: the small-quotient range
  have hA : ∑ k ∈ Ioc 0 N \ Ioc 0 K, |deltaN (N / k)| ≤ B * N := by
    have hpt : ∀ k ∈ Ioc 0 N \ Ioc 0 K, |deltaN (N / k)| ≤ B := by
      intro k hk
      simp only [Finset.mem_sdiff, Finset.mem_Ioc] at hk
      obtain ⟨⟨hk0, hkN⟩, hnot⟩ := hk
      have hkK : K < k := by
        by_contra hc
        exact hnot ⟨hk0, by omega⟩
      have : N / k ≤ n₁ := by
        by_contra hc
        push_neg at hc
        have : n₁ * k ≤ N := (Nat.le_div_iff_mul_le hk0).1 hc.le
        have : k ≤ N / n₁ := (Nat.le_div_iff_mul_le hn₁pos).2 (by lia)
        omega
      exact hsmall _ this
    calc ∑ k ∈ Ioc 0 N \ Ioc 0 K, |deltaN (N / k)|
        ≤ ∑ _k ∈ Ioc 0 N \ Ioc 0 K, B := Finset.sum_le_sum hpt
      _ = ((Ioc 0 N \ Ioc 0 K).card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * B := by
          have hcard : (Ioc 0 N \ Ioc 0 K).card ≤ N := by
            calc (Ioc 0 N \ Ioc 0 K).card ≤ (Ioc 0 N).card :=
                  Finset.card_le_card Finset.sdiff_subset
              _ = N := by simp
          have : ((Ioc 0 N \ Ioc 0 K).card : ℝ) ≤ (N : ℝ) := by exact_mod_cast hcard
          exact mul_le_mul_of_nonneg_right this hB0
      _ = B * N := mul_comm _ _
  -- Part B: the large-quotient range, where the telescoping tail lives
  have hBpart : ∑ k ∈ Ioc 0 K, |deltaN (N / k)| ≤ 3 * C₀ * N := by
    rcases Nat.eq_zero_or_pos K with hK0 | hK1
    · rw [hK0]
      simp only [Finset.Ioc_self, Finset.sum_empty]
      positivity
    have hKn₁ : K * n₁ ≤ N := Nat.div_mul_le_self N n₁
    have hN0 : (0:ℝ) < N := by exact_mod_cast hN
    have hK0R : (0:ℝ) < (K : ℝ) := by exact_mod_cast hK1
    have hK1R : (1:ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
    set v : ℕ → ℝ := fun k => Real.log N - Real.log k with hvdef
    have hvK : Real.log (n₁ : ℝ) ≤ v K := by
      have hle : ((n₁ : ℝ)) ≤ (N : ℝ) / (K : ℝ) := by
        rw [le_div_iff₀ hK0R]
        have : n₁ * K ≤ N := by lia
        exact_mod_cast this
      have h2 := Real.log_le_log (by positivity) hle
      rwa [Real.log_div hN0.ne' hK0R.ne'] at h2
    have hlogn₁ : (2:ℝ) < Real.log (n₁ : ℝ) :=
      lt_of_lt_of_le two_lt_log_eight
        (Real.log_le_log (by norm_num) (by exact_mod_cast hn₁8))
    have hvK2 : (2:ℝ) < v K := lt_of_lt_of_le hlogn₁ hvK
    have hvanti : ∀ k l : ℕ, 1 ≤ k → k ≤ l → v l ≤ v k := by
      intro k l hk hkl
      have : Real.log k ≤ Real.log l :=
        Real.log_le_log (by exact_mod_cast hk) (by exact_mod_cast hkl)
      simp only [hvdef]; linarith
    have hvpos : ∀ k, 1 ≤ k → k ≤ K → 0 < v k := by
      intro k h1 h2
      have := hvanti k K h1 h2
      linarith
    have htel := telescope_sum v K hK1 hvpos
      (fun k h1 _ => hvanti k (k + 1) h1 (by omega))
      (fun k h1 _ => by
        have hg := one_div_succ_le_log_sub h1
        have hc : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
        simp only [hvdef, hc]
        linarith)
    have htel2 : ∑ k ∈ Ioc 0 K, 1 / ((k : ℝ) * (v k) ^ 2) ≤ 5 / 4 := by
      have h1 : 2 / v K ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      have h2 : 1 / ((K : ℝ) * (v K) ^ 2) ≤ 1 / 4 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      linarith
    have hterm : ∀ k ∈ Ioc 0 K,
        |deltaN (N / k)| ≤ (2 * C₀ * (N : ℝ)) * (1 / ((k : ℝ) * (v k) ^ 2)) := by
      intro k hk
      simp only [Finset.mem_Ioc] at hk
      obtain ⟨hk0, hkK⟩ := hk
      have hk0R : (0:ℝ) < (k : ℝ) := by exact_mod_cast hk0
      have hmn₁ : n₁ ≤ N / k := by
        refine (Nat.le_div_iff_mul_le hk0).2 ?_
        have : k * n₁ ≤ K * n₁ := Nat.mul_le_mul_right n₁ hkK
        lia
      have hm8 : 8 ≤ N / k := le_trans hn₁8 hmn₁
      have hm0R : (0:ℝ) < ((N / k : ℕ) : ℝ) := by
        have : (0:ℕ) < N / k := by omega
        exact_mod_cast this
      have hlogm : (2:ℝ) < Real.log ((N / k : ℕ) : ℝ) :=
        lt_of_lt_of_le two_lt_log_eight
          (Real.log_le_log (by norm_num) (by exact_mod_cast hm8))
      have hvk : v k = Real.log ((N : ℝ) / (k : ℝ)) := by
        simp only [hvdef]; rw [Real.log_div hN0.ne' hk0R.ne']
      have hvkpos : 0 < v k := hvpos k hk0 hkK
      have hmle : ((N / k : ℕ) : ℝ) ≤ (N : ℝ) / (k : ℝ) := Nat.cast_div_le
      have h2m : (N : ℝ) / (k : ℝ) ≤ 2 * ((N / k : ℕ) : ℝ) :=
        cast_div_le_two_mul hk0 (by omega)
      have hlogcmp : (3 / 4 : ℝ) * v k ≤ Real.log ((N / k : ℕ) : ℝ) := by
        have h1 : v k ≤ Real.log 2 + Real.log ((N / k : ℕ) : ℝ) := by
          rw [hvk]
          calc Real.log ((N : ℝ) / (k : ℝ)) ≤ Real.log (2 * ((N / k : ℕ) : ℝ)) :=
                Real.log_le_log (by positivity) h2m
            _ = Real.log 2 + Real.log ((N / k : ℕ) : ℝ) :=
                Real.log_mul (by norm_num) (by positivity)
        have h8 : Real.log 8 ≤ Real.log ((N / k : ℕ) : ℝ) :=
          Real.log_le_log (by norm_num) (by exact_mod_cast hm8)
        rw [log_eight_eq] at h8
        linarith
      have hbound := hlarge (N / k) hmn₁
      calc |deltaN (N / k)| ≤ C₀ * ((N / k : ℕ) : ℝ) / (Real.log ((N / k : ℕ) : ℝ)) ^ 2 := hbound
        _ ≤ C₀ * ((N : ℝ) / (k : ℝ)) / ((9 / 16) * (v k) ^ 2) := by
            refine div_le_div₀ (by positivity) ?_ (by positivity) ?_
            · exact mul_le_mul_of_nonneg_left hmle hC₀pos.le
            · nlinarith
        _ = (16 / 9) * C₀ * (N : ℝ) * (1 / ((k : ℝ) * (v k) ^ 2)) := by
            field_simp
        _ ≤ (2 * C₀ * (N : ℝ)) * (1 / ((k : ℝ) * (v k) ^ 2)) := by
            have hpos : (0:ℝ) ≤ 1 / ((k : ℝ) * (v k) ^ 2) := by positivity
            have hle : (16 / 9) * C₀ * (N : ℝ) ≤ 2 * C₀ * (N : ℝ) := by nlinarith
            exact mul_le_mul_of_nonneg_right hle hpos
    calc ∑ k ∈ Ioc 0 K, |deltaN (N / k)|
        ≤ ∑ k ∈ Ioc 0 K, (2 * C₀ * (N : ℝ)) * (1 / ((k : ℝ) * (v k) ^ 2)) :=
          Finset.sum_le_sum hterm
      _ = (2 * C₀ * (N : ℝ)) * ∑ k ∈ Ioc 0 K, (1 / ((k : ℝ) * (v k) ^ 2)) := by
          rw [Finset.mul_sum]
      _ ≤ (2 * C₀ * (N : ℝ)) * (5 / 4) :=
          mul_le_mul_of_nonneg_left htel2 (by positivity)
      _ ≤ 3 * C₀ * N := by nlinarith
  have : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg _
  calc (∑ k ∈ Ioc 0 N \ Ioc 0 K, |deltaN (N / k)|) + ∑ k ∈ Ioc 0 K, |deltaN (N / k)|
      ≤ B * N + 3 * C₀ * N := add_le_add hA hBpart
    _ = (B + 3 * C₀) * N := by ring


/-- The floor costs at most `1`: `|⌊N/k⌋ − N/k| ≤ 1`. -/
lemma abs_cast_div_sub_le_one {N k : ℕ} (hk : 0 < k) :
    |((N / k : ℕ) : ℝ) - (N : ℝ) / (k : ℝ)| ≤ 1 := by
  have hk0R : (0:ℝ) < (k : ℝ) := by exact_mod_cast hk
  have h1 : ((N / k : ℕ) : ℝ) ≤ (N : ℝ) / (k : ℝ) := Nat.cast_div_le
  have hlt : N < (N / k + 1) * k := (Nat.div_lt_iff_lt_mul hk).1 (Nat.lt_succ_self _)
  have h2 : (N : ℝ) < (((N / k : ℕ) : ℝ) + 1) * k := by exact_mod_cast hlt
  have h3 : (N : ℝ) / (k : ℝ) < ((N / k : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hk0R]; exact h2
  rw [abs_le]
  constructor <;> linarith

/-- **L4 in real form.**  `∑_{k ≤ N} |ψ(⌊N/k⌋) − N/k| = O(N)`: the PNT error plus the floor
error, both inside the `O(N)` budget. -/
theorem exists_sum_psi_sub_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ∑ k ∈ Ioc 0 N, |psiN (N / k) - (N : ℝ) / (k : ℝ)| ≤ C * N := by
  obtain ⟨C, hC0, hC⟩ := exists_sum_abs_deltaN_le
  refine ⟨C + 1, by linarith, fun N ↦ ?_⟩
  have hpt : ∀ k ∈ Ioc 0 N, |psiN (N / k) - (N : ℝ) / (k : ℝ)|
      ≤ |deltaN (N / k)| + 1 := by
    intro k hk
    have hk0 : 0 < k := (Finset.mem_Ioc.1 hk).1
    have hsplit : psiN (N / k) - (N : ℝ) / (k : ℝ)
        = deltaN (N / k) + (((N / k : ℕ) : ℝ) - (N : ℝ) / (k : ℝ)) := by
      rw [deltaN]; ring
    rw [hsplit]
    exact (abs_add_le _ _).trans (by linarith [abs_cast_div_sub_le_one (N := N) hk0])
  calc ∑ k ∈ Ioc 0 N, |psiN (N / k) - (N : ℝ) / (k : ℝ)|
      ≤ ∑ k ∈ Ioc 0 N, (|deltaN (N / k)| + 1) := Finset.sum_le_sum hpt
    _ = (∑ k ∈ Ioc 0 N, |deltaN (N / k)|) + (N : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Nat.card_Ioc]
        simp
    _ ≤ C * N + (N : ℝ) := by linarith [hC N]
    _ = (C + 1) * N := by ring

end NormalNumbers.DelangeSlot
