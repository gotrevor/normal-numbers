import NormalNumbers.FiniteStateSelection
import NormalNumbers.NormalLower

namespace NormalNumbers.FiniteState

open NormalNumbers.NormalLower Finset Filter

variable {k : ℕ}

section CPNormal

variable [NeZero k]

theorem lexWord_map_val (n j : ℕ) :
    (lexWord k n j).map Fin.val = (List.range n).map (fun i => j / k ^ (n - 1 - i) % k) := by
  simp [lexWord]

theorem lexWord_reverse_map_val (n j : ℕ) :
    ((lexWord k n j).reverse).map Fin.val = (List.range n).map (fun i => j / k ^ i % k) := by
  rw [List.map_reverse, lexWord_map_val]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_reverse, List.getElem_map, List.getElem_range, List.length_map,
    List.length_range]
  have hi : i < n := by simpa using h2
  rw [show n - 1 - (n - 1 - i) = i by omega]

theorem isPrefixOf_of_digits {g : ℕ → ℕ} {n q : ℕ} {v : List ℕ} (hq : q + v.length ≤ n)
    (h : ∀ t < v.length, g (q + t) = v.getD t 0) :
    v.isPrefixOf (((List.range n).map g).drop q) := by
  rw [List.isPrefixOf_iff_prefix, List.prefix_iff_eq_take]
  apply List.ext_getElem (by simp; omega)
  intro t h1 h2
  simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
  rw [h t h1, List.getD_eq_getElem _ _ h1]

theorem count_word_ge (g : ℕ → ℕ) (n : ℕ) (v : List ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ q, q + v.length ≤ n → P q → ∀ t < v.length, g (q + t) = v.getD t 0) :
    ((range (n + 1 - v.length)).filter P).card ≤ countOccurrences v ((List.range n).map g) := by
  rw [countOccurrences_eq_card]
  apply Finset.card_le_card
  intro q hq
  simp only [Finset.mem_filter, Finset.mem_range, List.length_map, List.length_range] at hq ⊢
  have hq' : q + v.length ≤ n := by omega
  exact ⟨by omega, isPrefixOf_of_digits hq' (hP q hq' hq.2)⟩

theorem getD_reverse (v : List ℕ) (t : ℕ) (ht : t < v.length) :
    v.reverse.getD (v.length - 1 - t) 0 = v.getD t 0 := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ ht, List.getElem_reverse]
  congr 1; omega

theorem fwd_digits (hk : 0 < k) (v : List ℕ) (hv : ∀ d ∈ v, d < k) (n j q : ℕ)
    (hq : q + v.length ≤ n) (hP : j / k ^ (n - q - v.length) % k ^ v.length = lval k v.reverse) :
    ∀ t < v.length, j / k ^ (n - 1 - (q + t)) % k = v.getD t 0 := by
  intro t ht
  have he : n - 1 - (q + t) = (n - q - v.length) + (v.length - 1 - t) := by omega
  rw [he, pow_add, ← Nat.div_div_eq_div_mul, ← getD_reverse v t ht]
  exact mod_pow_eq_lval hk v.reverse (by simpa using hv) _ (by simpa using hP) _ (by simp; omega)

theorem rev_digits (hk : 0 < k) (v : List ℕ) (hv : ∀ d ∈ v, d < k) (j q : ℕ)
    (hP : j / k ^ q % k ^ v.length = lval k v) :
    ∀ t < v.length, j / k ^ (q + t) % k = v.getD t 0 := by
  intro t ht
  rw [pow_add, ← Nat.div_div_eq_div_mul]
  exact mod_pow_eq_lval hk v hv _ hP t ht

/-- Real form of the periodic count. -/
theorem real_le_card_div_mod {A t p q d : ℕ} (hp : 0 < p) (hq : 0 < q) (hd : d < q) :
    (t : ℝ) / q - 2 * p ≤ (((Finset.Ico A (A + t)).filter (fun n => n / p % q = d)).card : ℝ) := by
  have h := le_card_Ico_filter_div_mod' (A := A) (t := t) hp hq hd
  have hpq : 0 < p * q := Nat.mul_pos hp hq
  refine le_trans ?_ (Nat.cast_le (α := ℝ).mpr h)
  set a := t / (p * q)
  have hlt : t < (a + 1) * (p * q) := by
    have := Nat.lt_div_mul_add (a := t) hpq; rw [add_mul, one_mul]; exact this
  have hlt' : (t : ℝ) < ((a : ℝ) + 1) * ((p : ℝ) * q) := by exact_mod_cast hlt
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have htq : (t : ℝ) / q < ((a : ℝ) + 1) * p := by
    rw [div_lt_iff₀ hqR]; linarith
  rcases Nat.eq_zero_or_pos a with ha | ha
  · rw [ha]; simp only [Nat.zero_sub, zero_mul, Nat.cast_zero]
    rw [ha] at htq; simp at htq
    have : (0 : ℝ) ≤ p := by positivity
    linarith
  · rw [Nat.cast_mul, Nat.cast_sub ha]; push_cast; nlinarith

theorem geom_le (hk : 2 ≤ k) (m : ℕ) : ∑ i ∈ range m, (k : ℝ) ^ i ≤ (k : ℝ) ^ m := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, pow_succ]
    have : (0 : ℝ) ≤ (k : ℝ) ^ m := by positivity
    nlinarith

theorem sum_count_fwd (hk : 2 ≤ k) (v : List ℕ) (hv : v ≠ []) (hvd : ∀ d ∈ v, d < k)
    (n a t : ℕ) :
    ((n + 1 - v.length : ℕ) : ℝ) * t / (k : ℝ) ^ v.length - 2 * (k : ℝ) ^ n ≤
      ∑ j ∈ Ico a (a + t), (countOccurrences v ((lexWord k n j).map Fin.val) : ℝ) := by
  have hk0 : 0 < k := by omega
  set ℓ := v.length with hℓdef
  have hℓ : 1 ≤ ℓ := List.length_pos_iff.mpr hv
  set m := n + 1 - ℓ with hm
  set P : ℕ → ℕ → Prop := fun j q => j / k ^ (n - q - ℓ) % k ^ ℓ = lval k v.reverse with hP
  have hword : ∀ j, (((range m).filter (P j)).card : ℝ) ≤
      countOccurrences v ((lexWord k n j).map Fin.val) := by
    intro j; rw [lexWord_map_val]
    exact_mod_cast count_word_ge _ n v (P j) (fun q hq hPq => fwd_digits hk0 v hvd n j q hq hPq)
  have hswap : ∑ j ∈ Ico a (a + t), (((range m).filter (P j)).card : ℝ) =
      ∑ q ∈ range m, (((Ico a (a + t)).filter (fun j => P j q)).card : ℝ) := by
    simp only [Finset.card_filter]; push_cast; exact Finset.sum_comm
  have hq : ∀ q ∈ range m, (t : ℝ) / (k : ℝ) ^ ℓ - 2 * (k : ℝ) ^ (n - q - ℓ) ≤
      (((Ico a (a + t)).filter (fun j => P j q)).card : ℝ) := by
    intro q _
    have := real_le_card_div_mod (A := a) (t := t) (p := k ^ (n - q - ℓ)) (q := k ^ ℓ)
      (d := lval k v.reverse) (by positivity) (by positivity)
      (by simpa using lval_lt v.reverse (by simpa using hvd))
    push_cast at this; exact this
  have hgeo : ∑ q ∈ range m, (k : ℝ) ^ (n - q - ℓ) ≤ (k : ℝ) ^ n := by
    have : ∑ q ∈ range m, (k : ℝ) ^ (n - q - ℓ) = ∑ q ∈ range m, (k : ℝ) ^ (m - 1 - q) := by
      apply sum_congr rfl; intro q hq; simp only [Finset.mem_range] at hq; congr 1; omega
    rw [this, Finset.sum_range_reflect (fun i => (k : ℝ) ^ i) m]
    exact le_trans (geom_le hk m)
      (pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ k)) (by omega))
  have hcalc : ((m : ℕ) : ℝ) * t / (k : ℝ) ^ ℓ - 2 * (k : ℝ) ^ n ≤
      ∑ q ∈ range m, ((t : ℝ) / (k : ℝ) ^ ℓ - 2 * (k : ℝ) ^ (n - q - ℓ)) := by
    rw [sum_sub_distrib, sum_const, card_range, ← mul_sum, nsmul_eq_mul, mul_div_assoc]
    linarith
  exact le_trans hcalc (le_trans (sum_le_sum hq) (by rw [← hswap]; exact sum_le_sum fun j _ => hword j))

theorem sum_count_rev (hk : 2 ≤ k) (v : List ℕ) (hv : v ≠ []) (hvd : ∀ d ∈ v, d < k)
    (n a t : ℕ) :
    ((n + 1 - v.length : ℕ) : ℝ) * t / (k : ℝ) ^ v.length - 2 * (k : ℝ) ^ n ≤
      ∑ j ∈ Ico a (a + t), (countOccurrences v ((lexWord k n j).reverse.map Fin.val) : ℝ) := by
  have hk0 : 0 < k := by omega
  set ℓ := v.length with hℓdef
  have hℓ : 1 ≤ ℓ := List.length_pos_iff.mpr hv
  set m := n + 1 - ℓ with hm
  set P : ℕ → ℕ → Prop := fun j q => j / k ^ q % k ^ ℓ = lval k v with hP
  have hword : ∀ j, (((range m).filter (P j)).card : ℝ) ≤
      countOccurrences v ((lexWord k n j).reverse.map Fin.val) := by
    intro j; rw [lexWord_reverse_map_val]
    exact_mod_cast count_word_ge _ n v (P j) (fun q _ hPq => rev_digits hk0 v hvd j q hPq)
  have hswap : ∑ j ∈ Ico a (a + t), (((range m).filter (P j)).card : ℝ) =
      ∑ q ∈ range m, (((Ico a (a + t)).filter (fun j => P j q)).card : ℝ) := by
    simp only [Finset.card_filter]; push_cast; exact Finset.sum_comm
  have hq : ∀ q ∈ range m, (t : ℝ) / (k : ℝ) ^ ℓ - 2 * (k : ℝ) ^ q ≤
      (((Ico a (a + t)).filter (fun j => P j q)).card : ℝ) := by
    intro q _
    have := real_le_card_div_mod (A := a) (t := t) (p := k ^ q) (q := k ^ ℓ)
      (d := lval k v) (by positivity) (by positivity) (lval_lt v hvd)
    push_cast at this; exact this
  have hgeo : ∑ q ∈ range m, (k : ℝ) ^ q ≤ (k : ℝ) ^ n :=
    le_trans (geom_le hk m) (pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ k)) (by omega))
  have hcalc : ((m : ℕ) : ℝ) * t / (k : ℝ) ^ ℓ - 2 * (k : ℝ) ^ n ≤
      ∑ q ∈ range m, ((t : ℝ) / (k : ℝ) ^ ℓ - 2 * (k : ℝ) ^ q) := by
    rw [sum_sub_distrib, sum_const, card_range, ← mul_sum, nsmul_eq_mul, mul_div_assoc]
    linarith
  exact le_trans hcalc (le_trans (sum_le_sum hq) (by rw [← hswap]; exact sum_le_sum fun j _ => hword j))

theorem sum_le_count_flatMap {v : List ℕ} (hv : v ≠ []) (W : ℕ → List ℕ) (J : ℕ) :
    ∑ i ∈ range J, countOccurrences v (W i) ≤ countOccurrences v ((List.range J).flatMap W) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [sum_range_succ, List.range_succ, List.flatMap_append]
    have := add_countOccurrences_le_append hv ((List.range J).flatMap W) (W J)
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    omega

theorem count_take_flatMap {v : List ℕ} (hv : v ≠ []) (W : ℕ → List ℕ) {n T r : ℕ}
    (hW : ∀ i, (W i).length = n) (hr : r / n ≤ T) :
    ∑ i ∈ range (r / n), countOccurrences v (W i) ≤
      countOccurrences v (((List.range T).flatMap W).take r) := by
  set J := r / n
  have hsplit : (List.range T).flatMap W =
      (List.range J).flatMap W ++ ((List.range (T - J)).map (J + ·)).flatMap W := by
    rw [← List.flatMap_append, ← List.range_add]; congr 2; omega
  have hlen : ((List.range J).flatMap W).length = J * n := by simp [List.length_flatMap, hW]
  have hJn : J * n ≤ r := Nat.div_mul_le_self r n
  rw [hsplit, List.take_append, List.take_of_length_le (by omega)]
  exact le_trans (sum_le_count_flatMap hv W J)
    (le_trans (Nat.le_add_right _ _) (add_countOccurrences_le_append hv _ _))

theorem length_lexWord (n j : ℕ) : (lexWord k n j).length = n := by simp [lexWord]

theorem length_champBlock (n : ℕ) : (champBlock k n).length = n * k ^ n := by
  simp [champBlock, List.length_flatMap, length_lexWord, mul_comm]

theorem length_cpBlock (n : ℕ) : (cpBlock k n).length = 2 * (n * k ^ n) := by
  simp [cpBlock, length_champBlock]; ring

theorem champBlock_map (n : ℕ) : (champBlock k n).map Fin.val =
    (List.range (k ^ n)).flatMap (fun j => (lexWord k n j).map Fin.val) := by
  simp [champBlock, List.map_flatMap]

theorem range_reverse' (m : ℕ) : (List.range m).reverse = (List.range m).map (fun i => m - 1 - i) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_reverse, List.getElem_map, List.getElem_range, List.length_range]

theorem champBlock_reverse_map (n : ℕ) : ((champBlock k n).reverse).map Fin.val =
    (List.range (k ^ n)).flatMap (fun i => (lexWord k n (k ^ n - 1 - i)).reverse.map Fin.val) := by
  rw [champBlock, List.reverse_flatMap, range_reverse', List.flatMap_map, List.map_flatMap]
  rfl

theorem sum_reflect_Ico (g : ℕ → ℝ) {J K : ℕ} (hJ : J ≤ K) :
    ∑ i ∈ range J, g (K - 1 - i) = ∑ j ∈ Ico (K - J) (K - J + J), g j := by
  rw [Finset.sum_Ico_eq_sum_range, show K - J + J - (K - J) = J by omega,
    ← Finset.sum_range_reflect (fun i => g (K - J + i))]
  apply sum_congr rfl; intro i hi; simp only [Finset.mem_range] at hi
  congr 1; omega

theorem count_take_append {v : List ℕ} (hv : v ≠ []) (X Y : List ℕ) (r : ℕ) :
    countOccurrences v (X.take r) + countOccurrences v (Y.take (r - X.length)) ≤
      countOccurrences v ((X ++ Y).take r) := by
  rw [List.take_append]; exact add_countOccurrences_le_append hv _ _

/-- Arithmetic for one half-block: `J = r / n` complete words. -/
theorem half_arith (n r ℓ K : ℕ) (hn : 1 ≤ n) (hJ : r / n ≤ K) (c : ℝ) (hc : 0 ≤ c) :
    c * ((r : ℝ) - n - ℓ * K) ≤ c * (((n + 1 - ℓ : ℕ) : ℝ) * (r / n : ℕ)) := by
  apply mul_le_mul_of_nonneg_left _ hc
  have h1 : r < (r / n) * n + n := Nat.lt_div_mul_add (by omega)
  have h1' : (r : ℝ) < ((r / n : ℕ) : ℝ) * n + n := by exact_mod_cast h1
  have h2 : ((n : ℝ) - ℓ) ≤ ((n + 1 - ℓ : ℕ) : ℝ) := by
    rcases le_total ℓ (n + 1) with h | h
    · rw [Nat.cast_sub h]; push_cast; linarith
    · rw [Nat.sub_eq_zero_of_le h]; push_cast
      have : (n : ℝ) + 1 ≤ ℓ := by exact_mod_cast h
      linarith
  have hJK : ((r / n : ℕ) : ℝ) ≤ K := by exact_mod_cast hJ
  have hJ0 : (0 : ℝ) ≤ ((r / n : ℕ) : ℝ) := by positivity
  have hℓ0 : (0 : ℝ) ≤ ℓ := by positivity
  nlinarith

theorem count_fwd_take (hk : 2 ≤ k) (v : List ℕ) (hv : v ≠ []) (hvd : ∀ d ∈ v, d < k)
    (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ n * k ^ n) :
    ((k : ℝ) ^ v.length)⁻¹ * ((r : ℝ) - n - v.length * (k : ℝ) ^ n) - 2 * (k : ℝ) ^ n ≤
      countOccurrences v (((champBlock k n).map Fin.val).take r) := by
  rw [champBlock_map]
  have hJ : r / n ≤ k ^ n := Nat.div_le_of_le_mul hr
  have h1 := count_take_flatMap hv (fun j => (lexWord k n j).map Fin.val) (n := n) (T := k ^ n)
    (fun i => by simp [length_lexWord]) hJ
  have h2 := sum_count_fwd hk v hv hvd n 0 (r / n)
  rw [zero_add, ← range_eq_Ico] at h2
  have h1' : (∑ i ∈ range (r / n), (countOccurrences v ((lexWord k n i).map Fin.val) : ℝ)) ≤
      countOccurrences v (((List.range (k ^ n)).flatMap
        (fun j => (lexWord k n j).map Fin.val)).take r) := by exact_mod_cast h1
  have h3 := half_arith n r v.length (k ^ n) hn hJ ((k : ℝ) ^ v.length)⁻¹ (by positivity)
  rw [Nat.cast_pow] at h3
  have e : ((k : ℝ) ^ v.length)⁻¹ * (((n + 1 - v.length : ℕ) : ℝ) * ((r / n : ℕ) : ℝ)) =
      ((n + 1 - v.length : ℕ) : ℝ) * ((r / n : ℕ) : ℝ) / (k : ℝ) ^ v.length := by ring
  linarith [h3, h2, h1']

theorem count_rev_take (hk : 2 ≤ k) (v : List ℕ) (hv : v ≠ []) (hvd : ∀ d ∈ v, d < k)
    (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ n * k ^ n) :
    ((k : ℝ) ^ v.length)⁻¹ * ((r : ℝ) - n - v.length * (k : ℝ) ^ n) - 2 * (k : ℝ) ^ n ≤
      countOccurrences v ((((champBlock k n).reverse).map Fin.val).take r) := by
  rw [champBlock_reverse_map]
  have hJ : r / n ≤ k ^ n := Nat.div_le_of_le_mul hr
  have h1 := count_take_flatMap hv (fun i => (lexWord k n (k ^ n - 1 - i)).reverse.map Fin.val)
    (n := n) (T := k ^ n) (fun i => by simp [length_lexWord]) hJ
  have h2 := sum_count_rev hk v hv hvd n (k ^ n - r / n) (r / n)
  rw [← sum_reflect_Ico (fun j => (countOccurrences v ((lexWord k n j).reverse.map Fin.val) : ℝ))
    hJ] at h2
  have h1' : (∑ i ∈ range (r / n),
      (countOccurrences v ((lexWord k n (k ^ n - 1 - i)).reverse.map Fin.val) : ℝ)) ≤
      countOccurrences v (((List.range (k ^ n)).flatMap
        (fun i => (lexWord k n (k ^ n - 1 - i)).reverse.map Fin.val)).take r) := by
    exact_mod_cast h1
  have h3 := half_arith n r v.length (k ^ n) hn hJ ((k : ℝ) ^ v.length)⁻¹ (by positivity)
  rw [Nat.cast_pow] at h3
  have e : ((k : ℝ) ^ v.length)⁻¹ * (((n + 1 - v.length : ℕ) : ℝ) * ((r / n : ℕ) : ℝ)) =
      ((n + 1 - v.length : ℕ) : ℝ) * ((r / n : ℕ) : ℝ) / (k : ℝ) ^ v.length := by ring
  linarith [h3, h2, h1']

/-- One Carton–Perifel block, any prefix of it. -/
theorem count_block_take (hk : 2 ≤ k) (v : List ℕ) (hv : v ≠ []) (hvd : ∀ d ∈ v, d < k)
    (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ (cpBlock k n).length) :
    ((k : ℝ) ^ v.length)⁻¹ * r - (2 * v.length + 6) * (k : ℝ) ^ n ≤
      countOccurrences v (((cpBlock k n).map Fin.val).take r) := by
  set c := ((k : ℝ) ^ v.length)⁻¹ with hc
  have hc0 : 0 ≤ c := by positivity
  have hc1 : c ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ k)))
  have hkn : (0 : ℝ) ≤ (k : ℝ) ^ n := by positivity
  have hnk : (n : ℝ) ≤ (k : ℝ) ^ n := by exact_mod_cast (Nat.lt_pow_self (by omega : 1 < k)).le
  have hℓ0 : (0 : ℝ) ≤ v.length := by positivity
  rw [length_cpBlock] at hr
  have hsplit := count_take_append hv ((champBlock k n).map Fin.val)
    (((champBlock k n).reverse).map Fin.val) r
  rw [← List.map_append] at hsplit
  simp only [List.length_map, length_champBlock] at hsplit
  have hsplit' : (countOccurrences v (((champBlock k n).map Fin.val).take r) : ℝ) +
      countOccurrences v ((((champBlock k n).reverse).map Fin.val).take (r - n * k ^ n)) ≤
      countOccurrences v (((cpBlock k n).map Fin.val).take r) := by exact_mod_cast hsplit
  have hcn : c * n ≤ (k : ℝ) ^ n := le_trans (mul_le_of_le_one_left (by positivity) hc1) hnk
  have hcl : c * (v.length * (k : ℝ) ^ n) ≤ v.length * (k : ℝ) ^ n :=
    mul_le_of_le_one_left (by positivity) hc1
  have hr0 : (0 : ℝ) ≤ countOccurrences v
      ((((champBlock k n).reverse).map Fin.val).take (r - n * k ^ n)) := Nat.cast_nonneg _
  rcases le_total r (n * k ^ n) with h | h
  · have hf := count_fwd_take hk v hv hvd n r hn h
    nlinarith
  · have hf := count_fwd_take hk v hv hvd n (n * k ^ n) hn le_rfl
    have hb := count_rev_take hk v hv hvd n (r - n * k ^ n) hn (by omega)
    have htake : ((champBlock k n).map Fin.val).take r = ((champBlock k n).map Fin.val).take (n * k ^ n) := by
      rw [List.take_of_length_le (by simp [length_champBlock]; omega),
        List.take_of_length_le (by simp [length_champBlock])]
    rw [htake] at hsplit'
    have hcast : ((r - n * k ^ n : ℕ) : ℝ) = (r : ℝ) - ((n * k ^ n : ℕ) : ℝ) := Nat.cast_sub h
    rw [hcast] at hb
    push_cast at hb hf
    nlinarith

theorem count_cpPrefix (hk : 2 ≤ k) (v : List ℕ) (hv : v ≠ []) (hvd : ∀ d ∈ v, d < k) (N : ℕ) :
    ((k : ℝ) ^ v.length)⁻¹ * (cpPrefix k N).length - 2 * (2 * v.length + 6) * (k : ℝ) ^ N ≤
      countOccurrences v ((cpPrefix k N).map Fin.val) := by
  set E : ℝ := 2 * v.length + 6
  have hE : 0 ≤ E := by positivity
  induction N with
  | zero => simp [cpPrefix]; positivity
  | succ N ih =>
    have hb := count_block_take hk v hv hvd (N + 1) _ (by omega) le_rfl
    rw [List.take_of_length_le (by simp)] at hb
    rw [cpPrefix_succ, List.map_append, List.length_append]
    have hadd := add_countOccurrences_le_append hv ((cpPrefix k N).map Fin.val)
      ((cpBlock k (N + 1)).map Fin.val)
    have hadd' : (countOccurrences v ((cpPrefix k N).map Fin.val) : ℝ) +
        countOccurrences v ((cpBlock k (N + 1)).map Fin.val) ≤
        countOccurrences v ((cpPrefix k N).map Fin.val ++ (cpBlock k (N + 1)).map Fin.val) := by
      exact_mod_cast hadd
    have hkk : 2 * (k : ℝ) ^ N ≤ (k : ℝ) ^ (N + 1) := by
      rw [pow_succ]; have : (2 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ k) N]
    push_cast
    nlinarith

theorem range_map_cpSeq (N m : ℕ) (hm : m ≤ (cpPrefix k N).length) :
    (List.range m).map (fun i => (cpSeq k i : ℕ)) = ((cpPrefix k N).map Fin.val).take m := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_take]
  simp only [List.length_map, List.length_range] at h1
  rw [cpSeq_eq N i (by omega), List.getD_eq_getElem]

theorem count_range_lower (hk : 2 ≤ k) (v : List ℕ) (hv : v ≠ []) (hvd : ∀ d ∈ v, d < k)
    (N r : ℕ) (hr : r ≤ (cpBlock k (N + 1)).length) :
    ((k : ℝ) ^ v.length)⁻¹ * ((cpPrefix k N).length + r : ℕ) -
        2 * (2 * v.length + 6) * k * (k : ℝ) ^ N ≤
      countOccurrences v ((List.range ((cpPrefix k N).length + r)).map
        (fun i => (cpSeq k i : ℕ))) := by
  rw [range_map_cpSeq (N + 1) _ (by rw [cpPrefix_succ, List.length_append]; omega),
    cpPrefix_succ, List.map_append, List.take_append, List.take_of_length_le (by simp)]
  simp only [List.length_map, Nat.add_sub_cancel_left]
  have h1 := count_cpPrefix hk v hv hvd N
  have h2 := count_block_take hk v hv hvd (N + 1) r (by omega) hr
  have hadd := add_countOccurrences_le_append hv ((cpPrefix k N).map Fin.val)
      (((cpBlock k (N + 1)).map Fin.val).take r)
  have hadd' : (countOccurrences v ((cpPrefix k N).map Fin.val) : ℝ) +
      countOccurrences v (((cpBlock k (N + 1)).map Fin.val).take r) ≤
      countOccurrences v ((cpPrefix k N).map Fin.val ++ ((cpBlock k (N + 1)).map Fin.val).take r) := by
    exact_mod_cast hadd
  have hkk : 2 * (k : ℝ) ^ N ≤ (k : ℝ) ^ (N + 1) := by
    rw [pow_succ]; have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ k) N]
  have hE : (0 : ℝ) ≤ 2 * v.length + 6 := by positivity
  rw [pow_succ] at hkk h2
  push_cast
  nlinarith

end CPNormal

end NormalNumbers.FiniteState
