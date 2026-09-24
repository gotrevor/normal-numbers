import NormalNumbers.CastingOut
import NormalNumbers.PowerBaseCount
import NormalNumbers.SwingC3Split
import NormalNumbers.SwingC3Rotation

/-!
# Swing at C3: `G4` is rich (every word at positive lower density)

`ConjC3` (frozen in `CastingOut.lean`).  Intermediate rung: positive UPPER density, `IsRichUpper`.
-/

open Finset Filter Topology NormalNumbers.PrimeLambert

namespace NormalNumbers.CastingOut

/-- Every word occurs at a set of positions of positive UPPER density. -/
noncomputable def IsRichUpper (b : ℕ) (x : ℝ) : Prop :=
  open Classical in
  ∀ w : List ℕ, (∀ d ∈ w, d < b) → ∃ c : ℝ, 0 < c ∧
    ∃ᶠ N in atTop, c * N ≤ (((range N).filter (fun n => OccursAt b x w n)).card : ℝ)

theorem isRichUpper_of_isRich (b : ℕ) (x : ℝ) (h : IsRich b x) : IsRichUpper b x := by
  intro w hw
  obtain ⟨c, hc, hev⟩ := h w hw
  exact ⟨c, hc, hev.frequently⟩


/-! ## The amplification lemma: effective disjunctivity ⇒ richness

`isDisjunctive_base` (`G4SchedBAssembly.lean`) is a proof *by contradiction from total
omission*: the omitted cylinder enters only through `exists_cover_of_omit`, which needs the
word to be missing at **every** position in order to place `orbitClosure` inside a Cantor set
of covering number `(bᵍ−1)^M`.  So the theorem as proved guarantees exactly **one** occurrence
and no density whatsoever.

The route from there to `ConjC3` is *effectivity*, not a new density argument.  If the first
occurrence of a length-`L` word is bounded by `C·b^L` then applying that bound to the `b^{L−ℓ}`
extensions `w ++ v` of a fixed length-`ℓ` word `w` produces `b^{L−ℓ}` **distinct** positions
below `C·b^L` at which `w` occurs, which is a positive proportion of `C·b^L`.  That is
`isRich_of_effDisjRate` below, and it reduces `ConjC3` to a purely effective statement.
-/

/-- **Effective disjunctivity at rate `C`**: every base-`b` word `u` occurs at some position
`< C · b^{|u|}`.  This is the optimal rate: there are `b^{|u|}` words to fit in, so no rate
below `b^{|u|}` is possible for all of them. -/
def EffDisj (b : ℕ) (x : ℝ) (R : ℕ → ℕ) : Prop :=
  ∀ u : List ℕ, (∀ d ∈ u, d < b) → ∃ n < R u.length, OccursAt b x u n

/-- Effective disjunctivity at the **optimal rate** `C·b^L`. -/
def EffDisjRate (b : ℕ) (x : ℝ) (C : ℕ) : Prop := EffDisj b x (fun L => C * b ^ L)

open PowerBase in
/-- The big-endian value of `wordOf b m k` is `k` (for `k < bᵐ`). -/
lemma blockNatVal_wordOf (b : ℕ) (hb : 0 < b) :
    ∀ (m k : ℕ), k < b ^ m → blockNatVal b (wordOf b m k) = k := by
  intro m
  induction m with
  | zero =>
      intro k hk
      have : k = 0 := by simpa using hk
      subst this; simp [blockNatVal]
  | succ m ih =>
      intro k hk
      have hq : k / b < b ^ m := by
        rw [Nat.div_lt_iff_lt_mul hb]
        calc k < b ^ (m + 1) := hk
          _ = b ^ m * b := by ring
      have hkey : k / b * b + k % b = k := Nat.div_add_mod' k b
      have := wordOf_append b m (k / b) (k % b) hb (Nat.mod_lt _ hb)
      rw [hkey] at this
      rw [this]
      simp only [blockNatVal, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [show (List.foldl (fun acc d => acc * b + d) 0 (wordOf b m (k / b)))
          = blockNatVal b (wordOf b m (k / b)) from rfl, ih _ hq, hkey]

open PowerBase in
lemma wordOf_injOn (b : ℕ) (hb : 0 < b) {m k k' : ℕ} (hk : k < b ^ m) (hk' : k' < b ^ m)
    (h : wordOf b m k = wordOf b m k') : k = k' := by
  have := blockNatVal_wordOf b hb m k hk
  rw [h, blockNatVal_wordOf b hb m k' hk'] at this
  exact this.symm

/-- Occurrence of `w ++ v` at `n` gives occurrence of `w` at `n`. -/
lemma occursAt_of_append {b : ℕ} {x : ℝ} {w v : List ℕ} {n : ℕ}
    (h : OccursAt b x (w ++ v) n) : OccursAt b x w n := by
  intro j hj
  have hj' : j < (w ++ v).length := by simp; omega
  have := h j hj'
  rwa [List.getElem_append_left hj] at this

/-- Two suffixes of the same length occurring at the same place agree. -/
lemma suffix_eq_of_occursAt {b : ℕ} {x : ℝ} {w v v' : List ℕ} {n : ℕ}
    (hlen : v.length = v'.length)
    (h : OccursAt b x (w ++ v) n) (h' : OccursAt b x (w ++ v') n) : v = v' := by
  refine List.ext_getElem hlen fun j hj hj' => ?_
  have hjw : j + w.length < (w ++ v).length := by simp; omega
  have hjw' : j + w.length < (w ++ v').length := by simp; omega
  have e1 := h (w.length + j) (by simp; omega)
  have e2 := h' (w.length + j) (by simp; omega)
  rw [List.getElem_append_right (by omega)] at e1 e2
  simp only [Nat.add_sub_cancel_left] at e1 e2
  rw [← e1, ← e2]

open Classical in
/-- **The counting core of the amplification.**  Under a first-occurrence rate `R`, the
`bᵐ` extensions `w ++ v` with `|v| = m` all occur below `R (|w| + m)`, at *distinct* positions
(the position determines the digits, hence `v`).  So `w` itself occurs at `≥ bᵐ` positions
below `R (|w| + m)`.  This is the only place effectivity is used, and it is sharp: it is what
forces the rate `O(b^L)` in `isRich_of_effDisjRate` — a rate `C·L·b^L` yields occurrence
density `≍ 1/L → 0` at the horizon and no lower-density conclusion at all. -/
theorem card_occ_ge_of_effDisj {b : ℕ} (hb : 2 ≤ b) {x : ℝ} {R : ℕ → ℕ} (h : EffDisj b x R)
    (w : List ℕ) (hw : ∀ d ∈ w, d < b) (m N : ℕ) (hN : R (w.length + m) ≤ N) :
    b ^ m ≤ (((range N).filter (fun n => OccursAt b x w n) : Finset ℕ)).card := by
  classical
  have hb0 : 0 < b := by omega
  have hex : ∀ k : ℕ, ∃ n, n < R (w.length + m) ∧
      OccursAt b x (w ++ PowerBase.wordOf b m k) n := by
    intro k
    have hdig : ∀ d ∈ w ++ PowerBase.wordOf b m k, d < b := by
      intro d hd
      rcases List.mem_append.1 hd with hd | hd
      · exact hw d hd
      · exact PowerBase.wordOf_lt b m k hb0 d hd
    obtain ⟨n, hn, hocc⟩ := h _ hdig
    exact ⟨n, by simpa using hn, hocc⟩
  choose f hf hfocc using hex
  refine le_trans (le_of_eq (card_range (b ^ m)).symm) ?_
  refine Finset.card_le_card_of_injOn f (fun k hk => ?_) (fun k hk k' hk' hkk => ?_)
  · exact mem_filter.2 ⟨mem_range.2 (lt_of_lt_of_le (hf k) hN), occursAt_of_append (hfocc k)⟩
  · rw [coe_range, Set.mem_Iio] at hk hk'
    have h1 := hfocc k
    have h2 := hfocc k'
    rw [hkk] at h1
    exact wordOf_injOn b hb0 hk hk' (suffix_eq_of_occursAt (by simp) h1 h2)

/-- **Amplification.**  An effective first-occurrence bound at the optimal rate `C·b^L`
upgrades one occurrence per word into positive *lower* density for every word: `IsRich`. -/
theorem isRich_of_effDisjRate (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (C : ℕ) (hC : 0 < C)
    (h : EffDisjRate b x C) : IsRich b x := by
  classical
  intro w hw
  set ℓ := w.length with hℓ
  refine ⟨1 / (C * (b : ℝ) ^ (ℓ + 1)), by positivity, ?_⟩
  have hb0 : 0 < b := by omega
  have hbR : (1 : ℝ) < b := by exact_mod_cast hb
  have key : ∀ m N : ℕ, C * b ^ (ℓ + m) ≤ N →
      b ^ m ≤ ((range N).filter (fun n => OccursAt b x w n)).card :=
    fun m N hN => card_occ_ge_of_effDisj hb h w hw m N (by simpa [hℓ] using hN)
  -- for `N` large take the largest admissible `m`
  filter_upwards [eventually_ge_atTop (C * b ^ ℓ)] with N hN
  set P : ℕ → Prop := fun m => C * b ^ (ℓ + m) ≤ N with hP
  have hP0 : P 0 := by simpa [hP] using hN
  set m := Nat.findGreatest P N with hm
  have hPm : P m := Nat.findGreatest_spec (m := 0) (Nat.zero_le _) hP0
  have hmN : m ≤ N := Nat.findGreatest_le N
  -- `m + 1 ≤ N`, so `¬ P (m+1)`
  have hpow : ∀ j : ℕ, j < b ^ j := fun j =>
    lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_left hb j)
  have hm1N : m + 1 ≤ N := by
    have : b ^ m ≤ C * b ^ (ℓ + m) := by
      calc b ^ m ≤ b ^ (ℓ + m) := Nat.pow_le_pow_right hb0 (by omega)
        _ ≤ C * b ^ (ℓ + m) := Nat.le_mul_of_pos_left _ hC
    have := hpow m
    omega
  have hnot : ¬ P (m + 1) :=
    Nat.findGreatest_is_greatest (P := P) (n := N) (k := m + 1) (by rw [← hm]; omega) hm1N
  have hlt : N < C * b ^ (ℓ + m + 1) := by simpa [hP, Nat.add_assoc] using hnot
  have hcard := key m N hPm
  have hcardR : ((b : ℝ) ^ m) ≤ (((range N).filter (fun n => OccursAt b x w n)).card : ℝ) := by
    exact_mod_cast hcard
  refine le_trans ?_ hcardR
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  have hltR : (N : ℝ) < (C : ℝ) * (b : ℝ) ^ (ℓ + m + 1) := by exact_mod_cast hlt
  calc (N : ℝ) ≤ (C : ℝ) * (b : ℝ) ^ (ℓ + m + 1) := hltR.le
    _ = (b : ℝ) ^ m * ((C : ℝ) * (b : ℝ) ^ (ℓ + 1)) := by ring

/-! ## `ConjC3` reduced to an effective first-occurrence bound

`effDisjG4` is the crux after this lap.  It is *not* a density statement: it asks only that the
FIRST occurrence of a length-`L` base-`b` word in `∑ ω(n)/bⁿ` happen before `C_b · b^L`, the
optimal rate.  `isRich_of_effDisjRate` then supplies the density for free.

Distance to the existing proof.  `isDisjunctive_base` is run through the `ScheduleWitnessB`
schedule `k₄ = 8464·ℓ²·b^{2ℓ+2}`, `K = 4k₄`, `X = 2^K`, and the occurrence it produces sits
inside the sample window `Mx ≈ X = 2^{33856·ℓ²·b^{2ℓ+2}}`.  So the proof as written certifies
the rate `C·b^L` only with `C` doubly exponential in `L` — a first-occurrence bound
`N(b,ℓ) ≤ 2^{2^{O(ℓ)}}` where `effDisjG4` needs `N(b,ℓ) = O_b(b^ℓ)`.  The loss is not at a soft
step: `K` must be large for the determinant/Fourier budget `hbudget`, and `X = 2^K` is forced by
`hbig` (the row-`L¹`/`L²` bounds need `(apSample X P₀ b₀).card` comparable to `2^K`).  Any
attack on `effDisjG4` therefore needs a different mechanism from the §5 schedule — the natural
one being the Erdős–Kac normality heuristic: digit `n` of `∑ ω(n)/bⁿ` is `ω(n) + carry_n mod b`
with `ω(n)` asymptotically `N(log log n, log log n)`, whose mod-`b` discrepancy is
`≍ (log n)^{−2π²/b²}` — see `probes/g4_word_density.py`, which measures the base-4 digit
frequencies drifting `0.088 → 0.114 → 0.145` towards `1/4` for digit `1` as `N` runs
`2·10⁵ → 10⁶ → 5·10⁶`.  That heuristic predicts `N(b,ℓ) = b^{ℓ(1+o(1))}` — enough for
`IsRichUpper`-type rates but *not* obviously for the clean `O_b(b^ℓ)` of `effDisjG4`.

Is the optimal rate the right ask?  It is forced: `card_occ_ge_of_effDisj` is sharp, and any
rate `C·L·b^L` (what a *random* sequence has, by coupon collector) gives occurrence density
`≍ 1/L` at the horizon, hence lower density `0`.  So `effDisjG4` is exactly the de-Bruijn-like
efficiency `N(b,L) = O_b(b^L)`, strictly stronger than what a normal number has.
`probes/g4_first_occurrence.py` measures `N(4,L)/4^L` in the first `2·10⁷` digits of `G₄`:

    L        1     2     3     4     5     6     7
    N/4^L  7.2   411   288   451   747   930   952

— still climbing at `L = 7`, and already two orders of magnitude above the coupon-collector
value `L·log 4 ≈ 10`, because the Erdős–Kac bias makes the rarest length-`L` word have
probability `≈ (q_N)^L` with `4 q_N ≈ 0.58` at `N = 10⁶`.  The self-consistent model
`H = 4^L (4 q_H)^{-L}` with `1 − 4 q_H ≍ (log H)^{−π²/8}` predicts the ratio saturating and then
decaying back to the normal value `≍ L`, so `effDisjG4` as stated is *not* supported by the
numerics.  **Verdict for this lap**: effectivity of first occurrence is not a route to `ConjC3`
unless `G₄` is de-Bruijn-efficient, which it empirically is not; `ConjC3` is irreducibly a
counting statement, and the next attack is the Erdős–Kac one (positive density of `n` with
`ω(n+j) + carry ≡ w_j (mod b)` for `j < ℓ`), not a sharpening of the §5 schedule.
-/

/-- The effective form of the G4 disjunctivity theorem: for each base there is a constant `C_b`
with every length-`L` word occurring before position `C_b · b^L`. -/
def EffDisjG4 : Prop :=
  ∀ b, 3 ≤ b → ∃ C : ℕ, 0 < C ∧ EffDisjRate b (primeLambertAtBase b) C

/-- **`ConjC3` from effectivity** — true, but by the measurement above `EffDisjG4` is itself
false for `G₄`, so this reduction is recorded as a *refuted* route, not as the crux. -/
theorem conjC3_of_effDisj (h : EffDisjG4) : ConjC3 := by
  intro b hb
  obtain ⟨C, hC, hrate⟩ := h b hb
  exact isRich_of_effDisjRate b (by omega) _ C hC hrate

/-! ## The live decomposition: `ConjC3` as a statement about `ω` and its carries

`SwingC3Digits.digitOf_primeLambertAtBase` makes the digits arithmetic:
digit `n` of `G_b` is `(ω(n+1) + omegaCarry b (n+1)) % b`.  So a word `w` occurs at `n` exactly
when `ℓ` consecutive congruences hold, and `ConjC3` becomes a pure counting problem about the
additive function `ω` perturbed by a tail carry — `OmegaCarryRich` below.  This is the crux
after the 2026-09-24 lap, and unlike `EffDisjG4` it is *believed true*: `ω(n)` is asymptotically
`N(log log n, log log n)` (Erdős–Kac), jointly over the `ℓ` shifts, so each residue
`ω(n+1+j) mod b` equidistributes with discrepancy `≍ (log n)^{−2π²/b²}` and the `ℓ` shifts
decorrelate.  The two real obstacles are (i) Erdős–Kac is a CLT, giving equidistribution of
`ω mod b` only at that slowly-decaying discrepancy — enough for positive density but not
uniform in `ℓ` — and (ii) `omegaCarry b k` is a functional of the whole tail `ω(k+1), ω(k+2), …`
and so is *not* independent of the `ω(n+1+j)`; it must be frozen on a positive-density set
before the Erdős–Kac input can be applied.
-/

open Classical in
/-- `w` occurs at `n` in `G_b` iff `ℓ` consecutive `ω`-plus-carry congruences hold. -/
theorem occursAt_primeLambertAtBase_iff {b : ℕ} (hb : 2 ≤ b) (w : List ℕ) (n : ℕ) :
    OccursAt b (primeLambertAtBase b) w n ↔
      ∀ j, ∀ hj : j < w.length,
        (ArithmeticFunction.cardDistinctFactors (n + j + 1)
          + omegaCarry b (n + j + 1)) % b = w[j] := by
  unfold OccursAt
  refine forall_congr' fun j => forall_congr' fun hj => ?_
  rw [digitOf_primeLambertAtBase hb (n + j)]

open Classical in
/-- **The crux.**  The `ω`-plus-carry residue sequence in base `b` hits every word on a set of
positions of positive lower density. -/
def OmegaCarryRich (b : ℕ) : Prop :=
  ∀ w : List ℕ, (∀ d ∈ w, d < b) → ∃ c : ℝ, 0 < c ∧
    ∀ᶠ N in atTop, c * N ≤ (((range N).filter (fun n => ∀ j, ∀ hj : j < w.length,
      (ArithmeticFunction.cardDistinctFactors (n + j + 1)
        + omegaCarry b (n + j + 1)) % b = w[j])).card : ℝ)

/-- The reduction of `ConjC3` to the `ω`-plus-carry counting statement. -/
theorem isRich_of_omegaCarryRich {b : ℕ} (hb : 2 ≤ b) (h : OmegaCarryRich b) :
    IsRich b (primeLambertAtBase b) := by
  classical
  intro w hw
  obtain ⟨c, hc, hev⟩ := h w hw
  refine ⟨c, hc, ?_⟩
  filter_upwards [hev] with N hN
  refine hN.trans (le_of_eq ?_)
  congr 2
  exact Finset.filter_congr fun n _ => (occursAt_primeLambertAtBase_iff hb w n).symm

/-! ### Splitting off the carry

The carry `omegaCarry b k = ⌊∑_{j≥1} ω(k+j) b^{−j}⌋` is not independent of the `ω(n+j+1)`, so it
cannot simply be averaged out.  What the argument actually needs is far less than independence:
only that **one** residue class `g` of the carry survives jointly with every prescribed residue
vector for `ω`.  That is `OmegaCarryJoint`, and `omegaCarryRich_of_joint` shows it suffices —
the word `w` is then realised by solving `r j + g ≡ w_j (mod b)` for the `ω`-residues.

Why `∃ g` and not `∀ g` is the right ask: the carry has size `≈ (log log k)/(b−1) → ∞`, so its
residue is not constant, and pigeonhole already gives *some* class of positive upper density;
`OmegaCarryJoint` asks only that one such class be compatible with arbitrary `ω`-residues.
The two ingredients behind it are (a) joint Erdős–Kac for the `ℓ` shifts `ω(n+1), …, ω(n+ℓ)`
(classical, via the Kubilius model), and (b) the locality of the carry.  On (b) the situation is
much better than it looks: `SwingC3Carry.tailB_split` splits the tail EXACTLY as
`T_b(k) = carryHead b k J + b^{−J} T_b(k+J)`, and `tailB_le` bounds `T_b(m) ≤ m + 2`, so
`tailB_le_log` sharpens this to `T_b(m) ≤ log₂ m + 2` (from `ω(n) ≤ log₂ n`), so
`omegaCarry_sandwich_log` pins `omegaCarry b k` between `⌊carryHead b k J⌋` and
`carryHead b k J + (log₂(k+J)+2)/b^J`.  Taking `J = O(log_b log k)` makes the unseen remainder
`< 1`: the carry is a function of the SHORT window `ω(k+1), …, ω(k+J)` up to one unit, not of
the far future.  So the whole length-`ℓ` digit window at `n` is a function of `ω` on
`[n+1, n+ℓ+O(log log n)]` — an iterated-logarithmically short window, deep inside the Kubilius
regime (which tolerates windows up to `n^{o(1)}`).  `SwingC3Carry.omegaCarry_succ` makes this exact rather than approximate:
`omegaCarry b k = (ω(k+1) + omegaCarry b (k+1)) / b`, so the digit stream of `G_b` is literally
the output of the base-`b` addition automaton run right-to-left on the input stream
`ω(1), ω(2), …`, with `omegaCarry` the carry state.

**Route refuted this lap.**  The automaton form tempts one to reduce the crux to prescribing the
`ω(n+j+1)` *exactly* on a fixed-length window (then the carry recursion determines the digits
outright, given one incoming carry value).  That route is dead: by Landau, `#{n ≤ N : ω(n) = k}
∼ N (log log N)^{k−1} / ((k−1)! log N)`, so every EXACT value of `ω` has density zero, and a
fixed exact vector can never carry positive density.  The prescription must stay modular — which
is why `OmegaCarryJoint` couples `ω`-residues to a carry residue rather than to carry values,
and why it cannot be weakened to a pure statement about `ω mod b` alone: the carry recursion
`(ω + c) / b` sees `ω div b`, not just `ω mod b`.

**The softer route (next attack), set up in `SwingC3Split.lean`.**  Equidistribution of
`ω mod b` is Selberg–Delange-grade, but the crux may not need it, because the small-prime part
of `ω` acts on the orbit as a ROTATION.  Split `ω = ω_{≤P} + ω_{>P}`; then the tail splits,
`T_b(n) = tailSmall P b n + tailLarge P b n` (`tailB_eq_small_add_large`), and `tailSmall` is
periodic modulo `Q = ∏_{p ≤ P} p` (`tailSmall_congr`).  The digit window at `n` is determined by
`T_b(n) mod 1`, so along `n ≡ a (mod Q)` the orbit point is the large-prime tail *rotated by the
constant* `tailSmall P b a`.

Now choose `a` by CRT, using primes `> ℓ` so no prime divides two window entries, to force
`ω_{≤P}(a+j) = k_j` for `j = 1, …, ℓ`: the rotation constant becomes
`∑_{j ≤ ℓ} k_j b^{−j} + (tail)`, whose head runs over EVERY multiple of `b^{−ℓ}` as the `k_j`
run over `{0, …, b−1}`.  Rotating one fixed law by all `b^ℓ` multiples of `b^{−ℓ}` gives every
length-`ℓ` cylinder positive mass.  So every word occurs at positive density **whatever the law
of `tailLarge` is** — the argument never identifies it.  The single input needed is

    `OmegaLargeDecouple`: the law of `tailLarge P b n` along `n ≡ a (mod Q)` is asymptotically
    independent of the class `a`,

fundamental-lemma-of-the-sieve territory rather than Selberg–Delange.  The CRT prescription
half is now done: `SwingC3Split.exists_crt_pattern` produces, for any assignment of primes
`> ℓ` to window slots, a residue `a` whose window `a+1, …, a+ℓ` has exactly the prescribed
primes in each slot (the primes exceed `ℓ`, so each divides at most one window entry and the
slots are independent).  `OmegaLargeDecouple` is what is left.

**The argument in full, for the next lap.**  `orbit_eq_fract_tailB` says the orbit point is
`fract (T_b n)`, and `orbit_eq_rotation` says that along `n ≡ a (mod Q)` it is
`fract (θ(a) + tailLarge P b n)` with `θ(a) = tailSmall P b a`.  A word `w` of length `ℓ` occurs
at `n` exactly when that point lies in `w`'s cylinder, an interval of length `b^{−ℓ}`
(`occursAt_iff_orbit_mem`).  Let `μ_a` be the limit law of `fract (tailLarge P b n)` along the
class.  Then the density of occurrences of `w` is `(1/Q) ∑_a μ_a(I_w − θ(a))`.  Under
`OmegaLargeDecouple` (`μ_a = μ` for all `a`) and with the `θ(a)` running over all `b^ℓ`
multiples of `b^{−ℓ}` — which `exists_crt_pattern` delivers — the translates `I_w − θ(a)`
COVER the circle, so the sum is at least `μ(circle) = 1 > 0` for EVERY `w`.  Positive lower
density for every word, i.e. `IsRich`, with no knowledge of `μ` at all.  Note only covering is
needed, not a partition: a sum of masses always dominates the mass of the union.  That covering
is now proved — `SwingC3Split.exists_shift_mem_cylinder`, with
`fract_add_mem_cylinder_iff` (`fract (y + k/M) ∈ [w/M,(w+1)/M) ↔ (⌊yM⌋ + k) % M = w`) as its
arithmetic core.

One bookkeeping caveat to handle next lap: `θ(a)` is controlled only through the head
`∑_{j ≤ ℓ} ω_{≤P}(a+j) b^{−j}`; the slots `j > ℓ` contribute an uncontrolled `O(π(P) b^{−ℓ})`.
Prescribing `ℓ' > ℓ` slots instead, and fixing `a` modulo `∏_{p ≤ ℓ'} p` so the primes too small
to be steered contribute a constant, reduces the uncontrolled part below `b^{−ℓ}`.

**The route is confirmed numerically** (`probes/g4_rotation_route.py`, base 4, `N = 4·10⁶`,
`P`-primes `{5,7,11,13}`, `Q = 5005`, `ℓ = 4`).  The globally rare word `(1,1,1,1)` has
frequency `2.3·10⁻⁴` overall — sixteen times below the uniform `4⁻⁴ = 3.9·10⁻³` — yet reaches
`7.5·10⁻³` in the best class mod `Q`, i.e. **above** uniform and `33×` the global rate.  The
boosting classes are exactly those with elevated `ω_{≤P}` at the FIRST TWO window positions
(`ω_small(a+1..a+4) = [1,2,0,0]`, `[2,1,0,0]`, `[2,2,0,0]`), while the classes with
`ω_small = [0,0,0,0]` never produce the word at all.  That is the predicted rotation: mass at
`ω(a+j)` for small `j` rotates the orbit point by `≈ k_j b^{−j}`, which is what moves a rare
cylinder onto a common one.  The mechanism is real, not just formally available. -/

open Classical in
/-- **The carry-joint leaf.**  Some residue class `g` of the carry is compatible, at positive
lower density, with every prescribed residue vector for `ω` on a window of length `ℓ`. -/
def OmegaCarryJoint (b : ℕ) : Prop :=
  ∀ ℓ : ℕ, ∃ g : ℕ, ∀ r : ℕ → ℕ, ∃ c : ℝ, 0 < c ∧
    ∀ᶠ N in atTop, c * N ≤ (((range N).filter (fun n =>
      (∀ j < ℓ, omegaCarry b (n + j + 1) % b = g) ∧
      (∀ j < ℓ, ArithmeticFunction.cardDistinctFactors (n + j + 1) % b = r j))).card : ℝ)

/-- **The reduction.**  Solving `r j ≡ w_j − g (mod b)` turns the carry-joint leaf into
`OmegaCarryRich`. -/
theorem omegaCarryRich_of_joint {b : ℕ} (hb : 2 ≤ b) (h : OmegaCarryJoint b) :
    OmegaCarryRich b := by
  classical
  intro w hw
  obtain ⟨g, hg⟩ := h w.length
  obtain ⟨c, hc, hev⟩ := hg (fun j => (w.getD j 0 + b - g % b) % b)
  refine ⟨c, hc, ?_⟩
  filter_upwards [hev] with N hN
  refine hN.trans ?_
  have hsub : ((range N).filter (fun n =>
      (∀ j < w.length, omegaCarry b (n + j + 1) % b = g) ∧
      (∀ j < w.length, ArithmeticFunction.cardDistinctFactors (n + j + 1) % b
        = (w.getD j 0 + b - g % b) % b)))
      ⊆ (range N).filter (fun n => ∀ j, ∀ hj : j < w.length,
        (ArithmeticFunction.cardDistinctFactors (n + j + 1) + omegaCarry b (n + j + 1)) % b
          = w[j]) := by
    intro n hn
    rw [mem_filter] at hn ⊢
    refine ⟨hn.1, fun j hj => ?_⟩
    obtain ⟨hcar, hom⟩ := hn.2
    have hwj : w.getD j 0 = w[j] := List.getD_eq_getElem _ _ hj
    have hwlt : w[j] < b := hw _ (List.getElem_mem hj)
    have hgb : g % b < b := Nat.mod_lt _ (by omega)
    rw [Nat.add_mod, hom j hj, hcar j hj, hwj]
    have hd := Nat.div_add_mod g b
    rw [Nat.mod_add_mod]
    have hrw : w[j] + b - g % b + g = w[j] + b * (g / b) + b := by omega
    rw [hrw, Nat.add_mod_right, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hwlt]
  exact_mod_cast Nat.cast_le.2 (Finset.card_le_card hsub)

/-- The `ω`-residue route's leaf, kept as a proved conditional (`omegaCarryRich_of_joint`).
`conjC3` no longer goes through it: the rotation route below reaches `IsRich` from a strictly
weaker input, since it never has to identify any law.  See `SwingC3Split.lean`. -/
theorem omegaCarryRich_of_carryJoint {b : ℕ} (hb : 2 ≤ b) (h : OmegaCarryJoint b) :
    OmegaCarryRich b := omegaCarryRich_of_joint hb h


/-! ## `ConjC3` from a limit law for the large-prime tail

This packages the rotation route as a single hypothesis.  For each word length `ℓ` it asks for
a modulus `Q`, a family of residue classes `a 0, …, a (b^ℓ − 1)` that are distinct mod `Q` (the
`b^ℓ` steerings produced by `SwingC3Split.exists_crt_pattern`), and a limit law `μ` on the
`b^ℓ` cylinders with total mass `1`, such that along the class `a k` a word `v` occurs with
density `μ((val v + k) mod b^ℓ) / Q`.  The `+ k` is the rotation: class `a k` shifts the law by
`k·b^{−ℓ}` (`SwingC3Split.fract_add_mem_cylinder_iff`).

No property of `μ` beyond `∑ μ = 1` is used.  That is the whole point: the argument never
identifies the law of the large-prime tail, it only needs the SAME law in every class. -/

open Classical in
/-- **The limit-law leaf.**  See `SwingC3Split` for the construction of the classes and the
covering lemma that makes the rotation sweep all of them. -/
def LargeTailLaw (b : ℕ) : Prop :=
  ∀ ℓ : ℕ, ∃ (Q : ℕ) (a : ℕ → ℕ) (μ : ℕ → ℝ), 0 < Q ∧
    (∀ k < b ^ ℓ, ∀ k' < b ^ ℓ, a k ≡ a k' [MOD Q] → k = k') ∧
    (∑ u ∈ range (b ^ ℓ), μ u = 1) ∧
    ∀ v : List ℕ, v.length = ℓ → (∀ d ∈ v, d < b) → ∀ k < b ^ ℓ,
      Tendsto (fun N => (((range N).filter (fun n => n ≡ a k [MOD Q] ∧
          OccursAt b (primeLambertAtBase b) v n)).card : ℝ) / N)
        atTop (𝓝 (μ ((blockNatVal b v + k) % b ^ ℓ) / Q))

/-- Rotating the index by `k` permutes the `b^ℓ` cylinders, so the rotated masses still sum
to `1`. -/
lemma sum_rotate {M V : ℕ} (hM : 0 < M) (μ : ℕ → ℝ) :
    ∑ k ∈ range M, μ ((V + k) % M) = ∑ u ∈ range M, μ u := by
  refine Finset.sum_nbij' (fun k => (V + k) % M) (fun u => (u + (M - V % M)) % M)
    (fun k _ => mem_range.2 (Nat.mod_lt _ hM)) (fun u _ => mem_range.2 (Nat.mod_lt _ hM))
    (fun k hk => ?_) (fun u hu => ?_) (fun k _ => rfl)
  · rw [mem_range] at hk
    have h1 : (V + k) % M + (M - V % M) ≡ V + k + (M - V % M) [MOD M] :=
      Nat.ModEq.add_right _ (Nat.mod_modEq _ _)
    have h2 : (V + k + (M - V % M)) % M = k % M := by
      have hV : V % M < M := Nat.mod_lt _ hM
      have hd := Nat.div_add_mod V M
      have : V + k + (M - V % M) = k + M * (V / M) + M := by omega
      rw [this, Nat.add_mod_right, Nat.add_mul_mod_self_left]
    rw [show ((V + k) % M + (M - V % M)) % M = (V + k + (M - V % M)) % M from h1, h2,
      Nat.mod_eq_of_lt hk]
  · rw [mem_range] at hu
    have hV : V % M < M := Nat.mod_lt _ hM
    have hd := Nat.div_add_mod V M
    have h1 : (V + (u + (M - V % M)) % M) % M = (V + (u + (M - V % M))) % M :=
      Nat.ModEq.add_left V (Nat.mod_modEq _ M)
    have h2 : V + (u + (M - V % M)) = u + M * (V / M) + M := by omega
    rw [h1, h2, Nat.add_mod_right, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu]

/-- **`IsRich` from the limit law.**  The `b^ℓ` classes are disjoint, their occurrence densities
are the rotated masses `μ((val v + k) mod b^ℓ)/Q`, and those sum to `1/Q > 0`. -/
theorem isRich_of_largeTailLaw {b : ℕ} (hb : 2 ≤ b) (h : LargeTailLaw b) :
    IsRich b (primeLambertAtBase b) := by
  classical
  intro v hv
  obtain ⟨Q, a, μ, hQ, hinj, hsum, hlim⟩ := h v.length
  set M := b ^ v.length with hM
  have hM0 : 0 < M := Nat.pow_pos (by omega)
  -- the per-class counting functions
  set f : ℕ → ℕ → ℝ := fun k N =>
    (((range N).filter (fun n => n ≡ a k [MOD Q] ∧
      OccursAt b (primeLambertAtBase b) v n)).card : ℝ) / N with hf
  have hlim' : ∀ k ∈ range M, Tendsto (f k) atTop (𝓝 (μ ((blockNatVal b v + k) % M) / Q)) :=
    fun k hk => hlim v rfl hv k (mem_range.1 hk)
  have hsumlim : Tendsto (fun N => ∑ k ∈ range M, f k N) atTop
      (𝓝 (∑ k ∈ range M, μ ((blockNatVal b v + k) % M) / Q)) :=
    tendsto_finsetSum _ hlim'
  have hval : ∑ k ∈ range M, μ ((blockNatVal b v + k) % M) / Q = 1 / Q := by
    rw [← Finset.sum_div, sum_rotate hM0, hsum]
  rw [hval] at hsumlim
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  refine ⟨1 / (2 * Q), by positivity, ?_⟩
  -- eventually the sum of the class densities exceeds `1/(2Q)`
  have hev : ∀ᶠ N in atTop, 1 / (2 * (Q : ℝ)) < ∑ k ∈ range M, f k N := by
    have hlt : 1 / (2 * (Q : ℝ)) < 1 / Q := by
      rw [div_lt_div_iff₀ (by positivity) hQR]; linarith
    exact Filter.Tendsto.eventually_const_lt hlt hsumlim
  filter_upwards [hev, eventually_gt_atTop 0] with N hN hN0
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  -- the classes are disjoint, so their counts add up inside the full count
  have hcard : ∑ k ∈ range M, (((range N).filter (fun n => n ≡ a k [MOD Q] ∧
      OccursAt b (primeLambertAtBase b) v n)).card)
      ≤ ((range N).filter (fun n => OccursAt b (primeLambertAtBase b) v n)).card := by
    rw [← Finset.card_biUnion]
    · refine Finset.card_le_card fun n hn => ?_
      rw [Finset.mem_biUnion] at hn
      obtain ⟨k, -, hk⟩ := hn
      rw [mem_filter] at hk ⊢
      exact ⟨hk.1, hk.2.2⟩
    · intro k hk k' hk' hne
      refine Finset.disjoint_left.2 fun n hn hn' => ?_
      rw [mem_filter] at hn hn'
      exact hne (hinj k (mem_range.1 hk) k' (mem_range.1 hk')
        (hn.2.1.symm.trans hn'.2.1))
  have hcardR : ∑ k ∈ range M, f k N
      ≤ (((range N).filter (fun n => OccursAt b (primeLambertAtBase b) v n)).card : ℝ) / N := by
    rw [hf]
    simp only
    rw [← Finset.sum_div]
    gcongr
    exact_mod_cast hcard
  have hfin := lt_of_lt_of_le hN hcardR
  rw [lt_div_iff₀ hNR] at hfin
  exact hfin.le

/-! ### Superseded by the weaker pair of leaves in `SwingC3Rotation.lean`

`LargeTailLaw` asks for two things the covering argument does not need: *genuine limits* (so
the analytic leaf would have to identify something) and rotation constants sitting *exactly* on
the grid `b^{−ℓ}·ℤ` (which the slots `j > ℓ` spoil).  `SwingC3Rotation.lean` splits the
obligation into `RotationCover` (a `len`-net of rotation constants — arithmetic, CRT) and
`TailLargeDecouple` (the class-independence of the large-prime tail — no limit asserted), and
`ConjC3` now routes through those.  `isRich_of_largeTailLaw` above stays as the proved record
that the stronger hypothesis also suffices. -/

theorem conjC3 : ConjC3 := fun b hb =>
  isRich_of_rotationRoute (by omega) (rotationRoute_holds b (by omega))

/-- Rung: `G4_b` is upper-rich. -/
theorem isRichUpper_primeLambertAtBase (b : ℕ) (hb : 3 ≤ b) :
    IsRichUpper b (primeLambertAtBase b) :=
  isRichUpper_of_isRich b _ (conjC3 b hb)

end NormalNumbers.CastingOut
