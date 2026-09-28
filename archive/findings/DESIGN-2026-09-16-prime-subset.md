# DESIGN 2026-09-16 — prime-subset Lambert series: the audit lap (item 0)

Campaign A (`DIRECTION.md`, attended override 2026-09-15 23:58).  Read-only audit of how the
base-`b` schedule consumes the cutoff `R b K = 2^{2^{m₁ b K}}` and the lower Mertens input, to
decide between (i) "parametrize `R`" and (ii) "freeze a Mertens-in-AP `sorry` leaf".

## Verdict

**(i), but not in the form the override states, and (ii) is needed anyway — in a *quantitative*
form that is a real theorem, not a black box.**

The override's phrasing "any `R ≥ R b K` works if every other use of `R` is an inequality
`R ≤ Y`, `R ≤ X` or monotone in `R`" is **false**: `R` is genuinely capped from above.  What is
true, and what the existing `m₁`-march (`G4EntropyMTower*`) already demonstrates, is that the
schedule constrains the *cutoff exponent* `e` (with `R = 2^{2^e}`, `m₁ ↦ e`) inside a window
whose two ends are separated by a doubly-exponential factor in `K`.  So the correct
generalization is: **make `e` a free parameter and carry it through `G4SchedB*`**, and supply the
`S`-side lower bound as a *rate* hypothesis.

## The four constraints on `e`, with the declarations that impose them

Writing `r = (K²)^K`, `θ = freqSeed b K = b^{−4}(2/b²)^K`, `T = T K`, `m₂ = 8K²`, `m = e + m₂`,
`Mc = 10⁵·T·e`:

1. **Gain (lower, and the ONLY place divergence enters).**  `G4SchedBBudget.main_term_le` needs
   exactly `2(Kr) − 4θ·Sg ≤ −4`, i.e.

       Sg ≥ (2·K·r + 4) / (4θ)          (≈ 500·2^K·K^{2K+1} for b = 3)

   where `Sg = ∑_{p ∈ smallPrimes R P₀} 1/p`.  This is a bound **in `K` alone** — `e` appears
   only because `G4SchedBParams.sum_inv_smallPrimes_ge` supplies `Sg ≥ e·log 2 − 21K² − 4` and
   `m₁` was *defined* to make that exceed the demand.  This is the seam: for a subset `S` the
   demand is unchanged and only the supply shrinks.
2. **Upper harmonic (free under subsetting).**  `sum_inv_smallPrimes_le : Sg ≤ 3e + 5`, consumed
   by `term_b_le`/`term_c_le` (they need `Mc ≳ 44·T·e`).  Restricting to `S` only decreases
   `Sg`, so this direction is monotone in the good direction — **no new work**.
3. **Moment cap (upper, the constraint the override missed).**  `term_b_le` forces
   `Mc ≳ 44·T·e`, and `G4SchedBParams.R_pow_two_Mc_le` (`R^{2Mc} ≤ 2^{10·2^m}`) forces
   `Mc ≤ 2^{m₂}` (`Mc_le_two_pow_m₂`).  Hence

       e ≤ 2^{8K²} / (10⁵·T K)                     (the cap)

   `R` is therefore **not** free upward: raising `R` raises the moment order `Mc`, and `Mc` is
   capped by the `X`-side counting budget.
4. **Rigid gap `m − e = m₂`.**  `G4SchedBParams.dyadic_factor_le` needs
   `1 + log log Y − log log R ≤ 1 + 6K²`, i.e. `(m − e)·log 2 ≤ 6K²`, satisfied by
   `m = e + 8K²` exactly as now; `R_le_Y`, `natLog_R/natLog_Y`, `m₁_le_m` follow.
   `m₁_ge_cube` (`K³ ≤ e`) is a harmless floor.

Full list of the declarations that mention `R b K` and must be re-read with `e`:
`G4SchedBParams` (`m₁ m Mc R Y X m₁_le m₁_ge m_le Mc_le natLog_R log_R log_log_R_ge
sum_inv_smallPrimes_ge sum_inv_smallPrimes_le dyadic_factor_le R_pow_two_Mc_le R_ge_two
Mc_le_two_pow_m₂ Kr_le_T_mul_m₁ m₁_le_m m_sub_m₁`), `G4SchedBBudget` (`main_term_le term_a_le
term_b_le term_c_le`, the `smallPrimes (R b K) P₀` occurrences), `G4SchedBAssembly` (`R_le_Y`,
the `√(4(1+log log Y − log log R)·rowL2)` block, the final `Sched` record at line 478).
The generic-in-`e` versions of the two harmonic bounds **already exist**:
`G4EntropyMTowerHarmonic.sum_inv_smallPrimes_ge_gen / _le_gen {Rg} (hK) (e) (hRg : Rg = 2^2^e)`,
whose own docstring records the same finding ("the cone constrains `m₁` only from below").

## Consequence for `S`

* `e_min(K) ≈ m₁ b K = 1000·b^{2K+4}·K^{2K+1} = exp(O(K log K))`,
  `e_max(K) = 2^{8K²}/(10⁵ T K) = exp(Θ(K²))`.  The window is enormous, so a *constant-factor*
  loss in the Mertens supply is free: **any `S` with
  `∑_{p∈S, p<2^{2^e}} 1/p ≥ c·e − C` for a fixed `c > 0`** is admissible, by taking
  `e ≈ (m₁ b K + C)/c`, which is `≤ e_max(K)` for all large `K`.
* Residue classes `p ≡ a (q)`, `a` a unit: `c = 1/φ(q)` — admissible for every fixed `q`.
* **Mere divergence `∑_{p∈S} 1/p = ∞` is NOT sufficient.**  The demand `exp(O(K log K))` must be
  met before the cap `exp(Θ(K²))`; a set whose partial sums diverge arbitrarily slowly (e.g.
  like `log* `) fails.  So the override's Objective A must be restated with a **rate**: this is a
  proved limitation of the G4 route, not a defect of the formalization.  (It is not a limitation
  of the *theorem*: `c_S` is presumably still disjunctive.  It is this proof that needs the rate.)

## The crux, and why it is now a finite program

The rate for a residue class — Mertens in arithmetic progressions — is not in mathlib, but every
ingredient is:

* `ArithmeticFunction.vonMangoldt.LSeries_residueClass_lower_bound` (mathlib,
  `LSeries/PrimesInAP.lean:348`): `(φ q)⁻¹/(x−1) − C ≤ ∑' n, Λ_a(n)/n^x` for `x ∈ (1,2]`.
* `ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div` (ibid. :181) — the
  prime-power part is `O(1)`, uniformly for `x ≥ 1` by term-wise monotonicity.
* `Chebyshev.psi_le_const_mul_self : ψ x ≤ (log 4 + 4)·x` (mathlib `NumberTheory/Chebyshev.lean`)
  — Chebyshev upper bound, for the tail.
* `Mathlib/NumberTheory/AbelSummation.lean` (`sum_mul_eq_sub_integral_mul₀'`) — partial summation.

The elementary chain (no Tauberian theorem):

1. Put `x = 1 + λ/log N`, `λ := λ_q` a constant.  Split
   `∑_p∈S log p·p^{−x} = ∑_{p≤N} (log p/p)·p^{−(x−1)} + tail ≤ A_S(N) + tail`,
   `A_S(N) := ∑_{p∈S, p≤N} log p / p`.
2. Tail `∑_{n>N} Λ(n) n^{−x} ≤ C₁·e^{−λ}·(log N)/λ` by Abel summation against `ψ(t) ≤ 5.4 t`.
3. LHS `≥ (1/φ(q))·(log N)/λ − C₀` by the mathlib lower bound (minus the `O(1)` prime powers).
4. Choose `λ_q := log(11·C₁·φ(q))` so that `C₁e^{−λ} ≤ 1/(2φ(q))`; then
   `A_S(N) ≥ (1/(2φ(q)λ_q))·log N − C₀`.
5. Partial summation once more, `1/p = (log p/p)·(1/log p)`, gives
   `∑_{p∈S,p<N} 1/p ≥ c_q·log log N − C_q`, which is the interface `MertensRate`.

Steps 2 and 5 are the two real Abel-summation lemmas; 1, 3, 4 are bookkeeping.

## Order of work (revises the override's items, same objective)

* **A0 (this lap):** `src/NormalNumbers/G4MertensAP.lean` — `sumInvPrimesIn`, `sumLogPrimesIn`,
  the `MertensRate` interface, and the chain above as four named `sorry` leaves.
* **A1:** discharge `mertensRate_of_sumLog` (step 5) and `sumLog_tail_le` (step 2); these are
  self-contained Abel-summation facts and do not mention residue classes.
* **A2:** `sumLog_residueClass_ge` from the mathlib `LSeries` bound (steps 1, 3, 4).
* **A3:** the `e`-parametrization of `G4SchedB*` (the declaration list above), consuming
  `MertensRate` in place of `sum_inv_smallPrimes_ge`.
* **A4:** definitions + transport (`G4SubsetWeight.lean`, override item 1) and assembly;
  `S = univ` must re-derive `isDisjunctive_base`.

Items A1–A2 are the crux: they are the only place where anything is *not* a rerun of G4.

---

## 2026-09-16 (campaign B, lap B2d/B2e): `effC` must be `max_{p∣P₀} c_p`, not `frozenCap`

**The obstruction found, and removed.**  `G4UnboundedAvg.effC` was first defined as
`max (A + frozenHarm c P₀) (frozenCap c P₀)` with `frozenCap c P₀ = ∑_{p∣P₀} c_p·v_p(P₀)`.
That branch is *fatal* for the schedule: the schedule's modulus satisfies
`gridQ K N ^ (T·(H−1)) ≤ P₀ ≤ gridQ K N ^ (7T²)` (`G4GridP0Lower`), with
`gridQ K N = (U+K+N+2)!`, so `frozenCap ≥ Ω(P₀) ≈ log P₀` is astronomically larger than the
budget `2^{k₄}` that `hjunk_holdsCE` / `hfarC_holdsE` allow (`100000·C·k₄³ ≤ 2^{k₄}`,
`κ ≤ 2^{k₄}`).  Even for `c ≡ 1` that branch would fail; it only ever appeared multiplied by
`Ω(P₀)` in a *ratio*.

**The fix (this lap, machine-checked).**  The far field consumes `frozenCap` only through
`frozenCap c P₀ ≤ effC · Ω(P₀)`, and `Ω(P₀) = ∑_{p∣P₀} v_p(P₀)`, so

> `frozenCap c P₀ = ∑_{p∣P₀} c_p v_p(P₀) ≤ (max_{p∣P₀} c_p) · Ω(P₀)`  (`frozenCap_le_cMax_mul`)

and `effC c P₀ A := max (A + frozenHarm c P₀) (cMax c P₀)` with
`cMax c P₀ = P₀.primeFactors.sup c`.  Both branches now depend on `P₀` only through its
**largest prime factor** `pMax ≤ U + K + N + 2` (every prime factor of `P₀` divides a power of
`gridQ K N = (U+K+N+2)!`).

**Consequence for B2e — the schedule is feasible for `c_p ≍ log p`, and the budget is the
binding constraint for anything much larger.**  With `K = 4k₄`, `U = gridUmax K N ≤ K³·B^K`,
`B = K²(K+N)+1`, so `log₂ pMax = O(k₄ log k₄)` (for `N` polynomial in `K`).  Hence

* `c_p ≤ A(1 + log₂ p)` ⇒ `cMax ≤ A·(1 + log₂ pMax) = O(k₄ log k₄)` and
  `frozenHarm ≤ cMax · ∑_{p∣P₀} 1/(p−1) = O((k₄ log k₄)²)`, both `≪ 2^{k₄}/(100000 k₄³)`;
* `c_p ≤ A p^θ` (`θ > 0`) ⇒ `cMax ≈ pMax^θ ≈ 2^{θ·O(k₄ log k₄)}`, which is **doubly** past the
  budget — the far field would need `2^{k₄} ≥ 2^{θ k₄ log k₄}`, false for large `k₄`.

So the growth class the closed proof supports is **`c_p = O(polylog p)`**, not `c_p = O(p^θ)`:
the binding constraint is not the junk error term `∑_{p ≤ √N} c_p` (that one is `Tame`'s linear
prefix condition, satisfied even by `c_p ≍ log p` via `Nat.primorial_le_4_pow`) but `cMax`
against the far-field budget.  `k₄` must now be chosen *after* `effC(k₄)`, which is polynomial
in `k₄`, so `exists_good_k₄` has to be re-run with `C := ⌈F(k₄)⌉₊` for an explicit polynomial
`F`; `2^{k₄}` still wins.  That is the next step.

### The quantitative verdict: the achievable growth class is **doubly logarithmic**

Chasing the two budgets to their real slack (this lap, from the schedule files, not conjecture):

| budget | statement | slack |
|---|---|---|
| junk | `hjunk_holdsCE`: `C·(junkShiftBound/|P|)·rowL1 ≤ (1/8)(1/K)2^{-k₄}` | `junkShiftBound/|P| ≤ 5+30K²` and `rowL1 b K ≤ 3(2/3)^K`, so `C ≲ 2^{0.58K}/K³ = 2^{Θ(K)}` |
| far | `hfarC_holdsE`: the four `Ω` pieces are each `≤ 2^{-50K²}`-small | `κ ≲ 2^{Θ(K²)}` |

So **junk binds**: the schedule can pay `effC ≤ 2^{Θ(K)} = 2^{Θ(k₄)}`, no more.  Against that,

* `effC ≤ A + cMax·(1 + log ω(P₀))` and `log ω(P₀) ≤ 5+30K²` (`log_card_primeFactors_P₀_leE`),
  so the demand is `cMax = max_{p∣P₀} c_p ≲ 2^{Θ(K)}/K²`;
* the largest prime dividing `P₀` is of the size of `gridDm ≤ 2^{2·2^{21K²}}`
  (`Sched.gridDm_le_two_pow`), i.e. `log₂ pMax ≈ 2^{21K²}`.

Hence, with `L = log₂ pMax ≈ 2^{21K²}`:

* `c_p = ⌊log₂ p⌋` gives `cMax ≈ 2^{21K²}` — **past the junk budget** `2^{Θ(K)}`. ✗
* `c_p = ⌊log₂ log₂ p⌋` gives `cMax ≈ 21K²` — polynomial, so `cMax·(1+30K²) ≈ 630K⁴ ≪ 2^{1.3k₄}`
  for `k₄ ≥ 40`. ✓  Same for `c_p ≤ A(1 + log₂log₂ p)^s`, any fixed `s`.

**Corrected headline target for campaign B:** `isDisjunctive_weight_of_growth` for
`c_p = O((log log p)^s)` — genuinely unbounded, and the *proved* boundary of this schedule is
that `c_p ≍ log p` is not reachable without re-engineering the junk budget (the `rowL1 ≈ (2/3)^K`
factor is the binding one; enlarging the far slack does not help).

**Next leaf:** `tame_of_log_le` — `c_p ≤ ⌊log₂ p⌋ ⇒ Tame c A`.  `pref` is exact and cheap:
`2^{∑_{p<M} ⌊log₂ p⌋} = ∏ 2^{⌊log₂ p⌋} ≤ ∏_{p<M} p ≤ primorial M ≤ 4^M` (mathlib
`Nat.primorial_le_4_pow`), so `∑ ≤ 2M`.  `tail` is the swap
`⌊log₂ n⌋ = #{j ≥ 1 : 2^j ≤ n}` followed by `∑_{n ≥ m} 1/(n(n−1)) = 1/(m−1)`, giving
`∑_p ⌊log₂ p⌋/(p(p−1)) ≤ ∑_{j≥1} 1/(2^j−1) ≤ 2`.
