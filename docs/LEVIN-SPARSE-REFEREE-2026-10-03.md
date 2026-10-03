# Referee: `NormalNumbers.LevinSparse` cited inputs (2026-10-03)

Scope: `src/NormalNumbers/LevinSparse.lean` on `proof/discr`, the two `Literature.*` Props, the leaf `bld_doubleSum_le`, vacuity of the headline, and a numeric tripwire (`probes/levin_sparse_probe.py`).  Sources read in full: Levin, Acta Arith. 88 (1999) 99-111 (matwbn.icm.edu.pl/ksiazki/aa/aa88/aa8821.pdf, 13 pp.); Becher-Lew Deveali 2607.06773v1 **TeX e-print** (`sparse.tex`), §2 in full.

## Verdicts

| Prop / leaf | Verdict | Confidence | Lean fix |
|---|---|---|---|
| `Literature.Levin1999` | **implied** by Levin Thm 2 (q = 2), faithful-or-weaker | 95% | none |
| `Literature.BLDLemma5` | **implied** by BLD Lemma 5 (`lem:combined`); thresholds transcribed correctly; proof re-derived and checks | 93% | none (optional docstring line below) |
| `bld_doubleSum_le` (leaf) | **established in BLD's proof of Lemma 7** (`lem:L2-key`), which bounds the cosine double sum first and never uses the integral again; the leaf still needs its own Lean proof of BLD Lemma 6 (LTE count) plus the combination, which is elementary | 90% | none to the statement |
| `exists_levinRate_oddNormal` | **meaningful**, not vacuous: `DiscLe` is Levin's eq. (1) star discrepancy, the bound tends to 0 so base-2 normality is genuinely implied (`isNormal_of_discLe`), both cited Props are satisfiable (and `Sparse expSet (1/2)` holds) | 90% | framing nit only (below) |

Neither cited Prop is false or vacuous.

## 1. `Literature.Levin1999`

- **Theorem number: Theorem 2** (eqs. (7)-(9)): `α = Σ_m q^{-n_m} Σ_{0≤n<q^{2^m}} q^{-n 2^m} Σ_{i=1}^{2^m} d_i(n) q^{-i}`, `d_i(n) ≡ Σ_j p_{i,j} e_j(n) mod q` (Pascal mod 2), `n_1 = 0`, `n_m = Σ_{r<m} 2^r q^{2^r}`; conclusion "α is normal to base q and `D(N, {αqⁿ}_{n≥0}) = O(N⁻¹ log² N)`".  Theorem 1 is a different construction with `log³`.  Docstring is correct.
- **Normalization.**  Eq. (1): `D(N) = sup_{γ∈(0,1]} |#{0 ≤ n < N : {x_n} < γ}/N − γ|`, i.e. the **star** discrepancy (anchored intervals `[0,γ)`), first `N` terms starting at `n = 0`, divided by `N` (not `N−1`).  Lean `DiscLe (orbit 2 α) N D` is `∀ c ∈ [0,1], |#{n<N : fract(α2ⁿ) ∈ [0,c)}/N − c| ≤ D`: identical (the extra `c = 0` term is `0`).  Even an off-by-one in the starting index would move `D` by `≤ 1/N`, absorbed in the constant.
- **All `N ≥ 2`**: Levin's proof gives the bound "for every `N ≥ q`"; for finitely many smaller `N`, `D ≤ 1` and `log²N/N > 0`, so enlarging `C` is legitimate.
- **q = 2 is the safest case.**  The only base-dependent input is Lemma 4 (unit determinants of Pascal subarrays, "clearly valid also for Pascal's triangle mod 2"); for `q = 2` only the determinant mod 2 matters, and that is 1.
- **x explicit/computable:** yes (digit concatenation; my probe builds it exactly, cross-checked loop vs vectorised).  Not needed: the Prop is existential in `α`.
- **Normality implied by the bound:** yes, `C log²N/N → 0` gives equidistribution of `{2ⁿα}`, hence normality (Wall); that is exactly the leaf `isNormal_of_discLe`.  Levin also states normality.
- Faithful-or-weaker: existential `α`, `q = 2` only, constant made uniform.  **No fix.**

## 2. `Literature.BLDLemma5`

From `sparse.tex` (the PDF garbling is gone in the source):

- **Lemma 1** (`lem:counting`): `S(a,a+k) > 30 log k` for `k ≥ δ₁(a) = (a^{1/ρ}+1)K`, `K ≥ 2` depending only on `S`.
- **Lemma 3** (`lem:obedient`): `δ₃(a) = max(δ₁(a), 10^{30})`.
- **Lemma 4** (`lem:geometric`): `δ₄(a) = 2^{δ₃(a)}`.
- **Lemma 5** (`lem:combined`): sparse `S`, integer `a ≥ 0`, **odd `r ≥ 3` and odd `ℓ > 0`**, every `N ≥ δ₄(a)`:
  `Σ_{n=0}^{N-1} Π_{k>a, k∈S} |cos(π ℓ rⁿ / 2^{k−a})| ≤ 2^{ν₂(r²−1)+2} N/(log N)^{1.005}`.
  The `|cos|` is in the display; the measure plays no role in Lemma 5 (pure Riesz-product sum; `μ` enters only in Lemma 7 via `|μ̂(t)| ≤ Π_{k∈S}|cos(πt/2ᵏ)|`, fair coins on `S`, digit 0 off `S` = `bldPoint` under `coinMeasure`).

Lean vs paper:
- **Bases:** `Odd r`, `3 ≤ r`, `Odd ℓ` (in ℕ, so `ℓ ≥ 1`).  Matches; odd bases only.
- **Product:** `rieszTail S a t` = infimum of the decreasing partial products over `k ∈ (a, M] ∩ S` of `|cos(πt/2^{k−a})|`, i.e. exactly the infinite product.
- **Threshold:** Lean `2^{K(a+1)^{1/ρ} + 10^{30}} ≤ N`.  With `K = 2K_S` (the docstring's `3K_S` also works): `(a+1)^{1/ρ} ≥ max(a^{1/ρ}, 1) ≥ (a^{1/ρ}+1)/2`, so the exponent `≥ max(δ₁(a), 10^{30})`.  Bonus: BLD's step "`N ≥ δ₄(a)` ⇒ `q = ⌊log₂ N⌋ ≥ δ₃(a)`" fails when `δ₃` is non-integer; the Lean threshold's additive `10^{30}` (≥ 1 of slack) makes `⌊log₂N⌋ ≥ δ₃(a)` hold outright.  So the Lean Prop is implied even by a pedantic reading.
- **Sparsity:** Lean `Sparse` (density zero, `0 ∉ S`, `ρ > 0`, `∃ε>0, K₀`, `∀k ≥ K₀ ∀a ≤ k^ρ, (1+ε)·30 log k ≤ S(a,a+k)`) is equivalent to BLD's `liminf_k min_{0≤a≤k^ρ} S(a,a+k)/(30 log k) > 1` (liminf > 1 iff eventually ≥ 1+ε).  BLD's own sparse sets satisfy it.  Faithful.
- **Proof re-derived** (so the cited lemma is believed, not just transcribed): Lemma 3's binomial-tail/entropy step (`H(6/31) ≈ 0.7086 < 0.709`; `4.365 log q − 0.291 > 3 log₂ q` needs `q ≳ 2600`; `(90/31) log q − 6/31 ≥ 2.9 log q` needs `q ≥ e^{60}`, both below `10^{30}`); Lemma 2's order of `r` mod `2^k` (`≤ 2^{ν₂(r²−1)−1}` per residue); Lemma 4's two-period count; Lemma 5's split: on `B` each obedient pair puts `{x/2^{i−a}} ∈ [1/4,3/4)`, `|cos| ≤ 2^{-1/2}`, giving `q^{-1.45 ln 2} = q^{-1.00507}`; constants `K_A = (ln2)² 2^{ν+2} ≈ 0.48·2^{ν+2}`, `K_B ≈ 1.97`, and `K_A + K_B ≤ 2^{ν+2}` because `ν₂(r²−1) ≥ 3`.  All check.  Stray "`N₁ = max(N₀,4)`" in their proof is harmless (`δ₄ ≥ 4`).
- **No fix needed.**  Optional docstring addition: "the additive `10^{30}` also absorbs the `⌊log₂ N⌋ ≥ δ₃(a)` floor step in BLD's Lemma 4; `K = 2K_S` suffices."

### `bld_doubleSum_le`: is it in BLD's proof?

Yes.  `lem:L2-key`'s proof opens with `∫|Σ_{j≤N} e(rʲhx)|² dμ ≤ Σ_{p,q} Π_{k∈S}|cos(πh(rᵖ−r^q)/2ᵏ)|` ("Expanding the square and using `|μ̂(t)| = Π|cos|`") and **every later line bounds that double sum**: diagonal `N`; off-diagonal via `h(rᵖ−r^q) = 2^{ν₂(h)+d(g)} ℓ_g r^q`, small valuations `d(g) ≤ B = ⌊2 log₂ log N⌋` by Lemma 5 + Lemma 6 (`#{g ≤ N : ν₂(r^g−1) = d} ≤ 2^{ν₂(r²−1)−1}N/2ᵈ`), large valuations by `2^B ≥ (log N)²/2`; total `≤ N + 2^{2ν+3}N²/(log N)^{1.005}`, then `/N²` gives `2^{2ν+4}/(log N)^{1.005}`.  The audit's claim is right.  The leaf `∃ C N₀` (fixed `h ≠ 0`) is exactly this with `C = 2^{2ν₂(r²−1)+4}`, `N₀` absorbing BLD's `|h| ≤ log log N` and `N ≥ δ₇`.

What the leaf proof must supply itself (not cited, all elementary, all written in BLD):
1. **Lemma 6** (LTE valuation count) — not in any cited Prop; prove in Lean.
2. **Sign:** `ℓ_g = u·(r^g−1)/2^{d(g)}` is negative when `h < 0`, and `p < q` gives `r^p − r^q < 0`; the Lean `BLDLemma5` takes `ℓ : ℕ`, so apply it to `|ℓ_g|` and use `|cos(−x)| = |cos x|`.
3. **Factor reduction** `rieszTail S 0 (2^a ℓ r^q) = rieszTail S a (ℓ r^q)` (factors `k ≤ a` are `|cos(π·integer)| = 1`; infimum over `M` unchanged).
4. **Threshold growth:** `2^{K(ν₂(h)+⌊2log₂log N⌋+1)^{1/ρ}+10^{30}} ≤ N` eventually (exponent is `O((log log N)^{1/ρ}) = o(log N)`).  BLD's "the inequality `N ≥ f(N)` persists for all `N ≥ δ₇`" (δ₇ the *smallest* such `N`) is a small gap in the paper, irrelevant to the leaf's `∃ N₀` form.
5. Index shift: BLD sums `j = 1..N`, Lean `range N`; irrelevant (Lemma 5 is applied to a full block `0..N−1` after extending the nonnegative inner sum).

`secondMoment_translate_le` (checked on paper): `𝔼|N⁻¹Σ e(hrʲ(α+y))|² = N⁻² Σ_{p,q} e(t_{pq}α) μ̂(t_{pq})`, `μ̂(t) = Π_{k∈S}(1+e(t/2ᵏ))/2`, `|(1+e(s))/2| = |cos πs|`; translation only adds a unimodular phase.  Statement is true (≈98%).  `discLe_fract_add`, `fract_bldPoint_small`, `sIcc_expSet_le`, `sparse_expSet` (count ≥ `100 log((a+k)/(a−1)) − 1 ≥ 50 log k − O(1)` for `a ≤ √k`, all integers 2..~100 hit for small `a`), `rate_arith` (at `N = 2`: LHS-excess `487.8 ≤ 961`): all re-checked, statements true.

## 3. Vacuity / meaning

- `DiscLe` is sane: `DiscLe u 0 D` forces `D ≥ 1`; for `N ≥ 1` it is Levin's eq. (1).  A bound `→ 0` cannot be met by a non-equidistributed orbit, so the headline's rate clause has teeth, and base-2 normality is *derived* (`isNormal_of_discLe`), not assumed.
- `Levin1999`, `BLDLemma5` are both true, hence not vacuous as hypotheses; `BLDLemma5`'s antecedent is inhabited (`Sparse expSet (1/2)`, 95%).
- Headline is not trivially satisfiable: no known number is normal in base 3 with base-2 discrepancy `o(N^{-1/2})`; Lebesgue-random `x` has `D* ≍ √(log log N / N)`; `y ∈ C(S)` alone is not base-2 normal.
- **Framing nit (docstring, not statement):** "far below the `N^{-1/2}` barrier of ABSS for numbers normal in several bases" — ABSS's barrier is a rate *in every base* for *absolutely normal* numbers; here only base 2 has a rate and odd bases are qualitative (DEL gives no rate), even non-power-of-2 bases are excluded.  Suggest: "base-2 rate `O(log²N/N)` for a number also normal in every odd base; the best published multi-base construction (ABSS) has `O(N^{-1/2})` in each base."

## 4. Prior art (10 min, on top of the audit's sweep)

Searched: "all odd bases" + discrepancy + Levin; "normal in two bases simultaneously small discrepancy"; Becher-Slaman *On the normality of numbers to different bases* (1311.0333): discrepancy functions for independent bases are independent, but their construction makes one base **slow** with a computable bound in the others — opposite direction.  Hofer-Larcher 2205.01566 / 2211.04212 (Levin's number, single base, sharpness).  BLD 2607.06773 itself: no discrepancy statements at all; they mention Rauzy (deterministic + normal stays normal) qualitatively.  Nothing found stating "normal in all odd bases with base-2 discrepancy `O(log²N/N)`".  Novelty ~75% (the step "Levin + BLD point, Rauzy-quantified" is short, so folklore risk is real).

## 5. Numeric tripwire: `probes/levin_sparse_probe.py 20`

Exact Levin `α` (Thm 2, q = 2) built from eqs. (7)-(9); `y` = fair coins on `expSet` (3 seeds); exact big-integer addition; exact star discrepancy from sorted points.

| log₂N | N·D*/log²N Levin | Champernowne (control) | Levin + sparse y (max of 3) | Levin + dense-even y (min of 3, control) | √N·D* sparse | √N·D* dense |
|---|---|---|---|---|---|---|
| 8 | 0.161 | 0.83 | 0.50 | 0.55 | 0.97 | 1.05 |
| 12 | 0.215 | 5.04 | 0.69 | 0.54 | 0.75 | 0.58 |
| 16 | 0.117 | 17.7 | 0.92 | 0.78 | 0.44 | 0.38 |
| 18 | 0.102 | 45.7 | 0.77 | 3.16 | 0.24 | 0.96 |
| 20 | 0.137 | 193 | 0.72 | 4.37 | 0.135 | 0.82 |

- Levin: `N·D*/log²N` flat at 0.10-0.25 (Thm 2 visible); Champernowne control blows up (Schiffer `D* ≳ 1/log N`).
- Sparse perturbation: `N·D*/log²N` flat at 0.5-1.1 (≈5x Levin), `√N·D* → 0`.  The shift bound `D*(α+y) ≤ 2D*(α) + 2/N + #B/N` held at every `N` (asserted in the probe; worst ratio 0.148).  At `N = 2²⁰`: change in `D*` ≈ `1.1e-4` vs `#S(N)·log N/N ≈ 0.014` — the "≲" holds with ~100x slack.
- Dense control (fair coins at all even positions): `√N·D*` stays at Θ(1) (0.8-1.0 from 2¹⁷ on), `N·D*/log²N` grows 0.23 → 4.37; the cancel control (`y = fract(−α)`) gives `D* = 1`.  Mechanism refuses the dense sibling as the audit says.
- Caveat on constants: the Lean budget `(log₂N+2)·S(1,N+log₂N+2)/N` is 0.022 at `2²⁰` and only drops below Levin's raw `D*` asymptotically (`expSet` has ~1000 points below 2²⁰; any BLD-sparse set has `≥ 30 log N`).  The proved constant `2C + 2000` is honest but loose; the real one looks like ~0.7.
