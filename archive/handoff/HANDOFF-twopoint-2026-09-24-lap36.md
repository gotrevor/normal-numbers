# HANDOFF twopoint — lap 36: `A(N)` dominated by its Euler product

Branch `wip/twopoint-avg`.  Extends `src/NormalNumbers/TwoPointDelangeLF.lean` (sorry-free,
trust-triple).

## The advance
The recursion of lap 35 carries the absolute companion `A(N) = Σ_{n≤N} μ²(n)u^{ω(n)}/n` in its
error term.  Its size is now bounded, and by **pure index-set inclusion** — no estimate at all:

| result | content |
|---|---|
| `primeFactors_injOn_squarefree` | squarefree naturals are determined by their prime-factor sets |
| **`delangeA_le_prod`** | `A(N) ≤ Π_{p≤N}(1 + u/p)`, `u = ‖z−1‖` |

Mechanism: expand `Π_{p≤N}(1+u/p)` over the subsets of `primesLe N` (`Finset.prod_add`); the
subset `t` contributes `u^{|t|}/∏t`, which is exactly the term of the squarefree integer `∏t`.
Every squarefree `n ≤ N` arises this way (its prime factors are `≤ N`), all terms are
nonnegative, so the sum over `n ≤ N` is a sub-sum.  Combined with Mertens
(`Σ_{p≤N}1/p = log log N + O(1)`) this gives `A(N) ≪ (log N)^u`, the classical size.

## Where `DelangeKernelMean` now stands
Everything arithmetic is done and machine-checked:
* `sum_delangeKernel_divisors`, `sum_zpow_omega_eq` (lap 27) — the hyperbola;
* `delangeKernelTail_of_norm_lt_one` (lap 28) — the `ℓ¹` residue, for `u < 1`;
* `sum_delangeKernel_mul_log` (lap 33) — the Levin–Fainleib identity;
* `delangeSrestr_rec`, `norm_delangeT_le` (lap 34) — restriction removal, working inequality;
* `delangeS_mul_log`, `norm_delangeS_mul_log_le` (lap 35) — Abel summation, the recursion;
* `delangeA_le_prod` (this lap) — the error term's size.

**The one remaining gap is analytic and is known to be so** (lap 35): the recursion is on `‖S‖`
and its fixed point is `(log N)^u`, not `o(1)`.  Reaching `o(1)` requires the complex step — the
cancellation from `Re z < 1` — which is Wirsing's/Halász's theorem proper.  The honest next move
is either to port `Σ_{p≤N} log p/p = log N + O(1)` and attempt the complex integral-equation
argument, or to leave `DelangeKernelMean` as the single named analytic residue with the entire
elementary scaffolding proved beneath it.  It is already the latter, which is a real narrowing of
the 🟡 axiom: `DelangeMean` for `‖t‖_{ℝ/ℤ} < 1/6` is now ONE statement, with its tail half proved
and its arithmetic fully discharged.

## Run to date
lap 28 `92ede26` · 29 `ab283df` · 30 `2d4d2c3` · 31 `6775ae3` · 32 `f29262a` · 33 `3019208` ·
34 `32cc493` · 35 `d847b72` · 36 (this).

C1 itself: measured and pinned by `pairDecorr_iff_unweighted` (lap 31) and the invariance results
(lap 32).

## Confidence
- `twoPointWeightedAvg_all` TRUE 90%; provable with known techniques 3%.
- `DelangeKernelMean` for `‖z−1‖<1` closable in this run: **20%** (all elementary work done; the
  residue is genuinely the complex Wirsing step).
