# HANDOFF twopoint — lap 50, 2026-09-25

Branch `wip/twopoint-avg`.  `src/NormalNumbers/TwoPointDelangeOmega.lean`.  Green; new theorems
`#print axioms`-clean.

## Crux
The single remaining obligation of the 🟡 `DelangeMean` axiom (regime `‖z−1‖<1`), lap 49 form:

    ∃B, ∀N, ∀r∈[0,1]:  ‖ Σ_{p ≤ N} (1/p)·( S(N/p; rv) − S(N; rv) ) ‖ ≤ B .

## Landed: the swap, and the weight is small in the bulk
* `delangeW N n := Σ_{p ≤ N, N/p < n} 1/p`.
* **`delangeToeplitz_swap`** — exact:

      Σ_{p≤N} (1/p)·( S(N/p;v) − S(N;v) )  =  − Σ_{n ≤ N} (h_v(n)/n) · w_N(n).

* **`delangeW_le`** — `w_N(n) ≤ (log N + log 4 + 9 − log⌊N/n⌋)/log⌊N/n⌋`, i.e.
  `w_N(n) ≲ log n/log(N/n)`.

## The reading
The obligation is now a **short-interval statement**: the weight is `≈ δ/(1−δ)` for `n ≤ N^{δ}`
(so `0.11` at `n = N^{0.1}`, `1` at `n = √N`) and only reaches the full `log log N` for `n` within
`N/n = O(1)`.  So the whole difficulty of the Delange axiom now lives in

    Σ_{n ≤ N} (h_v(n)/n)·w_N(n)  with `w_N` supported (effectively) on `n` within a bounded
    power of `N`, and `w_N` bounded by an absolute constant on `n ≤ N^{1/2}`.

Note this is the *same* shape as `S` itself but with a weight that suppresses the bulk — which is
exactly why the target is `O(1)` and not `o(1)`.

## Paper-level status of the remaining step (honest)
The absolute majorant still diverges here (`Σ_n μ²u^ω w_N(n)/n ≍ (log N)^u`, lap 47's computation
with the extra weight `−log(1−t)`, `t = log n/log N`, which only changes the constant).  So the
last step is irreducibly a cancellation statement — as every formulation of Wirsing's theorem must
be.  What laps 43–50 achieved is that it is now: (i) a *single explicit sum*, (ii) needing only
`O(1)` where the truth is `o(1)`, (iii) with the bulk suppressed by an explicit weight, and (iv)
with everything else machine-checked.  That is the honest narrowing; the final cancellation is
Wirsing/Halász and remains a multi-session target.

## Next
Two candidate attacks, in order of promise:
1. **Iterate the ODE on the difference.**  `Dp(v) := S(N/p;v) − S(N;v)` satisfies
   `∂_v Dp = Σ_q (1/q)(S^{(q)}(N/(pq);v) − S^{(q)}(N/q;v))` with `Dp(0) = 0`, i.e. the same
   Toeplitz object one scale down.  The integrating factor then gives `‖Dp‖ ≤ sup‖E_{Dp}‖/(L|Re v|)`
   with *zero* initial term.  The question to settle on paper first: the double sum `Σ_{p,q}
   1/(pq) = L²` against the gain `1/L` — so one iteration is neutral and the convergence must come
   from the fact that `q` ranges only up to `N/p`, i.e. from `L_{N/p} < L_N`.
2. If (1) does not close, formalise `w_N`'s smallness into a two-piece split of the swapped sum
   (`n ≤ √N` with `w ≤ C`, `n > √N` with the weight `≤ L` but the kernel mass `A(N) − A(√N)`),
   and see whether the second piece can be re-expressed through `S(√N)` by the same recursion.

## Confidence
- `twoPointWeightedAvg_all` TRUE 90%, provable with known techniques 3% (C1 unchanged).
- `DelangeKernelMean`: **48%** (unchanged; this lap reshapes rather than shrinks the gap, and
  records the honest paper-level status).
