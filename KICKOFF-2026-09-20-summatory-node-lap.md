# KICKOFF 2026-09-20 — ONE summatory node under the whole SD sector (`RoughSummatory`)

Branch `wip/g5-prime-subset`.  Engine Opus/low.  New file `src/NormalNumbers/G4WiringSummatory.lean`,
importing `NormalNumbers.G4WiringRough`.  **Do not change any existing statement**; add new ones.
Operator: Ren, attended; fired under Trevor's standing "go" (2026-09-20).

## Why

`HANDOFF-2026-09-20-parity-reduction.md` §6 / "Next steps" item 2: every window and half-window sum in the
two surviving nodes (`RoughIndependenceAt h 2`, `ParityDiscrepancy h`) is a difference of partial sums of the
rough phase product.  One Selberg–Delange-with-shifts statement about those partial sums, **restricted to
parity classes**, yields both nodes - and the parity-class form dissolves the bootstrap circularity flagged in
item 1 (the lower bound on `∏‖fullSiteMean‖` comes out of the node's own main terms).  Blueprint probe 11
(`probes/summatory_node.py`, data `probes/data-2026-09-20-summatory-node*.txt`) supports the node:

* exponent `κ_k = Σ_{j≤k}(e(h/4^j) − 1)`: at `M = 2^26` the fitted exponent lags the prediction by the
  **same** amount as the known-answer control `k = 1` (classical SD for `ω` over odd primes): `h=1`, `k=5`:
  fitted `−1.059+1.895i` vs predicted `−1.081+1.511i`; control `−1.034+1.327i` vs `−1+1i`.
* `Q_k = R_k(M)/(M (log M)^{κ_k})` moves by `< 1%` per doubling at `2^26` for `h = 1, 3`; the prefix ratios
  `|Q_k/Q_{k−1}|` flatten to `1.0015 / 0.992 / 1.005` at `k = 5` (`PrefixLimit`'s content, exponents cancel).
* singleton relative secondary term `|D|/|Q|`: `0.22, 0.015, 0.002, 0.0005, …` - geometric in `k` (`~4^{-k}`),
  as analyticity in `z_k` with the exact identity at `z_k = 1` predicts.  The PREFIX secondary is NOT geometric
  (`0.26` flat in `k`) - which is why the node carries `C/log M` for prefixes and `C·4^{-k}/log M` for sites.
* `|c_{\{k\}}|`: `4.91, 1.15, 1.009, 1.0006, 1.00004` → 1 geometrically; parity-class ratios `→ 1` for sites.
  For prefixes the parity ratio sits at `0.928 / 0.961 / 1.051` (`h = 1/3/5`) - the size of the expected
  `O(1/log M)` scale term, so the equal-constant clause is *consistent, not sharply tested*.

## Vocabulary (fixed; use these names)

From `G4WiringRough.lean`: `roughPhase h j n = ePhase (h · ω_{>2}(n+j) / 4^j)`, `roughSiteMean N h j 2`,
`roughWindowMean`, `roughPrefixMean`, `winMean`, `parityDisc`, `roughSum`, `RoughIndependenceAt`,
`ParityDiscrepancy`, `smoothNonvanishingAt_two`, `exists_smoothSiteMean_lower`, `parityDisc_eq_scale`,
`roughSiteMean_eq_roughSum`, `norm_ofReal_one_add_cpow_sub_one_le`, `isNormal_G4_of_parity`,
`windowJ_div_tendsto_zero`, `windowJ_log_div_tendsto_zero`.  From `G4WiringCRT.lean`: `ePhase`,
`fullSiteMean N h j = 𝔼_{[N,2N)} ePhase(h ω(n+j)/4^j)` (FULL `ω`), `windowJ`, `ChowlaSector`, `WindowDecay`,
`SiteDecayFull`.  `Complex.cpow` for `(log M : ℂ)^κ`; `Real.rpow` for `(log M)^(κ.re)`.

## The ratified new statements (verbatim; only their proofs are yours)

```lean
/-- The rough phase product over a site set `s` at `m`: `∏_{j∈s} e(h ω_{>2}(m+j)/4^j)`. -/
noncomputable def roughProd (h : ℤ) (s : Finset ℕ) (m : ℕ) : ℂ := ∏ j ∈ s, roughPhase h j m

/-- Summatory function of `roughProd` over `m < M` in the residue class `a mod 2`. -/
noncomputable def roughClassSum (h : ℤ) (s : Finset ℕ) (a M : ℕ) : ℂ :=
  ∑ m ∈ (Finset.range M).filter (fun m => m % 2 = a), roughProd h s m

/-- The Selberg–Delange exponent of a site set: `Σ_{j∈s} (e(h/4^j) − 1)`. -/
noncomputable def sdExponent (h : ℤ) (s : Finset ℕ) : ℂ :=
  ∑ j ∈ s, (ePhase ((h : ℝ) / (4 : ℝ) ^ j) - 1)

/-- Main term of one parity class at scale `M`: `(c/2) · M · (log M)^κ`. -/
noncomputable def sdMain (c κ : ℂ) (M : ℕ) : ℂ :=
  c / 2 * (M : ℂ) * (((Real.log M : ℝ)) : ℂ) ^ κ

/-- **The summatory node (frozen conjecture; blueprint probe 11).**  Selberg–Delange with shifts for the
rough phase product, on each parity class, for the prefixes `[1,k]` and the singletons `{k}`,
`1 ≤ k ≤ windowJ M`: main term `(c_s/2)·M·(log M)^{κ_s}` with `κ_s = sdExponent h s`, the SAME constant
`c_s` on both classes; relative error `C/log M` for prefixes and `C·4^{-k}/log M` for singletons
(analytic in `z_k`, exact at `z_k = 1`); constants bounded above, bounded away from `0`, and
`c_{\{k\}} → 1` geometrically. -/
def RoughSummatory (h : ℤ) : Prop :=
  ∃ (c : Finset ℕ → ℂ) (B C δ : ℝ), 0 ≤ C ∧ 0 < δ ∧
    (∀ s, ‖c s‖ ≤ B) ∧
    (∀ k, 1 ≤ k → δ ≤ ‖c (Finset.Icc 1 k)‖ ∧ δ ≤ ‖c {k}‖) ∧
    (∀ k, 1 ≤ k → ‖c {k} - 1‖ ≤ B * ((1:ℝ)/4) ^ k) ∧
    ∀ᶠ M : ℕ in atTop, ∀ a, a < 2 → ∀ k, 1 ≤ k → k ≤ windowJ M →
      ‖roughClassSum h (Finset.Icc 1 k) a M
          - sdMain (c (Finset.Icc 1 k)) (sdExponent h (Finset.Icc 1 k)) M‖
        ≤ C / Real.log M * ((M : ℝ) * Real.log M ^ (sdExponent h (Finset.Icc 1 k)).re)
      ∧ ‖roughClassSum h {k} a M - sdMain (c {k}) (sdExponent h {k}) M‖
        ≤ C * ((1:ℝ)/4) ^ k / Real.log M * ((M : ℝ) * Real.log M ^ (sdExponent h {k}).re)

/-- Both classes together give the plain partial sum. -/
theorem roughClassSum_zero_add_one (h : ℤ) (s : Finset ℕ) (M : ℕ) :
    roughClassSum h s 0 M + roughClassSum h s 1 M = ∑ m ∈ Finset.range M, roughProd h s m

/-- The exponent is additive along prefixes. -/
theorem sdExponent_Icc_succ (h : ℤ) (k : ℕ) :
    sdExponent h (Finset.Icc 1 (k+1)) = sdExponent h (Finset.Icc 1 k) + sdExponent h {k+1}

/-- The window quantities are differences of the summatory function. -/
theorem roughPrefixMean_eq_classSum (N : ℕ) (h : ℤ) (k : ℕ) (hN : 0 < N) :
    roughPrefixMean N h k
      = ((roughClassSum h (Finset.Icc 1 k) 0 (2*N) + roughClassSum h (Finset.Icc 1 k) 1 (2*N))
          - (roughClassSum h (Finset.Icc 1 k) 0 N + roughClassSum h (Finset.Icc 1 k) 1 N)) / N
theorem roughSiteMean_eq_classSum (N : ℕ) (h : ℤ) (k : ℕ) (hN : 0 < N) :
    roughSiteMean N h k 2
      = ((roughClassSum h {k} 0 (2*N) + roughClassSum h {k} 1 (2*N))
          - (roughClassSum h {k} 0 N + roughClassSum h {k} 1 N)) / N

/-- **Wiring 1**: the summatory node gives the rough factorisation (`c(J) = c_{[1,J]} / ∏_{j≤J} c_{\{j\}}`). -/
theorem roughIndependenceAt_two_of_summatory {h : ℤ} (hS : RoughSummatory h) : RoughIndependenceAt h 2

/-- **Wiring 2**: the summatory node gives the parity node (the class main terms cancel exactly; the
lower bound on `∏‖fullSiteMean‖` comes from the node's own main terms and `|cos(πh/4^j)| > 0` off the
Chowla sector). -/
theorem parityDiscrepancy_of_summatory {h : ℤ} (hh : h ≠ 0) (hc : ¬ ChowlaSector h)
    (hS : RoughSummatory h) : ParityDiscrepancy h

/-- **Headline**: off the Chowla sector the G₄ window law rests on ONE analytic input. -/
theorem isNormal_G4_of_summatory
    (hSD : ∀ h : ℤ, h ≠ 0 → ¬ ChowlaSector h → RoughSummatory h)
    (hCh : ∀ h : ℤ, h ≠ 0 → ChowlaSector h → WindowDecay h)
    (hSite : SiteDecayFull) : IsNormal 4 (primeLambertAtBase 4)
```

## The mathematics of the two wirings (do this, in this order)

Write `L = log N`, `x = log 2 / L`, so `log (2N) = L(1+x)`.  A class sum over `[N,2N)` is the node at `2N`
minus the node at `N`; the main term is `(c/2)·N·L^κ·(2(1+x)^κ − 1)`, and
`‖2(1+x)^κ − 1 − 1‖ = 2‖(1+x)^κ − 1‖ ≤ 4‖κ‖x` by `norm_ofReal_one_add_cpow_sub_one_le` (needs `‖κ‖x ≤ 1`,
true eventually since `‖κ‖ ≤ 2·windowJ N` and `windowJ N · log 2 / log N → 0`:
`windowJ_log_div_tendsto_zero`).  Also `‖(log M : ℂ)^κ‖ = (log M)^(κ.re)` (`Complex.norm_cpow_eq_rpow_re_of_pos`),
and `windowJ N ≤ windowJ (2N)` (monotone in `N`; `Nat.log` is monotone).

**Wiring 1.**  Window mean `roughPrefixMean N h J = roughWindowMean N J h 2` (`roughWindowMean_eq_winMean`)
`= c_{[1,J]} L^{κ_J}(1 + O(1/L))`; each site mean `= c_{\{j\}} L^{z_j−1}(1 + e_j)` with
`‖e_j‖ ≤ C'·4^{-j}/L` (node singleton clause + the `(1+x)^{z_j −1}` step, both geometric in `j`).  Since
`κ_J = Σ_{j≤J}(z_j − 1)` (`sdExponent_Icc_succ` by induction), `∏_j L^{z_j−1} = L^{κ_J}` exactly.  Set
`c J := c_{[1,J]} / ∏_{j≤J} c_{\{j\}}`; `‖∏ c_{\{j\}}‖ ≥ δ' > 0` uniformly in `J` from `δ ≤ ‖c_{\{j\}}‖` and
`‖c_{\{j\}} − 1‖ ≤ B 4^{-j}` (finitely many factors below `1/2`, the rest `≥ 1 − B4^{-j}`, product of
`(1 − B4^{-j})` bounded below via `prod_one_add_le_exp`-style estimates - compare the lap's own
`prod_one_add_le_exp`).  Then `∏(1+e_j) − 1 = O(Σ‖e_j‖) = O(1/L)` uniformly in `J`, and the frozen
inequality follows with `∏‖roughSiteMean‖ ≥ (δ'/2) L^{Re κ_J}` eventually.

**Wiring 2.**  `parityDisc N j r = c_o·Σ_{2∣n+j} r − c_e·Σ_{¬2∣n+j} r` with `c_o + c_e = N`, `|c_o − c_e| ≤ 1`.
Write it as `(N/2)(Σ_even − Σ_odd) + ε` with `‖ε‖ ≤ N` (each phase has norm `1`, so each class sum has norm
`≤ N`).  Both class sums come from the node (class index: `n` even ⇔ `m ≡ 0`, careful with the `n+j` vs `m`
bookkeeping - `roughProd h {j} m = roughPhase h j m`, and the node's class is the class of `m` itself); their
main terms are IDENTICAL, so the difference is bounded by the two error terms.  For `j ≥ 1` (site clause) that
is `≤ 2·C4^{-j}/L · N L^{Re(z_j−1)}·(1+O(x))`; for `j = 0` (window clause; `ePhase (h · roughTail 2 J n)
= roughProd h (Icc 1 J) n` via `ePhase_roughTail_prod` or directly) it is `≤ 2C/L · N L^{Re κ_J}`.
The `ε ≤ N` term is absorbed: `N ≤ (C/L)·N²·L^{Re κ − 1}` eventually, uniformly since `Re κ ≥ −2·windowJ N`
is NOT bounded - so do it honestly: `Re(z_j − 1) ≥ −2` for the site clause, and for the window clause use
`Re κ_J ≥ −2 Σ_j ‖z_j − 1‖·… ≥ −2·(2π|h|)·Σ 4^{-j} ≥ −(4π|h|)/3`, a bound independent of `J`
(`‖ePhase t − 1‖ ≤ 2π|t|`: `Complex.norm_exp_I_mul_ofReal_sub_one_le` or the file's own bound).
The RHS of `ParityDiscrepancy` is in terms of `‖fullSiteMean N h j‖`: `fullSiteMean = (α_j·Σ_{even n+j} rough
+ Σ_{odd n+j} rough)/N` with `α_j = ePhase(h/4^j)` (`omegaR = omegaLe 2 + omegaAbove 2`,
`omegaLe 2 (n+j) = 1 ⇔ 2 ∣ n+j`, cf. `fullPhase_eq`), so its main term is `((1+α_j)/2)·c_{\{j\}}·L^{z_j−1}`
and `‖(1+α_j)/2‖ = |cos(πh/4^j)| ≥ δ_h > 0` off the Chowla sector, `→ 1` geometrically
(`smoothNonvanishingAt_two`'s ingredients; `exists_smoothSiteMean_lower`).  Hence
`∏_{j≤J}‖fullSiteMean N h j‖ ≥ δ'' L^{Re κ_J}` and `‖fullSiteMean N h j‖ ≥ δ'' L^{Re(z_j −1)}` eventually,
uniformly in `J = windowJ N`, which converts the node's error terms into the frozen RHS.

## Leaves, in order (commit a compiling skeleton with named sorries FIRST)

1. Definitions, `roughClassSum_zero_add_one` (`Finset.sum_filter_add_sum_filter_not`), `sdExponent_Icc_succ`
   (`Finset.sum_Icc_succ_top`), `roughPrefixMean_eq_classSum`, `roughSiteMean_eq_classSum`
   (`Finset.range (2N) = range N ∪ Ico N (2N)`; `Finset.sum_Ico_eq_sub`).
2. Analytic toolbox: `norm_sdMain`, the `2(1+x)^κ − 1` step, `‖ePhase t − 1‖ ≤ 2π|t|`,
   `‖sdExponent h {k}‖ ≤ 2π|h|/4^k`, `(sdExponent h (Icc 1 k)).re ≥ −4π|h|/3`, monotonicity of `windowJ`.
3. Lower bounds on products of site constants uniform in `J` (`δ'`), and on `∏‖fullSiteMean‖` (`δ''`).
4. `roughIndependenceAt_two_of_summatory`.
5. `parityDiscrepancy_of_summatory`.
6. `isNormal_G4_of_summatory := isNormal_G4_of_parity (fun h hh hc => ⟨…, …⟩) hCh hSite`.

`RoughSummatory` is **never proved** - it is the frozen node.  If leaf 3 or 5 resists after a real attempt,
leave the resisting piece as a named `sorry` with a comment saying exactly which inequality is missing and
finish the wiring on top of it - the wiring theorems are the deliverable.  `native_decide`, long
`omega`/`nlinarith` steps, deprecations are all fine.  Report the crux advance, not the sorry count.

Ground rules: `lake build NormalNumbers.G4WiringSummatory` green before every commit; `git-safe` only; new
file only (touch `G4WiringRough.lean`/`G4WiringCRT.lean` only to *add* a lemma if a proof genuinely needs a
private helper made public - never change a statement).  End with `HANDOFF-2026-09-20-summatory-node.md`
(what is proved, what resists, and whether the probe's parity-class clause deserves a sharper test).  When
the override at the top of `DIRECTION.md` is done, STOP - the campaign-B section below it is CLOSED.
