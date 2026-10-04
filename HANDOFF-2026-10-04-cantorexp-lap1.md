# HANDOFF 2026-10-04 cantorexp lap 1

**Branch:** work is on `proof/cantorexp-wip` (side branch, written via git plumbing), NOT on
`proof/cantorexp`.  The box mounted `~/src` read-only (only `normal-numbers/.git` rw), so the
worktree could not be edited or `lake build`-ed.  Next lap: if the worktree is writable,
`git merge --ff-only proof/cantorexp-wip` (or checkout it) and run a real `lake build`.

**Build method used:** scratch copy compiled with `lean +leanprover/lean4:v4.33.1` against copies
of the repo's oleans (LEAN_PATH over every `.lake/packages/*/.lake/build/lib/lean`).  Green at HEAD
of the side branch except the 4 disclosed sorries below.

## Done (proved, in CantorExactExponent.lean)
expForced_recur, liouvilleWith_cantorExpReal, ae_frequently_two, abs_sub_ge_of_near,
coins_ball_le, card_near_le, window_freeCount_ge, summable_bc_of_threshold_lt,
freeCount_window_le_of_run, le_freeCount_exp, ae_isNormal_of_coprime_three.
Helpers: schedule structure (expFree_gap, ...), window_ge_gen (window end n ∈ [μ₀m, Λm+1],
BC range defined with μ₀ — no τ), pt_split, abs_pt_sub_ge, coins_cyl, coins_ball_le_gen,
card_near_le_gen, summable_exp_neg_sqrt, summable_sched_bound_exp, test vocabulary
(dgt, pnum, depth = ⌈μ₀m⌉+√m+3, hitP, inBC), hitP_of_close, mass_hitP.

## Open: ae_not_liouvilleWith (crux), exists_exponent_tests, exists_computable_normal_avoid,
not_isNormal_of_three_dvd_of_small.

## Plan for the crux (derive both ae and computable from ONE test family)
bad' j := T1 (j+J) ∨ T2 (j+J) ∨ T3 (j+J), J a fixed (noncomputable-OK) constant.
* T1 m = inBC m ∧ hitP m (done: mass ≤ Kρ^m, firing lemma).
* T2 k = ∃ a' ≤ a_k, digits 0 on [a', a_k) and on [E_k, ⌈μ₀a'⌉+√a').  NEEDED because the frozen
  English sketch misses: r/q = P/3^{a_k} with P ending in zeros has true denominator 3^{a'}.
  Mass ≤ (a_k+1)·2^{-c√a_k+1}.  Deterministic: a' := least j with zeros on [j,a); 3∤P' ⇒ 3^{a'}∣q.
* T3 k = no true coin on [E_k, E_k+2k+8) (free; mass 2^{-(2k+8)}).
* Deterministic assembly: for τ>μ₀, τ'=(μ₀+τ)/2, q∈[3^m,3^{m+1}), k = max with a_k+1 ≤ (τ'-1)m:
  BC case (E_k ≤ m+a_k+2) ⇒ inBC m ⇒ hitP_of_close contradiction; Tri case ⇒
  abs_sub_ge_of_near unless r/q = P/3^a, then T2.
* ae_not_liouvilleWith: Borel–Cantelli on Σ masses, then the deterministic lemma.
* Primrec: follow CantorLiouville.primrec_clBad etc.; ⌈μ₀a⌉₊ for rational μ₀ = (num·a+den-1)/den.
* exists_computable_normal_avoid: SchedFamily derandomizer with W N = exp(-c0 F_exp(log3 N/2))
  + N^{-1/2}, κ b = 16 b^6, Ns=clNs, nr=clNr; hev via le_freeCount_exp (like cl_ev).
