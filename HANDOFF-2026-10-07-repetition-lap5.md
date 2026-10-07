# HANDOFF 2026-10-07: repetition lap 5 end (branch proof/cantor-repetition, HEAD after 82fb3712)

Supersedes repetition-lap4.  DIRECTION.md CURRENT DIRECTIVE unchanged: prove the assembly.
Tree clean.

## State (CantorRepetition.lean, 3 sorries)
- `repPairPower_of_inputs` (NEW open leaf; the whole remaining assembly content). `repPairArith_of_inputs`
  is now PROVED from it via `repPairArith_of_power` (summability along sched). BarrierAudit waiver moved to it.
- `repPairArith_of_three_dvd` (crux, walls), `card_cycProd_ge_le` (off-path leaf) unchanged.

## Built this lap (all proved), toward `repPairPower_of_inputs`
- Concrete pair `pairNat s t e h' m d = 3ᵉh'(b^{m+d} − bᵐ)`; per-class bounds `pair_class1..6`;
  majorant `pairMaj` (copy terms over `copyRuns`: a_k ≤ u, T < (k+2)a_k);
  `exists_option_le_pairMaj` (six-way disjunction ⇒ option ≤ pairMaj);
  `pair_classes` (disjunction from `pair_classify_rep` at concrete positions; needs b ≤ 3^{s(ρ−1)},
  3ᵉh' < 3^{sm}, ρ(ρ+1) ≤ 4(k₀+3), a_{k₀} ≤ v, W,K ≤ v, four positions not NearCopyBdry).
- Sums: `sum_pairMaj_le` (total), `sum_copyRuns_le` (copy runs filtered a_k ≤ 2sN+e —
  a_L itself is superpolynomial, do NOT use N_L), `copy5_total_le`, `copy6_total_le` (any run set Ks
  with lengths ≤ Nmax), `sum_class_top_le` (Btop under Baker), class sums 1/3.
- Bands: `card_nearCopyBdry_le` (sn), `card_nearCopyBdry_le_of` (injective f) +
  `strictMono_log_mul_pow` (y), `strictMono_log_pair` (T in d).
- Glue: `exists_kappa_sum_le`, `repBound_le_one`, `RepPairPower`, `one_le_sched`.

## Next (in order)
1. Per N: M := big (≥ ρ(2sN+e)), κ from `exists_option_le_pairMaj` on good pairs, `repBound_le_one`
   on bad pairs (diagonal; n<m via sign symmetry `repBound_some_neg`/`Bf_neg`; small m with
   3ᵉh' ≥ 3^{sm} or a_{k₀} > v or W,K > v: O(N·(W+K+const)); band pairs via the band counts:
   O(N(W+K)log N)).  h = ±3ᵉh' (Nat.exists_eq_pow_mul_and_not_dvd).
2. Final arithmetic: W = j+1 with 3ʲ ≈ N^{ε}, K ≈ ε log₃ N; Btop with 9^W ≤ N^{κ/2};
   copy totals Nmax = (L+2)(2sN+e)+1, |Ks| ≤ L+1 = O(log N): all ≤ C N^{2−δ}.
