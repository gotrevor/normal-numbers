# HANDOFF 2026-09-21 — `PrimeLambertIndepChar`: two of three `MomentChain` obligations reduced

Branch `wip/g5-prime-subset`.  Commits `e55ffdf` … `5f85e20`.  Continues after the `windowK` lap
(`HANDOFF-2026-09-20-windowK.md`), whose override is DONE; the repo-wide stop gate declined the stop
because `src/` still carries two disclosed sorries, so this session moved to the deeper of them.

## Target

`src/NormalNumbers/PrimeLambertOscillation.lean:95` — `phaseOscillation`, the disclosed node gating the
headline `irrational_primeLambert`.  It is already decomposed in-repo:

```
phaseOscillation ⟸ ChainExists ⟸ TailTruncation ∧ LargePrimeNegligible ∧ BadPrimeFrozen ∧ SmallPrimeDecay
SmallPrimeDecay  ⟸ MomentChain = IndepCharDecay ∧ MomentComparison ∧ IndepMomentSmall
```

`IndepCharDecay` was an unanalyzed leaf: `indepAvg` appeared nowhere outside its defining file.

## Result — new file `src/NormalNumbers/PrimeLambertIndepChar.lean`, sorry-free, all axiom-clean

### `IndepCharDecay` → a Mertens-type prime count

| lemma | content |
|---|---|
| `sum_range_mul_of_coprime` | two-modulus CRT reindexing `range (a·m) ≃ range a ×ˢ range m` |
| `sum_prod_of_pairwise_coprime` | Finset CRT product formula for periodic functions (general purpose) |
| `e_smallSum_eq_prod` | exact pointwise Euler product `e(q S_N) = ∏_p e(q X_p)` |
| **`indepAvg_e_eq_prod`** | **the CRT factorization**: `indepAvg e(q·) = ∏_{p small} localChar p` |
| `norm_e_sub_e` | `‖e x − e y‖ = 2\|sin π(x−y)\|` |
| `norm_localChar_le_one_sub_sin` | `‖localChar p‖ ≤ 1 − sin²(π q (X_p(u)−X_p(v)))/p` (parallelogram law) |
| `primePart_eq_single` | a residue hit by exactly one `(a₀,i₀)` has `X_p = c(a₀)/2^{i₀+1}` |
| `hitResidue`, `dvd_iff_eq_hitResidue` | the class `s_a − (i+1)d_a (mod p)`, and divisibility ⟺ membership |
| `exists_free_residue` | pigeonhole: `p > \|support\|·(J−K)` ⟹ some residue is hit by no pair |
| `exists_single_hit_residue` | `p` class-separating ⟹ `(a₀,i₀)`'s own class is hit by it alone |
| `prod_norm_localChar_le_exp` | `∏(1−δ) ≤ exp(−∑δ)` on any subfamily |
| **`indepCharDecay_of_separating`** | **the assembled reduction** |

Final form, with no analysis in it:

```lean
indepCharDecay_of_separating :
  (∀ N, a₀ N ∈ (C.c N).support) → (∀ N, i₀ N ∈ Ico (C.K N) (C.S N).J) →
  (∀ N, Good N ⊆ (C.S N).small) →
  (∀ N, ∀ p ∈ Good N, SeparatingAt C N (a₀ N) (i₀ N) p) →
  Tendsto (fun N => ∑ p ∈ Good N, siteDefect q ((C.c N) (a₀ N)) (i₀ N) / p) atTop atTop →
  IndepCharDecay C
```

`siteDefect q w i = sin²(π q w / 2^{i+1})` — depends only on the coefficient and site index the chain
designer picks.  `SeparatingAt` is purely arithmetic.  The excluded primes are those dividing one of
finitely many fixed nonzero class differences, so `Good` is cofinite in `small` and the hypothesis is
`∑_{p small} 1/p → ∞`, which the sieve cutoff supplies.

### `IndepMomentSmall` → an explicit growth condition

The draft routes this through a two-sided mgf; unnecessary.  `abs_classSum_le_card` (pre-existing)
already gives the pointwise bound, so `momentBound C N = #small · ‖c‖₁/2^K`, `abs_smallSum_le`,
`abs_rIndepAvg_pow_le` (every moment `≤ momentBound^M`), and

```lean
indepMomentSmall_of_growth :
  Tendsto (fun N => (2π|q|)^{M N}/(M N)! * momentBound C N ^ M N) atTop (𝓝 0) → IndepMomentSmall C M
```

i.e. exactly the draft's `M_N ≫ V_N`.

## Also fixed

A latent name clash: my `primePart_eq_zero` duplicated `PrimeLambertLarge`'s.  The two files were
never co-imported, so `lake build` stayed green while `lake env lean` on a file importing both failed.
Removed mine; the file now imports `PrimeLambertLarge` and reuses `l1` / `abs_classSum_le_card`.

## Refuted / wasted probe

`badPrimeFrozen_of_congr` — proved it before finding `PrimeLambertTail.badPrimeFrozen_of_residue`
already does exactly that.  Reverted; nothing landed.  **Grep the `PrimeLambert*` files before adding
to this chain — it is more complete than it looks.**

## Next attack: `MomentComparison`

The sole remaining `MomentChain` obligation, and the only one still carrying real content — it is
where the arithmetic sample must be compared to the CRT model.  The route:

`S_N` is `modulus C N`-periodic (`smallSum_add_modulus`, pre-existing), so **both** averages in
`MomentComparison` are averages of the *same* periodic function `G(n) = S_N(n)^k`, one over the sample
`P_N` and one over a full period.  Partition `P_N` by residue mod `modulus` (`Finset.sum_fiberwise`)
to get

  `|rSampleAvg x^k − rIndepAvg x^k| ≤ (max |G|) · ∑_{u < Mod} |cnt_N(u)/|P_N| − 1/Mod|`

with `max |G| ≤ momentBound^k`.  So `MomentComparison` reduces to the **L¹ discrepancy of the sample
modulo the CRT modulus** — the draft's `δ_N = N^{−9/10+o(1)}` — with no moments left in it.  That is
the lemma to state and prove next; it is the last place a genuine equidistribution input can hide.

## State of the other src sorry

`src/NormalNumbers/MahlerDriftOne.lean:380` — `exists_prime_nonresidue`, a prime in `(p/3, p/2)` with
a prescribed Legendre symbol.  By reciprocity that is primes in a fixed residue class mod `4p` inside
an interval of length `p/6`: genuinely Linnik-strength, correctly left disclosed.
