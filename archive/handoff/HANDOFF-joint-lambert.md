# HANDOFF — joint Lambert: FINAL ASSEMBLY DONE (conditional headline proved)

Date: 2026-09-27 (lap D).  Operator objective at the top of `DIRECTION.md`
(final assembly, authorized after `b8a9d11`).

## Result

Both scoped targets are **proved, sorry-free**, in the new
`src/NormalNumbers/JointLambertDisjunctivity.lean` (in the root build):

```
jointLambertDisjunctivity : AGP → PrimeIntervalSupply → JointLambertDisjunctivity
jointWords_two_four       : AGP → PrimeIntervalSupply → JointWords {2, 4}
#print axioms  -- both: [propext, Classical.choice, Quot.sound]
```

The frozen `Prop`s in `JointLambertStatement.lean` are untouched (`78e6048`), so the proved
statement *is* the paper headline of §6: for every `Finset` of bases `≥ 2` and every
prescription `(lengths b, values b)` with `0 < lengths b` and `values b < b ^ lengths b`,
and every `N`, there is one offset `n ≥ N` with
`⌊b ^ lengths b * orbit b (erdosBorweinAtBase b) n⌋ = values b` for **every** `b` in the set.

`AGP` and `PrimeIntervalSupply` are unchanged and remain *hypotheses*.  No new analytic
input, no assumed digit bridge, no coprimality or multiplicative-independence hypothesis, no
per-coordinate offset.  The empty base set is handled (`n := N`).  All six previously frozen
JointLambert modules are byte-identical to their pins (`git diff` empty):
`Statement` @ `78e6048`, `EncodingProof` @ `7f05cb2`, `Arithmetic` @ `566586a`,
`PrimeSelection` @ `7dc2522`, `Tail`/`TailBounds` @ `b8a9d11`.

## How it is proved

Three new lemmas, then the assembly.

1. **`summable_shift_tail`** — `j ↦ τ(N+1+j)/b^(j+1)` is summable, by shifting
   `CastingOut.summable_lambert` and multiplying by `b^N`.  Nothing about the offset series
   is reasoned about vacuously.
2. **`lambertVal_mul_pow_eq`** — `lambertVal b w * b^N = (integer head) + Σ'_j w(N+1+j)/b^(j+1)`,
   the exact split of `floor_lambertVal_mul_pow` *before* taking a floor, which is what the
   digit reading needs.
3. **`floor_digit_of_common_offset`** — the **digit bridge**.  At offset `N` (word starts at
   digit `N+1`), with `b ∣ c`, `v < b^ℓ`, `r < k`,
   `c^(j+1) ∣ τ(N+1+j)` for `j < k`, `j ≠ r`, and `τ(N+1+r) = 2a`:
   * the prefix `Σ_{m ≤ N} τ(m) b^{N-m}` is an integer (lemma 2);
   * the shifted series splits at `k` by `Summable.sum_add_tsum_nat_add` (lemma 1) — the
     reindexing `N+1+(t+k) → N+1+k+t`, `(t+k)+1 → k+t+1` is done explicitly;
   * every killed slot `j ≠ r` is an **integer**: `b^(j+1) ∣ c^(j+1) ∣ τ(N+1+j)`, so
     `τ(N+1+j)/b^(j+1) = ((τ(N+1+j)/b^(j+1) : ℕ) : ℝ)` by `Nat.cast_div`;
   * the survivor slot contributes exactly `2a/b^(r+1)`;
   * so `Int.fract (E_b · b^N) = {2a/b^(r+1)} + T_b` with `T_b` the base-`b` tail, using
     `Int.fract_intCast_add` twice and `Int.fract_eq_self` (the sum is in `[0,1)` because
     `{2a/b^(r+1)} < (v+1/2)/b^ℓ` and `T_b < (1/2)/b^ℓ` and `v+1 ≤ b^ℓ`);
   * `Int.floor_eq_iff` then gives the window value `v`, the carry being controlled by
     exactly the interior margin `1/2` of the cylinder.
4. **`jointWords_of_inputs`** — the assembly.  `c := ∏_{b ∈ S} b` is the common multiple
   (`Finset.dvd_prod_of_mem` gives `b ∣ c`; `Finset.single_le_prod'` gives `2 ≤ c` for
   nonempty `S`), which is a proved common multiple of the bases in place of the `lcm`.
   The one positive common margin over the finite set is `ε := 1/P` with
   `P := ∏_{b ∈ S} b ^ lengths b`; `Finset.single_le_prod'` gives `b^{lengths b} ≤ P`, hence
   `ε/2 ≤ (1/2)/b^{lengths b}` in every coordinate simultaneously — no `inf'` needed.
   Interior cylinders are `(v/b^ℓ, (v+1/2)/b^ℓ)`, strictly inside the digit cylinder, so
   `evenEncoding` yields `s ≥ 2`, `a ≥ 2` hitting all of them; put `r := s-1 ≥ 1`.
   `exists_joint_small_tail_all_bases … hε 0 (N+1)` then supplies `k` and `n ≥ N+1`, and
   `n = M+1` puts the common digit offset at `M ≥ N`.  Every coordinate is read at that one
   `M` by lemma 3.

## Boundary — what is and is not claimed

* **Conditional.**  `AGP` and `PrimeIntervalSupply` are Lean hypotheses.  This is not an
  unconditional Lean theorem.  Formalizing those inputs is a separate campaign.
* **Qualitative.**  Existence of a common offset `≥ N` for every `N`, i.e. infinitely many
  simultaneous occurrences.  The paper's quantitative count
  `N exp{-C(log log N)^3}` is **not** formalized.
* Not normality, and not positive density.
* Novelty is **not** confirmed by formalization; §1 of the paper records the prior scalar art.
* The dependent-base controls kept as checks: `jointWords_two_four` (headline level) and
  `evenEncoding_two_four`, `evenEncoding_two_three_six` (encoder level).

## Next work, if the campaign is resumed

1. The quantitative §6 count (needs the candidate-set cardinality already proved in
   `JointLambertPrimeSelection` carried through the pigeonhole with a Markov bound).
2. Formalize `AGP` / `PrimeIntervalSupply` from `PrimeNumberTheoremAnd`, discharging the
   two hypotheses.

The remaining `sorry`s in `src/` are the same pre-existing designated-open holes
(`SwingC2`, `SwingC1Log`, `SwingC3Rotation`, `PairDecoupleProve`, `MahlerDriftOne`,
`PrimeLambertOscillation`), all out of scope by the operator objective; the repo-wide sorry
gate is unsatisfiable here by construction and the host scoped predicate is the one that
should recognise completion.
