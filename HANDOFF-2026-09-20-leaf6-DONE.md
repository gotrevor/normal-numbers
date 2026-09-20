# HANDOFF 2026-09-20 — sparse-subset lap, leaf 6 DONE

## What landed

`NormalNumbers.G4Sparse.exists_relDensityZero_divergent` is a machine-checked theorem
(`#print axioms`: `[propext, Classical.choice, Quot.sound]`).  The π-indexed construction of the
22:20 operator override works exactly as written; the previous lap's "needs PNT" claim is dead.

Construction (`namespace SparseExists` in `src/NormalNumbers/G4WiringSparse.lean`):
`mu a = log₂ a + 1`, `modulus k = mu (log₂ k)`, `Keep k ↔ modulus k ∣ k`,
`PSet p ↔ p.Prime ∧ Keep (π' p)`.

Sub-leaves, all proved:

* **(a)** `nth_prime_le_mul_log : 16 ≤ k → p_k ≤ 20 k log k`.  `Chebyshev.pi_ge` at `p = p_k` with
  `π p_k = k+1` gives `p log 2 ≤ (k+3) log p`; `log p ≤ 2√p` self-bounds to `p ≤ 9(k+3)²`, whence
  `log p ≤ 4.6 log k` and the claim.  Only one-sided Chebyshev is used.
* **(b)** `tendsto_keepCount_div : #{k<K : Keep k}/K → 0`.  Cover `[0,K)` by `[0,2^a₀)` plus dyadic
  blocks `[2^a,2^{a+1})`, `a ≥ a₀ = 2^{m₀-1}`, on each of which the modulus is the constant
  `mu a ≥ m₀`; `card_multiples_le` per block, geometric sum `≤ 2K/m₀`, and
  `Nat.log 2 K + 1 = o(K)` (`tendsto_natLog_div`, via `Real.isLittleO_log_id_atTop`).
  Limsup `≤ 2/m₀` for every `m₀`.
* **(c)** `not_summable_keep_harmonic : ¬ Summable (1/(k log k) · 1_A)`.  Per dyadic block an
  explicit injection `j ↦ (mu a) j` gives `card_block`/`block_sum`; regrouping `a ∈ [2^t,2^{t+1})`
  (where `mu a = t+1`) gives `superblock : ≥ 1/(4(t+1)log 2) − (3/log 2)2^{-(t+1)}`; harmonic
  divergence then contradicts boundedness of the finite block sums by the `tsum`.
* **(d)** `relDensityZero_PSet` (via `card_filter_PSet`: `π` is a bijection from the kept primes
  `< x` onto `{k < π'(x) : Keep k}`, composed with `Nat.tendsto_primeCounting'`) and
  `divergentRecip_PSet` (reindex by `Function.Injective.summable_iff` along `Nat.nth Nat.Prime`,
  then compare with `harm/20` past `k = 16` using (a) and (c)).

## Gotcha worth keeping

The `ite` on `Keep` must sit behind a **named def** (`recipNth`).  Unifying `fun k => g (k+16)`
with an inline `if Keep (k+16) then …` makes `whnf` unfold `Nat.log`'s well-founded recursion and
diverge (1M heartbeats, no progress).  Same shape will bite any future shifted-index summability
argument over a `Nat.log`-defined predicate.

## State

`src/NormalNumbers/G4WiringSparse.lean`: the only remaining sorry is `exists_good` (out of scope by
the override).  `PrimeLambertOscillation.lean:94` is the untouched pre-expedition sorry.
Build green; `box done --green` fired on this.

## Next

`exists_good` (the block schedule `Jᵢ, εᵢ, xᵢ` of the docstring) is the next real leaf, and after it
the `KMT_quant` wiring is what the headline actually waits on.
