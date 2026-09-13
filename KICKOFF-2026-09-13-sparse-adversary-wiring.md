# KICKOFF 2026-09-13 — sparse-adversary wiring theorem (node N1 of the hitting-set graph) 🧵

*Context: `docs/hitting-set-invariant-2026-09-13.md` (the invariant `S(g,k)`, the data, the node
graph N1–N4).  This kickoff is N1 only: one elementary theorem, one new file.  N2/N4 are frozen
Props needing an idea; do not attempt them.*

## Objective

New file `src/NormalNumbers/SparseAdversary.lean` (add `import NormalNumbers.SparseAdversary` to
`src/NormalNumbers.lean`), proving:

```lean
/-- The base-`g` digit string of `n`, most significant digit first, with `k-1` zeros on each side:
every length-`k` window of `m·α` that meets a block of a block-sparse `α` is a window of this. -/
def paddedDigits (g k n : ℕ) : List ℕ :=
  List.replicate (k - 1) 0 ++ (Nat.digits g n).reverse ++ List.replicate (k - 1) 0

/-- **Sparse adversaries defeat hitting sets.**  If one integer `B ≥ 1` has the block `w ≠ 0^k`
absent from the padded digit string of every `m·B`, `m ∈ S`, then `S` is not a per-block hitting
set for `(g, k)`.  Berend–Boshernitzan 1994 §3 is the case `B = 1`. -/
theorem not_isHittingSet_of_avoider (g k : ℕ) (hg : 2 ≤ g) (hk : 1 ≤ k)
    (S : Finset ℕ) (w : List ℕ) (hw : w.length = k) (hwd : ∀ d ∈ w, d < g)
    (hw0 : ∃ d ∈ w, d ≠ 0) (B : ℕ) (hB : 1 ≤ B)
    (havoid : ∀ m ∈ S, 1 ≤ m → ¬ (w <:+: paddedDigits g k (m * B))) :
    ¬ IsHittingSet g k S
```

`IsHittingSet` is `src/NormalNumbers/Literature.lean` (≈ line 149): for every irrational `α` and
every block `w` of length `k` with digits `< g`, some `m ∈ S`, `1 ≤ m`, has
`∀ N, ∃ n, N ≤ n ∧ OccursAt g (m * α) w n`; `OccursAt` (Disjunctive.lean:59) is
`∀ j (hj : j < w.length), digitOf b (Int.fract x) (n + j) = w[j]`; `digitOf` (RealDefs.lean:26) is
`(⌊x * b^(i+1)⌋).toNat % b`.

Two concrete corollaries, as theorems in the same file (the automaton and the sparse probe agree
on both; `decide`/`native_decide` on `Nat.digits` and `List.IsInfix` are fine at this tier):

```lean
theorem pair_one_eleven_not_hitting : ¬ IsHittingSet 4 1 {1, 11}      -- B = 62, w = [1]:
  -- digits₄ 62 = 3,3,2 and digits₄ 682 = 2,2,2,2,2
theorem triple_one_three_five_not_hitting : ¬ IsHittingSet 2 3 {1, 3, 5}   -- B = 1, w = [1,1,1]:
  -- 1, 11, 101 in binary contain no 111
```

## The proof to formalize

Choose `L` with `m * B < g ^ L` for every `m ∈ S` (any explicit choice; `S` is finite).  Put
`i₀ := L + k + 2` and `e i := (i + i₀)!`.  Then `e` is strictly increasing, `L + 1 ≤ e 0`, and
`e (i+1) - e i = (i + i₀) * (i + i₀)! ≥ L + k`: consecutive digit blocks are separated by at least
`k` zeros.

**α.**  `α := (B : ℝ) * LiouvilleNumber.remainder g i₀`, where `remainder m k = ∑' i, 1 / m ^ (i + k)!`
(`Mathlib/NumberTheory/Transcendental/Liouville/LiouvilleNumber.lean`, line ≈ 71).  Irrational:
`liouville_liouvilleNumber (hm : 2 ≤ g)` gives `Liouville (liouvilleNumber g)`, hence
`Liouville.irrational` (Basic.lean:41); `partialSum_add_remainder` writes the Liouville number as
`partialSum + remainder` and `partialSum_eq_rat` makes the partial sum rational, so the remainder
is irrational (`Irrational.sub_rat` or `rat_sub`), and `Irrational.natCast_mul` (Irrational.lean:328,
needs `B ≠ 0`) finishes.

**Digits of `m * α`.**  For `m ∈ S`, `m * α = ∑' i, (m * B : ℝ) / g ^ (e i) =: x_m`, and
`0 ≤ x_m < 1` (each term `< g ^ L / g ^ (e i)`, geometric tail; `e 0 ≥ L + 1`), so
`Int.fract (m * α) = x_m`.  Define the digit sequence `s_m : ℕ → ℕ`:
`s_m n = (m * B) / g ^ (e i - 1 - n) % g` when `e i - L ≤ n < e i` for (the unique) `i`, else `0`.
Then

1. `∑' n, (s_m n : ℝ) / g ^ (n + 1) = x_m` — the crux.  Group by blocks: the `n` in block `i`
   contribute `∑_{j < L} ((m*B) / g^j % g) / g^(e i - j) = (m * B) / g ^ (e i)` by the base-`g`
   expansion of `m * B` (`Nat.ofDigits_digits`, or a direct `Finset.sum` identity
   `∑_{j<L} (n / g^j % g) * g^j = n` for `n < g^L`), and everything outside the blocks is `0`.
   Rearrange with `HasSum` on the disjoint blocks (`hasSum_sum`, `HasSum.sigma`, or partial sums +
   `tendsto_nhds_unique`); every term is nonnegative, so summability is by comparison with the
   geometric series (see `Bridge.summable_digitTerm` for the pattern).
2. `ProperDigits g s_m` (Bridge.lean:30 — past every index a digit `≠ g - 1`): the zeros between
   blocks.
3. `digitOf g x_m = s_m` by `Bridge.digitOf_realOfDigits` (Bridge.lean:168; `realOfDigits` is
   defined in Bridge.lean — match its exact form in step 1).
4. `OccursAt g (m * α) w n` says the window `s_m [n, n + k)` equals `w`.  `w` has a nonzero digit,
   so the window meets some block `i`; the `≥ k` zeros on both sides of that block force the
   window inside positions `[e i - L' - (k - 1), e i + (k - 1))` where
   `L' = (Nat.digits g (m*B)).length ≤ L` (positions `e i - L .. e i - L' - 1` hold leading zeros),
   and there `s_m` reads exactly `paddedDigits g k (m * B)` most-significant-first.  Hence
   `w <:+: paddedDigits g k (m * B)`, contradicting `havoid`.  So no `n` at all, let alone
   infinitely many: `IsHittingSet` fails at `(α, w)`.

Useful mathlib: `Nat.digits`, `Nat.ofDigits_digits`, `Nat.digits_lt_base`,
`Nat.lt_base_pow_length_digits`, `Nat.digits_len`, `List.IsInfix` (`<:+:`, `List.infix_iff_prefix_suffix`,
`List.IsInfix.length_le`), `Nat.factorial_succ`, `Nat.self_le_factorial`.

## Ground rules

- Touch only the new file and the one import line.  Never edit `DIRECTION.md` or any existing
  Lean file.  Commit on the current branch (`wip/adder-tower-c9`), message naming what was proved.
- Decomposing into named leaves is progress; a leaf left as `sorry` must carry its mathematics in
  a docstring.  Report the ADVANCE (which statements are proved, which leaves remain and why),
  never a sorry tally.
- Evidence: `lake build` green, and `lean-green --axioms not_isHittingSet_of_avoider` (or
  `#print axioms`) — the standard triple is expected; `Lean.ofReduceBool` on the two concrete
  corollaries is fine.
- Report what the mathematics says.  Nothing about this node is a headline; it is a green edge.
