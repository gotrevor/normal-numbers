# HANDOFF twopoint lap 18 — the ℓ² obstruction, with constants

Branch `wip/twopoint-avg`.  New file `src/NormalNumbers/TwoPointGramForced.lean`, sorry-free,
axioms `[propext, Classical.choice, Quot.sound]`.

## Advance on the crux

Lap 17's verdict rested on "`≍`" prose.  It is now a theorem with explicit constants.

* **`maxRecipSum_le_two_card`** — `M(w) = Σ_{p≠q≤w} 1/max(p,q) ≤ 2π(w)`.  Split at `q < p`;
  the inner sum is `#{q < p}/p ≤ 1` since the primes below `p` are distinct naturals in `[0,p)`.
  No prime counting, no Mertens.
* **`sum_min_le`** — `Σ_{p,q≤w} min(⌊N/p⌋,⌊N/q⌋) ≤ N·(M(w) + L(w))`.
* `sum_floor_sq_ge` — `Σ_{p≤w}⌊N/p⌋² ≥ ⌊N/2⌋²` (the prime `2` alone suffices).
* **`fourthMoment_offDiag_ge`** — for `25 ≤ w`, `w² ≤ N`, `‖a‖ ≡ 1`:

      Σ_{m ≠ m' ≤ N} ‖Σ_{p≤w} a(pm) conj a(pm')‖²  ≥  kataiPairGramSq a w N  +  N²/8 .

## What this settles

The off-diagonal fourth moment of the dilation family is `≥ N²/8` unconditionally, for every
unimodular `a` — the bound uses nothing about `a`.  The `ℓ²` route (lap 15) needs
`kataiPairGramSq ≤ ε²N²L(w)⁴/π(w)²`, i.e. it needs that `≥ N²/8` quantity evaluated to relative
accuracy `8ε²L(w)⁴/π(w)² → 0`.

So the Cauchy–Schwarz-over-multipliers route does not ask for an *estimate*; it asks for an
**asymptotic evaluation of a fourth moment of dilates, to vanishing relative error**.  Together
with lap 13 (the `ℓ¹` route loses by an unbounded factor) both standard routes are now refuted
with kernel-checked constants rather than heuristics.  This is the run's strongest negative
result and it holds for *any* unimodular sequence, so it is a statement about the Kátai/BSZ
architecture, not about `ζ^{ω}` in particular.

## Where that leaves the bet

- The honest chain `conjC1_of_delange_twoPointGram` (laps 11–12) is intact and minimal: Delange
  plus one arithmetic leaf.
- The leaf is genuinely open, is not equivalent to fixed-pair Elliott in either direction
  (lap 14), and cannot be reached by either Cauchy–Schwarz route (laps 13, 17, 18).
- Any proof must use the arithmetic of `ω(pm+1)` directly.  That is a research programme, not a
  lap.

## Next attack (lap 19)

Formalise the one arithmetic handle not yet used: the `p`-peel.  For `p ∤ (m+1)`,
`ω(pm+1)` and `ω(m+1)` are unrelated, but `pm+1 ≡ 1 (mod p)` pins the dilate to a fixed residue
class — so the dilation family `{m ↦ a(pm)}` is a family of *shifted-residue* restrictions of
`ζ^ω`.  Concretely: state and prove `omegaNat (p*m+1)` restricted to `m ≡ r (mod q)` and look for
an exact relation letting `dilationPairSum` be rewritten as a character sum over residues mod
`pq`.  If such a rewrite exists, the leaf becomes a Weyl-sum statement in the CRT variables and
the repo's existing `G4WIRINGCRT` machinery applies.

## Confidence
- `twoPointWeightedAvg_all` TRUE: 88%.
- `twoPointGramSum` leaf TRUE: 80%; provable with known techniques: 3%.
