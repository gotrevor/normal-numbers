# HANDOFF — entropy lap 19 (2026-09-14, Opus)

**Branch** `wip/g4-entropy`, HEAD `97ff8b8`.  `lake build` green, **8958 jobs**.  New module
`src/NormalNumbers/G4EntropyShift.lean`, sorry-free, trust triple.  `Stoneham.lean` and
`DigitInterval.lean` imported, not edited.

## What was proved

`PENDING_WORK` item 1 asked to *name the room outside digit-locality*.  The answer turned out
to be sharper than "name it":

* **`isNormalSequence_shift_iff`** — normality of a digit sequence is invariant under shifting.
  Window count: the length-`ℓ` windows of `j ↦ s(r+j)` below `n` are those of `s` below `n+r`
  minus at most `r` (`countOcc_shift_le`, `countOcc_shift_ge`); divide by `n`, correct by
  `(n+r)/n → 1`.
* **`isNormal_orbit_iff`** — `{b^i x}` is normal iff `x` is (uses the repo's `digitOf_orbit`).
* **`exists_orbitLocal_forces_normal`** — for every `i`, the property `P x := IsNormal 2 {2^i x}`
  depends on `x` only through the single unquantized orbit value `{2^i x}`, is satisfiable
  (Stoneham), and implies `IsNormal 2 x`.

## The dichotomy

| what the hypothesis reads | can it force normality? |
|---|---|
| binary digits on a set of density `< 1`, at any number of times | **never** (lap 16) |
| binary digits on a density-one set | yes, and it is normality itself (laps 17–18) |
| one unquantized orbit value `{2^i x}` | **yes** (lap 19) |

So the expedition's obstruction is the **quantizer**, not the sparsity of the sampled times.
`Z^x_{K,α}(n) = ⌊2^{m_K} {4^{k} x}⌋` is an orbit value truncated to `m_K` bits; the truncation
is what turns a normality-forcing datum into one that forces nothing.  Sampling more times, at
more scales, with better-distributed multipliers — the whole §6 positive branch as the brief
framed it — cannot repair this, because the failure is already complete at a single time.

## Next bounded test

The campaign's question is now precise: **can a quantized sample force normality if the
quantization level grows?**  The sample uses a fixed `m_K` per scale but `m_K = K/4 → ∞`.  So
the honest next statement is a *diagonal* one:

> if `P x` depends only on the values `⌊2^{m_i} {2^{r_i} x}⌋` for a sequence of times `r_i` and
> levels `m_i → ∞`, when can `P` force normality?

Each such datum is digit-local (positions `[r_i, r_i + m_i)`), so lap 16 applies to the union:
`P` forces normality iff `⋃_i [r_i, r_i+m_i)` has density one.  That is a complete answer and it
is already derivable from `forces_normal_iff_density_one` + `ZSample_eq_blockVal`; the bounded
next lap is to *state and prove it in that form* (`G4EntropyDiagonal.lean`), giving the
expedition a single theorem covering every quantized sampler, of any schedule, at any growth
rate of the quantization level — and then check the implemented schedule against it
(`card_isSampled_le_real` gives `≤ 1/4`, so it fails).
