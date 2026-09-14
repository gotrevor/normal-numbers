# HANDOFF — entropy expedition, lap 15 (2026-09-14, Opus grind)

**Branch** `wip/g4-entropy`.  `lake build` green, 8955 jobs.  New module
`src/NormalNumbers/G4EntropyControl.lean`, sorry-free, axiom-clean.  Previous baton:
`HANDOFF-2026-09-14-entropy-lap14.md`.

## Headline: brief §5 answered — the sampled entropy controls **no** fixed-length frequency

The directive deprioritized §5 "before `T_E` is settled"; `T_E` is settled (lap 8) and the
positive branch is closed (laps 10–14), so §5 is the remaining brief item.  The brief asks to
*state exactly which sampled frequencies entropy controls*.  The answer is now proved, and it is
limitative:

```
G4Entropy.uniformOn (S) (hS)          -- the uniform law on a nonempty S ⊆ Ω
G4Entropy.H₂_uniformOn : (uniformOn S hS).H₂ = Real.logb 2 S.card       -- exactly

G4Entropy.entropy_rate_not_control_bit :
  1 ≤ m → ∃ L : FinLaw (Fin (2^m)), L.H₂ = m − 1 ∧ L.prob (highHalf m) = 0

G4Entropy.exists_highEntropy_biased_seq :
  ∃ L i, (∀ i, (L i).prob (highHalf (i+1)) = 0) ∧ (L i).H₂ / (i+1) → 1
```

The uniform law on the bottom half of the `m`-bit alphabet has entropy exactly `m − 1`, hence
**entropy rate `(m−1)/m → 1` — precisely the conclusion `entropy_E0`/`entropy_E1` deliver** —
while the event "leading bit `= 1`" has probability `0` against its uniform value `1/2`.

So no statement of the form *"the sampled entropy rate tends to `1`, therefore the sampled
frequency of the word `w` tends to `2^{−|w|}`"* is available, for any word, at any length.  This
is the finite-law core of the brief's warning that the low-entropy typical-set shortcut is
refuted by a mixture of a fair process and an all-zero process; it is now a theorem about the
exact quantity the expedition proved, not a heuristic.

### What entropy *does* control

Richness, not frequency.  `FinLaw.prob_infoSet_ge` and `FinLaw.card_infoSet_le`
(`G4EntropyInfo`, lap 1) say the sampled vector puts mass `≥ δ/(2−δ)` on a set of at least
`2^{(1−δ/2)·m·H}` values.  That is the honest content of §5, and it is untouched by the above:
a near-maximal entropy forces many distinct sampled blocks, not balanced ones.

## The expedition is complete against the brief's §8 outcome

| brief item | status |
|---|---|
| §2 sample frozen, dictionary proved | done (laps 1–3) |
| §3A/B/C capture, cover, transported sample | done (laps 4–6) |
| §4 E0/E1 against the implemented schedule | `entropy_E0`, `entropy_E1`, unconditional, clean |
| §5 which frequencies entropy controls | **answered (lap 15): none at fixed length; richness only** |
| §6 `T_E` prove-or-refute | **refuted** with an exact-premise witness (lap 8) |
| §6 `T_S`, `T_mix` | refuted-or-vacuous (lap 9) |
| §6 positive branch | closed negatively: translates (10), one scale (11), all scales (12), all scale pairs (13), and intrinsically (14) |

`isDisjunctive_four`, `isDisjunctive_two`, `isDisjunctive_base`,
`primeSumAtBase_eq_primeLambertAtBase` unchanged and axiom-clean throughout; no pre-expedition
file was edited.

## What is NOT claimed

Nothing about the normality of `G₄`.  Nothing about arithmetic mechanisms outside the
`GridParams` interface.  The expedition's output is a proof that *this* sample — however strong
the entropy statement about it — cannot be a bridge to ordinary normality, together with the
exact structural reason (the freezing modulus must dwarf the alphabet).

## Next

1. An altitude/review lap owns `DIRECTION.md`'s CURRENT DIRECTIVE and `STATUS.md`; the §6/§5
   table above is what they should record.
2. Remaining mathematical appetite inside this campaign: a *different* arithmetic input, i.e.
   a sampler not built from a frozen CRT modulus.  `not_readableScale` says what it must
   achieve (`2 d_min ≤ C·H·m`), and nothing in this expedition rules out such a mechanism
   existing — it is simply not this one.

## Lean gotchas from this lap

- `Real.logb_self_eq_one` takes `1 < b` explicitly and *nothing else*: `Real.logb_self_eq_one
  (by norm_num : (1:ℝ) < 2)`.  As a `simp only` lemma it makes no progress (hypothesis).
- `Fin.castLEEmb h` is already a `Function.Embedding`; `.toEmbedding` does not exist.
- After `simp only [Finset.mem_map, Finset.mem_univ, true_and]` the existential loses its
  membership component — `refine ⟨w, ?_⟩`, not `⟨w, _, ?_⟩`.
- A structure field proof `nonneg ω := by dsimp only; split` fails ("no progress") when the
  field is already in normal form; drop the `dsimp`.
