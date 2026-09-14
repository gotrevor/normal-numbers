# HANDOFF — entropy lap 38 (rung 3: the joint frequency theorem for `G₄`), 2026-09-14, Opus

**Branch** `wip/g4-entropy`.  Working tree clean at commit.  `lake build` 🟢 **8973 jobs**.
New module sorry-free and `#print axioms`-clean (trust triple).  No pre-expedition file edited;
`entropy_E0`/`entropy_E1`, `isDisjunctive_four/two/base`, `primeSumAtBase_eq_primeLambertAtBase`
re-checked and untouched.

## 0. The lap in one line

Rung 3 landed: **the 🎯 objective of the lap-37 directive — the joint (`t`-wise) sampled-word
frequency theorem for `G₄` — is MET**, as
`Sched.tendsto_occursCountJoint_primeLambertFour`.

## 1. What was proved

### The design correction (in `G4EntropyJoint.lean`)

The first draft's `leftCoord` needed `hm : m ≤ ℓ * t`, which **fails at the schedule** for fixed
`ℓ, t` (`m_K = K/4 → ∞`).  Fixed exactly as scoped: all three families of `jointFam` now land in
`Fin (2 ^ (ℓ * t + m))`, via the two injective casts

```
upPat  m ℓ t : Fin (2 ^ (ℓ*t)) → Fin (2 ^ (ℓ*t + m))
upLeft m ℓ t : Fin (2 ^ m)     → Fin (2 ^ (ℓ*t + m))
```

`H₂_map_congr_comp` strips each cast, so every bits bound is unchanged and `hm` disappears from
`leftCoord`, `jointFam`, `jointFam_injective`, `H₂_map_leftCoord_le`, `sum_patCoord_deficit_le`,
`abs_avg_patCoord_prob_le`, `abs_avg_patCoord_prob_opt`.

### `G4EntropyJointSched.lean` (new)

```
nblk i t                        = |Atom_K| / t
blkSched / blkSched_lt / blkSched_injective
    the blocking: enumerate the atoms, cut into consecutive t-blocks;
    injective by uniqueness of division (mod t, then Nat.eq_of_mul_eq_mul_right)
KK_le_card_Atom                 K ≤ |Atom_K|            (so 2t ≤ |Atom_K| eventually)
nblk_pos
patFreq i ℓ t x w               the ℓt-bit pattern frequency over (n, block, aligned position)
abs_patFreq_sub_le_of_deficit   ≤ 2√(2 log2 · ℓ t δ / m_K)
abs_patFreq_sub_le_primeLambertFour
                                ≤ 2√(400 log2 · ℓ t / √K)   (entropy_E1's δ = 50√K)
tendsto_patFreq_primeLambertFour
patCoord_eq_pack_iff            unpacking packFin into the t component blocks
patFreq_eq_count / patFreq_eq_digits
tendsto_occursCountJoint_primeLambertFour        -- THE ENDPOINT
```

The endpoint, in full: for every `t`, every `ℓ`, and any binary words `v₀,…,v_{t−1}` of length
`ℓ`,

```
 #{(n,b,j) : ∀ s < t, OccursAt 2 G₄ (v s) (2·kIdx(n, blkSched b s) + jℓ)}
 ────────────────────────────────────────────────────────────────────────  →  2^{−ℓt}
                     |P_K| · nblk_K · ⌊m_K/ℓ⌋
```

The `t` sampled windows of a block are asymptotically **independent**: a prescribed word at each
of `t` prescribed sampled positions occurs at exactly the independent frequency.  `t = 1` is
`tendsto_occursCountT_primeLambertFour`.  The constant is the `t = 1` constant with `ℓ ↦ ℓt`
(twice over: once from `sum_patCoord_deficit_le`'s zero-slack ledger, once from the schedule
instance), the extra factor `2` paying only for `nblk = ⌊|A|/t⌋ ≥ |A|/(2t)`.

**Not a normality claim.**  The sampled positions still have density `≤ ½(3/K⁴)^K`.

## 2. Which bottleneck moved

The lap-37 objective is closed.  Per trigger **E-T7** this lap does **not** pick its own next
target; the next altitude lap sets one.  The bounded secondary named in the directive (measure
the wall: `Sched.density_le_pow`, `Sched.window_needed_ge`) remains unstarted and is the only
scoped work left in `PENDING_WORK.md`'s ACTIVE section.

## 3. Lean notes harvested this lap

- `nblk`/`blkSched` must be `noncomputable`: they go through `gridAt` and `Fintype.equivFin`.
- `omega` cannot see through `t * nblk i t`; introduce the product as a hypothesis
  (`h1 : t * nblk i t + C % t = C`, `h4 : t ≤ t * nblk i t`, `h5 : 2*t*nblk = 2*(t*nblk)`) and it
  closes.
- `Nat.mul_add_mod a b c : (a * b + c) % b = c % b` is the right lemma for slot recovery in a
  block index `b*t + s`.
- `rw [Fintype.card_prod, Fintype.card_fin]` rewrites only the first `Fin` card; `simp
  [Fintype.card_prod]` does both.
- When a bound's LHS is stated with `Fintype.card (X × Y)` and the goal with the product, rewrite
  the hypothesis (`rw [hN] at hmain`) *before* `refine hmain.trans`.
