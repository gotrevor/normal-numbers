# DESIGN 2026-09-15 — objective F: one deformation of the carry/tensor construction

*Design lap (Fable), per the ACTIVE "AFTER THE EXTRACTION" override.  Paper first; the four
preconditions of `BRIEF-after-extraction-2026-09-14.md` are discharged below with numbers.
Lean follows only after this document (frozen `Prop` interfaces first).*

## 0. The deformation chosen

**Deformation T(K′) — "free tensor deformation with partial cancellation".**  Keep the
implemented sampler's shape (one progression class, all `H` atoms read from the same `n`, the
exact dilation transport `n + ρ_{α,j} = d_α (k_α(n) + j)`), but let the multiplier vector
`d : Atom → ℕ` and the offset vector `t : Atom → ℕ` vary *jointly and freely*, subject only to

* pairwise coprime `d_α`, `0 ≤ t_α < d_α` (so the CRT sample exists and the physical index
  `k_α = (n − t_α)/d_α` is an integer on it), and
* **coordinatewise cancellation of the first `K′` layers only**: for `1 ≤ j ≤ K′`, the shift
  `ρ_{α,j} = j d_α − t_α` ignores coordinate `j − 1` of `α`.  Layers `K′ < j ≤ K` are *not*
  cancelled: they stay in the transported row sum and are paid for in the error term.

`K′ = K` is the implemented mechanism (every layer `≤ K` cancels; `G4Grid.proj_update_eq`).
`K′ = 0` is total release (no cancellation, every offset free).  L1 says a fixed `(d,t)` is
confined; L2 says changing `t` alone at `K′ = K` only translates.  T(K′) is the smallest family
containing both of the brief's remaining moves — *vary the multipliers* and *replace exact
cancellation by a controlled error* — so its verdict settles both at once.

What is **not** tested here (named so the next design can pick it up): a non-coordinatewise
exact cancellation of the heavy layers ("balanced shifts": for every row `ν` and heavy layer
`j`, the signed multiplicities of the values `ρ_{α,j}` over `supp A_ν` vanish), a different
matrix `A`, or giving up the single-`n` joint sample.

## 1. Precondition (1): actual orbit indices of the unchanged `G₄`

Unchanged real: `G₄ = Σ ω(n) 4^{-n}` (`primeLambertAtBase 4`).  Atom `α` reads the base-4 orbit
point `{4^{k_α(n)} G₄}`, i.e. binary digits from position `2 k_α(n)`, `m` of them.

* `k_α(n) = (n − t_α)/d_α` (`G4Confine.physIdx`; on the schedule `= kIdx`, `kIdx_eq_physIdx : rfl`).
* Divisibility hypotheses, all visible: `d_α ∣ n − t_α` for **every** atom simultaneously — the
  sample lives in one class mod `P` with `∏ d_α ∣ P`.  The transport correction
  `E_α = Σ_{p | d_α} Σ_j 4^{-j} 1_{p | k_α + j}` is constant on the sample iff `k_α mod rad d_α`
  is frozen, i.e. `d_α · rad d_α ∣ P` (implemented: `d_α² ∣ Mprod ∣ P₀`,
  `GridParams.exists_mult_mul`).  Frozen small primes: `∏_{p ≤ 2T} p ∣ freezeQ ∣ P₀`.
* Under T(K′) none of this changes: the identity `n + ρ_{α,j} = d_α(k_α + j)` is verbatim
  `G4Grid.add_shiftG_eq` for any `(d,t)` with `n = t_α + d_α k_α`, and
  `Frame.propA_of_progression` already accepts an arbitrary residue vector `c`.

## 2. Precondition (2): coverage AND weighting — what T(K′) can reach

**Per member.**  For one `(d,t)` with `D = ∏ d_α`, L1 (`G4Confine.density_bound`) gives, for
every prefix `[0,L)`,

    #(read positions < L)  ≤  L · m Σ_α d_α / (2D) + H·m,

hypothesis only `n ≡ t_α (mod d_α)` — so it applies to every member of T(K′), cancelled or not.
Positions reached by atom `α`: one class of `k` mod `D/d_α` (`physIdx_modEq`), windows of
length `m` at `2k`.  Different members reach different classes; that is the "access to new
positions".  Weighting within a member is uniform in `n` (each `(n, α, h)` has weight
`1/(|P| H m)`), and two windows either coincide or are disjoint on the implemented grid
(`windows_eq_or_disjoint`); coincidences only *lower* the support.  Weighting therefore cannot
rescue coverage: a mixture supported on a set of density `≤ ε` is at TV distance `≥ 1 − ε` from
uniform on `[0,L)` (brief §6's own inequality).  Coverage is the whole question.

**How many members are there?  Rigidity.**  Write `Δ_i f (α) = f(update α i c) − f(α)`.
Cancellation at layer `j ≤ K′` says `Δ_{j−1}(j d − t) = 0`, i.e.

    Δ_i t = (i+1) · Δ_i d      for every coordinate i < K′.                        (R1)

Applying `Δ_{i′}` to (R1) at `i` and `Δ_i` to (R1) at `i′`, and using that first differences
commute,

    (i+1) Δ_{i′}Δ_i d = (i′+1) Δ_iΔ_{i′} d  ⇒  (i − i′) Δ_iΔ_{i′} d = 0  ⇒  Δ_iΔ_{i′} d = 0   (R2)

for all `i ≠ i′ < K′` (ℤ is torsion-free).  Vanishing mixed differences among the first `K′`
coordinates mean `d` is *additive* in them, with the free coordinates `β = α|_{[K′,K)}` as a
parameter:

    d(α) = Σ_{i<K′} φ_i(α_i ; β) + ψ(β),   φ_i(0 ; β) = 0,
    t(α) = Σ_{i<K′} (i+1) φ_i(α_i ; β) + χ(β).                                      (R3)

(`t` from (R1) by walking the first `K′` coordinates.)  Conversely every (R3) pair cancels the
first `K′` layers.  **L2 is the case `K′ = K`, `d` fixed: then `t` is determined up to `χ`, a
constant.**  The draft's `u_α = Σ α_i B^i, v_α = Σ i α_i B^i` is (R3) with `φ_i(x) = x B^{i+1}`.

**Count.**  With all values in `[0, M]` (`M = d_max`), (R3) is determined by
`(s+1)^{K−K′}` choices of `β`, each carrying `K′` one-variable functions on `s` nonzero
arguments plus `ψ(β), χ(β)`:

    |T(K′)|  ≤  (2M+1)^{(s+1)^{K−K′} (sK′ + 2)}.                                      (C)

**Union.**  Members are all confined by L1 with `D ≥ d_min^H`, `Σ d_α ≤ H d_max`, so the union
of every member's read set has upper density

    ≤ |T(K′)| · m H d_max / (2 d_min^H)  ≤  (2M+1)^{(s+1)^{K−K′}(sK′+2)} · m H / d_min^{H−1}.  (U)

Density `≥ δ` needs `|T(K′)| ≥ δ d_min^{H−1}/(mH)`.  Compare exponents: (C) has
`(s+1)^{K−K′}(sK′+2) log(2M+1)`, the requirement has `(H−1) log d_min − log(mH/δ)`, with
`H = (s+1)^K` and `M = d_max < 2 d_min` on the schedule (`gridD₀ = K·gridUmax ≥ U`).  So

* `K′ ≥ 2`: `(s+1)^{K−2}(2s+2) ≤ 2H/(s+1) ≪ H` — the family is **too small by a factor
  `(s+1)/2` in the exponent**; the union has density `→ 0`.
* `K′ = 1`: `(s+1)^{K−1}(s+2) ≈ H` — counting alone no longer forbids density.  (Indeed at
  `K′ = 1` the constraint is only `t = d + χ(α_{≥1})`: `d` is essentially free.)
* `K′ = 0`: fully free; the union over all `(d,t)` trivially reads every position.

So coverage is available **only** if at most one layer keeps its cancellation.  The price of
that is precondition (3).

## 3. Precondition (3): the replacement transport identity and its error, priced

**Identity.**  For a member of T(K′), the row sum over all layers is still exact (draft (4.1),
`dilatedTailB_eq`, `coe_sum_dilatedTailB`):

    Σ_α A_{να} Σ_{j≥1} 4^{-j} ω(n + ρ_{α,j})  =  (A x(n))_ν + θ_ν      (mod 1),

with `x_α(n) = {4^{k_α(n)} G₄}` and `θ` the frozen transport translate.  The implemented `F`
keeps only `j > K` and relies on the layers `j ≤ K` vanishing identically under `A`.  Under
T(K′) the layers `j ≤ K′` vanish identically and the **replacement identity** is

    F′_ν(n) := Σ_α A_{να} Σ_{j > K′} 4^{-j} ω(n + ρ_{α,j})  =  (A x(n))_ν + θ_ν   (mod 1),

with **no new error at the identity level** — the deformation is arithmetically free.  The new
term is inside `F′`: the heavy layers `K′ < j ≤ K` now sit in the quantity the small-prime vector
must approximate.

**Error.**  The rough-prime part of a row (draft (6.4)–(6.5), coefficients
`c_{α,j} = A_{να} 4^{-j}`, `2^K` nonzero `A_{να}` per row) has second moment
`≪ (Σ c²) log M + exp(−βL)`, and

    Σ_{α, j>K′} c_{α,j}²  =  2^K Σ_{j>K′} 16^{-j}  <  2^{K − 4K′} / 15.

The capture inequality needs the average coordinate distance `a_K` to satisfy `a_K ≪ ρ_K = ε η`
with `η = 2^{-m}`, `m = K/4` (`kk i = KK i / 4`), i.e. row error `≪ η² = 2^{-K/2}` in second
moment.  Implemented mechanism (`K′ = K`): `2^{-3K}/15 ≪ 2^{-K/2}` — a margin of `2^{5K/2}`
that the schedule spends elsewhere.  Under T(K′) the requirement is

    2^{K − 4K′} ≪ 2^{-K/2}   ⇔   K′ > 3K/8  (+ O(log K) for the `log M` and ε factors).   (E)

**Priced against the saving.**  The entropy/volume saving is `η^{(1−ε) r − d′H}` with
`r/H → 1` — it lives at resolution `η = 2^{-K/4}` per coordinate and is insensitive to which
layers are cancelled.  The error is *additive* in the released layers and grows by `16` per
released layer while the saving is unchanged; there is no trade available inside the saving.
Releasing even layer `j = 3K/8` alone already costs `2^{K − 3K/2} = 2^{-K/2}`, the whole budget.

## 4. Precondition (4): verdict — a proved limitation, with the exact obstruction

Combine §2 and §3.  (E) forces `K′ ≥ 3K/8`; at `K′ ≥ 2` (a fortiori `K′ ≥ 3K/8`) bound (U) gives

    density(⋃ T(K′))  ≤  (2 d_max+1)^{(s+1)^{5K/8}(sK+2)} · m H / d_min^{H−1}.

**Numbers at scale `i = 0`** (`K = 160000`, `s = K² = 2.56·10^10`, `H = (s+1)^K > 10^{1665000}`,
`m = 40000`, `d_min = 1 + Q D₀ > 10^6`, `d_max < 2 d_min`):
exponent of the family bound `≈ (s+1)^{100000} · 4.1·10^{15} · log(2d_max+1) < 10^{1040020}`,
exponent of the confinement `≈ (H−1) log d_min > 10^{1665000}`.  The union density is below
`10^{−10^{1665000}}`, i.e. **zero to every practical purpose, for the entire admissible family
at once** — not merely per member.

**Verdict on T(K′): proved limitation.**  Varying the multipliers and offsets jointly, with any
amount of cancellation the rough-error budget permits, reads a set of digit positions whose
union over the *whole* family has upper density essentially `0`.  The two escape values
`K′ ∈ {0, 1}` are exactly the ones the error budget forbids, by a factor `≥ 2^{K/2}` in the row
second moment.

**Exact obstruction (a theorem to state, not a sentence):** *any sampler of this shape reads
density `≤ m Σ d_α/(2D)` per member (L1), the coordinatewise cancellation of `K′` layers forces
form (R3) (rigidity), hence the family has `≤ (2M+1)^{(s+1)^{K−K′}(sK′+2)}` members, and
`K′ ≥ 2` already makes that count too small by `(s+1)/2` in the exponent.*  Combined with (E),
which is a draft-level estimate (formal status: the implemented remainder bounds in
`G4ScheduleBudget`/`G4TransferMoment` carry the `2^K·16^{-j}` structure; (E) is read off them,
not re-proved here), the deformation is closed.

What would evade it — the honest frontier after F: a cancellation of the heavy layers that is
**not** coordinatewise (balanced shifts on every row: the multiset `{ρ_{α,j} : α ∈ supp A_ν}` with
signs cancelling), which would break (R1) and therefore (R3) without paying (E).  Whether
"balanced on every row of `D_s^{⊗K}`" forces "ignores a coordinate" is open; for `K = 1` it does
(adjacent pairs force `g` constant).  That is the next design question, and it is a question
about the tensor matrix, not about `G₄`.

## 5. Lean plan (frozen interfaces first)

New module `G4TensorRigidity.lean` (one writer; nothing pre-expedition touched):

1. `CoordCancelUpTo (K′) d t : Prop` — layers `j ≤ K′` cancel coordinatewise (over `ℤ`).
2. `diff_rel` — (R1) as an update equation.  `mixed_diff_zero` — (R2).
3. `additive_of_mixed_diff` — a function on `Fin K → X` with vanishing mixed differences on a
   coordinate set `S` is `f α₀ + Σ_{i∈S} (f(update α₀ i (α i)) − f α₀)` on each fibre of the
   complementary coordinates; `offset_of_diff_rel` — `t` from (R1).  Together: (R3) as an
   `∃ φ ψ χ` statement.  `offset_rigidity` (L2) recovered as the instance `K′ = K`, `d` fixed.
4. `card_family_le` — (C), by an injection into parameter tuples.
5. `union_density_le` — (U): L1's `density_bound` summed over the family.
6. `Sched.T_verdict` — the schedule numbers: the `(U)` coefficient is
   `≤ (2 d_max+1)^{(s+1)^{K−K′}(sK′+2)} · mH/d_min^{H−1}` with the schedule's `K, s, H, m, d_min`;
   and a kernel-checked anchor that the exponent comparison holds at `i = 0` (as an inequality
   between the two logarithms in `ℕ`, not the astronomically large numbers themselves).
7. (E) stays a **documented external estimate** in the module docstring, with the pointer to the
   draft and to the implemented budget modules; it is not made an axiom.

Transport identity + error term as the first proof target, per the override: item 1–2 first
(they are the identity's cancellation hypothesis), then 3.
