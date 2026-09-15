# DESIGN 2026-09-15 — objective R: row-balanced cancellation on `D_s^{⊗K}`

*Record of R-a (exact proposition + `K = 1`), R-b (computational probe), R-c (kernel verdict),
R-d (pricing).  Everything asserted as proved here is machine-checked in
`src/NormalNumbers/G4BalancedRigidity.lean`; `#print axioms` on every headline declaration is
`[propext, Classical.choice, Quot.sound]`.  Nothing here is a claim about the normality of `G₄`.*

## R-a. The exact combinatorial proposition

Atoms are `α : Fin K → Fin (s+1)`.  A **row** `ν` of the tensor matrix `D_s^{⊗K}` is a unit cube
of the grid: a base `c : Fin K → Fin s` together with the `2^K` corners

    corner c T = (i ↦ if i ∈ T then (c i).succ else (c i).castSucc),    T ⊆ Fin K,

carried with the parity signs `(−1)^{|T|}` (`RowBalance.corner`).  The shift of atom `α` in layer
`j` is `ρ_{α,j} = j d_α − t_α` (`RowBalance.layer`).

> **Balanced** (`RowBalance.Balanced ρ`): for every row `c` and every value `v ∈ ℤ`,
> `∑_{T} (−1)^{|T|} 1[ρ(corner c T) = v] = 0` — the multiset of shift values over the corners
> cancels with signs.

> **The question (DESIGN §4):** does `Balanced ρ` force `ρ` to ignore a coordinate, i.e.
> `∃ i, ∀ α c, ρ (update α i c) = ρ α`?

**`K = 1`.** A row is an adjacent pair `{c, c+1}` with signs `+,−`.  Balance at `v = ρ(c)` reads
`1 − 1[ρ(c+1) = ρ(c)] = 0`, so `ρ(c+1) = ρ(c)` for every `c`: `ρ` is constant, which ignores the
only coordinate.  ∎

## R-b. The probe, before proving (as the override required)

Transfer-matrix DFS over columns (`K = 2`; a configuration is a grid `f : [n]² → V`, the
constraint couples only adjacent columns), searching for a **balanced but non-ignoring** witness:

| `K` | grid | values | result |
|---|---|---|---|
| 2 | `n ≤ 6` | 2 and 3 | **no witness** (exhaustive) |
| 3 | `3 × 3 × 3` | {0,1} | witness found |

The `K = 2` exhaustion is what redirected the lap from hunting a refutation to proving rigidity;
the `K = 3` witness is the one formalized below.

## R-c. The verdict — proved, with an exact threshold

**Rigidity holds at `K ≤ 2` and fails at `K ≥ 3`.**

* `K = 2`: `RowBalance.ignores_coord_of_balanced_two` — for every `s`, a balanced `ρ` ignores
  coordinate `0` or coordinate `1`.  The core is `RowBalance.two_dim_rigidity`: if every unit
  square of a grid function `f : ℕ → ℕ → ℤ` has its two diagonals matched as multisets, then `f`
  is constant in one of the two directions.  *Mechanism*: each square forces
  `(f(a,b) = f(a+1,b) ∧ f(a+1,b+1) = f(a,b+1))` or `(f(a,b) = f(a,b+1) ∧ f(a+1,b+1) = f(a+1,b))`;
  hence the predicate "the vertical step at `(a,b)` is nontrivial" is independent of `a`, and
  "every horizontal step at height `b` is trivial" propagates in `b` to the whole grid.  (The
  clamped extension `f a b = ρ(min a s, min b s)` satisfies the square condition everywhere, so
  the `ℕ`-grid statement transfers to `Fin (s+1)` with no boundary case.)
* `K = 3`: `RowBalance.ex_balanced` / `ex_not_ignoring` — `[α₀=1 ∧ α₁=2] + [α₀=2 ∧ α₂=2]` on
  `(Fin 3 → Fin 3)` is balanced on all eight rows and ignores no coordinate (`decide`).

**And the refutation does not reopen the deformation.**  The confinement never needed rigidity.
The right invariant is the lattice `MDF` — all full mixed differences vanish:

1. `mdf_of_balanced` — balanced ⇒ `MDF` (sum the level-set identities against the values);
2. `mdf_d_t_of_two_balanced_layers` — two balanced layers `j ≠ j′` put **both** `d` and `t` in
   `MDF`, since `(j′−j) d = ρ_{j′} − ρ_j` and `t = j d − ρ_j`, and `ℤ` is torsion-free;
3. `mdf_eq_zero_of_skel` — an `MDF` function is determined by the coordinate skeleton
   `{α : ∃ i, α i = 0}` (induction on the coordinate sum: a cube's top corner is determined by the
   other `2^K − 1`), and `card_skel_le` bounds `|skel| ≤ K (s+1)^{K−1}`;
4. `card_mdf_pairs_le` — hence at most `(2M+1)^{2|skel|}` members;
5. `Sched.balanced_coeff_le`, `Sched.balanced_union_le` — at the schedule this gives, below `L`,
   at most `L / dmin^{H/2} + (2 dmax+1)^{2K(s+1)^{K−1}} H m` read positions: **upper density
   `≤ dmin^{−H/2}`**, the same verdict as `Sched.deformation_union_le`.

`balanced_of_update_invariant` shows coordinatewise cancellation is a special case, so this
subsumes `G4DeformationVerdict` for `K′ ≥ 2` with a shorter proof and no rigidity (R1)–(R3).

## R-d. Pricing: what a non-coordinatewise cancellation could buy — nothing

A `K ≥ 3` balanced-but-not-ignoring cancellation is real (R-c), so the question is whether it
survives the §3 transport identity and its error term.  It does not, and the reason is now a
theorem rather than an estimate:

* **The density side is already closed.**  `Sched.balanced_union_le` asks only for *two* balanced
  layers.  It does not ask for coordinatewise cancellation, for rigidity, or for anything about
  *how* the layers cancel.  So the `K = 3` witness — and every non-coordinatewise cancellation —
  lands inside the same confinement: union density `≤ dmin^{−H/2}` over the whole family.
* **The error side supplies the second layer.**  §3's budget (E) forces `K′ ≥ 3K/8`, hence
  `K′ ≥ 2` at the schedule's `K = 160000`.  Each cancelled layer is balanced
  (`balanced_layer_of_coordCancel` for the coordinatewise form; by hypothesis for the
  row-balanced replacement).  Two cancelled layers is exactly the hypothesis of
  `balanced_union_le`.  The two escape values `K′ ∈ {0,1}` are the ones (E) forbids, by a factor
  `≥ 2^{K/2}` in the row second moment.
* **And the two-layer hypothesis is sharp**, so this is not a gap that a cleverer sampler slips
  through by cancelling *one* layer: `one_balanced_layer_insufficient` — for any `j`, taking
  `t := j d` makes `layer j d t ≡ 0`, a constant, hence balanced (`balanced_const`), for a
  multiplier vector `d` that is *not* `MDF` (`not_mdf_prod`: `α ↦ ∏ α i` fails the mixed
  difference at the cube based at the origin).  One layer pins nothing; the confinement genuinely
  begins at two, which is precisely where (E) starts.

**Verdict.** The escape route left open by `DESIGN-2026-09-15-deformation.md` §4 is closed.
Row-balanced cancellation is *strictly more general* than coordinatewise cancellation (proved: the
`K = 3` witness) and *equally confined* (proved: `balanced_union_le`).  The `K ≤ 2` rigidity is
recorded as the exact threshold, not as a load-bearing step.

## What is still open after R

Not covered by `balanced_union_le`, and therefore the honest frontier:

* a sampler whose error budget tolerates `K′ ≤ 1` cancelled layers.  (E) is no longer external in
  full: `Budget.released_coeff_sum` proves the coefficient sum `Σ_{j>K′} 16^{-j} = 16^{-K′}/15`
  exactly, `Budget.released_budget_exceeded` proves the threshold (if `8K′ + 8 ≤ 3K` the released
  second moment `2^K·16^{-K′}/15` already exceeds the whole capture budget `2^{-K/2}`), and
  `Budget.two_layers_of_budget` closes the loop: at `K ≥ 8` a sampler inside the budget has
  `K′ ≥ 2`, which is exactly the hypothesis of `Sched.balanced_union_le`.  What stays external is
  now *one* inequality — the rough-prime variance bound `≪ (Σc²) log M + exp(−βL)`, draft
  (6.4)–(6.5), carried by `G4TransferMoment`/`G4ScheduleBudget` — and nothing else;
* a different matrix `A` in place of `D_s^{⊗K}`, whose rows are not unit cubes — **but the
  counting mechanism is now matrix-agnostic**: `card_pairs_le_of_determining` proves the
  `(2M+1)^{2|S|}` bound for *any* invariant `Inv` determined by a finite set `S`, with
  `card_mdf_pairs_le` the instance `Inv = MDF`, `S = skel`.  So a new matrix only has to be shown
  to have a small determining set for its own balance relations; the rest of the verdict
  (`balanced_coeff_le`, `balanced_union_le`) is unchanged;
* giving up the single-`n` joint sample — **now quantified, not open**.
  `Grouped.grouped_union_card_le` partitions the atoms into `G` groups, each sharing one sample
  point (`G = 1` is the implemented sampler, `G = H` total release), and bounds the read set below
  `L` by `G · |𝓕| · (L m H dmax / (2 dmin^w) + H m)` with `w` the smallest group size.  So the
  density coefficient is `G H dmax / (2 dmin^w)` and confinement survives **iff** `dmin^w ≳ G H`,
  i.e. iff every group has size `w ≳ (log G + log H)/log dmin ≈ 2 log H / log dmin` at `G = H/w`.
  The joint sample may therefore be broken into `H/w` independent blocks with no loss — the blocks
  must simply be that large.  At the schedule (`H = (s+1)^K`, `dmin > 10^6`) that is
  `w ≳ 2K log(s+1)/log dmin`: enormous absolutely, a vanishing fraction of `H`.  What is *not*
  covered, and is the honest residue of this item, is a sampler with groups below that size.

Each of these leaves the tensor-matrix question behind; none of them is "normality of `G₄`".
