# KICKOFF 2026-10-05: cantorexp in base 5 (and any missing-digit set)

Branch `proof/cantorexp5`, worktree `~/src/nn-cantorexp5`.  Trevor approved this edge tidying.

## Goal

The base-3 result `CantorExactExponent.exists_computable_mem_cantorSet_irrExponent_normal`
(K ∩ exact exponent μ₀ ∩ normal to every base prime to 3, `μ₀ > 2 + log₂3`) for the base-5
middle-fifth set `K₅` (digits `{0, 1, 3, 4}`, dimension `log 4 / log 5 ≈ 0.861`):

> For every rational `μ₀ > T₅`, a computable `x ∈ K₅` with irrationality exponent exactly `μ₀`,
> normal to every base `b ≥ 2` with `5 ∤ b`, not normal to base 5.

`T₅` is to be derived, not assumed.  Ren's back-of-envelope (2026-10-05, unverified): the
trivial count's threshold is `2 + log_k g` for base `g` with `k` kept digits, so
`T₅ = 2 + log₄5 ≈ 3.161`.  Check it with kernel red/green controls on the real schedule, as
`bcTerm_red_mu_three` / `bcTerm_green_mu_four` do in base 3.  Freeze the headline with the
threshold you derive.

## Design (lap 1 decides, and writes the reason in the handoff)

- **Preferred: generalize.**  `CantorExpGeneric.lean` and `CantorExactExponent.lean` are built on
  fair coins (`Bool`, digits `{0,2}`).  Generalize to base `g` and a digit set `D` with uniform
  letters `Fin k`, and get base 3 back as an instance (leave the existing base-3 files and frozen
  statements untouched; the generic file proves them as corollaries if convenient).  Stripping the
  specific is the edge tidying worth doing.
- **Fallback: a base-5 copy** if the generalization costs more than about two laps.  Say so in the
  handoff.

## Ingredients to adapt

Forced runs of `0` (base-5 non-normality, `not_isNormal_*` analogue); the window/Borel–Cantelli
count (`window_core`, `expTest_mass_le`); normality for bases prime to `g` via the repo's own
second-moment route (`summable_sched_bound_gen`, `CantorLiouvilleAll`), not a citation if the
Fourier decay adapts; computability (`primrec_*`).

## Records

- Frozen statements: new file `src/NormalNumbers/CantorExactExponentFive.lean` (or a generic file
  plus that instance file).  Headline names: `exists_computable_mem_cantorFive_irrExponent_normal`
  and `exists_mem_cantorFive_irrExponent_normal`.
- Note that He–Liao 2602.01307 Thm 1.5 covers exactly this set (one missing digit, base 5); the
  Stretch wall analysis (`thickening_cost_ge_one`) is set-independent, so measure counts still cap
  at `μ₀ > 3`.  Record the base-5 stretch range `2 < μ₀ ≤ T₅` as its own open node.

Rules: commit a compiling state with named `sorry` leaves early in each lap; scoped builds;
frozen statements byte-identical; a false leaf gets a refutation and a Maze row.  Done when the
headline file is sorry-free and `#print axioms` on both headlines shows no `sorryAx`.
