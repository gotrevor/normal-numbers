# Attack map: Vandehey §7 problem 1 (quadratic-irrational LFTs preserve CF-normality?)

*Ren, 2026-08-23.  Companion to `papers/vandehey-2017-matrix-actions-cf-normality.md`.
Question: x CF-normal, q,r quadratic irrationals, q ≠ 0 ⇒ qx + r CF-normal?
Simplest instances: x ↦ φx, x ↦ x + φ.  Status: open (posed Compositio 2017).*

## 1. The structural diagnosis: it dies on Dirichlet's unit theorem

Vandehey's proof rides on one finiteness: matrices over ℤ with |det| = D and
his Type I–VI window conditions form a FINITE state set M_D, because entry
bounds |α| ≤ D pin down finitely many integers.  Run the same transducer for
M = (q r; 0 1) with q,r ∈ ℚ(√5): after clearing denominators the states live
over ℤ[φ], digit matrices A_j, J stay integer (self-conjugate), so det(state)
is fixed up to sign and the states have entries in ℤ[φ] with the SAME
real-place window bounds.  But bounded real embedding does not make a subset
of ℤ[φ] finite — ℤ[φ] is dense in ℝ.  Finiteness over ℤ worked because
ℤˣ = {±1}; over a real quadratic ring O_K, Dirichlet gives infinite units
(±φⁿ), equivalently a second archimedean place where entries drift.  Wall and
Vandehey are theorems about number fields with finite unit group (ℚ); the
quadratic question is the first infinite-regulator case.

Cute reframing for q = φ, r ∈ ℤ[φ]: N(φ) = φ(1−φ) = −1, so det M is a UNIT
and the state matrices sit in GL₂(ℤ[φ]) — the Hilbert modular group for
ℚ(√5).  So "multiply by φ" is the det = ±1 case over O_K, the analogue of the
TRIVIAL (Serret) case over ℤ.  Serret fails anyway because GL₂(ℤ[φ]) is far
bigger than the regular CF's symmetry group: its projection to the real place
is dense in PGL₂(ℝ) (irreducible lattice in PGL₂(ℝ)², projections dense), so
there is no fundamental-domain/tail-surgery argument.  Also explains why the
base-b analogue of the problem degenerates: the eventually-periodic numbers
of base b are the RATIONALS, so "Wall for base-b-periodic coefficients" is
just Wall.  The CF question is genuinely richer because CF-periodic points
are irrational.

## 2. Dead ends (know why, don't relitigate)

- **Serret/commensurator**: g = diag(√φ, 1/√φ) ∉ Comm(PSL₂(ℤ)); Γ and gΓg⁻¹
  incommensurable, equidistribution on one quotient says nothing pointwise
  about the translate.  This is the geodesic-flow face of the same unit drift.
- **Soft rigidity**: reformulated on X × X, the pair (Γh_t, Γg h_t) is a
  single orbit whose empirical limits are self-joinings of the geodesic flow
  with Haar first marginal.  Geodesic flow is Bernoulli — self-joinings are
  wild, no Ratner (not unipotent), no measure rigidity applies.  Same wall as
  "normal base 2 ⇒ normal base 3".  Nothing pointwise available off the shelf.

## 3. Route A (the real attack): Vandehey with a COMPACT fiber

Key observation: the conjugate place never feeds back.  The transducer update
M_{n+1} = A_out⁻¹ M_n A_{a_{n+1}} and the emission rule read ONLY the real
embedding of M_n (as a projectivized Möbius map on the interval).  The
real-place state evolves autonomously; the conjugate place was only
Vandehey's finiteness certificate, not part of the dynamics.  So replace
finiteness by compactness:

- **State space**: W = closure of {real embeddings of post-emission states},
  a compact window in PGL₂(ℝ) of bounded-distortion maps.  Post-emission
  boundedness should be automatic exactly as in the integer case: emission
  fires when the image interval falls deep into a cylinder, and pulling the
  emitted digits off re-expands the map; degeneration toward a singular map
  = deep-cylinder image = emission, so the renormalization enforces the
  window.  (This is the first lemma to prove carefully; it is the compact
  analogue of "entries ≤ D".)
- **Merging**: his finite-chain transitivity + Saloff-Coste–Zúñiga becomes a
  Doeblin/coupling condition for a time-inhomogeneous chain on compact W.
  The fiber maps are compositions of POSITIVE matrices: Birkhoff–Hopf
  contraction of the Hilbert projective metric supplies asymptotic loss of
  memory — cone contraction replaces finite-state merging.
- **Counting (§5–6)**: trigger strings become trigger WINDOWS (C_s × U,
  U ⊂ W open); his f_j^± upper/lower approximant machinery is already shaped
  for Riemann-squeeze over such families; needs ρ(∂U) = 0 bookkeeping
  (Portmanteau) instead of finiteness.
- **Endgame is FREE**: his either-or trick (E_M ⊆ E or E_M ∩ E = ∅, and
  E_M = M(co-null) has positive measure) works verbatim for any M.  So the
  ENTIRE problem reduces to: every string appears in Mx with a limiting
  frequency independent of the CF-normal x.  No limit identification needed.

Crux risks, in order: (i) uniform merging on W along arbitrary CF-normal
inputs (CF-normality controls fixed-rank cylinder frequencies; excursion
events are unbounded-rank — must be squeezed by the f_j^± method); (ii) the
window lemma; (iii) stationary measure on W may be singular/weird — fine,
nothing needs smoothness.  Estimate: months-scale research program, paper-
sized.  P(this program closes it) ≈ 50%; P(wall at uniform merging) ≈ 35%.

⚠️ **Lit sweep before investing**: Fisher–Schmidt, *Distribution of
approximants and geodesic flows*, ETDS 34 (2014) — Vandehey's own Remark 4.2
says "non-trivial resemblance… no direct overlap"; check whether their
skew-product with continuous fiber already contains Route A's Theorem-3.1
analogue.  Also sweep: Rosen CFs / ℚ(√5)-continued fractions; literature on
regular CFs of quadratic-irrational multiples (Burger?); anything citing
Vandehey 2017 (Google Scholar forward citations — has someone resolved §7?).

## 4. Route B (our lane, concrete): an explicit WITNESS via the brick method

Weaker but new and in-programme: construct an explicit x* with x* CF-normal
AND φx* CF-normal (a.e. x works; no explicit witness is known — the
existence statement is trivial, the witness is not).  Mechanism: the B5′
brick framework already tracks incommensurable digit systems (base 2..t + CF)
by nesting intervals and paying discrepancy rent.  "CF of φx" is one more
digit system whose cylinders are φ⁻¹·C_s — an interval family with
Gauss∘(×φ) measure; ×φ maps bricks to intervals with distortion exactly φ.
Every Lemma-13-style estimate needed is the image-interval version of what
W1–W3 supply (cylinder measure toolkit, digit law, mixing on φI).  Greedy
version composes with B5′ itself: one witness that is absolutely normal +
CF-normal + Khinchin-typical + φ·(it) CF-normal; extends to any finite set
of quadratic maps (φx, x+φ, x/φ, …).  P(structurally sound) ≈ 75–90%; risk
is bookkeeping bloat, not a conceptual wall.  This directly pokes Vandehey's
question with a constructive data point and would be first-in-any-prover by
a wide margin (it'd be first on PAPER).

## 5. Bonus separations worth remembering

- Khinchin-value transfer is a SEPARATE gap even over ℤ (pin note §
  "Khinchin-value transfer"): CF-normal ⇒ geometric mean → K₀ needs a
  uniform-integrability tail argument nobody has written.  Two publishable
  gaps, one elementary-looking.
- Mendès France's simple-normality version (§7 problem 2) is independent and
  might be MUCH harder (Vandehey's proof needs full normality).
