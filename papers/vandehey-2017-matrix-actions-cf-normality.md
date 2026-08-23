# Vandehey 2017 — pin note (read in full 2026-08-23)

J. Vandehey, *Non-trivial matrix actions preserve normality for continued
fractions*, Compositio Math. 153 (2017) 274–293; arXiv:1504.05121 (25 pp,
v1 numbering here).  PDF alongside (gitignored).  Read against the Track B
programme; this is the CF analogue of Wall's rational-arithmetic corollary.

## Theorem 1.1

M a 2×2 integer matrix with det M ≠ 0.  If x ∈ ℝ is CF-normal, so is
Mx = (ax+b)/(cx+d).  CF-normal (eq. (1)): every finite digit string s appears
with limiting frequency μ(C_s), Gauss measure — i.e. the Gauss orbit visits
every cylinder with the right frequency; extended to ℝ via x ~ x − a₀(x).
det = ±1 is the trivial case (head surgery only, tail unchanged — Serret).
The content is det = ±D, D ≥ 2: answers Bugeaud's Problem 10.56 (rational
multiplication) affirmatively; history: Mendès France asked first, sparked
here by Justin Moore's MathOverflow question about x + 1/2.
Kraaikamp–Nakada + [21] transfer the theorem to nearest-integer and odd CFs.

## Proof architecture (6 sections — no geodesic flow, no natural extension)

1. **§2 Transducer layer** (pure integer-matrix combinatorics, Raney-style).
   M_D = the finite set of det ±D matrices in 6 normal-form types (I–VI).
   Lemma 2.1 (Euclidean-type algorithm): M·J·A_j = A_{d₀}J A_{d₁}…J A_{d_m}·M′
   with M′ ∈ M_D — push one input digit through M, emit a bounded burst of
   output digits, land in a new state.  I.e. a finite-state transducer with
   state set M_D: R(s,M) = output string, U(s,M) = new state, and the key
   identity (9): Mx = R([a₁…aₙ],M).(U([a₁…aₙ],M)(Tⁿx)).  Lemma 2.2: burst
   length uniformly bounded in D.  Lemma 2.3: [−1;1]-cancellation runs
   bounded.  Heavy case analysis, fully elementary — very formalizable.
2. **§3 Skew product**: T̃(x,M) = (Tx, f_{a₁(x)}(M)) on Ω × M, μ̃ = μ ×
   counting/|M|.  Theorem 3.1: T̃ transitive ⇒ ∃ probability ρ ≪≫ μ̃ (Remark
   3.6), T̃-invariant, ergodic, AND x CF-normal ⇒ (x,M) is T̃-normal wrt ρ for
   EVERY M — pointwise, via the Pyatetskii-Shapiro criterion
   (Moshchevitin–Shkredov form, Lemma 3.2: lim sup ≤ σ·ρ on cylinders
   suffices), NOT via Birkhoff.  Inputs: Rényi quasi-independence (10)
   (∃C: μ(T⁻ⁿE ∩ C_s) ≍ μ(E)μ(C_s)) — **our W3 `cylinder_mixing` with its
   1±Cρᵏ envelope is strictly stronger than this**; a time-inhomogeneous
   Markov merging lemma (3.4, from Saloff-Coste–Zúñiga); quasi-invariance
   (11); then ρ = limit of Cesàro averages of μ̃∘T̃⁻ᵏ via Ryll-Nardzewski
   a.e.-convergence + Vitali-Hahn-Saks.  (With a quantitative Gauss–Kuzmin
   rate in hand, this soft-analysis layer looks compressible.)
3. **§4 Transitive components**: T̃ need not be transitive on all of M_D;
   sink-SCCs of the state digraph are, and every state feeds one (Lemma 4.1),
   so WLOG M ∈ a transitive component (with Remark 2.4's reduction to
   x ∈ [0,1), M ∈ M_D).  Lemma 4.3: Cesàro counting for countable cylinder
   families with bounded overlap, via upper/lower approximants f_j^±.
4. **§5 Trigger strings**: the CF version of "which strings in x produce
   string r in Mx" (cf. base 10: strings 35,…,89 in x trigger digit 7 in 2x).
   Nice appearance = away from both ends; minimal decomposition; multiplicity.
   Trigger lengths not provably bounded — hence the f_j^± machinery.
5. **§6 Assembly**: ℓ(n) = c₁n(1+o(1)) (output length linear, Lemma 6.1);
   trigger-count = c_r n(1+o(1)) (Lemma 6.2); so every string r appears in Mx
   with SOME frequency ρ_r, the SAME for all CF-normal x.  Endgame trick
   (lovely, formalization-friendly): E_M = M·(CF-normals) vs E = CF-normals;
   either ρ_r ≡ μ(C_r) and E_M ⊆ E, or E_M ∩ E = ∅; but E_M has positive
   Lebesgue measure and E is co-null ⇒ E_M ⊆ E.  No ρ_r is ever computed.

## §7 Open problems (both still open AFAIK 2026-08-23)

1. **Quadratic-irrational coefficients**: x CF-normal, q, r quadratic
   irrationals (i.e. eventually periodic CFs), q ≠ 0 — must qx + r be
   CF-normal?  Vandehey calls this the *natural* generalization (rationals
   are the eventually-periodic numbers of base-b expansions).  This is
   exactly the "φ·x, φ+x" question (φ = ⟨1;1,1,…⟩ is the simplest quadratic
   irrational).  Nothing known even for x ↦ φx.
2. **Mendès France's original**: does rational arithmetic preserve CF-*simple*
   normality (single-digit frequencies only)?  The proof needs full
   CF-normality; simple normality is much weaker.  Open.

## Khinchin-value transfer: NOT addressed (checked)

The paper is entirely about block frequencies.  "x Khinchin-typical ⇒ Mx
Khinchin-typical" does NOT follow: CF-normality controls each cylinder's
frequency but not the log-weighted tail Σ freq(k)·log k, so even
"CF-normal ⇒ geometric mean → K₀" needs a separate uniform-integrability
argument (rare huge digits can carry the mean while every fixed-digit
frequency is correct).  For Khinchin-typical-but-not-CF-normal x, the
rational-map question appears untouched in the literature.  Two distinct
gaps, both plausibly publishable, certainly formalizable-frontier.

## Formalization assessment (for the target shelf, behind B5′)

- **Dependencies we already have or are building**: Rényi (10) ⊆ W3
  `cylinder_mixing`; cylinder measure toolkit = W1/W2.  Dependencies we
  lack: P-S criterion (self-contained counting lemma), the Markov merging
  lemma (or bypass via our quantitative rate), Ryll-Nardzewski/VHS (or
  bypass likewise), and the whole §2 transducer layer (elementary, chunky).
- **No deep imports**: no natural extension, no transfer operator, no
  geodesic flow.  Character: long elementary case analysis + one soft-
  analysis patch that quantitative mixing likely replaces.
- **Size**: ≥ Stoneham, order of B5′.  First-in-any-prover: near-certain
  (CF-normality machinery exists only here + ronut01/erdos1002-lean).
- Alt targets it unlocks: Bugeaud's Problem 10.56 as stated (det = D
  diagonal), or the det ±1 (Serret) case as a warm-up brick.

## Also picked up from the intro

- Aistleitner (Unif. Distrib. Theory 6 (2011) 49–58): x normal base 10,
  y with density-1 zero digits, r rational ⇒ x + ry normal.  The one
  significant extension of Wall on the addition side — the "sparse
  perturbation survives" theorem.
- Airey–Mance–Vandehey (arXiv:1409.5220): same program for Q-Cantor series.
