# KICKOFF 2026-10-06: is the profile cut forced? (prepped, not launched)

File `src/NormalNumbers/CantorRepetition.lean`.  Node: `liouvilleCantorFullProfile`: a Liouville
number in `K` normal to every base that is not a power of 3 (base 6 included).  Mechanism and
sibling are in the module doc.

1. Define the repetition construction: free blocks, and at stage `k` the prefix of length `ℓ_k`
   copied `M_k → ∞` times.  Prove `x ∈ cantorSet` and `Liouville x` (approximants
   `W/(3^ℓ−1)`).
2. The law is a product over free coins with copy weights `w_i`.  State the Fourier product
   formula, then a Cassels second moment in base `b` (not a power of 3) with the copy places
   standing in for free places.  Find the free-count analogue (`le_freeCount_exp`) first.
3. Wire through `CantorLiouvilleAll` (`ae_isNormal_of_secondMoment`); the powers-of-3 direction
   is elementary (digits in {0,2} ternary).
A refutation of step 2 (e.g. copies aligning phases for some `b = 3ˢt`) is an advance: freeze
the counterexample and a Maze row.
