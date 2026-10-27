# Result: sharp degree-five oscillator threshold for the word [1]

Module: `src/NormalNumbers/PiDisjunctiveRoutes/RoundTwoOscillatorSharp.lean`
(imports `RoundTwoOscillator`).  Targeted build green; each delivered theorem
type-checks against its frozen target, and `#print axioms` reports only
`propext`, `Classical.choice`, `Quot.sound`.

| Frozen target | Declaration |
|---|---|
| `QuinticEndpointControl` | `quinticEndpointControl` |
| `WordOneAvoidanceClassification` | `wordOneAvoidanceClassification` |
| `QuinticWordOneCertificate` | `quinticWordOneCertificate` |
| `MinimumDegreeWordOne` | `minimumDegreeWordOne` |

Auxiliary lemmas: `realPoly_quinticControl`, `eq_zero_of_digitOf_two_eq_zero`
(every canonical binary digit of y in [0,1) zero implies y = 0, by induction
showing floor(y*2^i) = 0), `natDegree_quinticControl` (= 5),
`five_le_natDegree_of_wordOne`.

The proofs:
- Quintic control: residual is x(x-2)^4 + 1/4, endpoint sums -1/2 and -63/2
  by `norm_num`.
- Classification: avoiding [1] forces every `digitOf 2 (fract x)` digit to be 0,
  so fract x = 0 and x is 3 or 4.  The converse is direct.
- Minimum degree: 3 and 4 both avoid [1], so a certificate rejects both, which
  contradicts `not_quartic_endpoint_certificate` in degree <= 4.  The degree-5
  witness is `quinticControl`.

Not claimed: anything about pi's digits.  `FixedDegreeBlindInterval` was left
untouched.  The full host build and the commit are left to the parent.
