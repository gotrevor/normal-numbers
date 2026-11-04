/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SqrtTwoRoutes.NormScale
import NormalNumbers.SqrtTwoRoutes.WordCertificate

/-!
# Known-answer controls for the integer word certificates

These finite examples validate the meaning and orientation of the certificate.
They are not evidence for its unproved uniform supply statement.
-/

namespace NormalNumbers.SqrtTwoRoutes

/-- `00` at shift seven: Q=128, P=181, using the Pell pair (7,5),(17,12). -/
theorem zero_zero_certificate_control : PellWordCertificate 2 0 7 3 4 9 := by
  norm_num [PellWordCertificate, pellWordNumerator, pellP, pellQ, pellPair]

/-- `11` at shift one: Q=2, P=2. -/
theorem one_one_certificate_control : PellWordCertificate 2 3 1 1 2 0 := by
  norm_num [PellWordCertificate, pellWordNumerator, pellP, pellQ, pellPair]

/-- The same state cannot certify `01`; this catches a lost word constraint. -/
theorem wrong_word_certificate_rejected : ¬ PellWordCertificate 2 1 7 3 4 9 := by
  norm_num [PellWordCertificate, pellWordNumerator, pellP, pellQ, pellPair]

/-- The coefficient norm has the correct sign relative to the odd Pell index. -/
theorem coefficient_norm_control :
    (4 : ℤ) ^ 2 + 2 * 4 * 9 - 9 ^ 2 = 7 ∧
    (181 : ℤ) ^ 2 - 2 * 128 ^ 2 = -7 := by norm_num

end NormalNumbers.SqrtTwoRoutes
