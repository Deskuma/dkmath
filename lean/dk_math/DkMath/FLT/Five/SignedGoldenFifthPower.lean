/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.SignedGoldenConjugateCoprime

#print "file: DkMath.FLT.Five.SignedGoldenFifthPower"

namespace DkMath.FLT.Five

/-- Integer embedding respects fifth powers in the explicit golden API. -/
theorem goldenOfInt_pow_five (b : ℤ) :
    goldenOfInt (b ^ 5) = goldenPow (goldenOfInt b) 5 := by
  apply GoldenInt.ext
  · simp [goldenOfInt, goldenPow, goldenMul, goldenOne]
    ring
  · simp [goldenOfInt, goldenPow, goldenMul, goldenOne]

/-- The stripped element times its conjugate is an embedded fifth power. -/
theorem SignedGoldenRamifierStrippedPacket.beta_mul_conj_eq_fifth
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w) :
    goldenMul p.beta (goldenConj p.beta) =
      goldenPow (goldenOfInt (p.exceptional.powerSplit.b : ℤ)) 5 := by
  rw [golden_mul_conj, p.beta_norm, goldenOfInt_pow_five]

/--
The narrow factorization theorem missing from the current library: a factor of
a fifth power that is relatively prime to its complementary factor is itself a
fifth power up to a unit.
-/
abbrev GoldenCoprimeFactorOfFifthPower : Prop :=
  ∀ x y z : GoldenInt,
    GoldenRelPrime x y →
    goldenMul x y = goldenPow z 5 →
    ∃ epsilon gamma : GoldenInt,
      GoldenUnit epsilon ∧
      x = goldenMul epsilon (goldenPow gamma 5)

/-- The generic missing factorization theorem exactly inhabits the cp-004e core. -/
theorem signedGoldenFifthPowerUpToUnitCore_of_coprimeFactor
    (hFactor : GoldenCoprimeFactorOfFifthPower) :
    SignedGoldenFifthPowerUpToUnitCore := by
  intro u v w p
  exact hFactor p.beta (goldenConj p.beta)
    (goldenOfInt (p.exceptional.powerSplit.b : ℤ))
    p.beta_relPrime_conj p.beta_mul_conj_eq_fifth

end DkMath.FLT.Five
