/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafePrimeAnchorCap
import DkMathTest.NumberTheory.LegendreCanonicalTailCalibration
import DkMathTest.NumberTheory.LegendreCanonicalTailRegression

#print "file: DkMathTest.NumberTheory.LegendreCanonicalPrimeCapCalibration"

namespace DkMathTest.LegendreCanonicalPrimeCapCalibration
open DkMath.NumberTheory.Legendre

/-- The generic probe is now a regression consumer of the promoted production theorem. -/
theorem cap_probe {n q : ℕ} (hn : n.Prime) (hne : n ≠ 2)
    (hq : q ∈ squareAnchorOddActivePrimes n) :
    paritySafeTwoPrimeWaveUpper n q = primeAnchorProductWaveCount n q :=
  primeAnchorTwoPrimeWaveUpper_eq_count hn hne hq

/-- Exact lost credit of the existing generic union provider at all seven anchors. -/
theorem old_sieve_credit_checked : ∀ t ∈ DkMathTest.LegendreCanonicalTailCalibration.unionData,
    canonicalRootSieveLower t.1 11 = t.2.1 ∧ canonicalRootCharge11 t.1 = t.2.1 + t.2.2 := by
  intro t ht
  have H : ∀ u ∈ DkMathTest.LegendreCanonicalTailCalibration.unionData,
      u.1.Prime ∧ 11 < u.1 := by decide +kernel
  obtain ⟨hn,hlarge⟩ := H t ht
  rw [DkMathTest.LegendreCanonicalTailRegression.root11_sieve_eq_floor_union hn hlarge]
  exact DkMathTest.LegendreCanonicalTailCalibration.union_credit_checked t ht

end DkMathTest.LegendreCanonicalPrimeCapCalibration
