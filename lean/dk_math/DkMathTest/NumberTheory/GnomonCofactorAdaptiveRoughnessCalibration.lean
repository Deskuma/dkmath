/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.GnomonCofactorAdaptiveRoughness
import DkMathTest.NumberTheory.GnomonCofactorThreePrimeCalibration

#print "file: DkMathTest.NumberTheory.GnomonCofactorAdaptiveRoughnessCalibration"

namespace DkMathTest.NumberTheory.GnomonCofactorAdaptiveRoughnessCalibration
open DkMath.NumberTheory.Legendre

theorem basis32_checked : gnomonCofactorAdaptiveBasis 32 = {2, 3, 5} := by
  decide +kernel

/-- The adaptive basis retains both previously checked repeated-factor triples. -/
theorem witnesses32_checked :
    539 ∈ gnomonCofactorThreePrimeWitnesses 32 2 (gnomonCofactorAdaptiveBasis 32) ∧
    343 ∈ gnomonCofactorThreePrimeWitnesses 32 3 (gnomonCofactorAdaptiveBasis 32) := by
  rw [basis32_checked]
  decide +kernel

/-- The old fixed-wheel counterexample remains available unchanged. -/
theorem fixed69_checked :
    2401 ∈ gnomonCofactorSieveCandidates 69 2 {2, 3, 5} ∧
    2401 = 7 ^ 4 ∧
    2401 ∉ gnomonCofactorThreePrimeCombinedWitnesses 69 2 {2, 3, 5} :=
  GnomonCofactorThreePrimeCalibration.fourth_power69_checked

/-- Coverage of 7 structurally removes 7^4 from every adaptive quotient window. -/
theorem adaptive69_removed (k : ℕ) :
    2401 ∉ gnomonCofactorSieveCandidates 69 k (gnomonCofactorAdaptiveBasis 69) := by
  intro hq
  have h := gnomonCofactorSurvivor_prime_gt (gnomonCofactorAdaptiveBasis_prime 69)
    (gnomonCofactorAdaptiveBasis_cover 69) hq (show Nat.Prime 7 by decide)
    (show 7 ∣ 2401 by decide)
  norm_num at h

/-- Large anchors instantiate a universal proof, with no large enumerator reduction. -/
theorem anchor_exhaustion {n : ℕ} (_hn : n ∈ ({32, 69, 210, 297, 1031, 5000} : Finset ℕ))
    (k : ℕ) :
    gnomonCofactorThreePrimeCombinedWitnesses n k (gnomonCofactorAdaptiveBasis n) =
      (gnomonCofactorSieveCandidates n k (gnomonCofactorAdaptiveBasis n)).filter
        (fun q => ¬ q.Prime) := gnomonCofactorAdaptive_exhaustion n k

theorem anchor_budget {n : ℕ} (hn : n ∈ ({32, 69, 210, 297, 1031, 5000} : Finset ℕ)) :
    gnomonCofactorThreePrimeBudget n (gnomonCofactorAdaptiveBasis n) =
      gnomonCofactorWindowMass n := by
  apply gnomonCofactorAdaptive_budget_eq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  omega

end DkMathTest.NumberTheory.GnomonCofactorAdaptiveRoughnessCalibration
