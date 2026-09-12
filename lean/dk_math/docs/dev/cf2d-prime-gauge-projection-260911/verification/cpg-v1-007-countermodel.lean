/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.Goldbach.Capacity
import DkMath.NumberTheory.Goldbach.PairOverlap
import DkMath.NumberTheory.PrimeGauge.GoldbachRefinement
import DkMath.NumberTheory.Primitive.PHZ30

#print "file: CPG-V1-007 bounded phase/interval countermodel"

namespace CPGV1007Countermodel

open DkMath.NumberTheory
open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.PrimeGauge

example : primeWorldModulus primeWorld235 = 30 := by
  decide

example :
    (primeWorldChild primeWorld235 29 0,
      primeWorldChild primeWorld235 29 1,
      primeWorldChild primeWorld235 29 2,
      primeWorldChild primeWorld235 29 3) = (29, 59, 89, 119) := by
  decide

/-!
The finite phase survivor set is indexed by `j < q`, while the actual
Goldbach interval is a set of offset values.  This local observer records the
attempted bridge by filtering phase survivors according to whether their
affine child value lands in the actual offset interval.
-/
def phaseSurvivorsWithinGoldbachOffsets
    (n : ℕ) (S : Finset ℕ) (q r : ℕ) : Finset ℕ :=
  (pairedSurvivingChildIndices n S q r).filter
    (fun j => primeWorldChild S r j ∈ goldbachOffsets n)

example :
    (pairedSurvivingChildIndices 10 primeWorld235 7 29).card = 5 := by
  apply pairedSurvivingChildIndices_card_eq_q_sub_two
    knownPrimeScales_primeWorld235
  · norm_num
  · simp [primeWorld235]
  · norm_num [primeWorldModulus, primeWorld235]
  · norm_num

example :
    phaseSurvivorsWithinGoldbachOffsets 10 primeWorld235 7 29 = ∅ := by
  decide

example :
    (goldbachOffsets 10).card = 9 := by
  decide

end CPGV1007Countermodel
