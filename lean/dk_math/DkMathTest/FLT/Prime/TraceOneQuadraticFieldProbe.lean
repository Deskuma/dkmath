/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.TraceOneQuadraticField

#print "file: DkMathTest.FLT.Prime.TraceOneQuadraticFieldProbe"

open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.NumberTheory.TraceOneQuadraticField

namespace DkMathTest.FLT.Prime.TraceOneQuadraticFieldProbe

example {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    IsIntegralClosure (TraceOneInt (signedPrimeParameter p)) ℤ
      (TraceOneRat (signedPrimeParameter p)) :=
  traceOneRat_isIntegralClosure hp hp2

example {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ r : ℚ,
      r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r :=
  traceOneRat_no_rational_root hp hp2

example {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Nonempty (Field (TraceOneRat (signedPrimeParameter p))) := by
  exact ⟨traceOneRatField hp hp2⟩

example : signedPrimeParameter 3 = -1 := by
  norm_num [signedPrimeParameter, signedPrimeDiscriminant]

example : signedPrimeParameter 5 = 1 := by
  norm_num [signedPrimeParameter, signedPrimeDiscriminant]

example : signedPrimeParameter 7 = -2 := by
  norm_num [signedPrimeParameter, signedPrimeDiscriminant]

example : signedPrimeParameter 11 = -3 := by
  norm_num [signedPrimeParameter, signedPrimeDiscriminant]

example : signedPrimeParameter 13 = 3 := by
  norm_num [signedPrimeParameter, signedPrimeDiscriminant]

example :
    ∃ inst : Field (TraceOneRat (signedPrimeParameter 13)),
      @NumberField (TraceOneRat (signedPrimeParameter 13)) inst := by
  exact traceOneRat_numberField (by norm_num) (by norm_num)

end DkMathTest.FLT.Prime.TraceOneQuadraticFieldProbe
