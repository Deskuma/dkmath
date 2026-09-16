/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.QuadraticEuclidean
import DkMath.Lib.NumberTheory.ClassGroupTorsionBridge
import DkMath.NumberTheory.PrimeQuadraticDiscriminant

#print "file: DkMath.FLT.Prime.PrimeTraceOneClassGroupClosure"

namespace DkMath.FLT.Prime

open DkMath.Lib.NumberTheory
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic

/-! The p=7 carrier is definitionally the Euclidean `TraceOneInt (-2)` order. -/
theorem classGroupPTorsionFreeAt_traceOneNegTwo_seven :
    classGroupPTorsionFreeAt (TraceOneInt (-2)) 7 :=
  classGroupPTorsionFreeAt_of_isPrincipalIdealRing 7

end DkMath.FLT.Prime
