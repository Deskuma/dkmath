/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.GoldenOrder
import DkMath.NumberTheory.TraceOneQuadratic

#print "file: DkMath.FLT.Five.TraceOneBridge"

namespace DkMath.FLT.Five

open DkMath.NumberTheory.TraceOneQuadratic

local notation "tqNorm" => DkMath.NumberTheory.TraceOneQuadratic.norm

/-- Coordinate-preserving observation of the golden order in the neutral core. -/
def goldenToTraceOne (x : GoldenInt) : TraceOneInt 1 := ⟨x.fst, x.snd⟩

@[simp] theorem goldenToTraceOne_fst (x : GoldenInt) : (goldenToTraceOne x).fst = x.fst := rfl
@[simp] theorem goldenToTraceOne_snd (x : GoldenInt) : (goldenToTraceOne x).snd = x.snd := rfl

/-- Structured golden norm compatibility. -/
theorem goldenNorm_eq_traceOneNorm_one (x : GoldenInt) :
    goldenNorm x = tqNorm (goldenToTraceOne x) := by
  simp [goldenNorm, DkMath.NumberTheory.TraceOneQuadratic.norm, goldenToTraceOne]

/-- Binary golden quadratic-form compatibility. -/
theorem GoldenNorm_eq_traceOneNorm_one (m n : ℤ) :
    GoldenNorm m n = tqNorm (⟨m, n⟩ : TraceOneInt 1) := by
  simp [GoldenNorm, DkMath.NumberTheory.TraceOneQuadratic.norm]

/-- GN5 in endpoint-square coordinates is the `s = 1` neutral norm. -/
theorem GN5_eq_traceOneNorm_squareLink (g y : ℕ) :
    ((GN5 g y : ℕ) : ℤ) =
      tqNorm
        (⟨(((g + y) ^ 2 + y ^ 2 : ℕ) : ℤ), (((g + y) * y : ℕ) : ℤ)⟩ :
          TraceOneInt 1) := by
  rw [GN5_eq_goldenNorm_squareLink]
  exact GoldenNorm_eq_traceOneNorm_one _ _

end DkMath.FLT.Five
