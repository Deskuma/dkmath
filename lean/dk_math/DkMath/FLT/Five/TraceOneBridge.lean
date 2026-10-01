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

/-- The coordinate inverse from the neutral trace-one carrier. -/
def traceOneToGolden (x : TraceOneInt 1) : GoldenInt := ⟨x.fst, x.snd⟩

/-- The golden order is exactly the `s = 1` trace-one order. -/
def goldenTraceOneRingEquiv : GoldenInt ≃+* TraceOneInt 1 where
  toFun := goldenToTraceOne
  invFun := traceOneToGolden
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    cases x
    rfl
  map_add' := by
    intro x y
    ext <;> simp [goldenToTraceOne]
  map_mul' := by
    intro x y
    ext <;> simp [goldenToTraceOne]

@[simp] theorem goldenToTraceOne_fst (x : GoldenInt) : (goldenToTraceOne x).fst = x.fst := rfl
@[simp] theorem goldenToTraceOne_snd (x : GoldenInt) : (goldenToTraceOne x).snd = x.snd := rfl

@[simp] theorem traceOneToGolden_fst (x : TraceOneInt 1) :
    (traceOneToGolden x).fst = x.fst := rfl

@[simp] theorem traceOneToGolden_snd (x : TraceOneInt 1) :
    (traceOneToGolden x).snd = x.snd := rfl

@[simp] theorem traceOneToGolden_goldenToTraceOne (x : GoldenInt) :
    traceOneToGolden (goldenToTraceOne x) = x := by
  exact goldenTraceOneRingEquiv.left_inv x

@[simp] theorem goldenToTraceOne_traceOneToGolden (x : TraceOneInt 1) :
    goldenToTraceOne (traceOneToGolden x) = x := by
  exact goldenTraceOneRingEquiv.right_inv x

theorem goldenTraceOneRingEquiv_map_goldenPhi :
    goldenTraceOneRingEquiv goldenPhi =
      DkMath.NumberTheory.TraceOneQuadratic.tau 1 := by
  rfl

theorem goldenTraceOneRingEquiv_map_goldenConj (x : GoldenInt) :
    goldenTraceOneRingEquiv (goldenConj x) =
      conj (goldenTraceOneRingEquiv x) := by
  apply traceOne_ext
  · change x.fst + x.snd = x.fst + x.snd
    rfl
  · change -x.snd = -x.snd
    rfl

theorem goldenTraceOneRingEquiv_map_pow (x : GoldenInt) (n : ℕ) :
    goldenTraceOneRingEquiv (x ^ n) = (goldenTraceOneRingEquiv x) ^ n := by
  exact goldenTraceOneRingEquiv.map_pow x n

/-- Structured golden norm compatibility. -/
theorem goldenNorm_eq_traceOneNorm_one (x : GoldenInt) :
    goldenNorm x = tqNorm (goldenToTraceOne x) := by
  simp [goldenNorm, DkMath.NumberTheory.TraceOneQuadratic.norm, goldenToTraceOne]

theorem goldenTraceOneRingEquiv_map_goldenNorm (x : GoldenInt) :
    goldenNorm x = tqNorm (goldenTraceOneRingEquiv x) :=
  goldenNorm_eq_traceOneNorm_one x

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
