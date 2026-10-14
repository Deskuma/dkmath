/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.TraceOnePowerLanding

#print "file: DkMathTest.Lib.NumberTheory.TraceOnePowerCoordinatesApiAudit"

open DkMath.Lib.NumberTheory
open DkMath.NumberTheory.TraceOneQuadratic

#check TraceOneInt
#check TraceOneInt.fst
#check TraceOneInt.snd
#check traceOne_ext
#check fst_mul
#check snd_mul
#check fst_one
#check snd_one
#check traceOne_sq_coordinates
#check traceOne_norm_pow
#check traceOne_norm_eq_norm_mul_pow_of_eq
#check traceOnePowCoords
#check traceOnePowCoords_zero
#check traceOnePowCoords_succ
#check traceOne_pow_coordinates
#check pow_zero
#check pow_succ
#check pow_two
#check Prod.fst
#check Prod.snd

#synth CommRing (TraceOneInt 0)

example (s m n : ℤ) : traceOnePowCoords s m n 0 = (1, 0) := by
  rfl

example (s m n : ℤ) : traceOnePowCoords s m n 1 = (m, n) := by
  simp [traceOnePowCoords]

example (s m n : ℤ) :
    traceOnePowCoords s m n 2 = (m ^ 2 + s * n ^ 2, 2 * m * n + n ^ 2) := by
  ext <;> simp [traceOnePowCoords] <;> ring

example (s m n : ℤ) :
    (⟨m, n⟩ : TraceOneInt s) ^ 0 =
      ⟨(traceOnePowCoords s m n 0).1,
       (traceOnePowCoords s m n 0).2⟩ := by
  exact traceOne_pow_coordinates s m n 0

example (s m n : ℤ) :
    (⟨m, n⟩ : TraceOneInt s) ^ 1 =
      ⟨(traceOnePowCoords s m n 1).1,
       (traceOnePowCoords s m n 1).2⟩ := by
  exact traceOne_pow_coordinates s m n 1

example (s m n : ℤ) :
    (⟨m, n⟩ : TraceOneInt s) ^ 2 =
      ⟨m ^ 2 + s * n ^ 2, 2 * m * n + n ^ 2⟩ := by
  exact traceOne_sq_coordinates s m n

example (s m n : ℤ) :
    (⟨m, n⟩ : TraceOneInt s) ^ 2 =
      ⟨(traceOnePowCoords s m n 2).1,
       (traceOnePowCoords s m n 2).2⟩ := by
  exact traceOne_pow_coordinates s m n 2

example : traceOnePowCoords (-2) 1 1 2 = (-1, 3) := by
  norm_num [traceOnePowCoords]

example : traceOnePowCoords (-1) 1 2 2 = (-3, 8) := by
  norm_num [traceOnePowCoords]
