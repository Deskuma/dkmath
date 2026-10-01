/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.TraceOnePowerLanding

#print "file: DkMathTest.Lib.NumberTheory.TraceOnePowerLandingApiAudit"

open DkMath.Lib.NumberTheory
open DkMath.NumberTheory.TraceOneQuadratic

#check traceOnePowCoords
#check traceOnePowCoords_zero
#check traceOnePowCoords_succ
#check traceOne_pow_coordinates
#check traceOne_sq_coordinates
#check traceOne_norm_pow
#check traceOne_norm_eq_norm_mul_pow_of_eq
#check traceOne_sq_core_landing_iff
#check traceOne_pow_core_landing_iff
#check traceOne_mul_conj
#check traceOne_norm_conj
#check traceOne_mul_right_cancel_of_norm_ne_zero
#check TraceOneInt.fst
#check TraceOneInt.snd
#check traceOne_ext
#check ofInt
#check conj
#check norm
#check DkMath.NumberTheory.TraceOneQuadratic.norm

#synth CommRing (TraceOneInt 0)

example (s k a b : ℤ) :
    (ofInt s k * (⟨a, b⟩ : TraceOneInt s)).fst = k * a := by
  simp [ofInt]

example (s k a b : ℤ) :
    (ofInt s k * (⟨a, b⟩ : TraceOneInt s)).snd = k * b := by
  simp [ofInt]

example {s : ℤ} {alpha beta : TraceOneInt s}
    (hNorm : norm beta ≠ 0) :
    (∃ gamma : TraceOneInt s, alpha = beta * gamma ^ 0) ↔
      ∃ m n : ℤ,
        (alpha * conj beta).fst =
            norm beta * (traceOnePowCoords s m n 0).1 ∧
          (alpha * conj beta).snd =
            norm beta * (traceOnePowCoords s m n 0).2 := by
  exact traceOne_pow_core_landing_iff hNorm

example {s : ℤ} {alpha beta : TraceOneInt s}
    (hNorm : norm beta ≠ 0) :
    (∃ gamma : TraceOneInt s, alpha = beta * gamma ^ 1) ↔
      ∃ m n : ℤ,
        (alpha * conj beta).fst =
            norm beta * (traceOnePowCoords s m n 1).1 ∧
          (alpha * conj beta).snd =
            norm beta * (traceOnePowCoords s m n 1).2 := by
  exact traceOne_pow_core_landing_iff hNorm

example {s : ℤ} {alpha beta : TraceOneInt s}
    (hNorm : norm beta ≠ 0) :
    (∃ gamma : TraceOneInt s, alpha = beta * gamma ^ 2) ↔
      ∃ m n : ℤ,
        (alpha * conj beta).fst =
            norm beta * (traceOnePowCoords s m n 2).1 ∧
          (alpha * conj beta).snd =
            norm beta * (traceOnePowCoords s m n 2).2 := by
  exact traceOne_pow_core_landing_iff hNorm

example (s m n : ℤ) :
    traceOnePowCoords s m n 2 = (m ^ 2 + s * n ^ 2, 2 * m * n + n ^ 2) := by
  ext <;> simp [traceOnePowCoords] <;> ring

example {s : ℤ} {alpha beta : TraceOneInt s}
    (hNorm : norm beta ≠ 0) :
    (∃ gamma : TraceOneInt s, alpha = beta * gamma ^ 2) ↔
      ∃ m n : ℤ,
        (alpha * conj beta).fst = norm beta * (m ^ 2 + s * n ^ 2) ∧
          (alpha * conj beta).snd = norm beta * (2 * m * n + n ^ 2) := by
  exact traceOne_sq_core_landing_iff hNorm

example : traceOnePowCoords (-2) 1 1 2 = (-1, 3) := by
  norm_num [traceOnePowCoords]

example : traceOnePowCoords (-1) 1 2 2 = (-3, 8) := by
  norm_num [traceOnePowCoords]
