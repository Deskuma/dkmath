/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Gauge.Landing

#print "file: DkMathTest.NumberTheory.Gauge.Landing"

namespace DkMathTest.NumberTheory.Gauge.Landing

open DkMath.NumberTheory.Gauge
open DkMath.NumberTheory.TraceOneQuadratic

example : PowerLanding 2 36 := by
  exact ⟨6, by norm_num⟩

example : ValueGaugePure 2 36 := by
  apply powerLanding_valueGaugePure (a := 36) (by norm_num)
  exact ⟨6, by norm_num⟩

example : PositiveAdditiveLanding 2 3 4 := by
  exact ⟨5, by norm_num, by norm_num, by norm_num, by norm_num⟩

example : ValueGaugePure 2 (3 ^ 2 + 4 ^ 2) := by
  apply positiveAdditiveLanding_valueGaugePure
  exact ⟨5, by norm_num, by norm_num, by norm_num, by norm_num⟩

example {s : ℤ} {alpha beta : TraceOneInt s}
    (hNorm : DkMath.NumberTheory.TraceOneQuadratic.norm beta ≠ 0) :
    CorePowerLanding 2 alpha beta ↔
      ∃ m n : ℤ,
        (alpha * conj beta).fst =
            DkMath.NumberTheory.TraceOneQuadratic.norm beta *
              (DkMath.Lib.NumberTheory.traceOnePowCoords s m n 2).1 ∧
          (alpha * conj beta).snd =
            DkMath.NumberTheory.TraceOneQuadratic.norm beta *
              (DkMath.Lib.NumberTheory.traceOnePowCoords s m n 2).2 := by
  exact corePowerLanding_traceOne_iff hNorm

end DkMathTest.NumberTheory.Gauge.Landing
