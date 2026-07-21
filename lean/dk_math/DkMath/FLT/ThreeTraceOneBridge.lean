/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.GEisensteinBridge
import DkMath.NumberTheory.TraceOneQuadratic

#print "file: DkMath.FLT.ThreeTraceOneBridge"

namespace DkMath.FLT

open DkMath.FLT.PetalDetect
open DkMath.CosmicFormulaBinom
open DkMath.NumberTheory.TraceOneQuadratic

local notation "tqNorm" => DkMath.NumberTheory.TraceOneQuadratic.norm

/-- The natural cubic kernel is the `s = -1` trace-one norm. -/
theorem S0_nat_eq_traceOneNorm_negOne (a b : ℕ) :
    (S0_nat a b : ℤ) =
      tqNorm (⟨(a : ℤ), (b : ℤ)⟩ : TraceOneInt (-1)) := by
  simp [S0_nat, DkMath.NumberTheory.TraceOneQuadratic.norm]

/-- The ring-polymorphic cubic kernel, specialized to integers. -/
theorem S0_int_eq_traceOneNorm_negOne (a b : ℤ) :
    S0 ℤ a b = tqNorm (⟨a, b⟩ : TraceOneInt (-1)) := by
  simp [S0, DkMath.NumberTheory.TraceOneQuadratic.norm]

/-- The cubic gap `GN` coordinate is the same neutral norm. -/
theorem GN_three_sub_eq_traceOneNorm_negOne (a b : ℕ) (hab : b ≤ a) :
    ((GN 3 (a - b) b : ℕ) : ℤ) =
      tqNorm (⟨(a : ℤ), (b : ℤ)⟩ : TraceOneInt (-1)) := by
  rw [GN3_sub_eq_S0 a b hab]
  exact S0_nat_eq_traceOneNorm_negOne a b

/-- Compatibility with the existing shifted standard Eisenstein coordinates. -/
theorem eisensteinNorm_shift_eq_traceOneNorm_negOne (a b : ℕ) :
    (eisensteinNormNat (a + b) b : ℤ) =
      tqNorm (⟨(a : ℤ), (b : ℤ)⟩ : TraceOneInt (-1)) := by
  rw [← S0_eq_eisensteinNorm_shift a b]
  exact S0_nat_eq_traceOneNorm_negOne a b

end DkMath.FLT
