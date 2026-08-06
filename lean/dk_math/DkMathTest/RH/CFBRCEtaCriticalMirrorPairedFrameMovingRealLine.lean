/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameMovingRealLine

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameMovingRealLine

open DkMath.RH.CFBRCProjection

example (s : ℂ) (k : ℕ) (z : ℂ) :
    z ∈ etaPairMovingRealLine s k ↔
      etaPairBaseRotation s k * z ∈ complexRealAxis := by
  exact etaPairMovingRealLine_mem_iff_baseRotation_mul_mem_realAxis s k z

example (s : ℂ) (k : ℕ) (r : ℝ) :
    etaPairMovingRealLine (s + (r : ℂ)) k =
      etaPairMovingRealLine s k := by
  exact etaPairMovingRealLine_add_real s k r

example (s : ℂ) (k : ℕ) (t : ℝ) (z : ℂ) :
    z ∈ etaPairMovingRealLine (s + Complex.I * (t : ℂ)) k ↔
      etaPairSpectralPhaseRotation k t * z ∈
        etaPairMovingRealLine s k := by
  exact etaPairMovingRealLine_add_imag_mem_iff s k t z

example (s : ℂ) (k : ℕ) :
    EtaPairMovingRealLineGeometryCertificate s k := by
  exact etaPairMovingRealLineGeometryCertificate s k

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameMovingRealLine
