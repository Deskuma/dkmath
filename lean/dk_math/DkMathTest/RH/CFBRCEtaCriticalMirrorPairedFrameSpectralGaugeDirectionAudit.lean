/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameSpectralGaugeDirectionAudit

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameSpectralGaugeDirectionAudit

open DkMath.RH.CFBRCProjection

example {k : ℕ} (hk : 0 < k) :
    0 < etaPairBaseRotationSpectralPhaseRate k := by
  exact etaPairBaseRotationSpectralPhaseRate_pos hk

example (s : ℂ) (k : ℕ) (r : ℝ) :
    etaPairBaseRotation (s + (r : ℂ)) k =
      etaPairBaseRotation s k := by
  exact etaPairBaseRotation_add_real s k r

example (s : ℂ) (k : ℕ) (t : ℝ) :
    etaPairBaseRotation (s + Complex.I * (t : ℂ)) k =
      etaPairBaseRotation s k *
        Complex.exp
          (Complex.I *
            (((t * etaPairBaseRotationSpectralPhaseRate k : ℝ) : ℂ))) := by
  exact etaPairBaseRotation_add_imag s k t

example (s : ℂ) (k : ℕ) (r : ℝ) :
    etaPairBaseRotationRealSpectralIncrement s k r = 0 := by
  exact etaPairBaseRotationRealSpectralIncrement_eq_zero s k r

example (s : ℂ) (k : ℕ) (t : ℝ) :
    etaPairBaseRotationImagSpectralIncrement s k t =
      etaPairBaseRotation s k *
        (Complex.exp
            (Complex.I *
              (((t * etaPairBaseRotationSpectralPhaseRate k : ℝ) : ℂ))) -
          1) := by
  exact etaPairBaseRotationImagSpectralIncrement_eq s k t

example (s : ℂ) (k : ℕ) :
    EtaPairBaseRotationSpectralDirectionCertificate s k := by
  exact etaPairBaseRotationSpectralDirectionCertificate s k

example : etaPairBaseRotationSpectralPhaseRate 0 = 0 := by
  exact etaPairBaseRotationSpectralPhaseRate_zero

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameSpectralGaugeDirectionAudit
