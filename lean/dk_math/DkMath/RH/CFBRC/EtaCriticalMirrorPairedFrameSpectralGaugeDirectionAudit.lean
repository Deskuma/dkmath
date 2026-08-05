/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaFirstOrderOrbitAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameSpectralGaugeDirectionAudit"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

/-- Logarithmic spectral phase rate of the `k`-th pair-left gauge. -/
noncomputable def etaPairBaseRotationSpectralPhaseRate
    (k : ℕ) : ℝ :=
  Real.log (etaPairFrameLeftEndpoint k)

/-- At positive pair index, the pair-left endpoint is strictly larger than one. -/
theorem one_lt_etaPairFrameLeftEndpoint_of_pos
    {k : ℕ} (hk : 0 < k) :
    1 < etaPairFrameLeftEndpoint k := by
  unfold etaPairFrameLeftEndpoint
  norm_num
  exact_mod_cast (by omega : 1 < 2 * k + 1)

/-- The spectral phase rate is strictly positive away from the initial pair. -/
theorem etaPairBaseRotationSpectralPhaseRate_pos
    {k : ℕ} (hk : 0 < k) :
    0 < etaPairBaseRotationSpectralPhaseRate k := by
  unfold etaPairBaseRotationSpectralPhaseRate
  exact Real.log_pos
    (one_lt_etaPairFrameLeftEndpoint_of_pos hk)

/-- Real spectral translation leaves the pair-left rotation unchanged. -/
theorem etaPairBaseRotation_add_real
    (s : ℂ) (k : ℕ) (r : ℝ) :
    etaPairBaseRotation (s + (r : ℂ)) k =
      etaPairBaseRotation s k := by
  unfold etaPairBaseRotation
  simp

/--
Imaginary spectral translation adds the exact logarithmic phase increment.
-/
theorem etaPairBaseRotation_add_imag
    (s : ℂ) (k : ℕ) (t : ℝ) :
    etaPairBaseRotation (s + Complex.I * (t : ℂ)) k =
      etaPairBaseRotation s k *
        Complex.exp
          (Complex.I *
            (((t * etaPairBaseRotationSpectralPhaseRate k : ℝ) : ℂ))) := by
  unfold etaPairBaseRotation
  unfold etaPairBaseRotationSpectralPhaseRate
  rw [← Complex.exp_add]
  congr 1
  simp
  push_cast
  ring

/-- Finite real-direction spectral increment of the moving gauge. -/
noncomputable def etaPairBaseRotationRealSpectralIncrement
    (s : ℂ) (k : ℕ) (r : ℝ) : ℂ :=
  etaPairBaseRotation (s + (r : ℂ)) k -
    etaPairBaseRotation s k

/-- Finite imaginary-direction spectral increment of the moving gauge. -/
noncomputable def etaPairBaseRotationImagSpectralIncrement
    (s : ℂ) (k : ℕ) (t : ℝ) : ℂ :=
  etaPairBaseRotation (s + Complex.I * (t : ℂ)) k -
    etaPairBaseRotation s k

/-- Every real-direction gauge increment vanishes exactly. -/
theorem etaPairBaseRotationRealSpectralIncrement_eq_zero
    (s : ℂ) (k : ℕ) (r : ℝ) :
    etaPairBaseRotationRealSpectralIncrement s k r = 0 := by
  unfold etaPairBaseRotationRealSpectralIncrement
  rw [etaPairBaseRotation_add_real]
  exact sub_self _

/--
Every imaginary-direction gauge increment is the base rotation multiplied by
its exact logarithmic phase displacement.
-/
theorem etaPairBaseRotationImagSpectralIncrement_eq
    (s : ℂ) (k : ℕ) (t : ℝ) :
    etaPairBaseRotationImagSpectralIncrement s k t =
      etaPairBaseRotation s k *
        (Complex.exp
            (Complex.I *
              (((t * etaPairBaseRotationSpectralPhaseRate k : ℝ) : ℂ))) -
          1) := by
  unfold etaPairBaseRotationImagSpectralIncrement
  rw [etaPairBaseRotation_add_imag]
  ring

/--
Exact directional certificate for the moving pair-left spectral gauge.
It records real-shift invariance, imaginary logarithmic phase covariance, and
strict positivity of the phase rate at positive pair index.
-/
structure EtaPairBaseRotationSpectralDirectionCertificate
    (s : ℂ) (k : ℕ) : Prop where
  real_shift_invariant :
    ∀ r : ℝ,
      etaPairBaseRotation (s + (r : ℂ)) k =
        etaPairBaseRotation s k
  imag_shift_covariant :
    ∀ t : ℝ,
      etaPairBaseRotation (s + Complex.I * (t : ℂ)) k =
        etaPairBaseRotation s k *
          Complex.exp
            (Complex.I *
              (((t * etaPairBaseRotationSpectralPhaseRate k : ℝ) : ℂ)))
  phase_rate_pos :
    0 < k → 0 < etaPairBaseRotationSpectralPhaseRate k

/-- Build the exact directional gauge certificate. -/
theorem etaPairBaseRotationSpectralDirectionCertificate
    (s : ℂ) (k : ℕ) :
    EtaPairBaseRotationSpectralDirectionCertificate s k :=
  { real_shift_invariant := etaPairBaseRotation_add_real s k
    imag_shift_covariant := etaPairBaseRotation_add_imag s k
    phase_rate_pos := fun hk =>
      etaPairBaseRotationSpectralPhaseRate_pos hk }

/--
The initial pair is the unique degenerate gauge scale: its logarithmic phase
rate is zero because the left endpoint is one.
-/
theorem etaPairBaseRotationSpectralPhaseRate_zero :
    etaPairBaseRotationSpectralPhaseRate 0 = 0 := by
  norm_num [etaPairBaseRotationSpectralPhaseRate,
    etaPairFrameLeftEndpoint]

end DkMath.RH.CFBRCProjection
