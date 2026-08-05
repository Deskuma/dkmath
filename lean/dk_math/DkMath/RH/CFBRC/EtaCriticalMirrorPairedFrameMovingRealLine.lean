/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameSpectralGaugeClosureDecision
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameMovingRealLine"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

/-- The real line through the origin with complex direction `direction`. -/
noncomputable def complexRealLine (direction : ℂ) : Set ℂ :=
  {z | ∃ r : ℝ, z = direction * (r : ℂ)}

/-- The ordinary real axis viewed as a complex real line. -/
noncomputable def complexRealAxis : Set ℂ :=
  complexRealLine 1

/--
The pair-left moving real line.  Its direction is the inverse base rotation,
so multiplication by the base rotation transports it back to the real axis.
-/
noncomputable def etaPairMovingRealLine
    (s : ℂ) (k : ℕ) : Set ℂ :=
  complexRealLine (etaPairBaseCounterRotation s k)

/-- Exact phase rotation introduced by an imaginary spectral translation. -/
noncomputable def etaPairSpectralPhaseRotation
    (k : ℕ) (t : ℝ) : ℂ :=
  Complex.exp
    (Complex.I *
      (((t * etaPairBaseRotationSpectralPhaseRate k : ℝ) : ℂ)))

/-- Signed transverse defect from the ordinary real axis. -/
noncomputable def complexRealAxisDefect (z : ℂ) : ℝ :=
  z.im

/-- Signed transverse defect from the pair-left moving real line. -/
noncomputable def etaPairMovingRealLineDefect
    (s : ℂ) (k : ℕ) (z : ℂ) : ℝ :=
  complexRealAxisDefect (etaPairBaseRotation s k * z)

@[simp]
theorem zero_mem_complexRealLine (direction : ℂ) :
    0 ∈ complexRealLine direction := by
  refine ⟨0, ?_⟩
  simp [complexRealLine]

@[simp]
theorem zero_mem_etaPairMovingRealLine
    (s : ℂ) (k : ℕ) :
    0 ∈ etaPairMovingRealLine s k := by
  exact zero_mem_complexRealLine _

/-- A complex value lies on the real axis exactly when its imaginary part vanishes. -/
theorem mem_complexRealAxis_iff_im_eq_zero
    (z : ℂ) :
    z ∈ complexRealAxis ↔ z.im = 0 := by
  constructor
  · rintro ⟨r, hr⟩
    change z = (1 : ℂ) * (r : ℂ) at hr
    rw [one_mul] at hr
    simpa [hr]
  · intro him
    refine ⟨z.re, ?_⟩
    change z = (1 : ℂ) * ((z.re : ℝ) : ℂ)
    rw [one_mul]
    apply Complex.ext
    · simp
    · simpa using him

/--
Multiplication by the pair-left base rotation transports the moving real line
exactly onto the ordinary real axis.
-/
theorem etaPairMovingRealLine_mem_iff_baseRotation_mul_mem_realAxis
    (s : ℂ) (k : ℕ) (z : ℂ) :
    z ∈ etaPairMovingRealLine s k ↔
      etaPairBaseRotation s k * z ∈ complexRealAxis := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_⟩
    change etaPairBaseRotation s k * z =
      (1 : ℂ) * (r : ℂ)
    rw [hr, ← mul_assoc,
      etaPairBaseRotation_mul_counterRotation, one_mul, one_mul]
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_⟩
    change z = etaPairBaseCounterRotation s k * (r : ℂ)
    calc
      z = 1 * z := by simp
      _ = (etaPairBaseCounterRotation s k *
            etaPairBaseRotation s k) * z := by
          rw [etaPairBaseCounterRotation_mul_baseRotation]
      _ = etaPairBaseCounterRotation s k *
            (etaPairBaseRotation s k * z) := by
          rw [mul_assoc]
      _ = etaPairBaseCounterRotation s k *
            ((1 : ℂ) * (r : ℂ)) := by
          rw [hr]
      _ = etaPairBaseCounterRotation s k * (r : ℂ) := by
          rw [one_mul]

/-- Moving-line membership is equivalently zero transverse defect. -/
theorem mem_etaPairMovingRealLine_iff_defect_eq_zero
    (s : ℂ) (k : ℕ) (z : ℂ) :
    z ∈ etaPairMovingRealLine s k ↔
      etaPairMovingRealLineDefect s k z = 0 := by
  rw [etaPairMovingRealLine_mem_iff_baseRotation_mul_mem_realAxis]
  exact mem_complexRealAxis_iff_im_eq_zero _

/-- Real spectral translation leaves the moving real line unchanged. -/
theorem etaPairMovingRealLine_add_real
    (s : ℂ) (k : ℕ) (r : ℝ) :
    etaPairMovingRealLine (s + (r : ℂ)) k =
      etaPairMovingRealLine s k := by
  ext z
  simp [etaPairMovingRealLine, complexRealLine,
    etaPairBaseCounterRotation, etaPairBaseRotation_add_real]

/-- Real spectral translation also leaves the transverse defect unchanged. -/
theorem etaPairMovingRealLineDefect_add_real
    (s : ℂ) (k : ℕ) (r : ℝ) (z : ℂ) :
    etaPairMovingRealLineDefect (s + (r : ℂ)) k z =
      etaPairMovingRealLineDefect s k z := by
  unfold etaPairMovingRealLineDefect
  rw [etaPairBaseRotation_add_real]

/--
Imaginary spectral translation rotates moving-line membership by the exact
logarithmic phase increment.
-/
theorem etaPairMovingRealLine_add_imag_mem_iff
    (s : ℂ) (k : ℕ) (t : ℝ) (z : ℂ) :
    z ∈ etaPairMovingRealLine (s + Complex.I * (t : ℂ)) k ↔
      etaPairSpectralPhaseRotation k t * z ∈
        etaPairMovingRealLine s k := by
  rw [etaPairMovingRealLine_mem_iff_baseRotation_mul_mem_realAxis,
    etaPairMovingRealLine_mem_iff_baseRotation_mul_mem_realAxis]
  unfold etaPairSpectralPhaseRotation
  rw [etaPairBaseRotation_add_imag]
  simp only [mul_assoc]

/--
Certificate collecting the exact first-stage moving-line geometry.
-/
structure EtaPairMovingRealLineGeometryCertificate
    (s : ℂ) (k : ℕ) : Prop where
  real_shift_invariant :
    ∀ r : ℝ,
      etaPairMovingRealLine (s + (r : ℂ)) k =
        etaPairMovingRealLine s k
  imag_shift_covariant :
    ∀ (t : ℝ) (z : ℂ),
      z ∈ etaPairMovingRealLine (s + Complex.I * (t : ℂ)) k ↔
        etaPairSpectralPhaseRotation k t * z ∈
          etaPairMovingRealLine s k
  base_rotation_transports_to_real_axis :
    ∀ z : ℂ,
      z ∈ etaPairMovingRealLine s k ↔
        etaPairBaseRotation s k * z ∈ complexRealAxis

/-- Build the exact moving-line geometry certificate. -/
theorem etaPairMovingRealLineGeometryCertificate
    (s : ℂ) (k : ℕ) :
    EtaPairMovingRealLineGeometryCertificate s k :=
  { real_shift_invariant := etaPairMovingRealLine_add_real s k
    imag_shift_covariant := etaPairMovingRealLine_add_imag_mem_iff s k
    base_rotation_transports_to_real_axis :=
      etaPairMovingRealLine_mem_iff_baseRotation_mul_mem_realAxis s k }

end DkMath.RH.CFBRCProjection
