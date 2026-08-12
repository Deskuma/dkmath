/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiCompletedZetaLogDerivBridge
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

/-!
# Symmetric explicit-formula contour geometry

This module fixes the ordinary-coordinate geometry used after XDP-008.  A
centered circle is translated by `criticalLineCenter`, while the primary
transport window is a rectangle symmetric about the critical line.  The
rectangle is deliberately a contract rather than an inferred replacement for
the circle: safe-radius information alone does not identify their enclosed
zero sets.

The boundary integral uses the four oriented segments explicitly.  This is a
small path-level representation, not a general contour-deformation theorem;
the latter is recorded as a conditional provider in the companion transport
module.  No explicit formula, residue theorem, prime-sum evaluation, defect
statement, or RH result is asserted here.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open MeasureTheory
open Set
open scoped Interval Topology

/-! ## Centered and ordinary coordinates -/

/-- The ordinary coordinate associated with a centered coordinate. -/
noncomputable def pascalCenteredToOrdinary (z : ℂ) : ℂ :=
  criticalLineCenter + z

/-- The ordinary critical circle of radius `R`. -/
def pascalOrdinaryCriticalCircle (R : ℝ) : Set ℂ :=
  Metric.sphere criticalLineCenter R

/-- Translation identifies the centered circle with the ordinary critical
circle. -/
theorem mem_centeredSphere_iff_mem_ordinaryCriticalCircle
    {z : ℂ} {R : ℝ} :
    z ∈ Metric.sphere (0 : ℂ) R ↔
      pascalCenteredToOrdinary z ∈ pascalOrdinaryCriticalCircle R := by
  change dist z 0 = R ↔ dist (criticalLineCenter + z) criticalLineCenter = R
  rw [dist_eq_norm, dist_eq_norm]
  ring_nf

/-! ## Symmetric rectangle -/

/-- Parameters for a rectangle whose vertical sides are
`Re(s) = 1 - σ` and `Re(s) = σ`. -/
structure PascalCenteredXiSymmetricRectangle where
  σ : ℝ
  T : ℝ
  hσ : 1 < σ
  hT : 0 < T

/-- Ordinary-coordinate interior of the symmetric rectangle. -/
def pascalSymmetricRectangleInterior (σ T : ℝ) : Set ℂ :=
  {s | 1 - σ < s.re ∧ s.re < σ ∧ -T < s.im ∧ s.im < T}

/-- Right vertical edge, oriented from bottom to top. -/
def pascalSymmetricRectangleRightEdge (σ : ℝ) (t : ℝ) : ℂ :=
  (σ : ℂ) + (t : ℂ) * Complex.I

/-- Left vertical edge, with the same parameter orientation convention. -/
def pascalSymmetricRectangleLeftEdge (σ : ℝ) (t : ℝ) : ℂ :=
  ((1 - σ : ℝ) : ℂ) + (t : ℂ) * Complex.I

/-- Top horizontal edge. -/
def pascalSymmetricRectangleTopEdge (u T : ℝ) : ℂ :=
  (u : ℂ) + (T : ℂ) * Complex.I

/-- Bottom horizontal edge. -/
def pascalSymmetricRectangleBottomEdge (u T : ℝ) : ℂ :=
  (u : ℂ) - (T : ℂ) * Complex.I

/-- Right-edge points lie strictly in the ordinary-zeta half-plane. -/
theorem one_lt_re_pascalSymmetricRectangleRightEdge
    {σ t : ℝ} (hσ : 1 < σ) :
    1 < (pascalSymmetricRectangleRightEdge σ t).re := by
  simpa [pascalSymmetricRectangleRightEdge] using hσ

/-- The two vertical edges are exchanged by the completed-zeta reflection
`s ↦ 1 - s`. -/
theorem pascalSymmetricRectangleLeftEdge_eq_one_sub_rightEdge
    (σ t : ℝ) :
    pascalSymmetricRectangleLeftEdge σ (-t) =
      1 - pascalSymmetricRectangleRightEdge σ t := by
  apply Complex.ext <;>
    simp [pascalSymmetricRectangleLeftEdge, pascalSymmetricRectangleRightEdge]

/-- The horizontal edges are exchanged by `s ↦ 1 - s` together with reversal
of the horizontal parameter. -/
theorem pascalSymmetricRectangleBottomEdge_eq_one_sub_topEdge
    (u _σ T : ℝ) :
    pascalSymmetricRectangleBottomEdge (1 - u) T =
      1 - pascalSymmetricRectangleTopEdge u T := by
  apply Complex.ext <;>
    simp [pascalSymmetricRectangleBottomEdge, pascalSymmetricRectangleTopEdge]

/-- The rectangle interior is invariant under the critical reflection. -/
theorem mem_pascalSymmetricRectangleInterior_one_sub_iff
    {σ T : ℝ} {s : ℂ} :
    1 - s ∈ pascalSymmetricRectangleInterior σ T ↔
      s ∈ pascalSymmetricRectangleInterior σ T := by
  simp only [pascalSymmetricRectangleInterior, Set.mem_setOf_eq,
    Complex.sub_re, Complex.sub_im]
  norm_num
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-! ## Same-zero-set transport contract -/

/-- A conditional window asserting that the centered circle and symmetric
rectangle enclose exactly the same centered-Xi zeros.

This field is intentionally not derived from a safe radius.  It is the
explicit geometry hypothesis required before any circle/rectangle transport
can preserve a finite zero contribution. -/
structure PascalCenteredXiContourTransportWindow where
  R : ℝ
  rectangle : PascalCenteredXiSymmetricRectangle
  hR : 0 < R
  zero_mem_iff : ∀ z ∈ pascalCenteredXiZeros,
    z ∈ Metric.ball (0 : ℂ) R ↔
      pascalCenteredToOrdinary z ∈
        pascalSymmetricRectangleInterior rectangle.σ rectangle.T

/-- Projection of the same-zero-set contract to its radius. -/
theorem PascalCenteredXiContourTransportWindow.radius_pos
    (W : PascalCenteredXiContourTransportWindow) : 0 < W.R :=
  W.hR

/-! ## Oriented four-segment boundary -/

/-- The oriented boundary integral of a four-segment symmetric rectangle.

The order is right edge bottom-to-top, top edge right-to-left, left edge
top-to-bottom, and bottom edge left-to-right.  The factors `Complex.I` occur
on the vertical segments because `ds = I dt`. -/
noncomputable def pascalSymmetricRectangleBoundaryIntegral
    (F : ℂ → ℂ) (σ T : ℝ) : ℂ :=
  (∫ t in (-T)..T, F (pascalSymmetricRectangleRightEdge σ t) * Complex.I) +
    (∫ u in σ..(1 - σ), F (pascalSymmetricRectangleTopEdge u T)) +
    (∫ t in T..(-T), F (pascalSymmetricRectangleLeftEdge σ t) * Complex.I) +
    (∫ u in (1 - σ)..σ, F (pascalSymmetricRectangleBottomEdge u T))

/-- The four segment integrability contract for a rectangle boundary. -/
def PascalSymmetricRectangleBoundaryIntegrable
    (F : ℂ → ℂ) (σ T : ℝ) : Prop :=
  IntervalIntegrable
      (fun t => F (pascalSymmetricRectangleRightEdge σ t) * Complex.I)
      volume (-T) T ∧
    IntervalIntegrable
      (fun u => F (pascalSymmetricRectangleTopEdge u T))
      volume σ (1 - σ) ∧
    IntervalIntegrable
      (fun t => F (pascalSymmetricRectangleLeftEdge σ t) * Complex.I)
      volume T (-T) ∧
    IntervalIntegrable
      (fun u => F (pascalSymmetricRectangleBottomEdge u T))
      volume (1 - σ) σ

/-- Every point on the right edge has ordinary real part `σ`. -/
theorem re_pascalSymmetricRectangleRightEdge
    (σ t : ℝ) :
    (pascalSymmetricRectangleRightEdge σ t).re = σ := by
  simp [pascalSymmetricRectangleRightEdge]

/-- Every point on the left edge has ordinary real part `1 - σ`. -/
theorem re_pascalSymmetricRectangleLeftEdge
    (σ t : ℝ) :
    (pascalSymmetricRectangleLeftEdge σ t).re = 1 - σ := by
  simp [pascalSymmetricRectangleLeftEdge]

/-- The top edge has imaginary coordinate `T`. -/
theorem im_pascalSymmetricRectangleTopEdge
    (u T : ℝ) :
    (pascalSymmetricRectangleTopEdge u T).im = T := by
  simp [pascalSymmetricRectangleTopEdge]

/-- The bottom edge has imaginary coordinate `-T`. -/
theorem im_pascalSymmetricRectangleBottomEdge
    (u T : ℝ) :
    (pascalSymmetricRectangleBottomEdge u T).im = -T := by
  simp [pascalSymmetricRectangleBottomEdge]

end DkMath.RH.CFBRCProjection
