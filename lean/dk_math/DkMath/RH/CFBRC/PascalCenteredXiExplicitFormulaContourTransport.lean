/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiExplicitFormulaSingularityLedger
import Mathlib.Tactic

/-!
# Conditional symmetric contour transport for the completed-zeta terms

This module supplies the XDP-009 contour-level contracts.  The four-segment
rectangle boundary is explicit, and each of the ordinary-zeta, archimedean,
and elementary contributions has its own regularity and transport record.
The records are conditional providers: because the current Mathlib import set
does not provide the required rectangle deformation/residue theorem, this file
does not manufacture an existence proof for them.

The right-edge theorem is only a pointwise adapter to the already proved
prime-power endpoint.  No exchange between a rectangle integral and a limit is
asserted, and no left-edge reflection or closed residue formula is hidden in
the API.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open MeasureTheory
open scoped Interval Topology

/-! ## Named decomposed terms -/

/-- The weighted ordinary-zeta term in centered coordinates. -/
def pascalExplicitFormulaOrdinaryZetaTerm
    (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  h z * pascalXiOrdinaryZetaNegLogDeriv (criticalLineCenter + z)

/-- The weighted archimedean term in centered coordinates. -/
def pascalExplicitFormulaArchimedeanTerm
    (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  h z * pascalXiArchimedeanLogDeriv (criticalLineCenter + z)

/-- The weighted elementary correction in centered coordinates. -/
def pascalExplicitFormulaElementaryTerm
    (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  h z * pascalXiElementaryLogDerivCorrection (criticalLineCenter + z)

/-- The four-edge rectangle contribution of a function. -/
def pascalExplicitFormulaRectangleContribution
    (F : ℂ → ℂ) (W : PascalCenteredXiContourTransportWindow) : ℂ :=
  pascalSymmetricRectangleBoundaryIntegral F W.rectangle.σ W.rectangle.T

/-- The centered-circle contribution of a function. -/
def pascalExplicitFormulaCircleContribution
    (F : ℂ → ℂ) (W : PascalCenteredXiContourTransportWindow) : ℂ :=
  circleIntegral F 0 W.R

/-! ## Gate E: right-edge prime-power adapter -/

/-- The right edge lies in the half-plane needed by the existing finite
prime-power endpoint.  This theorem changes only the evaluation point; it does
not perform any contour or integral limiting operation. -/
theorem tendsto_pascalPrimePowerPHZFiniteUpTo_pascalXiOrdinaryZetaNegLogDeriv_rightEdge
    {σ t : ℝ} (hσ : 1 < σ) :
    Tendsto (fun X => pascalPrimePowerPHZFiniteUpTo X
        (pascalSymmetricRectangleRightEdge σ t)) atTop
      (nhds (pascalXiOrdinaryZetaNegLogDeriv
        (pascalSymmetricRectangleRightEdge σ t))) := by
  apply tendsto_pascalPrimePowerPHZFiniteUpTo_pascalXiOrdinaryZetaNegLogDeriv
  exact one_lt_re_pascalSymmetricRectangleRightEdge hσ

/-! ## Gate F2: conditional contour-transport provider -/

/-- A conditional provider for one decomposed term.

The fields are the exact obligations needed by an eventual deformation
argument: all four oriented segments are integrable, the centered circle is
integrable, the circle/rectangle window carries the same-zero-set contract,
and the difference of the two concrete integrals is a named crossed local
charge.  The charge is deliberately an opaque value: no residue sign or
closed form is assumed here. -/
structure PascalExplicitFormulaContourTransportProvider
    (F : ℂ → ℂ) (W : PascalCenteredXiContourTransportWindow) where
  same_zero_set : ∀ z ∈ pascalCenteredXiZeros,
    z ∈ Metric.ball (0 : ℂ) W.R ↔
      pascalCenteredToOrdinary z ∈
        pascalSymmetricRectangleInterior W.rectangle.σ W.rectangle.T
  boundary_integrable :
    PascalSymmetricRectangleBoundaryIntegrable F
      W.rectangle.σ W.rectangle.T
  circle_integrable : CircleIntegrable F 0 W.R
  crossed_local_charge : ℂ
  boundary_minus_circle_eq :
    pascalExplicitFormulaRectangleContribution F W -
        pascalExplicitFormulaCircleContribution F W =
      crossed_local_charge

/-! ## Three separate charge ledgers -/

/-- The ordinary-zeta transport provider, kept separate from the other two
terms so that its pole and zero classes remain auditable. -/
structure PascalExplicitFormulaOrdinaryZetaTransport
    (h : ℂ → ℂ) (W : PascalCenteredXiContourTransportWindow) where
  provider : PascalExplicitFormulaContourTransportProvider
    (pascalExplicitFormulaOrdinaryZetaTerm h) W

/-- The archimedean Gammaℝ transport provider. -/
structure PascalExplicitFormulaArchimedeanTransport
    (h : ℂ → ℂ) (W : PascalCenteredXiContourTransportWindow) where
  provider : PascalExplicitFormulaContourTransportProvider
    (pascalExplicitFormulaArchimedeanTerm h) W

/-- The elementary correction transport provider. -/
structure PascalExplicitFormulaElementaryTransport
    (h : ℂ → ℂ) (W : PascalCenteredXiContourTransportWindow) where
  provider : PascalExplicitFormulaContourTransportProvider
    (pascalExplicitFormulaElementaryTerm h) W

/-- The complete XDP-009 F2 package.  The three crossed local charges remain
named and separate; their sum is not identified with a residue or a defect. -/
structure PascalCenteredXiExplicitFormulaContourTransport
    (h : ℂ → ℂ) (W : PascalCenteredXiContourTransportWindow) where
  ordinary : PascalExplicitFormulaOrdinaryZetaTransport h W
  archimedean : PascalExplicitFormulaArchimedeanTransport h W
  elementary : PascalExplicitFormulaElementaryTransport h W

/-- The ordinary-zeta contribution has exactly the charge supplied by its
provider. -/
theorem ordinaryZeta_rectangle_minus_circle_eq_crossedLocalCharge
    {h : ℂ → ℂ} {W : PascalCenteredXiContourTransportWindow}
    (P : PascalCenteredXiExplicitFormulaContourTransport h W) :
    pascalExplicitFormulaRectangleContribution
        (pascalExplicitFormulaOrdinaryZetaTerm h) W -
        pascalExplicitFormulaCircleContribution
          (pascalExplicitFormulaOrdinaryZetaTerm h) W =
      P.ordinary.provider.crossed_local_charge :=
  P.ordinary.provider.boundary_minus_circle_eq

/-- The archimedean contribution has exactly the charge supplied by its
provider. -/
theorem archimedean_rectangle_minus_circle_eq_crossedLocalCharge
    {h : ℂ → ℂ} {W : PascalCenteredXiContourTransportWindow}
    (P : PascalCenteredXiExplicitFormulaContourTransport h W) :
    pascalExplicitFormulaRectangleContribution
        (pascalExplicitFormulaArchimedeanTerm h) W -
        pascalExplicitFormulaCircleContribution
          (pascalExplicitFormulaArchimedeanTerm h) W =
      P.archimedean.provider.crossed_local_charge :=
  P.archimedean.provider.boundary_minus_circle_eq

/-- The elementary contribution has exactly the charge supplied by its
provider. -/
theorem elementary_rectangle_minus_circle_eq_crossedLocalCharge
    {h : ℂ → ℂ} {W : PascalCenteredXiContourTransportWindow}
    (P : PascalCenteredXiExplicitFormulaContourTransport h W) :
    pascalExplicitFormulaRectangleContribution
        (pascalExplicitFormulaElementaryTerm h) W -
        pascalExplicitFormulaCircleContribution
          (pascalExplicitFormulaElementaryTerm h) W =
      P.elementary.provider.crossed_local_charge :=
  P.elementary.provider.boundary_minus_circle_eq

/-- The three independent transport identities add to a ledger identity.
This is algebra on the supplied providers, not a proof that any provider
exists and not a closed explicit formula. -/
theorem pascalCenteredXiExplicitFormulaContourTransport_ledger
    {h : ℂ → ℂ} {W : PascalCenteredXiContourTransportWindow}
    (P : PascalCenteredXiExplicitFormulaContourTransport h W) :
    (pascalExplicitFormulaRectangleContribution
        (pascalExplicitFormulaOrdinaryZetaTerm h) W -
      pascalExplicitFormulaCircleContribution
        (pascalExplicitFormulaOrdinaryZetaTerm h) W) +
    (pascalExplicitFormulaRectangleContribution
        (pascalExplicitFormulaArchimedeanTerm h) W -
      pascalExplicitFormulaCircleContribution
        (pascalExplicitFormulaArchimedeanTerm h) W) +
    (pascalExplicitFormulaRectangleContribution
        (pascalExplicitFormulaElementaryTerm h) W -
      pascalExplicitFormulaCircleContribution
        (pascalExplicitFormulaElementaryTerm h) W) =
      P.ordinary.provider.crossed_local_charge +
        P.archimedean.provider.crossed_local_charge +
        P.elementary.provider.crossed_local_charge := by
  rw [ordinaryZeta_rectangle_minus_circle_eq_crossedLocalCharge P,
    archimedean_rectangle_minus_circle_eq_crossedLocalCharge P,
    elementary_rectangle_minus_circle_eq_crossedLocalCharge P]

end DkMath.RH.CFBRCProjection
