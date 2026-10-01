/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.IntegralMod2Bridge
import DkMathTest.Tromino.LocalFrameEquivAxiomAudit
import DkMathTest.Tromino.PortDualityKernelAxiomAudit

#print "file: DkMathTest.Tromino.IntegralMod2BridgeAxiomAudit"

namespace DkMathTest.Tromino.IntegralMod2BridgeAxiomAudit

open DkMath.Tromino
open DkMath.Lib.NumberTheory
open DkMath.NumberTheory.TraceOneQuadratic
open DkMathTest.Tromino.LocalFrameEquivAxiomAudit
open DkMathTest.Tromino.PortDualityKernelAxiomAudit
open DkMathTest.Tromino.PortKirchhoffFlowAxiomAudit

example : gaussianParity 0 = 0 := gaussianParity_zero
example : gaussianParity 1 = deltaA := gaussianParity_one
example : gaussianParity gaussianI = deltaB := gaussianParity_i
example : gaussianParity (⟨1, 1⟩ : GaussianInt) = deltaC :=
  gaussianParity_one_add_i

example : Function.Surjective gaussianParity := gaussianParity_surjective

example : eisensteinParity (eisensteinCoord 0 0) = 0 :=
  eisensteinParity_coord_00
example : eisensteinParity (eisensteinCoord 1 0) = deltaA :=
  eisensteinParity_coord_10
example : eisensteinParity (eisensteinCoord 0 1) = deltaB :=
  eisensteinParity_coord_01
example : eisensteinParity (eisensteinCoord 1 1) = deltaC :=
  eisensteinParity_coord_11

example : Function.Surjective eisensteinParity := eisensteinParity_surjective

example (s : TrominoState) :
    gaussianParity (gaussianStateRep s) = s :=
  gaussianParity_gaussianStateRep s

example (s : TrominoState) :
    eisensteinParity (eisensteinStateRep s) = s :=
  eisensteinParity_eisensteinStateRep s

example (p : gaussianExchangeFrame.Panel) :
    gaussianParity (gaussianPanelIntegral p) = frameColor gaussianExchangeFrame p :=
  gaussianPanelIntegral_parity p

example (p : gaussianExchangeFrame.Panel) :
    gaussianParity
        (gaussianPanelIntegral gaussianExchangeFrame.gap - gaussianPanelIntegral p) =
      frameDelta gaussianExchangeFrame p :=
  gaussian_relative_parity p

example (p : gaussianExchangeFrame.Panel) :
    gaussianEisensteinFrameEquiv.panelEquiv p =
      gaussianParity
        (gaussianPanelIntegral gaussianExchangeFrame.gap - gaussianPanelIntegral p) :=
  gaussianEisensteinFrameEquiv_panelEquiv_relative_parity p

example :
    gaussianParity
          (gaussianPanelIntegral gaussianExchangeFrame.gap - gaussianPanelIntegral gaussianPanel00) =
        deltaC ∧
      gaussianParity
          (gaussianPanelIntegral gaussianExchangeFrame.gap - gaussianPanelIntegral gaussianPanel10) =
        deltaB ∧
      gaussianParity
          (gaussianPanelIntegral gaussianExchangeFrame.gap - gaussianPanelIntegral gaussianPanel01) =
        deltaA := gaussian_relative_direction_order

example :
    gaussianNonzeroDirectionParities = {deltaA, deltaB, deltaC} :=
  gaussianNonzeroDirectionParities_eq

example :
    eisensteinNonzeroDirectionParities = {deltaA, deltaB, deltaC} :=
  eisensteinNonzeroDirectionParities_eq

example :
    gaussianNonzeroDirectionParities = eisensteinNonzeroDirectionParities :=
  gaussian_eisenstein_nonzero_direction_parities_eq

example (x y : GaussianInt) :
    gaussianParity (x * y) =
      gaussianMulMod2 (gaussianParity x) (gaussianParity y) :=
  gaussianParity_mul x y

example (x y : TraceOneInt (-1)) :
    eisensteinParity (x * y) =
      eisensteinMulMod2 (eisensteinParity x) (eisensteinParity y) :=
  eisensteinParity_mul x y

example (a b c d : ℤ) :
    eisensteinParity (eisensteinCoord a b * eisensteinCoord c d) =
      eisensteinMulMod2 (eisensteinParity (eisensteinCoord a b))
        (eisensteinParity (eisensteinCoord c d)) :=
  eisensteinCoord_mulMod2 a b c d

example : gaussianMulMod2 deltaB deltaB = deltaA :=
  gaussianMulMod2_deltaB_deltaB
example : gaussianMulMod2 deltaC deltaC = 0 :=
  gaussianMulMod2_deltaC_deltaC
example : eisensteinMulMod2 deltaB deltaB = deltaC :=
  eisensteinMulMod2_deltaB_deltaB
example : eisensteinMulMod2 deltaC deltaC = deltaB :=
  eisensteinMulMod2_deltaC_deltaC

example {x : TrominoState} (hx : x ≠ 0) :
    eisensteinMulMod2 x x ≠ 0 :=
  eisensteinMulMod2_sq_ne_zero hx

example :
    ¬ ∃ φ : TrominoState ≃ TrominoState,
        φ 0 = 0 ∧
          ∀ x y,
            φ (gaussianMulMod2 x y) =
              eisensteinMulMod2 (φ x) (φ y) :=
  no_zero_preserving_mul_equiv_gaussian_eisenstein

example :
    Function.Surjective gaussianParity ∧
      Function.Surjective eisensteinParity ∧
      gaussianNonzeroDirectionParities = eisensteinNonzeroDirectionParities ∧
      (¬ ∃ φ : TrominoState ≃ TrominoState,
        φ 0 = 0 ∧
          ∀ x y,
            φ (gaussianMulMod2 x y) =
              eisensteinMulMod2 (φ x) (φ y)) :=
  additive_parity_frame_agreement

example :
    ({gaussianParity (⟨1, 0⟩ : GaussianInt),
      gaussianParity (⟨0, 1⟩ : GaussianInt),
      gaussianParity (⟨1, 1⟩ : GaussianInt)} : Finset TrominoState) =
      {deltaA, deltaB, deltaC} :=
  integral_parity_coefficients

example : deltaA + deltaB + deltaC = 0 :=
  triangle_dual_integral_parity_balance

example :
    (coloringToV4Assignment triangleColoring).label t01 =
        gaussianParity (⟨1, 0⟩ : GaussianInt) ∧
      (coloringToV4Assignment triangleColoring).label t11 =
        gaussianParity (⟨1, 1⟩ : GaussianInt) ∧
      (coloringToV4Assignment triangleColoring).label t21 =
        gaussianParity (⟨0, 1⟩ : GaussianInt) := by
  rcases triangleColoring_edge_labels with ⟨hA, hC, hB⟩
  rw [hA, hC, hB]
  decide

example :
    triangleDualAssignment.label d00 = gaussianParity (⟨0, 1⟩ : GaussianInt) ∧
      triangleDualAssignment.label d01 = gaussianParity (⟨1, 1⟩ : GaussianInt) ∧
      triangleDualAssignment.label d02 = gaussianParity (⟨1, 0⟩ : GaussianInt) := by
  rcases triangleColoring_to_dual_labels with ⟨hB, hC, hA⟩
  rw [hB, hC, hA]
  decide

#print axioms DkMath.Tromino.gaussianParity
#print axioms DkMath.Tromino.eisensteinParity
#print axioms DkMath.Tromino.gaussianParity_mul
#print axioms DkMath.Tromino.eisensteinParity_mul
#print axioms DkMath.Tromino.no_zero_preserving_mul_equiv_gaussian_eisenstein
#print axioms DkMath.Tromino.additive_parity_frame_agreement

end DkMathTest.Tromino.IntegralMod2BridgeAxiomAudit
