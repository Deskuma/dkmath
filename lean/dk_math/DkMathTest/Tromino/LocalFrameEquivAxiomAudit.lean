import DkMath.Tromino.LocalFrameEquiv
import DkMathTest.Tromino.PortKirchhoffFlowAxiomAudit
import DkMathTest.Tromino.PortDualityKernelAxiomAudit

namespace DkMathTest.Tromino.LocalFrameEquivAxiomAudit

open DkMath.Tromino
open DkMathTest.Tromino.PortKirchhoffFlowAxiomAudit
open DkMathTest.Tromino.PortDualityKernelAxiomAudit

example : Fintype.card gaussianExchangeFrame.Panel = 4 :=
  frame_panel_card gaussianExchangeFrame

example : (frameBody gaussianExchangeFrame).card = 3 :=
  frame_body_card gaussianExchangeFrame

example : gaussianGap.1 = (1, 1) := gaussian_gap_eq_11

example : frameDelta gaussianExchangeFrame gaussianPanel00 = deltaC := gaussian_delta_00
example : frameDelta gaussianExchangeFrame gaussianPanel10 = deltaB := gaussian_delta_10
example : frameDelta gaussianExchangeFrame gaussianPanel01 = deltaA := gaussian_delta_01

example : (frameBody gaussianExchangeFrame).image (frameDelta gaussianExchangeFrame) =
    ({deltaA, deltaB, deltaC} : Finset TrominoState) := by
  rw [frame_delta_image_body]
  ext x
  fin_cases x <;> simp only [
    ne_eq, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Finset.mem_filter,
    Finset.mem_univ, true_and, deltaA, deltaB, deltaC,
    Finset.mem_insert, Finset.mem_singleton] <;> decide

example : (frameBody eisensteinExchangeFrame).card = 3 :=
  frame_body_card eisensteinExchangeFrame

example (p : eisensteinPanel) :
    p ∈ frameBody eisensteinExchangeFrame ↔ p ≠ 0 :=
  eisenstein_body_iff p

example : gaussianEisensteinFrameEquiv.panelEquiv gaussianGap =
    eisensteinExchangeFrame.gap :=
  gaussianEisensteinFrameEquiv_maps_gap

example (p : gaussianExchangeFrame.Panel) :
    frameDelta eisensteinExchangeFrame
        (gaussianEisensteinFrameEquiv.panelEquiv p) =
      frameDelta gaussianExchangeFrame p :=
  gaussianEisensteinFrameEquiv_maps_delta p

example (p : gaussianExchangeFrame.Panel) (x : TrominoState) :
    localExchange eisensteinExchangeFrame
        (gaussianEisensteinFrameEquiv.panelEquiv p) x =
      localExchange gaussianExchangeFrame p x :=
  localExchange_conjugate gaussianEisensteinFrameEquiv p x

example : deltaA = ((1 : ZMod 2), 0) := by decide
example : deltaB = ((0 : ZMod 2), 1) := by decide
example : deltaC = ((1 : ZMod 2), 1) := by decide
example : deltaA + deltaB = deltaC := deltaA_add_deltaB
example : deltaA + deltaB + deltaC = 0 := deltaA_add_deltaB_add_deltaC

example :
    (coloringToV4Assignment triangleColoring).label t01 = deltaA ∧
      (coloringToV4Assignment triangleColoring).label t11 = deltaC ∧
      (coloringToV4Assignment triangleColoring).label t21 = deltaB :=
  triangleColoring_edge_labels

example :
    triangleDualAssignment.label d00 + triangleDualAssignment.label d01 +
      triangleDualAssignment.label d02 = 0 := by
  rcases triangleColoring_to_dual_labels with ⟨h0, h1, h2⟩
  rw [h0, h1, h2]
  decide

example (x : TrominoState) :
    localExchange gaussianExchangeFrame gaussianPanel00 x = exchange deltaC x := by
  simp [localExchange, gaussian_delta_00]

#print axioms DkMath.Tromino.frame_delta_image_body
#print axioms DkMath.Tromino.gaussianEisensteinFrameEquiv

end DkMathTest.Tromino.LocalFrameEquivAxiomAudit
