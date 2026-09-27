/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.TetrahedralClosure

#print "file: DkMathTest.Tromino.TetrahedralClosureAxiomAudit"

namespace DkMathTest.Tromino.TetrahedralClosureAxiomAudit

open DkMath.Tromino
open scoped BigOperators

example : Fintype.card TetraFace = 4 := tetraFace_card
example : Fintype.card TetraEdge = 6 := tetraEdge_card
example (E : TetraEdge) : tetraEdgeDelta E ≠ 0 := tetraEdgeDelta_ne_zero E
example :
    (Finset.univ : Finset TetraEdge).image tetraEdgeDelta =
      {deltaA, deltaB, deltaC} := tetraEdgeDelta_image
example : (tetraEdgesWithDelta deltaA).card = 2 := tetraEdgesWithDelta_deltaA_card
example : (tetraEdgesWithDelta deltaB).card = 2 := tetraEdgesWithDelta_deltaB_card
example : (tetraEdgesWithDelta deltaC).card = 2 := tetraEdgesWithDelta_deltaC_card
example (E : TetraEdge) :
    E ∈ tetraEdgesWithDelta deltaA ∨ E ∈ tetraEdgesWithDelta deltaB ∨
      E ∈ tetraEdgesWithDelta deltaC := tetraEdge_mem_delta_partition E

example : Disjoint
    (tetraEdgeBetween (0 : TetraFace) deltaA (by decide)).val
    (tetraEdgeBetween deltaB deltaC (by decide)).val := by
  apply tetraEdgesWithDelta_pairwise_disjoint
    (d := deltaA) (E := tetraEdgeBetween 0 deltaA (by decide))
    (F := tetraEdgeBetween deltaB deltaC (by decide)) <;> decide

example : Fintype.card TetraDirection = 3 := tetraDirection_card
example (c : TetraFace) :
    (Finset.univ : Finset TetraDirection).image (tetraOtherFace c) =
      Finset.univ.erase c := tetraOtherFace_image c
example (c : TetraFace) : (tetraIncidentEdges c).card = 3 :=
  tetraIncidentEdges_card c
example (c : TetraFace) :
    (tetraIncidentEdges c).image tetraEdgeDelta =
      {deltaA, deltaB, deltaC} := tetraIncidentEdges_delta_image c

example (c : TetraFace) (d : TetraDirection) :
    tetraRollBottom c d ≠ c := tetraRollBottom_ne c d
example (c : TetraFace) (d : TetraDirection) :
    tetraRollBottom (tetraRollBottom c d) d = c := tetraRollBottom_twice c d
example : Fintype.card TetraRollStep = 12 := tetraRollStep_card
example (c : TetraFace) (d : TetraDirection) :
    tetraEdgeDelta (tetraRollEdge c d) = d.1 := tetraRollEdge_delta c d
example (c : TetraFace) (d : TetraDirection) :
    tetraRollEdge (tetraRollBottom c d) d = tetraRollEdge c d :=
  tetraRollEdge_reverse c d

example {a b c : TrominoState} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    a + b + c = 0 ↔ a ≠ b ∧ a ≠ c ∧ b ≠ c :=
  three_nonzero_sum_zero_iff_pairwise_distinct ha hb hc
example {a b c : TrominoState} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    a + b + c = 0 ↔
      ({a, b, c} : Finset TrominoState) = {deltaA, deltaB, deltaC} :=
  three_nonzero_sum_zero_iff_delta_finset ha hb hc
example : deltaA + deltaB + deltaC = 0 := deltaA_add_deltaB_add_deltaC_eq_zero_reused

example (c : TetraFace) : tetraRollBottomList c [] = c := by
  simp [tetraRollBottomList]
example (c : TetraFace) (ds : List TetraDirection) :
    tetraRollBottomList c ds = c + (ds.map (fun d => d.1)).sum :=
  tetraRollBottomList_eq_add_sum c ds
example (c : TetraFace) (ds : List TetraDirection)
    (h : (ds.map (fun d => d.1)).sum = 0) :
    tetraRollBottomList c ds = c := by
  rw [tetraRollBottomList_eq_add_sum, h, add_zero]

#print axioms DkMath.Tromino.tetraEdgeDelta_image
#print axioms DkMath.Tromino.tetraEdgesWithDelta_pairwise_disjoint
#print axioms DkMath.Tromino.three_nonzero_sum_zero_iff_delta_finset

end DkMathTest.Tromino.TetrahedralClosureAxiomAudit
