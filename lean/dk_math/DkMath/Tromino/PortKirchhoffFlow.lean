/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortCombinatorialMap
import DkMath.Tromino.PortTensionColoring

#print "file: DkMath.Tromino.PortKirchhoffFlow"

namespace DkMath.Tromino

open scoped BigOperators

/-!
`V4FlowAssignment` is the historical name of a nowhere-zero, crossing
invariant edge-label assignment.  The definitions below add the genuine
Kirchhoff condition: the incident labels at every PortNetwork region sum to
zero.  This is a local conservation law and is distinct from the
zero-holonomy/coboundary condition in `PortTensionColoring`.
-/

def vertexKirchhoffSum {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) (r : Fin P.regionCount) : TrominoState :=
  Finset.sum Finset.univ (fun i : Fin (P.arity r) => A.label ⟨r, i⟩)

theorem vertexKirchhoffSum_formula {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) (r : Fin P.regionCount) :
    vertexKirchhoffSum A r =
      ∑ i : Fin (P.arity r), A.label ⟨r, i⟩ := rfl

theorem vertexKirchhoffSum_incident_labels
    {P : PortNetwork} {C : PortCrossing P}
    {A B : V4FlowAssignment C} (r : Fin P.regionCount)
    (h : ∀ i : Fin (P.arity r), A.label ⟨r, i⟩ = B.label ⟨r, i⟩) :
    vertexKirchhoffSum A r = vertexKirchhoffSum B r := by
  apply Finset.sum_congr rfl
  intro i hi
  exact h i

theorem vertexKirchhoffSum_crossing_independent
    {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) (r : Fin P.regionCount) :
    vertexKirchhoffSum A r =
      Finset.sum Finset.univ (fun i : Fin (P.arity r) => A.label ⟨r, i⟩) := rfl

def IsKirchhoffV4Flow {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) : Prop :=
  ∀ r, vertexKirchhoffSum A r = 0

def HasKirchhoffV4Flow {P : PortNetwork}
    (M : PortCombinatorialMap P) : Prop :=
  ∃ A : V4FlowAssignment M.crossing, IsKirchhoffV4Flow A

theorem isKirchhoffV4Flow_iff_local_conservation
    {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) :
    IsKirchhoffV4Flow A ↔
      ∀ r, vertexKirchhoffSum A r = 0 := Iff.rfl

def assignmentFlowSignature {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) (r : Fin P.regionCount) : FlowSignature where
  arity := P.arity r
  label := fun i => A.label ⟨r, i⟩
  nonzero := fun i => A.nonzero ⟨r, i⟩

@[simp] theorem assignmentFlowSignature_arity
    {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) (r : Fin P.regionCount) :
    (assignmentFlowSignature A r).arity = P.arity r := rfl

@[simp] theorem assignmentFlowSignature_label
    {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) (r : Fin P.regionCount)
    (i : Fin (assignmentFlowSignature A r).arity) :
    (assignmentFlowSignature A r).label i = A.label ⟨r, i⟩ := rfl

theorem vertexKirchhoffSum_eq_flowSum
    {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) (r : Fin P.regionCount) :
    vertexKirchhoffSum A r = flowSum (assignmentFlowSignature A r) := rfl

theorem isKirchhoffV4Flow_iff_flowConserved
    {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) :
    IsKirchhoffV4Flow A ↔
      ∀ r, FlowConserved (assignmentFlowSignature A r) := by
  rfl

theorem vertexKirchhoffSum_iff_parity
    {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) (r : Fin P.regionCount) :
    vertexKirchhoffSum A r = 0 ↔
      flowLabelCount (assignmentFlowSignature A r) deltaA % 2 =
          flowLabelCount (assignmentFlowSignature A r) deltaC % 2 ∧
        flowLabelCount (assignmentFlowSignature A r) deltaB % 2 =
          flowLabelCount (assignmentFlowSignature A r) deltaC % 2 := by
  rw [vertexKirchhoffSum_eq_flowSum]
  exact flowConserved_iff_parity _

theorem isKirchhoffV4Flow_ignores_rotation
    {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) :
    IsKirchhoffV4Flow A ↔ IsKirchhoffV4Flow A := Iff.rfl

theorem isKirchhoffV4Flow_distinct_from_tension
    {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) :
    IsKirchhoffV4Flow A ↔ ∀ r, vertexKirchhoffSum A r = 0 := Iff.rfl

end DkMath.Tromino
