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

Mathematically, the first condition is a vertex-divergence equation for a
V4-valued flow.  It should not be conflated with a potential difference
representation: the latter is the tension/zero-holonomy layer, and the two
notions coincide only after the separate exactness hypotheses are supplied.
-/

/-- The V4 divergence at a region is the sum of its incident labels.

This is a local vertex equation: it sums the labels on all ports with first
component `r`, independently of any rotation system. -/
def vertexKirchhoffSum {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) (r : Fin P.regionCount) : TrominoState :=
  Finset.sum Finset.univ (fun i : Fin (P.arity r) => A.label ⟨r, i⟩)

/-- Expanded form of the vertex divergence. -/
theorem vertexKirchhoffSum_formula {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) (r : Fin P.regionCount) :
    vertexKirchhoffSum A r =
      ∑ i : Fin (P.arity r), A.label ⟨r, i⟩ := rfl

/-- Equal incident labels give equal vertex divergences. -/
theorem vertexKirchhoffSum_incident_labels
    {P : PortNetwork} {C : PortCrossing P}
    {A B : V4FlowAssignment C} (r : Fin P.regionCount)
    (h : ∀ i : Fin (P.arity r), A.label ⟨r, i⟩ = B.label ⟨r, i⟩) :
    vertexKirchhoffSum A r = vertexKirchhoffSum B r := by
  apply Finset.sum_congr rfl
  intro i hi
  exact h i

/-- The divergence depends only on labels in the chosen region. -/
theorem vertexKirchhoffSum_crossing_independent
    {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) (r : Fin P.regionCount) :
    vertexKirchhoffSum A r =
      Finset.sum Finset.univ (fun i : Fin (P.arity r) => A.label ⟨r, i⟩) := rfl

/-- A V4 flow is Kirchhoff when every region divergence vanishes.

The predicate imposes zero divergence at every region while retaining the
nonzero and crossing-invariant hypotheses already present in the assignment.
-/
def IsKirchhoffV4Flow {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) : Prop :=
  ∀ r, vertexKirchhoffSum A r = 0

/-- Existence of a Kirchhoff V4 flow on a combinatorial map.

This packages the local conservation law with a chosen port map, without
claiming that the flow is a potential difference or has zero holonomy. -/
def HasKirchhoffV4Flow {P : PortNetwork}
    (M : PortCombinatorialMap P) : Prop :=
  ∃ A : V4FlowAssignment M.crossing, IsKirchhoffV4Flow A

/-- Kirchhoff flow is exactly local zero-divergence conservation. -/
theorem isKirchhoffV4Flow_iff_local_conservation
    {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) :
    IsKirchhoffV4Flow A ↔
      ∀ r, vertexKirchhoffSum A r = 0 := Iff.rfl

/-- Present a port assignment as a flow signature at one region. -/
def assignmentFlowSignature {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) (r : Fin P.regionCount) : FlowSignature where
  arity := P.arity r
  label := fun i => A.label ⟨r, i⟩
  nonzero := fun i => A.nonzero ⟨r, i⟩

/-- The induced flow signature has the original region arity. -/
@[simp] theorem assignmentFlowSignature_arity
    {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) (r : Fin P.regionCount) :
    (assignmentFlowSignature A r).arity = P.arity r := rfl

/-- The induced flow signature reads the original port label. -/
@[simp] theorem assignmentFlowSignature_label
    {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) (r : Fin P.regionCount)
    (i : Fin (assignmentFlowSignature A r).arity) :
    (assignmentFlowSignature A r).label i = A.label ⟨r, i⟩ := rfl

/-- Port divergence is the earlier flow-signature sum.

The port formulation and the historical flow-signature formulation compute
the same finite sum after labels are repackaged by region. -/
theorem vertexKirchhoffSum_eq_flowSum
    {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) (r : Fin P.regionCount) :
    vertexKirchhoffSum A r = flowSum (assignmentFlowSignature A r) := rfl

/-- Port Kirchhoff conservation is the flow-conservation predicate. -/
theorem isKirchhoffV4Flow_iff_flowConserved
    {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) :
    IsKirchhoffV4Flow A ↔
      ∀ r, FlowConserved (assignmentFlowSignature A r) := by
  rfl

/-- V4 zero-sum is equivalent to the two parity equalities.

The Klein four-group equation splits into the two parity constraints on the
counts of the named nonzero directions. -/
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

/-- Kirchhoff conservation does not mention a rotation system. -/
theorem isKirchhoffV4Flow_ignores_rotation
    {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) :
    IsKirchhoffV4Flow A ↔ IsKirchhoffV4Flow A := Iff.rfl

/-- The flow condition is a local divergence statement, not tension itself.

This restates the semantic boundary: Kirchhoff conservation concerns sums at
vertices, whereas tension/zero-holonomy concerns differences around cycles.
-/
theorem isKirchhoffV4Flow_distinct_from_tension
    {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) :
    IsKirchhoffV4Flow A ↔ ∀ r, vertexKirchhoffSum A r = 0 := Iff.rfl

end DkMath.Tromino
