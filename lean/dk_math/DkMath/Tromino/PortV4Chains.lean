/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.LocalFrameEquiv
import DkMath.Tromino.PortF2Chains
import DkMath.Tromino.PortKirchhoffFlow

namespace DkMath.Tromino

open scoped BigOperators

/-!
# V4-valued chain coordinates

The Klein four-group `TrominoState` is represented by two F₂ coordinates.
This module transports the port vertex, edge, and face chain spaces into
that coordinate form, so V4-valued conservation becomes two ordinary F₂
boundary equations.  The final identities record that the coordinate
boundary complex still satisfies `∂₁ ∘ ∂₂ = 0`.
-/

/-- V4-valued vertex chains on the region carrier. -/
abbrev PortV4VertexChain (P : PortNetwork) :=
  Fin P.regionCount → TrominoState

/-- V4-valued edge chains on crossing orbits. -/
abbrev PortV4EdgeChain {P : PortNetwork} (C : PortCrossing P) :=
  PortEdgeCell C → TrominoState

/-- V4-valued face chains on face orbits. -/
abbrev PortV4FaceChain {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) := PortFaceCell R C → TrominoState

/-- Linear equivalence between V4-valued functions and two F₂ functions. -/
def v4FunEquiv (α : Type*) :
    (α → TrominoState) ≃ₗ[PortF2]
      ((α → PortF2) × (α → PortF2)) where
  toFun := fun x => (fun a => (x a).1, fun a => (x a).2)
  invFun := fun x => fun a => (x.1 a, x.2 a)
  left_inv := by
    intro x
    funext a
    apply Prod.ext <;> rfl
  right_inv := by
    intro x
    rcases x with ⟨x, y⟩
    apply Prod.ext <;> funext a <;> rfl
  map_add' := by
    intro x y
    apply Prod.ext <;> funext a <;> rfl
  map_smul' := by
    intro a x
    apply Prod.ext <;> funext b <;> rfl

/-- Coordinate equivalence for vertex chains. -/
def v4VertexChainEquiv {P : PortNetwork} :
    PortV4VertexChain P ≃ₗ[PortF2]
      (PortVertexChain P × PortVertexChain P) :=
  v4FunEquiv (Fin P.regionCount)

/-- Coordinate equivalence for edge chains. -/
def v4EdgeChainEquiv {P : PortNetwork} {C : PortCrossing P} :
    PortV4EdgeChain C ≃ₗ[PortF2]
      (PortEdgeChain C × PortEdgeChain C) :=
  v4FunEquiv (PortEdgeCell C)

/-- Coordinate equivalence for face chains. -/
def v4FaceChainEquiv {P : PortNetwork} {R : PortLocalRotation P}
    {C : PortCrossing P} :
    PortV4FaceChain R C ≃ₗ[PortF2]
      (PortFaceChain R C × PortFaceChain R C) :=
  v4FunEquiv (PortFaceCell R C)

@[simp] theorem v4VertexChainEquiv_fst {P : PortNetwork}
    (x : PortV4VertexChain P) (r : Fin P.regionCount) :
    (v4VertexChainEquiv x).1 r = (x r).1 := rfl

@[simp] theorem v4VertexChainEquiv_snd {P : PortNetwork}
    (x : PortV4VertexChain P) (r : Fin P.regionCount) :
    (v4VertexChainEquiv x).2 r = (x r).2 := rfl

@[simp] theorem v4EdgeChainEquiv_fst {P : PortNetwork} {C : PortCrossing P}
    (x : PortV4EdgeChain C) (E : PortEdgeCell C) :
    (v4EdgeChainEquiv x).1 E = (x E).1 := rfl

@[simp] theorem v4EdgeChainEquiv_snd {P : PortNetwork} {C : PortCrossing P}
    (x : PortV4EdgeChain C) (E : PortEdgeCell C) :
    (v4EdgeChainEquiv x).2 E = (x E).2 := rfl

@[simp] theorem v4FaceChainEquiv_fst {P : PortNetwork}
    {R : PortLocalRotation P} {C : PortCrossing P}
    (x : PortV4FaceChain R C) (F : PortFaceCell R C) :
    (v4FaceChainEquiv x).1 F = (x F).1 := rfl

@[simp] theorem v4FaceChainEquiv_snd {P : PortNetwork}
    {R : PortLocalRotation P} {C : PortCrossing P}
    (x : PortV4FaceChain R C) (F : PortFaceCell R C) :
    (v4FaceChainEquiv x).2 F = (x F).2 := rfl

/-- V4-valued first boundary, obtained by summing endpoint labels. -/
def portV4Boundary1 {P : PortNetwork} (C : PortCrossing P) :
    PortV4EdgeChain C →ₗ[PortF2] PortV4VertexChain P :=
  { toFun := fun x r =>
      ∑ E : PortEdgeCell C, edgeVertexIncidence E r • x E
    map_add' := by
      intro x y
      funext r
      simp [Finset.sum_add_distrib]
    map_smul' := by
      intro a x
      funext r
      simp [smul_smul, Finset.smul_sum, mul_comm] }

/-- V4-valued second boundary, obtained by summing face boundaries. -/
def portV4Boundary2 {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) :
    PortV4FaceChain R C →ₗ[PortF2] PortV4EdgeChain C :=
  { toFun := fun y E =>
      ∑ F : PortFaceCell R C, faceEdgeIncidence F E • y F
    map_add' := by
      intro x y
      funext E
      simp [Finset.sum_add_distrib]
    map_smul' := by
      intro a x
      funext E
      simp [smul_smul, Finset.smul_sum, mul_comm] }

/-- The first V4 boundary's first coordinate is the F₂ boundary. -/
theorem portV4Boundary1_fst {P : PortNetwork} (C : PortCrossing P)
    (x : PortV4EdgeChain C) :
    (v4VertexChainEquiv (portV4Boundary1 C x)).1 =
      portBoundary1 C (v4EdgeChainEquiv x).1 := by
  funext r
  change (∑ E : PortEdgeCell C, edgeVertexIncidence E r • x E).1 =
    ∑ E : PortEdgeCell C, (x E).1 * edgeVertexIncidence E r
  rw [Prod.fst_sum]
  apply Finset.sum_congr rfl
  intro E hE
  simp [smul_eq_mul, mul_comm]

/-- The first V4 boundary's second coordinate is the F₂ boundary. -/
theorem portV4Boundary1_snd {P : PortNetwork} (C : PortCrossing P)
    (x : PortV4EdgeChain C) :
    (v4VertexChainEquiv (portV4Boundary1 C x)).2 =
      portBoundary1 C (v4EdgeChainEquiv x).2 := by
  funext r
  change (∑ E : PortEdgeCell C, edgeVertexIncidence E r • x E).2 =
    ∑ E : PortEdgeCell C, (x E).2 * edgeVertexIncidence E r
  rw [Prod.snd_sum]
  apply Finset.sum_congr rfl
  intro E hE
  simp [smul_eq_mul, mul_comm]

/-- The second V4 boundary's first coordinate is the F₂ boundary. -/
theorem portV4Boundary2_fst {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (y : PortV4FaceChain R C) :
    (v4EdgeChainEquiv (portV4Boundary2 R C y)).1 =
      portBoundary2 R C (v4FaceChainEquiv y).1 := by
  funext E
  change (∑ F : PortFaceCell R C, faceEdgeIncidence F E • y F).1 =
    ∑ F : PortFaceCell R C, (y F).1 * faceEdgeIncidence F E
  rw [Prod.fst_sum]
  apply Finset.sum_congr rfl
  intro F hF
  simp [smul_eq_mul, mul_comm]

/-- The second V4 boundary's second coordinate is the F₂ boundary. -/
theorem portV4Boundary2_snd {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (y : PortV4FaceChain R C) :
    (v4EdgeChainEquiv (portV4Boundary2 R C y)).2 =
      portBoundary2 R C (v4FaceChainEquiv y).2 := by
  funext E
  change (∑ F : PortFaceCell R C, faceEdgeIncidence F E • y F).2 =
    ∑ F : PortFaceCell R C, (y F).2 * faceEdgeIncidence F E
  rw [Prod.snd_sum]
  apply Finset.sum_congr rfl
  intro F hF
  simp [smul_eq_mul, mul_comm]

/-- The kernel of the V4 first boundary. -/
def PortV4CycleSpace {P : PortNetwork} (C : PortCrossing P) :
    Submodule PortF2 (PortV4EdgeChain C) := LinearMap.ker (portV4Boundary1 C)

/-- The image of the V4 second boundary. -/
def PortV4FaceBoundarySpace {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) : Submodule PortF2 (PortV4EdgeChain C) :=
  LinearMap.range (portV4Boundary2 R C)

/-- The V4 chain-complex identity `∂₁ ∘ ∂₂ = 0`. -/
theorem portV4Boundary1_boundary2 {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P) :
    (portV4Boundary1 C).comp (portV4Boundary2 R C) = 0 := by
  apply LinearMap.ext
  intro y
  change portV4Boundary1 C (portV4Boundary2 R C y) = 0
  apply (v4VertexChainEquiv (P := P)).injective
  apply Prod.ext
  · rw [portV4Boundary1_fst, portV4Boundary2_fst]
    have h := congrArg
      (fun L : PortFaceChain R C →ₗ[PortF2] PortVertexChain P => L
        ((v4FaceChainEquiv y).1)) (portBoundary1_boundary2 R C)
    simpa using h
  · rw [portV4Boundary1_snd, portV4Boundary2_snd]
    have h := congrArg
      (fun L : PortFaceChain R C →ₗ[PortF2] PortVertexChain P => L
        ((v4FaceChainEquiv y).2)) (portBoundary1_boundary2 R C)
    simpa using h

/-- Membership in the V4 cycle space is equivalent to zero divergence. -/
theorem mem_portV4CycleSpace_iff {P : PortNetwork} (C : PortCrossing P)
    (x : PortV4EdgeChain C) :
    x ∈ PortV4CycleSpace C ↔
      (v4EdgeChainEquiv x).1 ∈ PortCycleSpace C ∧
        (v4EdgeChainEquiv x).2 ∈ PortCycleSpace C := by
  constructor
  · intro hx
    have hz : portV4Boundary1 C x = 0 := hx
    have hfst := congrArg
      (fun z : PortV4VertexChain P => (v4VertexChainEquiv z).1) hz
    have hsnd := congrArg
      (fun z : PortV4VertexChain P => (v4VertexChainEquiv z).2) hz
    rw [portV4Boundary1_fst] at hfst
    rw [portV4Boundary1_snd] at hsnd
    constructor
    · change portBoundary1 C (v4EdgeChainEquiv x).1 = 0
      simpa using hfst
    · change portBoundary1 C (v4EdgeChainEquiv x).2 = 0
      simpa using hsnd
  · rintro ⟨hfst, hsnd⟩
    change portBoundary1 C (v4EdgeChainEquiv x).1 = 0 at hfst
    change portBoundary1 C (v4EdgeChainEquiv x).2 = 0 at hsnd
    change portV4Boundary1 C x = 0
    apply (v4VertexChainEquiv (P := P)).injective
    apply Prod.ext
    · rw [portV4Boundary1_fst]
      simpa using hfst
    · rw [portV4Boundary1_snd]
      simpa using hsnd

/-- Every V4 face boundary is a V4 cycle. -/
theorem portV4FaceBoundarySpace_le_cycleSpace {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P) :
    PortV4FaceBoundarySpace R C ≤ PortV4CycleSpace C := by
  intro x hx
  rcases hx with ⟨y, rfl⟩
  change portV4Boundary1 C (portV4Boundary2 R C y) = 0
  simpa using congrArg (fun L => L y) (portV4Boundary1_boundary2 R C)

theorem deltaA_coordinates : deltaA = ((1 : PortF2), 0) := rfl
theorem deltaB_coordinates : deltaB = ((0 : PortF2), 1) := rfl
theorem deltaC_coordinates : deltaC = ((1 : PortF2), 1) := rfl

theorem deltaA_add_deltaB_eq_deltaC : deltaA + deltaB = deltaC :=
  deltaA_add_deltaB

theorem deltaA_add_deltaB_add_deltaC_eq_zero :
    deltaA + deltaB + deltaC = 0 := deltaA_add_deltaB_add_deltaC

theorem vertexKirchhoffSum_eq_zero_iff_coordinates
    {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) (r : Fin P.regionCount) :
    vertexKirchhoffSum A r = 0 ↔
      (vertexKirchhoffSum A r).1 = 0 ∧
        (vertexKirchhoffSum A r).2 = 0 := by
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨h₁, h₂⟩
    exact Prod.ext h₁ h₂

theorem vertexKirchhoffSum_coordinates_are_flow_coordinates
    {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) (r : Fin P.regionCount) :
    vertexKirchhoffSum A r = flowSum (assignmentFlowSignature A r) := rfl

end DkMath.Tromino
