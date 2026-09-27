/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortFaceStarSubdivision
import DkMath.Tromino.PortF2Exactness

#print "file: DkMath.Tromino.PortTriangulationReduction"

/-!
# Face-star triangulation reduction

This module records the semantic crossing and rotation permutations for the
face-star carrier. The actual dependent-Fin transport is kept separate so
that these operations can be checked without duplicating their mathematics.

The central combinatorial fact is that old-edge, radial-old, and
radial-center darts form a three-step face orbit. The dependent codecs below
transport this semantic picture to the finite port network.
-/

namespace DkMath.Tromino

/-! ## Semantic crossing -/

/-- The semantic crossing keeps old edges on the old crossing and swaps the
two darts of each radial edge. -/
def faceStarCrossDesc {P : PortNetwork} (M : PortCombinatorialMap P) :
    FaceStarPortDesc M → FaceStarPortDesc M
  | .oldEdge p => .oldEdge (M.crossing.cross p)
  | .radialOld p => .radialCenter p
  | .radialCenter p => .radialOld p

/-- The semantic crossing is an involution, as required of an unoriented
crossing structure. -/
theorem faceStarCrossDesc_involutive {P : PortNetwork}
    (M : PortCombinatorialMap P) :
    Function.Involutive (faceStarCrossDesc M) := by
  intro d
  cases d with
  | oldEdge p =>
      exact congrArg FaceStarPortDesc.oldEdge (M.crossing.involutive p)
  | radialOld p =>
      rfl
  | radialCenter p =>
      rfl

/-! ## Semantic rotation -/

/-- Semantic local rotation: old and radial-old darts alternate at old
regions, while center darts rotate by the inverse old face step. -/
def faceStarRotateDesc {P : PortNetwork} (M : PortCombinatorialMap P) :
    FaceStarPortDesc M → FaceStarPortDesc M
  | .radialOld p => .oldEdge p
  | .oldEdge p => .radialOld (M.localRotation.rotate p)
  | .radialCenter p =>
      .radialCenter ((portFaceEquiv M.localRotation M.crossing).symm p)

/-- The semantic rotation has an explicit inverse and is therefore a finite
permutation of the new darts. -/
def faceStarRotateDescEquiv {P : PortNetwork} (M : PortCombinatorialMap P) :
    FaceStarPortDesc M ≃ FaceStarPortDesc M where
  toFun := faceStarRotateDesc M
  invFun
    | .oldEdge p => .radialOld p
    | .radialOld p => .oldEdge (M.localRotation.rotate.symm p)
    | .radialCenter p =>
        .radialCenter (portFaceEquiv M.localRotation M.crossing p)
  left_inv := by
    intro d
    cases d with
    | oldEdge p =>
        simp [faceStarRotateDesc]
    | radialOld p =>
        simp [faceStarRotateDesc]
    | radialCenter p =>
        simp [faceStarRotateDesc]
  right_inv := by
    intro d
    cases d with
    | oldEdge p =>
        simp [faceStarRotateDesc]
    | radialOld p =>
        simp [faceStarRotateDesc]
    | radialCenter p =>
        simp [faceStarRotateDesc]

/-! ## Dependent-Fin port codec -/

/-- The abstract vertex index of a port network is its region index. -/
theorem faceStar_vertexCount_eq {P : PortNetwork}
    {M : PortCombinatorialMap P} : M.vertexCount = P.regionCount := by
  simp [PortCombinatorialMap.vertexCount, portRegionVertexCount]

/-- Old-region arity is twice the original arity, matching the two dart
slots introduced at each old port. -/
theorem faceStarOldArity_eq_index {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (r : Fin M.vertexCount) :
    2 * P.arity (Fin.cast faceStar_vertexCount_eq r) =
      (faceStarNetwork M I).arity (oldRegion I r) := by
  change 2 * P.arity (Fin.cast faceStar_vertexCount_eq r) =
    faceStarRegionArity M I
    (finSumFinEquiv.symm (finSumFinEquiv (.inl r)))
  rw [Equiv.symm_apply_apply]
  rfl

/-- A center region has one new port for each old boundary port. -/
theorem faceStarCenterArity_eq {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (F : PortFaceCell M.localRotation M.crossing) :
    F.val.card =
      (faceStarNetwork M I).arity (faceCenterRegion I F) := by
  change F.val.card = faceStarRegionArity M I
    (finSumFinEquiv.symm (finSumFinEquiv (.inr (I.faceEquiv F))))
  rw [Equiv.symm_apply_apply]
  simp [faceStarRegionArity]

/-- Center arity calibration after indexing an old face by `Fin`. -/
theorem faceStarCenterArity_eq_index {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (F : Fin M.faceCount) :
    (I.faceEquiv.symm F).val.card =
      (faceStarNetwork M I).arity
        (faceCenterRegion I (I.faceEquiv.symm F)) := by
  let F' := I.faceEquiv.symm F
  exact faceStarCenterArity_eq I F'

/-- Center arity calibration in the disjoint-sum region carrier. -/
theorem faceStarCenterArity_eq_sum_index {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (F : Fin M.faceCount) :
    (I.faceEquiv.symm F).val.card =
      (faceStarNetwork M I).arity (faceStarRegionEquiv M I (.inr F)) := by
  change (I.faceEquiv.symm F).val.card = faceStarRegionArity M I
    (finSumFinEquiv.symm (finSumFinEquiv (.inr F)))
  rw [Equiv.symm_apply_apply]
  simp [faceStarRegionArity]

/-- Identify each old-region fiber with two copies of the original fiber. -/
def faceStarOldFiberEquiv {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (r : Fin M.vertexCount) :
    Fin ((faceStarNetwork M I).arity (oldRegion I r)) ≃
      Fin 2 × Fin (P.arity
        (Fin.cast faceStar_vertexCount_eq r)) where
  toFun i := finProdFinEquiv.symm
    (Fin.cast (faceStarOldArity_eq_index I r).symm i)
  invFun bi := Fin.cast (faceStarOldArity_eq_index I r)
    (finProdFinEquiv bi)
  left_inv := by
    intro i
    have hcast (x : Fin ((faceStarNetwork M I).arity (oldRegion I r))) :
        Fin.cast (faceStarOldArity_eq_index I r)
            (Fin.cast (faceStarOldArity_eq_index I r).symm x) = x := by
      apply Fin.ext
      rfl
    change Fin.cast (faceStarOldArity_eq_index I r)
      (finProdFinEquiv (finProdFinEquiv.symm
        (Fin.cast (faceStarOldArity_eq_index I r).symm i))) = i
    rw [finProdFinEquiv.apply_symm_apply, hcast]
  right_inv := by
    intro bi
    have hcast (x : Fin (2 * P.arity (Fin.cast faceStar_vertexCount_eq r))) :
        Fin.cast (faceStarOldArity_eq_index I r).symm
            (Fin.cast (faceStarOldArity_eq_index I r) x) = x := by
      apply Fin.ext
      rfl
    have hfin := hcast (finProdFinEquiv bi)
    change finProdFinEquiv.symm
      (Fin.cast (faceStarOldArity_eq_index I r).symm
        (Fin.cast (faceStarOldArity_eq_index I r) (finProdFinEquiv bi))) = bi
    rw [hfin, finProdFinEquiv.symm_apply_apply]

/-- Identify a center-region fiber with the boundary ports of its old face. -/
def faceStarCenterFiberEquiv {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (F : Fin M.faceCount) :
    Fin ((faceStarNetwork M I).arity
      (faceStarRegionEquiv M I (.inr F))) ≃
      {p : PortNetworkPort P // p ∈ (I.faceEquiv.symm F).val} where
  toFun i := (I.facePortEquiv (I.faceEquiv.symm F)).symm
    (Fin.cast (faceStarCenterArity_eq_sum_index I F).symm i)
  invFun q := Fin.cast (faceStarCenterArity_eq_sum_index I F)
    (I.facePortEquiv (I.faceEquiv.symm F) q)
  left_inv := by
    intro i
    have hcast (x : Fin ((faceStarNetwork M I).arity
        (faceStarRegionEquiv M I (.inr F)))) :
        Fin.cast (faceStarCenterArity_eq_sum_index I F)
            (Fin.cast (faceStarCenterArity_eq_sum_index I F).symm x) = x := by
      apply Fin.ext
      rfl
    change Fin.cast (faceStarCenterArity_eq_sum_index I F)
      ((I.facePortEquiv (I.faceEquiv.symm F))
        ((I.facePortEquiv (I.faceEquiv.symm F)).symm
          (Fin.cast (faceStarCenterArity_eq_sum_index I F).symm i))) = i
    rw [(I.facePortEquiv (I.faceEquiv.symm F)).apply_symm_apply, hcast]
  right_inv := by
    intro q
    have hcast (x : Fin ((I.faceEquiv.symm F).val.card)) :
        Fin.cast (faceStarCenterArity_eq_sum_index I F).symm
            (Fin.cast (faceStarCenterArity_eq_sum_index I F) x) = x := by
      apply Fin.ext
      rfl
    have hq : (I.facePortEquiv (I.faceEquiv.symm F)).symm
        (Fin.cast (faceStarCenterArity_eq_sum_index I F).symm
          (Fin.cast (faceStarCenterArity_eq_sum_index I F)
            ((I.facePortEquiv (I.faceEquiv.symm F)) q))) = q := by
      rw [hcast, (I.facePortEquiv (I.faceEquiv.symm F)).symm_apply_apply]
    exact hq

/-- Cast a face-star old-region index to the original region index. -/
def faceStarVertexToOld {P : PortNetwork}
    {M : PortCombinatorialMap P} (r : Fin M.vertexCount) :
    Fin P.regionCount :=
  Fin.cast faceStar_vertexCount_eq r

/-- Cast an original region index into the face-star old-region index type. -/
def faceStarOldToVertex {P : PortNetwork}
    {M : PortCombinatorialMap P} (r : Fin P.regionCount) :
    Fin M.vertexCount :=
  Fin.cast faceStar_vertexCount_eq.symm r

/-- The two region-index casts compose to the identity on original indices. -/
theorem faceStarVertexToOld_oldToVertex {P : PortNetwork}
    {M : PortCombinatorialMap P} (r : Fin P.regionCount) :
    faceStarVertexToOld (M := M) (faceStarOldToVertex (M := M) r) = r := by
  apply Fin.ext
  rfl

/-- The two region-index casts compose to the identity on face-star indices. -/
theorem faceStarOldToVertex_vertexToOld {P : PortNetwork}
    {M : PortCombinatorialMap P} (r : Fin M.vertexCount) :
    faceStarOldToVertex (M := M) (faceStarVertexToOld (M := M) r) = r := by
  apply Fin.ext
  rfl

/-- Package all old-region fibers into the two old dart slots over old ports. -/
def faceStarOldSigmaEquiv {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    (Σ r : Fin M.vertexCount,
      Fin ((faceStarNetwork M I).arity (oldRegion I r))) ≃
      Fin 2 × PortNetworkPort P where
  toFun q :=
    let b := (faceStarOldFiberEquiv I q.1) q.2
    ⟨b.1, ⟨faceStarVertexToOld q.1, b.2⟩⟩
  invFun q :=
    let r := faceStarOldToVertex q.2.1
    have hr : faceStarVertexToOld r = q.2.1 :=
      faceStarVertexToOld_oldToVertex q.2.1
    let i : Fin (P.arity (faceStarVertexToOld r)) :=
      Fin.cast (congrArg P.arity hr).symm q.2.2
    ⟨r, (faceStarOldFiberEquiv I r).symm ⟨q.1, i⟩⟩
  left_inv := by
    rintro ⟨r, i⟩
    dsimp
    simp only [faceStarVertexToOld, faceStarOldToVertex, Fin.cast_cast, Fin.cast_eq_self,
      Prod.mk.eta, Sigma.mk.injEq, heq_eq_eq, true_and]
    exact (faceStarOldFiberEquiv I r).symm_apply_apply i
  right_inv := by
    rintro ⟨b, ⟨r, i⟩⟩
    dsimp
    have hr : faceStarVertexToOld (M := M) (faceStarOldToVertex (M := M) r) = r :=
      faceStarVertexToOld_oldToVertex (M := M) r
    simp only [Equiv.apply_symm_apply]
    apply Prod.ext
    · rfl
    · apply Sigma.ext hr
      apply (Fin.heq_ext_iff (congrArg P.arity hr)).2
      rfl

/-- Package all center-region fibers into the old port carrier. -/
def faceStarCenterSigmaEquiv {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    (Σ F : Fin M.faceCount,
      Fin ((faceStarNetwork M I).arity
        (faceStarRegionEquiv M I (.inr F)))) ≃
      PortNetworkPort P :=
  (Equiv.sigmaCongrRight (fun F => faceStarCenterFiberEquiv I F)).trans
    { toFun := fun q => q.2.1
      invFun := fun p =>
        let F := faceCellOfPort M.localRotation M.crossing p
        ⟨I.faceEquiv F, ⟨p, by
          rw [I.faceEquiv.symm_apply_apply]
          exact faceCellOfPort_mem _ _ _⟩⟩
      left_inv := by
        rintro ⟨F, q⟩
        dsimp
        have hF : faceCellOfPort M.localRotation M.crossing q.1 =
            I.faceEquiv.symm F :=
          (faceCellOfPort_eq_iff M.localRotation M.crossing q.1
            (I.faceEquiv.symm F)).2 q.2
        have hE : I.faceEquiv (faceCellOfPort M.localRotation M.crossing q.1) = F := by
          rw [hF, I.faceEquiv.apply_symm_apply]
        apply Sigma.ext hE
        apply (Subtype.heq_iff_coe_eq (fun x => by simp [hF])).2
        rfl
      right_inv := by
        intro p
        rfl }

/-- Decompose every actual new port into its region summand and local fiber. -/
def faceStarActualRegionEquiv {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    PortNetworkPort (faceStarNetwork M I) ≃
      (Σ s : Fin M.vertexCount ⊕ Fin M.faceCount,
        Fin ((faceStarNetwork M I).arity (faceStarRegionEquiv M I s))) :=
  Equiv.sigmaCongr (faceStarRegionEquiv M I).symm
    (fun r => finCongr (congrArg (fun t =>
      (faceStarNetwork M I).arity t)
      ((faceStarRegionEquiv M I).apply_symm_apply r).symm))

/-- Split new ports into old-region slots and center-region ports. -/
def faceStarPortSumEquiv {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    PortNetworkPort (faceStarNetwork M I) ≃
      (Fin 2 × PortNetworkPort P) ⊕ PortNetworkPort P :=
  (faceStarActualRegionEquiv I).trans
    ((Equiv.sumSigmaDistrib
        (fun s : Fin M.vertexCount ⊕ Fin M.faceCount =>
          Fin ((faceStarNetwork M I).arity (faceStarRegionEquiv M I s)))).trans
      (Equiv.sumCongr (faceStarOldSigmaEquiv I)
        (faceStarCenterSigmaEquiv I)))

/-- Translate the sum decomposition into the semantic three-way descriptor. -/
def faceStarSumDescEquiv {P : PortNetwork} {M : PortCombinatorialMap P} :
    (Fin 2 × PortNetworkPort P) ⊕ PortNetworkPort P ≃
      FaceStarPortDesc M where
  toFun
    | Sum.inl ⟨b, p⟩ => Fin.cases (.oldEdge p) (fun _ => .radialOld p) b
    | Sum.inr p => .radialCenter p
  invFun
    | .oldEdge p => Sum.inl ⟨0, p⟩
    | .radialOld p => Sum.inl ⟨1, p⟩
    | .radialCenter p => Sum.inr p
  left_inv := by
    rintro (⟨b, p⟩ | p)
    · fin_cases b <;> rfl
    · rfl
  right_inv := by
    intro d
    cases d <;> rfl

/-- The complete computable equivalence between actual new ports and semantic
face-star descriptors. -/
def faceStarPortEquiv {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    PortNetworkPort (faceStarNetwork M I) ≃ FaceStarPortDesc M :=
  (faceStarPortSumEquiv I).trans faceStarSumDescEquiv

/-- Encode a semantic descriptor as an actual dependent-Fin port. -/
def faceStarPortEncode {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    FaceStarPortDesc M → PortNetworkPort (faceStarNetwork M I) :=
  (faceStarPortEquiv I).symm

/-- Decode an actual dependent-Fin port into its semantic descriptor. -/
def faceStarPortDecode {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    PortNetworkPort (faceStarNetwork M I) → FaceStarPortDesc M :=
  faceStarPortEquiv I

/-- Decoding an encoded descriptor recovers that descriptor. -/
@[simp] theorem faceStarPortDecode_encode {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (d : FaceStarPortDesc M) :
    faceStarPortDecode I (faceStarPortEncode I d) = d :=
  (faceStarPortEquiv I).apply_symm_apply d

/-- Encoding a decoded port recovers the original port. -/
@[simp] theorem faceStarPortEncode_decode {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort (faceStarNetwork M I)) :
    faceStarPortEncode I (faceStarPortDecode I p) = p :=
  (faceStarPortEquiv I).symm_apply_apply p

private theorem faceStarPortSumEquiv_oldSlot {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) (b : Fin 2) :
    faceStarPortSumEquiv I
        ⟨oldRegion I p.1, oldPortFin I p b⟩ =
      Sum.inl (b, p) := by
  have hi : oldPortFin I p b =
      (faceStarOldFiberEquiv I p.1).symm (b, p.2) := by
    apply Fin.ext
    rfl
  have hfiber : (faceStarOldFiberEquiv I p.1) (oldPortFin I p b) =
      (b, p.2) := by
    rw [hi, (faceStarOldFiberEquiv I p.1).apply_symm_apply]
  have hs : (faceStarRegionEquiv M I).symm
      (oldRegion I p.1) = Sum.inl p.1 := by
    change (faceStarRegionEquiv M I).symm
      ((faceStarRegionEquiv M I) (Sum.inl p.1)) = Sum.inl p.1
    rw [Equiv.symm_apply_apply]
    rfl
  have hactual : faceStarActualRegionEquiv I
      ⟨oldRegion I p.1, oldPortFin I p b⟩ =
        ⟨Sum.inl p.1, oldPortFin I p b⟩ := by
    simp only [faceStarNetwork, faceStarRegionArity, faceStarRegionEquiv, faceStarActualRegionEquiv,
      oldRegion, oldPortFin]
    have hfirst : (faceStarRegionEquiv M I).symm
        ((faceStarRegionEquiv M I) (Sum.inl p.1)) =
          (Sum.inl p.1 : Fin M.vertexCount ⊕ Fin M.faceCount) := by
      exact (faceStarRegionEquiv M I).symm_apply_apply _
    apply Sigma.ext hfirst
    apply (Fin.heq_ext_iff (congrArg (fun s =>
      (faceStarNetwork M I).arity (faceStarRegionEquiv M I s)) hfirst)).2
    rfl
  simp only [faceStarPortSumEquiv, Equiv.trans_apply]
  rw [hactual]
  simp only [Equiv.sumCongr, Equiv.sumSigmaDistrib, Equiv.coe_fn_mk, Sum.map_inl, Sum.inl.injEq]
  change (let q := (faceStarOldFiberEquiv I p.1) (oldPortFin I p b)
    ⟨q.1, ⟨faceStarVertexToOld p.1, q.2⟩⟩) = (b, p)
  rw [hfiber]
  rfl

/-- The codec sends an old-edge descriptor to its actual old-edge port. -/
@[simp] theorem faceStarPortEncode_oldEdge {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    faceStarPortEncode I (.oldEdge p) = faceStarOldEdgePort I p := by
  apply (faceStarPortEquiv I).injective
  simp only [faceStarPortEncode, Equiv.apply_symm_apply,
    faceStarPortEquiv, Equiv.trans_apply]
  rw [show faceStarOldEdgePort I p =
      ⟨oldRegion I p.1, oldPortFin I p 0⟩ by rfl,
    faceStarPortSumEquiv_oldSlot I p 0]
  rfl

/-- The codec sends a radial-old descriptor to its actual radial-old port. -/
@[simp] theorem faceStarPortEncode_radialOld {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    faceStarPortEncode I (.radialOld p) = faceStarRadialOldPort I p := by
  apply (faceStarPortEquiv I).injective
  simp only [faceStarPortEncode, Equiv.apply_symm_apply,
    faceStarPortEquiv, Equiv.trans_apply]
  rw [show faceStarRadialOldPort I p =
      ⟨oldRegion I p.1, oldPortFin I p 1⟩ by rfl,
    faceStarPortSumEquiv_oldSlot I p 1]
  rfl

/-- The codec sends a radial-center descriptor to its actual radial-center
port. -/
@[simp] theorem faceStarPortEncode_radialCenter {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    faceStarPortEncode I (.radialCenter p) = faceStarRadialCenterPort I p := by
  apply (faceStarPortEquiv I).injective
  simp only [faceStarPortEncode, Equiv.apply_symm_apply,
    faceStarPortEquiv, Equiv.trans_apply]
  let F := faceCellOfPort M.localRotation M.crossing p
  let q : {q : PortNetworkPort P // q ∈ F.val} :=
    ⟨p, by exact faceCellOfPort_mem _ _ _⟩
  change .radialCenter p = faceStarSumDescEquiv (faceStarPortSumEquiv I
    ⟨faceCenterRegion I F, centerPortFin I F q⟩)
  have hactual : faceStarActualRegionEquiv I
      ⟨faceCenterRegion I F, centerPortFin I F q⟩ =
        ⟨Sum.inr (I.faceEquiv F), centerPortFin I F q⟩ := by
    simp only [faceStarRegionEquiv, faceStarActualRegionEquiv, faceCenterRegion]
    have hfirst : (faceStarRegionEquiv M I).symm
        ((faceStarRegionEquiv M I) (Sum.inr (I.faceEquiv F))) =
          (Sum.inr (I.faceEquiv F) : Fin M.vertexCount ⊕ Fin M.faceCount) := by
      exact (faceStarRegionEquiv M I).symm_apply_apply _
    apply Sigma.ext hfirst
    apply (Fin.heq_ext_iff (congrArg (fun s =>
      (faceStarNetwork M I).arity (faceStarRegionEquiv M I s)) hfirst)).2
    rfl
  have hF : I.faceEquiv.symm (I.faceEquiv F) = F :=
    I.faceEquiv.symm_apply_apply F
  let q' : {q : PortNetworkPort P //
      q ∈ (I.faceEquiv.symm (I.faceEquiv F)).val} :=
    (I.faceEquiv.symm_apply_apply F).symm ▸ q
  have hport : HEq (I.facePortEquiv F q)
      (I.facePortEquiv (I.faceEquiv.symm (I.faceEquiv F)) q') := by
    dsimp [q']
    congr -- 12 goals
    all_goals try simp only [hF]
    all_goals try rfl  --2 goals
    · have hdom :
        {q : PortNetworkPort P // q ∈ F.val} =
          {q : PortNetworkPort P //
            q ∈ (I.faceEquiv.symm (I.faceEquiv F)).val} :=
      congrArg (fun G : PortFaceCell M.localRotation M.crossing =>
        {q : PortNetworkPort P // q ∈ G.val}) hF.symm
      apply Function.hfunext hdom
      intro a a' haa
      rfl
    · simp
  have hcard : (faceCellOfPort M.localRotation M.crossing p).val.card =
      (I.faceEquiv.symm (I.faceEquiv
        (faceCellOfPort M.localRotation M.crossing p))).val.card := by
    exact congrArg (fun G => G.val.card) hF.symm
  have hval : (I.facePortEquiv F q).val =
      (I.facePortEquiv (I.faceEquiv.symm (I.faceEquiv F)) q').val := by
    exact (Fin.heq_ext_iff hcard).1 hport
  have hfin : centerPortFin I F q =
      (faceStarCenterFiberEquiv I (I.faceEquiv F)).symm q' := by
    apply Fin.ext
    simpa [centerPortFin, faceStarCenterFiberEquiv] using hval
  have hqheq : HEq q' q := by
    dsimp [q']
    exact eqRec_heq_self
      (motive := fun G _ => {q : PortNetworkPort P // q ∈ G.val}) q
      (I.faceEquiv.symm_apply_apply F).symm
  have hqval : q'.val = q.val := by
    apply (Subtype.heq_iff_coe_eq (fun x => by simp [hF])).1
    exact hqheq
  have hcenter : faceStarCenterSigmaEquiv I
      ⟨I.faceEquiv F, centerPortFin I F q⟩ = p := by
    simp only [faceStarCenterSigmaEquiv, Equiv.trans_apply,
      Equiv.sigmaCongrRight]
    rw [hfin]
    simp
    simpa only [q] using hqval
  simp only [faceStarPortSumEquiv, Equiv.trans_apply]
  rw [hactual]
  simp [Equiv.sumSigmaDistrib, Equiv.sumCongr, hcenter]
  rfl

/-! ## Decoder calibration -/

/-- Decode calibration for old-edge ports. -/
@[simp] theorem faceStarPortDecode_oldEdgePort {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    faceStarPortDecode I (faceStarOldEdgePort I p) = .oldEdge p := by
  rw [← faceStarPortEncode_oldEdge I p]
  exact faceStarPortDecode_encode I _

/-- Decode calibration for radial-old ports. -/
@[simp] theorem faceStarPortDecode_radialOldPort {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    faceStarPortDecode I (faceStarRadialOldPort I p) = .radialOld p := by
  rw [← faceStarPortEncode_radialOld I p]
  exact faceStarPortDecode_encode I _

/-- Decode calibration for radial-center ports. -/
@[simp] theorem faceStarPortDecode_radialCenterPort {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    faceStarPortDecode I (faceStarRadialCenterPort I p) = .radialCenter p := by
  rw [← faceStarPortEncode_radialCenter I p]
  exact faceStarPortDecode_encode I _

/-- The semantic source region of a face-star descriptor. -/
def faceStarDescSource {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    FaceStarPortDesc M → Fin (faceStarNetwork M I).regionCount
  | .oldEdge p => oldRegion I p.1
  | .radialOld p => oldRegion I p.1
  | .radialCenter p =>
      faceCenterRegion I (faceCellOfPort M.localRotation M.crossing p)

/-- Decoding an actual port recovers its semantic source region. -/
theorem faceStarPortDecode_source {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    ∀ d : FaceStarPortDesc M,
      (faceStarPortEncode I d).1 = faceStarDescSource I d := by
  intro d
  cases d <;> rfl

/-- Transport the semantic face-star crossing through the port codec. -/
def faceStarCrossing {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    PortCrossing (faceStarNetwork M I) where
  cross := fun p =>
    faceStarPortEncode I
      (faceStarCrossDesc M (faceStarPortDecode I p))
  involutive := by
    intro p
    change faceStarPortEncode I
        (faceStarCrossDesc M
          (faceStarPortDecode I
            (faceStarPortEncode I
              (faceStarCrossDesc M (faceStarPortDecode I p))))) = p
    rw [faceStarPortDecode_encode, faceStarCrossDesc_involutive,
      faceStarPortEncode_decode]
  changesRegion := by
    intro p
    generalize hd : faceStarPortDecode I p = d
    have hp : p.1 = faceStarDescSource I d := by
      rw [← faceStarPortEncode_decode I p, hd]
      exact faceStarPortDecode_source I d
    have hc :
        (faceStarPortEncode I (faceStarCrossDesc M d)).1 =
          faceStarDescSource I (faceStarCrossDesc M d) := by
      exact faceStarPortDecode_source I (faceStarCrossDesc M d)
    cases d with
    | oldEdge q =>
        intro h
        have hs : faceStarDescSource I (faceStarCrossDesc M (.oldEdge q)) =
            faceStarDescSource I (.oldEdge q) := by
          exact hc.symm.trans (h.trans hp)
        apply M.crossing.changesRegion q
        apply (oldRegion_injective I)
        exact hs
    | radialOld q =>
        intro h
        have hs : faceStarDescSource I (faceStarCrossDesc M (.radialOld q)) =
            faceStarDescSource I (.radialOld q) := by
          exact hc.symm.trans (h.trans hp)
        exact (oldRegion_ne_faceCenterRegion I q.1
          (faceCellOfPort M.localRotation M.crossing q)).symm hs
    | radialCenter q =>
        intro h
        have hs : faceStarDescSource I (faceStarCrossDesc M (.radialCenter q)) =
            faceStarDescSource I (.radialCenter q) := by
          exact hc.symm.trans (h.trans hp)
        exact (oldRegion_ne_faceCenterRegion I q.1
          (faceCellOfPort M.localRotation M.crossing q)) hs

/-- Reversing an old face step leaves its face cell unchanged. -/
theorem faceStar_faceCell_portFaceEquiv_symm_eq {P : PortNetwork}
    (M : PortCombinatorialMap P) (p : PortNetworkPort P) :
    faceCellOfPort M.localRotation M.crossing
        ((portFaceEquiv M.localRotation M.crossing).symm p) =
      faceCellOfPort M.localRotation M.crossing p := by
  let q := (portFaceEquiv M.localRotation M.crossing).symm p
  have hstep : portFaceStep M.localRotation M.crossing q = p := by
    dsimp [q, portFaceStep]
    rw [portFaceEquiv_symm_apply, M.crossing.involutive,
      M.localRotation.rotate.apply_symm_apply]
  have hmem := portFaceOrbit_mem_iterate M.localRotation M.crossing q 1
  have hcell := faceCellOfPort_eq_of_mem M.localRotation M.crossing q
    (portFaceStep M.localRotation M.crossing q) hmem
  rw [hstep] at hcell
  exact hcell.symm

/-- Semantic rotation preserves the region source of every dart. -/
theorem faceStarRotateDesc_source {P : PortNetwork}
    (M : PortCombinatorialMap P) (I : PortFaceStarIndexing M)
    (d : FaceStarPortDesc M) :
    faceStarDescSource I (faceStarRotateDesc M d) =
      faceStarDescSource I d := by
  cases d with
  | oldEdge p =>
      exact congrArg (oldRegion I) (M.localRotation.preservesRegion p)
  | radialOld p =>
      rfl
  | radialCenter p =>
      exact congrArg (faceCenterRegion I)
        (faceStar_faceCell_portFaceEquiv_symm_eq M p)

/-- Transport the semantic rotation to the actual new-port carrier. -/
def faceStarLocalRotation {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    PortLocalRotation (faceStarNetwork M I) where
  rotate := (faceStarPortEquiv I).trans
    ((faceStarRotateDescEquiv M).trans (faceStarPortEquiv I).symm)
  preservesRegion := by
    intro p
    let d := faceStarPortDecode I p
    have hp : p.1 = faceStarDescSource I d := by
      rw [← faceStarPortEncode_decode I p]
      exact faceStarPortDecode_source I d
    have hr :
        ((faceStarPortEquiv I).symm
          (faceStarRotateDescEquiv M (faceStarPortEquiv I p))).1 =
          faceStarDescSource I (faceStarRotateDesc M (faceStarPortEquiv I p)) := by
      exact faceStarPortDecode_source I (faceStarRotateDesc M (faceStarPortEquiv I p))
    have hrr :
        ((faceStarPortEquiv I).symm
          (faceStarRotateDesc M (faceStarPortEquiv I p))).1 =
          faceStarDescSource I (faceStarRotateDesc M (faceStarPortEquiv I p)) := by
      simpa [faceStarRotateDescEquiv] using hr
    dsimp [d] at hp ⊢
    change ((faceStarPortEquiv I).symm
      (faceStarRotateDesc M (faceStarPortEquiv I p))).1 = p.1
    rw [hrr]
    exact (faceStarRotateDesc_source M I d).trans hp.symm

/-- Crossing commutes with the descriptor codec. -/
theorem faceStarCrossing_encode {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (d : FaceStarPortDesc M) :
    (faceStarCrossing I).cross (faceStarPortEncode I d) =
      faceStarPortEncode I (faceStarCrossDesc M d) := by
  change faceStarPortEncode I
      (faceStarCrossDesc M
        (faceStarPortDecode I (faceStarPortEncode I d))) = _
  rw [faceStarPortDecode_encode]

/-- Rotation commutes with the descriptor codec. -/
theorem faceStarLocalRotation_encode {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (d : FaceStarPortDesc M) :
    (faceStarLocalRotation I).rotate (faceStarPortEncode I d) =
      faceStarPortEncode I (faceStarRotateDesc M d) := by
  change faceStarPortEncode I
      (faceStarRotateDescEquiv M
        (faceStarPortDecode I (faceStarPortEncode I d))) = _
  rw [faceStarPortDecode_encode]
  rfl

/-! ## Exact constructor formulas -/

@[simp] theorem faceStarCross_oldEdge {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    (faceStarCrossing I).cross (faceStarOldEdgePort I p) =
      faceStarOldEdgePort I (M.crossing.cross p) := by
  rw [← faceStarPortEncode_oldEdge I p, faceStarCrossing_encode]
  change faceStarPortEncode I (.oldEdge (M.crossing.cross p)) = _
  rw [faceStarPortEncode_oldEdge]

@[simp] theorem faceStarCross_radialOld {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    (faceStarCrossing I).cross (faceStarRadialOldPort I p) =
      faceStarRadialCenterPort I p := by
  rw [← faceStarPortEncode_radialOld I p, faceStarCrossing_encode]
  change faceStarPortEncode I (.radialCenter p) = _
  rw [faceStarPortEncode_radialCenter]

@[simp] theorem faceStarCross_radialCenter {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    (faceStarCrossing I).cross (faceStarRadialCenterPort I p) =
      faceStarRadialOldPort I p := by
  rw [← faceStarPortEncode_radialCenter I p, faceStarCrossing_encode]
  change faceStarPortEncode I (.radialOld p) = _
  rw [faceStarPortEncode_radialOld]

@[simp] theorem faceStarRotate_radialOld {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    (faceStarLocalRotation I).rotate (faceStarRadialOldPort I p) =
      faceStarOldEdgePort I p := by
  rw [← faceStarPortEncode_radialOld I p, faceStarLocalRotation_encode]
  change faceStarPortEncode I (.oldEdge p) = _
  rw [faceStarPortEncode_oldEdge]

@[simp] theorem faceStarRotate_oldEdge {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    (faceStarLocalRotation I).rotate (faceStarOldEdgePort I p) =
      faceStarRadialOldPort I (M.localRotation.rotate p) := by
  rw [← faceStarPortEncode_oldEdge I p, faceStarLocalRotation_encode]
  change faceStarPortEncode I (.radialOld (M.localRotation.rotate p)) = _
  rw [faceStarPortEncode_radialOld]

@[simp] theorem faceStarRotate_radialCenter {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    (faceStarLocalRotation I).rotate (faceStarRadialCenterPort I p) =
      faceStarRadialCenterPort I
        ((portFaceEquiv M.localRotation M.crossing).symm p) := by
  rw [← faceStarPortEncode_radialCenter I p, faceStarLocalRotation_encode]
  change faceStarPortEncode I
      (.radialCenter ((portFaceEquiv M.localRotation M.crossing).symm p)) = _
  rw [faceStarPortEncode_radialCenter]

/-! ## Face-star rotation dynamics -/

/-- Every port at an old region is either old-edge or radial-old. -/
theorem faceStar_port_at_oldRegion_cases {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (r : Fin M.vertexCount) (q : PortNetworkPort (faceStarNetwork M I))
    (hq : q.1 = oldRegion I r) :
    ∃ p : PortNetworkPort P,
      p.1 = faceStarVertexToOld r ∧
        (q = faceStarOldEdgePort I p ∨ q = faceStarRadialOldPort I p) := by
  generalize hd : faceStarPortDecode I q = d
  have hs : q.1 = faceStarDescSource I d := by
    calc
      q.1 = (faceStarPortEncode I (faceStarPortDecode I q)).1 :=
        congrArg (fun x : PortNetworkPort (faceStarNetwork M I) => x.1)
          (faceStarPortEncode_decode I q).symm
      _ = faceStarDescSource I (faceStarPortDecode I q) :=
        faceStarPortDecode_source I (faceStarPortDecode I q)
      _ = faceStarDescSource I d := by rw [hd]
  have hqenc : faceStarPortEncode I d = q :=
    by
      calc
        faceStarPortEncode I d = faceStarPortEncode I (faceStarPortDecode I q) := by
          rw [hd]
        _ = q := faceStarPortEncode_decode I q
  cases d with
  | oldEdge p =>
      have hs' : q.1 = oldRegion I p.1 := by
        simpa [faceStarDescSource] using hs
      have hpr : p.1 = r := by
        apply oldRegion_injective I
        exact hs'.symm.trans hq
      refine ⟨p, ?_, ?_⟩
      · apply Fin.ext
        exact congrArg Fin.val hpr
      · left
        rw [← hqenc]
        exact faceStarPortEncode_oldEdge I p
  | radialOld p =>
      have hs' : q.1 = oldRegion I p.1 := by
        simpa [faceStarDescSource] using hs
      have hpr : p.1 = r := by
        apply oldRegion_injective I
        exact hs'.symm.trans hq
      refine ⟨p, ?_, ?_⟩
      · apply Fin.ext
        exact congrArg Fin.val hpr
      · right
        rw [← hqenc]
        exact faceStarPortEncode_radialOld I p
  | radialCenter p =>
      have hs' : q.1 = faceCenterRegion I
          (faceCellOfPort M.localRotation M.crossing p) := by
        simpa [faceStarDescSource] using hs
      exfalso
      exact oldRegion_ne_faceCenterRegion I r
        (faceCellOfPort M.localRotation M.crossing p)
        (hq.symm.trans hs')

/-- Every port at a center region is a radial-center port. -/
theorem faceStar_port_at_centerRegion_cases {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (F : PortFaceCell M.localRotation M.crossing)
    (q : PortNetworkPort (faceStarNetwork M I))
    (hq : q.1 = faceCenterRegion I F) :
    ∃ p : PortNetworkPort P, p ∈ F.val ∧
      q = faceStarRadialCenterPort I p := by
  generalize hd : faceStarPortDecode I q = d
  have hs : q.1 = faceStarDescSource I d := by
    calc
      q.1 = (faceStarPortEncode I (faceStarPortDecode I q)).1 :=
        congrArg (fun x : PortNetworkPort (faceStarNetwork M I) => x.1)
          (faceStarPortEncode_decode I q).symm
      _ = faceStarDescSource I (faceStarPortDecode I q) :=
        faceStarPortDecode_source I (faceStarPortDecode I q)
      _ = faceStarDescSource I d := by rw [hd]
  have hqenc : faceStarPortEncode I d = q :=
    by
      calc
        faceStarPortEncode I d = faceStarPortEncode I (faceStarPortDecode I q) := by
          rw [hd]
        _ = q := faceStarPortEncode_decode I q
  cases d with
  | oldEdge p =>
      have hs' : q.1 = oldRegion I p.1 := by
        simpa [faceStarDescSource] using hs
      exfalso
      exact oldRegion_ne_faceCenterRegion I p.1 F
        (hs'.symm.trans hq)
  | radialOld p =>
      have hs' : q.1 = oldRegion I p.1 := by
        simpa [faceStarDescSource] using hs
      exfalso
      exact oldRegion_ne_faceCenterRegion I p.1 F
        (hs'.symm.trans hq)
  | radialCenter p =>
      have hs' : q.1 = faceCenterRegion I
          (faceCellOfPort M.localRotation M.crossing p) := by
        simpa [faceStarDescSource] using hs
      have hcell : faceCellOfPort M.localRotation M.crossing p = F := by
        apply faceCenterRegion_injective I
        exact hs'.symm.trans hq
      refine ⟨p, ?_, ?_⟩
      · rw [← hcell]
        exact faceCellOfPort_mem _ _ _
      · rw [← hqenc]
        exact faceStarPortEncode_radialCenter I p

/-- Even rotation iterates at an old region return to the radial-old slot
after following the corresponding old rotation. -/
theorem faceStarRotate_radialOld_iterate_even {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (n : Nat) (p : PortNetworkPort P) :
    ((faceStarLocalRotation I).rotate^[2 * n])
        (faceStarRadialOldPort I p) =
      faceStarRadialOldPort I ((M.localRotation.rotate^[n]) p) := by
  have hcomm (f : PortNetworkPort P → PortNetworkPort P) (n : Nat)
      (x : PortNetworkPort P) :
      f (f^[n] x) = (f^[n]) (f x) :=
    (Function.iterate_succ_apply' f n x).symm.trans
      (Function.iterate_succ_apply f n x)
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show 2 * (n + 1) = 2 + 2 * n by omega,
        Function.iterate_add_apply]
      rw [ih]
      simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
      rw [faceStarRotate_radialOld, faceStarRotate_oldEdge]
      congr 1
      exact hcomm M.localRotation.rotate n p

/-- Odd rotation iterates at an old region land in the old-edge slot. -/
theorem faceStarRotate_radialOld_iterate_odd {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (n : Nat) (p : PortNetworkPort P) :
    ((faceStarLocalRotation I).rotate^[2 * n + 1])
        (faceStarRadialOldPort I p) =
      faceStarOldEdgePort I ((M.localRotation.rotate^[n]) p) := by
  rw [show 2 * n + 1 = 1 + 2 * n by omega, Function.iterate_add_apply]
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [faceStarRotate_radialOld_iterate_even, faceStarRotate_radialOld]

/-- Even rotation iterates preserve the old-edge slot while advancing the old
rotation. -/
theorem faceStarRotate_oldEdge_iterate_even {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (n : Nat) (p : PortNetworkPort P) :
    ((faceStarLocalRotation I).rotate^[2 * n])
        (faceStarOldEdgePort I p) =
      faceStarOldEdgePort I ((M.localRotation.rotate^[n]) p) := by
  rw [← faceStarRotate_radialOld I p]
  change ((faceStarLocalRotation I).rotate^[2 * n])
      (((faceStarLocalRotation I).rotate^[1])
        (faceStarRadialOldPort I p)) = _
  rw [← Function.iterate_add_apply]
  rw [faceStarRotate_radialOld_iterate_odd]

/-- Odd rotation iterates land in the radial-old slot. -/
theorem faceStarRotate_oldEdge_iterate_odd {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (n : Nat) (p : PortNetworkPort P) :
    ((faceStarLocalRotation I).rotate^[2 * n + 1])
        (faceStarOldEdgePort I p) =
      faceStarRadialOldPort I ((M.localRotation.rotate^[n + 1]) p) := by
  have hcomm (f : PortNetworkPort P → PortNetworkPort P) (n : Nat)
      (x : PortNetworkPort P) :
      f (f^[n] x) = (f^[n]) (f x) :=
    (Function.iterate_succ_apply' f n x).symm.trans
      (Function.iterate_succ_apply f n x)
  rw [show 2 * n + 1 = 1 + 2 * n by omega, Function.iterate_add_apply]
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [faceStarRotate_oldEdge_iterate_even, faceStarRotate_oldEdge]
  congr 1
  exact hcomm M.localRotation.rotate n p

/-- The transported rotation is cyclic on every old-region fiber. -/
theorem faceStar_oldRegion_cyclic {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (r : Fin M.vertexCount)
    (q1 q2 : PortNetworkPort (faceStarNetwork M I))
    (h1 : q1.1 = oldRegion I r) (h2 : q2.1 = oldRegion I r) :
    ∃ n : Nat, ((faceStarLocalRotation I).rotate^[n]) q1 = q2 := by
  rcases faceStar_port_at_oldRegion_cases I r q1 h1 with
    ⟨p1, hp1, hq1⟩
  rcases faceStar_port_at_oldRegion_cases I r q2 h2 with
    ⟨p2, hp2, hq2⟩
  have hp12 : p1.1 = p2.1 := by
    exact hp1.trans hp2.symm
  have reach (p q : PortNetworkPort P) (h : p.1 = q.1) :
      ∃ n : Nat, (M.localRotation.rotate^[n]) p = q :=
    M.rotation_reaches_same_region p q h
  rcases hq1 with rfl | rfl <;> rcases hq2 with rfl | rfl
  · rcases reach p1 p2 hp12 with ⟨n, hn⟩
    exact ⟨2 * n, by simpa [hn] using
      faceStarRotate_oldEdge_iterate_even I n p1⟩
  · have hrot : (M.localRotation.rotate p1).1 = p2.1 :=
      (M.localRotation.preservesRegion p1).trans hp12
    rcases reach (M.localRotation.rotate p1) p2 hrot with ⟨n, hn⟩
    refine ⟨2 * n + 1, ?_⟩
    rw [faceStarRotate_oldEdge_iterate_odd]
    congr 1
  · rcases reach p1 p2 hp12 with ⟨n, hn⟩
    exact ⟨2 * n + 1, by simpa [hn] using
      faceStarRotate_radialOld_iterate_odd I n p1⟩
  · rcases reach p1 p2 hp12 with ⟨n, hn⟩
    exact ⟨2 * n, by simpa [hn] using
      faceStarRotate_radialOld_iterate_even I n p1⟩

/-- The inverse face-step orbit reaches every port of an old face. -/
theorem oldFace_backward_reachable {P : PortNetwork}
    {M : PortCombinatorialMap P} (F : PortFaceCell M.localRotation M.crossing)
    (p q : PortNetworkPort P) (hp : p ∈ F.val) (hq : q ∈ F.val) :
    ∃ n : Nat,
      ((portFaceEquiv M.localRotation M.crossing).symm^[n]) p = q := by
  have hqorbit : q ∈ portFaceOrbit M.localRotation M.crossing p := by
    have hcellp : faceCellOfPort M.localRotation M.crossing p = F :=
      (faceCellOfPort_eq_iff M.localRotation M.crossing p F).2 hp
    change q ∈ (faceCellOfPort M.localRotation M.crossing p).val
    rw [hcellp]
    exact hq
  have hporbit : p ∈ portFaceOrbit M.localRotation M.crossing q :=
    portFaceOrbit_reverse_mem M.localRotation M.crossing p q hqorbit
  rcases (portFaceOrbit_mem_iff_iterate M.localRotation M.crossing q p).1
      hporbit with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  have hinv : ∀ (k : Nat) (x : PortNetworkPort P),
      ((portFaceEquiv M.localRotation M.crossing).symm^[k])
        ((portFaceEquiv M.localRotation M.crossing)^[k] x) = x := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
        intro x
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply']
        simp [ih]
  rw [← hn]
  exact hinv n q

/-- Rotation around a center region follows the inverse old face-step orbit. -/
theorem faceStarRotate_radialCenter_iterate {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (n : Nat) (p : PortNetworkPort P) :
    ((faceStarLocalRotation I).rotate^[n])
        (faceStarRadialCenterPort I p) =
      faceStarRadialCenterPort I
        ((portFaceEquiv M.localRotation M.crossing).symm^[n] p) := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, faceStarRotate_radialCenter]
      simpa only [Function.iterate_succ_apply] using
        ih ((portFaceEquiv M.localRotation M.crossing).symm p)

/-- The transported rotation is cyclic on every center-region fiber. -/
theorem faceStar_centerRegion_cyclic {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (F : PortFaceCell M.localRotation M.crossing)
    (q1 q2 : PortNetworkPort (faceStarNetwork M I))
    (h1 : q1.1 = faceCenterRegion I F)
    (h2 : q2.1 = faceCenterRegion I F) :
    ∃ n : Nat, ((faceStarLocalRotation I).rotate^[n]) q1 = q2 := by
  rcases faceStar_port_at_centerRegion_cases I F q1 h1 with
    ⟨p1, hp1, hq1⟩
  rcases faceStar_port_at_centerRegion_cases I F q2 h2 with
    ⟨p2, hp2, hq2⟩
  rcases oldFace_backward_reachable F p1 p2 hp1 hp2 with ⟨n, hn⟩
  exact ⟨n, by simpa [hq1, hq2, hn] using
    faceStarRotate_radialCenter_iterate I n p1⟩

/-- Package the transported local rotation as a cyclic rotation system. -/
def faceStarRotationSystem {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    PortRotationSystem (faceStarNetwork M I) where
  toPortLocalRotation := faceStarLocalRotation I
  cyclic := by
    intro s i j
    rcases finSumFinEquiv.surjective s with ⟨b, rfl⟩
    cases b with
    | inl r =>
        exact faceStar_oldRegion_cyclic I r
          ⟨_, i⟩ ⟨_, j⟩ rfl rfl
    | inr F =>
        let F' := I.faceEquiv.symm F
        exact faceStar_centerRegion_cyclic I F'
          ⟨_, i⟩ ⟨_, j⟩
          (by
            change finSumFinEquiv (Sum.inr F) = faceCenterRegion I F'
            dsimp [F', faceCenterRegion, faceStarRegionEquiv]
            rw [I.faceEquiv.apply_symm_apply]
            apply Fin.ext
            rfl)
          (by
            change finSumFinEquiv (Sum.inr F) = faceCenterRegion I F'
            dsimp [F', faceCenterRegion, faceStarRegionEquiv]
            rw [I.faceEquiv.apply_symm_apply]
            apply Fin.ext
            rfl)

/-- One face step from an old-edge dart moves to the radial-old dart of the
next old boundary port. -/
@[simp] theorem faceStarFaceStep_oldEdge {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    portFaceStep (faceStarRotationSystem I).toPortLocalRotation
        (faceStarCrossing I) (faceStarOldEdgePort I p) =
      faceStarRadialOldPort I
        (portFaceStep M.localRotation M.crossing p) := by
  change (faceStarLocalRotation I).rotate
      ((faceStarCrossing I).cross (faceStarOldEdgePort I p)) = _
  rw [faceStarCross_oldEdge, faceStarRotate_oldEdge]
  rfl

/-- One face step from a radial-old dart reaches the corresponding center
dart. -/
@[simp] theorem faceStarFaceStep_radialOld {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    portFaceStep (faceStarRotationSystem I).toPortLocalRotation
        (faceStarCrossing I) (faceStarRadialOldPort I p) =
      faceStarRadialCenterPort I
        ((portFaceEquiv M.localRotation M.crossing).symm p) := by
  change (faceStarLocalRotation I).rotate
      ((faceStarCrossing I).cross (faceStarRadialOldPort I p)) = _
  rw [faceStarCross_radialOld, faceStarRotate_radialCenter]

/-- One face step from a radial-center dart returns to the old-edge dart. -/
@[simp] theorem faceStarFaceStep_radialCenter {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    portFaceStep (faceStarRotationSystem I).toPortLocalRotation
        (faceStarCrossing I) (faceStarRadialCenterPort I p) =
      faceStarOldEdgePort I p := by
  change (faceStarLocalRotation I).rotate
      ((faceStarCrossing I).cross (faceStarRadialCenterPort I p)) = _
  rw [faceStarCross_radialCenter, faceStarRotate_radialOld]

/-- Every old-edge face orbit closes after exactly three steps. -/
theorem faceStarFaceStep_oldEdge_return {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    (portFaceStep (faceStarRotationSystem I).toPortLocalRotation
      (faceStarCrossing I))^[3] (faceStarOldEdgePort I p) =
      faceStarOldEdgePort I p := by
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply,
    faceStarFaceStep_oldEdge, faceStarFaceStep_radialOld,
    faceStarFaceStep_radialCenter]
  simp only [portFaceEquiv, Equiv.symm_mk, portFaceStep, Equiv.coe_fn_mk, Equiv.symm_apply_apply]
  rw [M.crossing.involutive]

/-- Every radial-old face orbit closes after three steps. -/
theorem faceStarFaceStep_radialOld_return {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    (portFaceStep (faceStarRotationSystem I).toPortLocalRotation
      (faceStarCrossing I))^[3] (faceStarRadialOldPort I p) =
      faceStarRadialOldPort I p := by
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply,
    faceStarFaceStep_radialOld, faceStarFaceStep_radialCenter,
    faceStarFaceStep_oldEdge]
  simp only [portFaceStep, portFaceEquiv, Equiv.symm_mk, Equiv.coe_fn_mk]
  rw [M.crossing.involutive]
  exact congrArg (faceStarRadialOldPort I)
    (M.localRotation.rotate.apply_symm_apply p)

/-- Every radial-center face orbit closes after three steps. -/
theorem faceStarFaceStep_radialCenter_return {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    (portFaceStep (faceStarRotationSystem I).toPortLocalRotation
      (faceStarCrossing I))^[3] (faceStarRadialCenterPort I p) =
      faceStarRadialCenterPort I p := by
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply,
    faceStarFaceStep_radialCenter, faceStarFaceStep_oldEdge,
    faceStarFaceStep_radialOld]
  simp only [portFaceEquiv, Equiv.symm_mk, portFaceStep, Equiv.coe_fn_mk, Equiv.symm_apply_apply]
  rw [M.crossing.involutive]

private theorem faceStar_oldEdge_ne_radialOld {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p q : PortNetworkPort P) :
    faceStarOldEdgePort I p ≠ faceStarRadialOldPort I q := by
  intro h
  have h' := congrArg (faceStarPortDecode I) h
  simp at h'

private theorem faceStar_oldEdge_ne_radialCenter {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p q : PortNetworkPort P) :
    faceStarOldEdgePort I p ≠ faceStarRadialCenterPort I q := by
  intro h
  have h' := congrArg (faceStarPortDecode I) h
  simp at h'

private theorem faceStar_radialOld_ne_radialCenter {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p q : PortNetworkPort P) :
    faceStarRadialOldPort I p ≠ faceStarRadialCenterPort I q := by
  intro h
  have h' := congrArg (faceStarPortDecode I) h
  simp at h'

/-- An old-edge dart does not return after one face step. -/
theorem faceStarFaceStep_oldEdge_no_return_one {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
  (portFaceStep (faceStarRotationSystem I).toPortLocalRotation
      (faceStarCrossing I))^[1] (faceStarOldEdgePort I p) ≠
      faceStarOldEdgePort I p := by
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [faceStarFaceStep_oldEdge]
  exact (faceStar_oldEdge_ne_radialOld I p
    (portFaceStep M.localRotation M.crossing p)).symm

/-- An old-edge dart does not return after two face steps. -/
theorem faceStarFaceStep_oldEdge_no_return_two {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    (portFaceStep (faceStarRotationSystem I).toPortLocalRotation
      (faceStarCrossing I))^[2] (faceStarOldEdgePort I p) ≠
      faceStarOldEdgePort I p := by
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [faceStarFaceStep_oldEdge, faceStarFaceStep_radialOld]
  have hphi : (portFaceEquiv M.localRotation M.crossing).symm
      (portFaceStep M.localRotation M.crossing p) = p := by
    rw [← portFaceEquiv_apply]
    exact (portFaceEquiv M.localRotation M.crossing).symm_apply_apply p
  rw [hphi]
  exact (faceStar_oldEdge_ne_radialCenter I p p).symm

/-- A radial-old dart does not return after one face step. -/
theorem faceStarFaceStep_radialOld_no_return_one {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    (portFaceStep (faceStarRotationSystem I).toPortLocalRotation
      (faceStarCrossing I))^[1] (faceStarRadialOldPort I p) ≠
      faceStarRadialOldPort I p := by
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [faceStarFaceStep_radialOld]
  exact (faceStar_radialOld_ne_radialCenter I p
    ((portFaceEquiv M.localRotation M.crossing).symm p)).symm

/-- A radial-old dart does not return after two face steps. -/
theorem faceStarFaceStep_radialOld_no_return_two {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    (portFaceStep (faceStarRotationSystem I).toPortLocalRotation
      (faceStarCrossing I))^[2] (faceStarRadialOldPort I p) ≠
      faceStarRadialOldPort I p := by
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [faceStarFaceStep_radialOld, faceStarFaceStep_radialCenter]
  exact faceStar_oldEdge_ne_radialOld I
    ((portFaceEquiv M.localRotation M.crossing).symm p) p

/-- A radial-center dart does not return after one face step. -/
theorem faceStarFaceStep_radialCenter_no_return_one {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    (portFaceStep (faceStarRotationSystem I).toPortLocalRotation
      (faceStarCrossing I))^[1] (faceStarRadialCenterPort I p) ≠
      faceStarRadialCenterPort I p := by
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [faceStarFaceStep_radialCenter]
  exact faceStar_oldEdge_ne_radialCenter I p p

/-- A radial-center dart does not return after two face steps. -/
theorem faceStarFaceStep_radialCenter_no_return_two {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    (portFaceStep (faceStarRotationSystem I).toPortLocalRotation
      (faceStarCrossing I))^[2] (faceStarRadialCenterPort I p) ≠
      faceStarRadialCenterPort I p := by
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [faceStarFaceStep_radialCenter, faceStarFaceStep_oldEdge]
  simpa [portFaceStep, portFaceEquiv] using faceStar_radialOld_ne_radialCenter I
    (portFaceEquiv M.localRotation M.crossing p) p

/-- The first return time of an old-edge dart is exactly three. -/
theorem firstPortFaceReturn_faceStar_oldEdge {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    firstPortFaceReturn (faceStarRotationSystem I).toPortLocalRotation
      (faceStarCrossing I) (faceStarOldEdgePort I p) = 3 := by
  have hs := firstPortFaceReturn_spec
    (faceStarRotationSystem I).toPortLocalRotation (faceStarCrossing I)
    (faceStarOldEdgePort I p)
  have hle : firstPortFaceReturn
      (faceStarRotationSystem I).toPortLocalRotation (faceStarCrossing I)
      (faceStarOldEdgePort I p) ≤ 3 := by
    apply firstPortFaceReturn_min
    exact ⟨by omega, faceStarFaceStep_oldEdge_return I p⟩
  have hge : 3 ≤ firstPortFaceReturn
      (faceStarRotationSystem I).toPortLocalRotation (faceStarCrossing I)
      (faceStarOldEdgePort I p) := by
    by_contra h
    have hcases : firstPortFaceReturn
        (faceStarRotationSystem I).toPortLocalRotation (faceStarCrossing I)
        (faceStarOldEdgePort I p) = 1 ∨
      firstPortFaceReturn
        (faceStarRotationSystem I).toPortLocalRotation (faceStarCrossing I)
        (faceStarOldEdgePort I p) = 2 := by omega
    rcases hcases with h1 | h2
    · exact faceStarFaceStep_oldEdge_no_return_one I p
        (by simpa [h1, PortFaceReturn] using hs.2)
    · exact faceStarFaceStep_oldEdge_no_return_two I p
        (by simpa [h2, PortFaceReturn] using hs.2)
  exact Nat.le_antisymm hle hge

/-- The first return time of a radial-old dart is exactly three. -/
theorem firstPortFaceReturn_faceStar_radialOld {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    firstPortFaceReturn (faceStarRotationSystem I).toPortLocalRotation
      (faceStarCrossing I) (faceStarRadialOldPort I p) = 3 := by
  let p0 := (portFaceEquiv M.localRotation M.crossing).symm p
  have hp0 : portFaceStep M.localRotation M.crossing p0 = p := by
    dsimp [p0]
    rw [← portFaceEquiv_apply]
    exact (portFaceEquiv M.localRotation M.crossing).apply_symm_apply p
  have hmem : faceStarRadialOldPort I p ∈
      portFaceOrbit (faceStarRotationSystem I).toPortLocalRotation
        (faceStarCrossing I) (faceStarOldEdgePort I p0) := by
    rw [← hp0, ← faceStarFaceStep_oldEdge I p0]
    exact portFaceOrbit_mem_iterate _ _ _ 1
  have heq := firstPortFaceReturn_eq_of_mem _ _
    (faceStarOldEdgePort I p0) (faceStarRadialOldPort I p) hmem
  rw [heq, firstPortFaceReturn_faceStar_oldEdge]

/-- The first return time of a radial-center dart is exactly three. -/
theorem firstPortFaceReturn_faceStar_radialCenter {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    firstPortFaceReturn (faceStarRotationSystem I).toPortLocalRotation
      (faceStarCrossing I) (faceStarRadialCenterPort I p) = 3 := by
  have hmem' : faceStarRadialCenterPort I
      ((portFaceEquiv M.localRotation M.crossing).symm
        (portFaceStep M.localRotation M.crossing p)) ∈
      portFaceOrbit (faceStarRotationSystem I).toPortLocalRotation
        (faceStarCrossing I) (faceStarOldEdgePort I p) := by
    rw [← faceStarFaceStep_radialOld I (portFaceStep M.localRotation M.crossing p),
      ← faceStarFaceStep_oldEdge I p]
    exact portFaceOrbit_mem_iterate _ _ _ 2
  have hphi : (portFaceEquiv M.localRotation M.crossing).symm
      (portFaceStep M.localRotation M.crossing p) = p := by
    rw [← portFaceEquiv_apply]
    exact (portFaceEquiv M.localRotation M.crossing).symm_apply_apply p
  have hmem : faceStarRadialCenterPort I p ∈
      portFaceOrbit (faceStarRotationSystem I).toPortLocalRotation
        (faceStarCrossing I) (faceStarOldEdgePort I p) := by
    rwa [hphi] at hmem'
  have heq := firstPortFaceReturn_eq_of_mem _ _
    (faceStarOldEdgePort I p) (faceStarRadialCenterPort I p) hmem
  rw [heq, firstPortFaceReturn_faceStar_oldEdge]

/-- The three darts in the face-star triangle generated by an old port. -/
def faceStarTriangle {P : PortNetwork} (M : PortCombinatorialMap P)
    (I : PortFaceStarIndexing M) (p : PortNetworkPort P) :
    Finset (PortNetworkPort (faceStarNetwork M I)) :=
  {faceStarOldEdgePort I p, faceStarRadialOldPort I
      (portFaceStep M.localRotation M.crossing p),
    faceStarRadialCenterPort I p}

/-- Each generated face-star triangle has exactly three distinct darts. -/
theorem faceStarTriangle_card {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    (faceStarTriangle M I p).card = 3 := by
  simp [faceStarTriangle, faceStar_oldEdge_ne_radialOld,
    faceStar_oldEdge_ne_radialCenter, faceStar_radialOld_ne_radialCenter]

/-- The generated triangle is the face orbit of its old-edge dart. -/
theorem faceStarTriangle_eq_oldEdge_orbit {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    faceStarTriangle M I p =
      portFaceOrbit (faceStarRotationSystem I).toPortLocalRotation
        (faceStarCrossing I) (faceStarOldEdgePort I p) := by
  let f := portFaceStep (faceStarRotationSystem I).toPortLocalRotation
    (faceStarCrossing I)
  have h0 : f^[0] (faceStarOldEdgePort I p) = faceStarOldEdgePort I p := rfl
  have h1 : f^[1] (faceStarOldEdgePort I p) =
      faceStarRadialOldPort I (portFaceStep M.localRotation M.crossing p) := by
    simpa only [f, Function.iterate_succ_apply, Function.iterate_zero_apply] using
      faceStarFaceStep_oldEdge I p
  have h2 : f^[2] (faceStarOldEdgePort I p) = faceStarRadialCenterPort I p := by
    rw [show 2 = 1 + 1 by omega, Function.iterate_add_apply]
    rw [h1]
    have hphi : (portFaceEquiv M.localRotation M.crossing).symm
        (portFaceStep M.localRotation M.crossing p) = p := by
      rw [← portFaceEquiv_apply]
      exact (portFaceEquiv M.localRotation M.crossing).symm_apply_apply p
    simpa only [f, Function.iterate_succ_apply, Function.iterate_zero_apply, hphi] using
      faceStarFaceStep_radialOld I (portFaceStep M.localRotation M.crossing p)
  have h1' : f (faceStarOldEdgePort I p) =
      faceStarRadialOldPort I (portFaceStep M.localRotation M.crossing p) := by
    simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using h1
  rw [show portFaceOrbit (faceStarRotationSystem I).toPortLocalRotation
      (faceStarCrossing I) (faceStarOldEdgePort I p) =
      (Finset.range 3).image (fun n => f^[n] (faceStarOldEdgePort I p)) by
        rw [portFaceOrbit, firstPortFaceReturn_faceStar_oldEdge]]
  have hrange : Finset.range 3 = ({0, 1, 2} : Finset Nat) := by
    decide
  rw [hrange]
  simp [faceStarTriangle, h0, h1', h2]

/-- The same triangle is the orbit of its radial-old dart. -/
theorem faceStarTriangle_eq_radialOld_orbit {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    faceStarTriangle M I p =
      portFaceOrbit (faceStarRotationSystem I).toPortLocalRotation
        (faceStarCrossing I)
        (faceStarRadialOldPort I (portFaceStep M.localRotation M.crossing p)) := by
  have hmem := portFaceOrbit_mem_iterate
    (faceStarRotationSystem I).toPortLocalRotation (faceStarCrossing I)
    (faceStarOldEdgePort I p) 1
  have hstep := faceStarFaceStep_oldEdge I p
  have hstep' :
      (portFaceStep (faceStarRotationSystem I).toPortLocalRotation
        (faceStarCrossing I))^[1] (faceStarOldEdgePort I p) =
        faceStarRadialOldPort I (portFaceStep M.localRotation M.crossing p) := by
    simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using hstep
  rw [hstep'] at hmem
  exact (faceStarTriangle_eq_oldEdge_orbit I p).trans
    (portFaceOrbit_eq_of_mem _ _ _ _ hmem).symm

/-- The same triangle is the orbit of its radial-center dart. -/
theorem faceStarTriangle_eq_radialCenter_orbit {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    faceStarTriangle M I p =
      portFaceOrbit (faceStarRotationSystem I).toPortLocalRotation
        (faceStarCrossing I) (faceStarRadialCenterPort I p) := by
  have hmem := portFaceOrbit_mem_iterate
    (faceStarRotationSystem I).toPortLocalRotation (faceStarCrossing I)
    (faceStarOldEdgePort I p) 2
  have hstep1 := faceStarFaceStep_oldEdge I p
  have hstep1' :
      (portFaceStep (faceStarRotationSystem I).toPortLocalRotation
        (faceStarCrossing I))^[1] (faceStarOldEdgePort I p) =
        faceStarRadialOldPort I (portFaceStep M.localRotation M.crossing p) := by
    simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using hstep1
  have hstep2 := faceStarFaceStep_radialOld I
    (portFaceStep M.localRotation M.crossing p)
  have hstep2' :
      (portFaceStep (faceStarRotationSystem I).toPortLocalRotation
        (faceStarCrossing I))^[1]
        (faceStarRadialOldPort I (portFaceStep M.localRotation M.crossing p)) =
        faceStarRadialCenterPort I
          ((portFaceEquiv M.localRotation M.crossing).symm
            (portFaceStep M.localRotation M.crossing p)) := by
    simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using hstep2
  rw [show 2 = 1 + 1 by omega, Function.iterate_add_apply] at hmem
  rw [hstep1', hstep2'] at hmem
  have hphi : (portFaceEquiv M.localRotation M.crossing).symm
      (portFaceStep M.localRotation M.crossing p) = p := by
    rw [← portFaceEquiv_apply]
    exact (portFaceEquiv M.localRotation M.crossing).symm_apply_apply p
  rw [hphi] at hmem
  exact (faceStarTriangle_eq_oldEdge_orbit I p).trans
    (portFaceOrbit_eq_of_mem _ _ _ _ hmem).symm

/-- Every new dart belongs to one of the generated face-star triangles. -/
theorem faceStarTriangle_coverage {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (q : PortNetworkPort (faceStarNetwork M I)) :
    ∃ p : PortNetworkPort P, q ∈ faceStarTriangle M I p := by
  generalize hd : faceStarPortDecode I q = d
  have hqenc : faceStarPortEncode I d = q := by
    calc
      faceStarPortEncode I d = faceStarPortEncode I (faceStarPortDecode I q) := by
        rw [hd]
      _ = q := faceStarPortEncode_decode I q
  cases d with
  | oldEdge p =>
      exact ⟨p, by rw [← hqenc]; simp [faceStarTriangle]⟩
  | radialOld p =>
      let p0 := (portFaceEquiv M.localRotation M.crossing).symm p
      have hp0 : portFaceStep M.localRotation M.crossing p0 = p := by
        dsimp [p0]
        rw [← portFaceEquiv_apply]
        exact (portFaceEquiv M.localRotation M.crossing).apply_symm_apply p
      exact ⟨p0, by
        rw [← hqenc, ← hp0]
        simp [faceStarTriangle]⟩
  | radialCenter p =>
      exact ⟨p, by rw [← hqenc]; simp [faceStarTriangle]⟩

/-- Every face orbit of the transported rotation has cardinality three. -/
theorem faceStar_everyFaceCell_card_three {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (F : PortFaceCell (faceStarRotationSystem I).toPortLocalRotation
      (faceStarCrossing I)) :
    F.val.card = 3 := by
  rcases (portFaceOrbits_mem_iff
    (faceStarRotationSystem I).toPortLocalRotation (faceStarCrossing I) F.val).mp
    F.property with ⟨q, hq⟩
  have hF : F = faceCellOfPort
      (faceStarRotationSystem I).toPortLocalRotation (faceStarCrossing I) q := by
    apply Subtype.ext
    exact hq
  rw [hF]
  change (portFaceOrbit (faceStarRotationSystem I).toPortLocalRotation
    (faceStarCrossing I) q).card = 3
  rcases faceStarTriangle_coverage I q with ⟨p, hp⟩
  rw [faceStarTriangle_eq_oldEdge_orbit I p] at hp
  rw [portFaceOrbit_eq_of_mem _ _ _ _ hp]
  rw [← faceStarTriangle_eq_oldEdge_orbit I p]
  exact faceStarTriangle_card I p

/-! ## Public carrier facts -/

/-- The face-star descriptor contains three ports for every old port. -/
theorem faceStar_descriptor_card {P : PortNetwork} (M : PortCombinatorialMap P) :
    Fintype.card (FaceStarPortDesc M) = 3 * M.portCount :=
  FaceStarPortDesc.card M

/-- The face-star network has one old region for every old region and one
center region for every old face. -/
theorem faceStar_regionCount_eq {P : PortNetwork} {M : PortCombinatorialMap P}
    (I : PortFaceStarIndexing M) :
    (faceStarNetwork M I).regionCount = M.vertexCount + M.faceCount :=
  faceStarNetwork_regionCount I

end DkMath.Tromino
