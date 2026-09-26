/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortFaceStarSubdivision
import DkMath.Tromino.PortF2Exactness

/-!
# Face-star triangulation reduction

This module records the semantic crossing and rotation permutations for the
face-star carrier. The actual dependent-Fin transport is kept separate so
that these operations can be checked without duplicating their mathematics.
-/

#print "file: DkMath.Tromino.PortTriangulationReduction"

namespace DkMath.Tromino

/-! ## Semantic crossing -/

def faceStarCrossDesc {P : PortNetwork} (M : PortCombinatorialMap P) :
    FaceStarPortDesc M → FaceStarPortDesc M
  | .oldEdge p => .oldEdge (M.crossing.cross p)
  | .radialOld p => .radialCenter p
  | .radialCenter p => .radialOld p

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

def faceStarRotateDesc {P : PortNetwork} (M : PortCombinatorialMap P) :
    FaceStarPortDesc M → FaceStarPortDesc M
  | .radialOld p => .oldEdge p
  | .oldEdge p => .radialOld (M.localRotation.rotate p)
  | .radialCenter p =>
      .radialCenter ((portFaceEquiv M.localRotation M.crossing).symm p)

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

theorem faceStar_vertexCount_eq {P : PortNetwork}
    {M : PortCombinatorialMap P} : M.vertexCount = P.regionCount := by
  simp [PortCombinatorialMap.vertexCount, portRegionVertexCount]

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

theorem faceStarCenterArity_eq {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (F : PortFaceCell M.localRotation M.crossing) :
    F.val.card =
      (faceStarNetwork M I).arity (faceCenterRegion I F) := by
  change F.val.card = faceStarRegionArity M I
    (finSumFinEquiv.symm (finSumFinEquiv (.inr (I.faceEquiv F))))
  rw [Equiv.symm_apply_apply]
  simp [faceStarRegionArity]

theorem faceStarCenterArity_eq_index {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (F : Fin M.faceCount) :
    (I.faceEquiv.symm F).val.card =
      (faceStarNetwork M I).arity
        (faceCenterRegion I (I.faceEquiv.symm F)) := by
  let F' := I.faceEquiv.symm F
  exact faceStarCenterArity_eq I F'

theorem faceStarCenterArity_eq_sum_index {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (F : Fin M.faceCount) :
    (I.faceEquiv.symm F).val.card =
      (faceStarNetwork M I).arity (faceStarRegionEquiv M I (.inr F)) := by
  change (I.faceEquiv.symm F).val.card = faceStarRegionArity M I
    (finSumFinEquiv.symm (finSumFinEquiv (.inr F)))
  rw [Equiv.symm_apply_apply]
  simp [faceStarRegionArity]

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

def faceStarVertexToOld {P : PortNetwork}
    {M : PortCombinatorialMap P} (r : Fin M.vertexCount) :
    Fin P.regionCount :=
  Fin.cast faceStar_vertexCount_eq r

def faceStarOldToVertex {P : PortNetwork}
    {M : PortCombinatorialMap P} (r : Fin P.regionCount) :
    Fin M.vertexCount :=
  Fin.cast faceStar_vertexCount_eq.symm r

theorem faceStarVertexToOld_oldToVertex {P : PortNetwork}
    {M : PortCombinatorialMap P} (r : Fin P.regionCount) :
    faceStarVertexToOld (M := M) (faceStarOldToVertex (M := M) r) = r := by
  apply Fin.ext
  rfl

theorem faceStarOldToVertex_vertexToOld {P : PortNetwork}
    {M : PortCombinatorialMap P} (r : Fin M.vertexCount) :
    faceStarOldToVertex (M := M) (faceStarVertexToOld (M := M) r) = r := by
  apply Fin.ext
  rfl

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

def faceStarActualRegionEquiv {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    PortNetworkPort (faceStarNetwork M I) ≃
      (Σ s : Fin M.vertexCount ⊕ Fin M.faceCount,
        Fin ((faceStarNetwork M I).arity (faceStarRegionEquiv M I s))) :=
  Equiv.sigmaCongr (faceStarRegionEquiv M I).symm
    (fun r => finCongr (congrArg (fun t =>
      (faceStarNetwork M I).arity t)
      ((faceStarRegionEquiv M I).apply_symm_apply r).symm))

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

def faceStarPortEquiv {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    PortNetworkPort (faceStarNetwork M I) ≃ FaceStarPortDesc M :=
  (faceStarPortSumEquiv I).trans faceStarSumDescEquiv

def faceStarPortEncode {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    FaceStarPortDesc M → PortNetworkPort (faceStarNetwork M I) :=
  (faceStarPortEquiv I).symm

def faceStarPortDecode {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    PortNetworkPort (faceStarNetwork M I) → FaceStarPortDesc M :=
  faceStarPortEquiv I

@[simp] theorem faceStarPortDecode_encode {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (d : FaceStarPortDesc M) :
    faceStarPortDecode I (faceStarPortEncode I d) = d :=
  (faceStarPortEquiv I).apply_symm_apply d

@[simp] theorem faceStarPortEncode_decode {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort (faceStarNetwork M I)) :
    faceStarPortEncode I (faceStarPortDecode I p) = p :=
  (faceStarPortEquiv I).symm_apply_apply p

def faceStarDescSource {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    FaceStarPortDesc M → Fin (faceStarNetwork M I).regionCount
  | .oldEdge p => oldRegion I p.1
  | .radialOld p => oldRegion I p.1
  | .radialCenter p =>
      faceCenterRegion I (faceCellOfPort M.localRotation M.crossing p)

theorem faceStarPortDecode_source {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    ∀ d : FaceStarPortDesc M,
      (faceStarPortEncode I d).1 = faceStarDescSource I d := by
  intro d
  cases d <;> rfl

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

theorem faceStarCrossing_encode {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (d : FaceStarPortDesc M) :
    (faceStarCrossing I).cross (faceStarPortEncode I d) =
      faceStarPortEncode I (faceStarCrossDesc M d) := by
  change faceStarPortEncode I
      (faceStarCrossDesc M
        (faceStarPortDecode I (faceStarPortEncode I d))) = _
  rw [faceStarPortDecode_encode]

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
