import DkMath.Tromino.PortCombinatorialMap
import DkMath.Tromino.PortF2Chains
namespace DkMath.Tromino
structure PortFaceStarIndexing {P : PortNetwork} (M : PortCombinatorialMap P) where
  faceEquiv : PortFaceCell M.localRotation M.crossing ≃ Fin M.faceCount
  facePortEquiv : ∀ F : PortFaceCell M.localRotation M.crossing,
    {p : PortNetworkPort P // p ∈ F.val} ≃ Fin F.val.card
theorem exists_portFaceStarIndexing {P : PortNetwork} (M : PortCombinatorialMap P) :
    Nonempty (PortFaceStarIndexing M) := by
  classical
  let e : PortFaceCell M.localRotation M.crossing ≃ Fin M.faceCount :=
    (Fintype.equivFin (PortFaceCell M.localRotation M.crossing)).trans
      (finCongr (PortFaceCell_card M.localRotation M.crossing))
  refine ⟨{faceEquiv := e, facePortEquiv := fun F => ?_}⟩
  exact (Fintype.equivFin {p : PortNetworkPort P // p ∈ F.val}).trans
    (finCongr (Fintype.card_coe F.val))
inductive FaceStarPortDesc {P : PortNetwork} (M : PortCombinatorialMap P)
  | oldEdge (p : PortNetworkPort P) | radialOld (p : PortNetworkPort P)
  | radialCenter (p : PortNetworkPort P)
deriving DecidableEq
def faceStarDescSumEquiv {P : PortNetwork} (M : PortCombinatorialMap P) :
    FaceStarPortDesc M ≃ PortNetworkPort P ⊕ (PortNetworkPort P ⊕ PortNetworkPort P) where
  toFun x := match x with
    | .oldEdge p => Sum.inl p | .radialOld p => Sum.inr (Sum.inl p)
    | .radialCenter p => Sum.inr (Sum.inr p)
  invFun x := match x with
    | Sum.inl p => .oldEdge p | Sum.inr (Sum.inl p) => .radialOld p
    | Sum.inr (Sum.inr p) => .radialCenter p
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x with | inl p => rfl | inr q => cases q <;> rfl
namespace FaceStarPortDesc
instance instFintype {P : PortNetwork} (M : PortCombinatorialMap P) :
    Fintype (FaceStarPortDesc M) := Fintype.ofEquiv _ (faceStarDescSumEquiv M).symm
theorem card {P : PortNetwork} (M : PortCombinatorialMap P) :
    Fintype.card (FaceStarPortDesc M) = 3 * M.portCount := by
  rw [Fintype.card_congr (faceStarDescSumEquiv M)]
  simp only [Fintype.card_sum]
  change Fintype.card (PortNetworkPort P) + (Fintype.card (PortNetworkPort P) +
    Fintype.card (PortNetworkPort P)) = 3 * Fintype.card (PortNetworkPort P)
  omega
end FaceStarPortDesc
def faceStarRegionArity {P : PortNetwork} (M : PortCombinatorialMap P)
    (I : PortFaceStarIndexing M) : Fin M.vertexCount ⊕ Fin M.faceCount → Nat
  | Sum.inl r => 2 * P.arity r | Sum.inr F => (I.faceEquiv.symm F).val.card
def faceStarNetwork {P : PortNetwork} (M : PortCombinatorialMap P)
    (I : PortFaceStarIndexing M) : PortNetwork where
  regionCount := M.vertexCount + M.faceCount
  arity := fun r => faceStarRegionArity M I (finSumFinEquiv.symm r)
def faceStarRegionEquiv {P : PortNetwork} (M : PortCombinatorialMap P)
    (I : PortFaceStarIndexing M) : (Fin M.vertexCount ⊕ Fin M.faceCount) ≃
      Fin (faceStarNetwork M I).regionCount := finSumFinEquiv
def oldRegion {P : PortNetwork} {M : PortCombinatorialMap P}
    (I : PortFaceStarIndexing M) (r : Fin M.vertexCount) :
    Fin (faceStarNetwork M I).regionCount := faceStarRegionEquiv M I (.inl r)
def faceCenterRegion {P : PortNetwork} {M : PortCombinatorialMap P}
    (I : PortFaceStarIndexing M) (F : PortFaceCell M.localRotation M.crossing) :
    Fin (faceStarNetwork M I).regionCount := faceStarRegionEquiv M I (.inr (I.faceEquiv F))
theorem oldRegion_injective {P : PortNetwork} {M : PortCombinatorialMap P}
    (I : PortFaceStarIndexing M) : Function.Injective (oldRegion I) := by
  intro r s h; have h' : (Sum.inl r : Fin M.vertexCount ⊕ Fin M.faceCount) = Sum.inl s :=
    (faceStarRegionEquiv M I).injective h; cases h'; rfl
theorem faceCenterRegion_injective {P : PortNetwork} {M : PortCombinatorialMap P}
    (I : PortFaceStarIndexing M) : Function.Injective (faceCenterRegion I) := by
  intro F G h
  have h' : (Sum.inr (I.faceEquiv F) : Fin M.vertexCount ⊕ Fin M.faceCount) =
      Sum.inr (I.faceEquiv G) := (faceStarRegionEquiv M I).injective h
  have hfg : I.faceEquiv F = I.faceEquiv G := by injection h'
  exact Subtype.ext (congrArg Subtype.val (I.faceEquiv.injective hfg))
theorem oldRegion_ne_faceCenterRegion {P : PortNetwork} {M : PortCombinatorialMap P}
    (I : PortFaceStarIndexing M) (r : Fin M.vertexCount)
    (F : PortFaceCell M.localRotation M.crossing) : oldRegion I r ≠ faceCenterRegion I F := by
  intro h; have h' : (Sum.inl r : Fin M.vertexCount ⊕ Fin M.faceCount) =
      Sum.inr (I.faceEquiv F) := (faceStarRegionEquiv M I).injective h; cases h'
def oldPortFin {P : PortNetwork} {M : PortCombinatorialMap P}
    (I : PortFaceStarIndexing M) (p : PortNetworkPort P) (b : Fin 2) :
    Fin ((faceStarNetwork M I).arity (oldRegion I p.1)) := by
  refine Fin.cast ?_ (finProdFinEquiv (m := 2) (n := P.arity p.1) (b, p.2))
  change 2 * P.arity p.1 = faceStarRegionArity M I
    (finSumFinEquiv.symm (finSumFinEquiv (.inl p.1)))
  rw [Equiv.symm_apply_apply]; rfl
def centerPortFin {P : PortNetwork} {M : PortCombinatorialMap P}
    (I : PortFaceStarIndexing M) (F : PortFaceCell M.localRotation M.crossing)
    (q : {p : PortNetworkPort P // p ∈ F.val}) :
    Fin ((faceStarNetwork M I).arity (faceCenterRegion I F)) := by
  refine Fin.cast ?_ (I.facePortEquiv F q)
  change F.val.card = faceStarRegionArity M I
    (finSumFinEquiv.symm (finSumFinEquiv (.inr (I.faceEquiv F))))
  rw [Equiv.symm_apply_apply]; simp [faceStarRegionArity]
def faceStarOldEdgePort {P : PortNetwork} {M : PortCombinatorialMap P}
    (I : PortFaceStarIndexing M) (p : PortNetworkPort P) :
    PortNetworkPort (faceStarNetwork M I) := ⟨oldRegion I p.1, oldPortFin I p 0⟩
def faceStarRadialOldPort {P : PortNetwork} {M : PortCombinatorialMap P}
    (I : PortFaceStarIndexing M) (p : PortNetworkPort P) :
    PortNetworkPort (faceStarNetwork M I) := ⟨oldRegion I p.1, oldPortFin I p 1⟩
def faceStarRadialCenterPort {P : PortNetwork} {M : PortCombinatorialMap P}
    (I : PortFaceStarIndexing M) (p : PortNetworkPort P) :
    PortNetworkPort (faceStarNetwork M I) :=
  let F := faceCellOfPort M.localRotation M.crossing p
  let q : {q : PortNetworkPort P // q ∈ F.val} := ⟨p, faceCellOfPort_mem _ _ _⟩
  ⟨faceCenterRegion I F, centerPortFin I F q⟩
theorem faceStarOldEdgePort_source {P : PortNetwork} {M : PortCombinatorialMap P}
    (I : PortFaceStarIndexing M) (p : PortNetworkPort P) :
    (faceStarOldEdgePort I p).1 = oldRegion I p.1 := rfl
theorem faceStarRadialOldPort_source {P : PortNetwork} {M : PortCombinatorialMap P}
    (I : PortFaceStarIndexing M) (p : PortNetworkPort P) :
    (faceStarRadialOldPort I p).1 = oldRegion I p.1 := rfl
theorem faceStarRadialCenterPort_source {P : PortNetwork} {M : PortCombinatorialMap P}
    (I : PortFaceStarIndexing M) (p : PortNetworkPort P) :
    (faceStarRadialCenterPort I p).1 = faceCenterRegion I
      (faceCellOfPort M.localRotation M.crossing p) := rfl
theorem faceStarNetwork_regionCount {P : PortNetwork} {M : PortCombinatorialMap P}
    (I : PortFaceStarIndexing M) : (faceStarNetwork M I).regionCount =
      M.vertexCount + M.faceCount := rfl
end DkMath.Tromino
