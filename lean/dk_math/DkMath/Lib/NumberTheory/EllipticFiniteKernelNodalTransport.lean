/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelNodalDistance
import DkMath.Lib.NumberTheory.EllipticNodalReduction

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelNodalTransport"

/-!
# 候補中心の一致を保持した零成分輸送

[DkMath.Lib] 同じ標的の臨界中心の剰余xが前章の候補値に一致する場合、
非衝突点の商像はその節点から離れ、標的で滑らかである。
衝突点は既存の無限遠近傍の定理で扱い、全零成分を同じ商写像で輸送する。
中心一致は明示的な仮定であり、この章では供給していない。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open EllipticTorsionRepresentation EllipticGoodReductionSeparation EllipticSmoothReduction
open EllipticCriticalCentre EllipticNodalReduction WeierstrassModelReduction
open EllipticNodalTorsion.NodalTorsion
open scoped BigOperators
noncomputable local instance instDecidableEqEllipticFiniteKernelNodalTransport {α : Type*} : DecidableEq α :=
  Classical.decEq _
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
  (H : AddSubgroup (Points E)) [Fintype H] (n : ℕ) [Fact n.Prime]
  (hkill : ∀ Q : H, n • Q.val = 0)
  (A : ValuationSubring (AlgebraicClosure K)) (M : WeierstrassCurve A)
  (hM : M.map A.subtype = E.map (algebraMap K (AlgebraicClosure K)))
  (hn : A.valuation (n : AlgebraicClosure K) = 1)
  (hs : ∀ Q : H, HasSmoothReduction M Q.val) (hcard : Nat.card H = n)
  (ho : Odd (Nat.card H))
  {x₀ y₀ α : ResidueField A} (F : Frame (M.map (residue A)) x₀ y₀ α)
  (hsep : α ≠ -(M.map (residue A)).a₁ - α)
  (C : CriticalCentre A (kernelModel E H))
  (hc : residue A ⟨C.x, C.x_mem⟩ =
    (n : ResidueField A) * x₀ - ∑ Q : H, (smoothKernelReduction E H A M hM hs Q).xc)

include hcard F hsep C hc in
/-- [DkMath.Lib] 候補値と同じ標的節点のx座標が一致すれば、非衝突点の像は滑らか。
同じ一般ファイバーのX,Yを剰余化し、標的方程式と節点からの距離を使用する。 -/
theorem oddKernelPointMap_smooth_of_noncollision_candidate (P : Points E)
    (hP : HasSmoothReduction M P)
    (hout : ∀ Q : H, modelReduce A M _ hM P ≠ modelReduce A M _ hM Q.val) :
    HasSmoothReduction (valuationKernelModel E H n hkill A M hM hn) (oddKernelPointMap E H ho P) := by
  let U := valuationKernelModel E H n hkill A M hM hn
  let hU := valuationKernelModel_map E H n hkill A M hM hn ho
  let : (kernelModel E H).IsElliptic := kernelModel_isElliptic_of_odd_card E H ho
  let hp := not_mem_of_reduction_noncollision E H A M hM P hout
  have hxy := kernelAt_coordinates_mem E H n hkill A M hM hn hs P hP hout
  have heq : (U.map A.subtype).toAffine.Equation (kernelXAt E H P hp) (kernelYAt E H P hp) :=
    hU.symm ▸ kernelAt_equation E H P hp
  have hred := equation_residue U (x := ⟨kernelXAt E H P hp, hxy.1⟩)
    (y := ⟨kernelYAt E H P hp, hxy.2⟩) heq
  have hC := CriticalCentre.residue_singular_of_model U hU C
  have hnode : (U.map (residue A)).b₂ + 12 * residue A ⟨C.x, C.x_mem⟩ ≠ 0 := by
    let v : A := U.b₂ + 12 * (⟨C.x, C.x_mem⟩ : A)
    have hb : A.subtype U.b₂ = (kernelModel E H).b₂ := by
      have h := congrArg WeierstrassCurve.b₂ hU
      simpa only [map_b₂] using h
    have hvco : (v : AlgebraicClosure K) = (kernelModel E H).b₂ + 12 * C.x := by
      change A.subtype (U.b₂ + 12 * (⟨C.x, C.x_mem⟩ : A)) = _
      simp only [map_add, map_mul, map_ofNat]
      change A.subtype U.b₂ + 12 * C.x = _
      rw [hb]
    have hv : IsUnit v := (A.valuation_eq_one_iff _).mpr (hvco.symm ▸ C.node_unit)
    have hr := (residue_ne_zero_iff_isUnit v).mpr hv
    simpa only [v, map_add, map_mul, map_ofNat, map_b₂] using hr
  have hx := kernelXAt_residue_ne_nodal_candidate E H n hkill A M hM hn hs P hP hout hcard F hsep
  have hne : residue A ⟨kernelXAt E H P hp, hxy.1⟩ ≠ residue A ⟨C.x, C.x_mem⟩ := by
    rw [hc]
    exact hx
  have hns := nonsingular_of_node_of_x_ne (U.map (residue A)) _ _ hC.1 hC.2 hnode hred hne
  rw [show oddKernelPointMap E H ho P = Point.some _ _ (kernelAt_nonsingular E H P hp) from
    kernelPointMap_of_not_mem E H P hp, hasSmoothReduction_some_iff]
  intro _ _
  exact hns

include hcard F hsep C hc in
/-- [DkMath.Lib] 同じ標的中心の候補一致の下で、衝突・非衝突の両方を合わせた全零成分輸送。
中心一致は明示的な仮定として残る。 -/
theorem oddKernelPointMap_smooth_of_candidate (P : Points E) (hP : HasSmoothReduction M P) :
    HasSmoothReduction (valuationKernelModel E H n hkill A M hM hn) (oddKernelPointMap E H ho P) := by
  by_cases hout : ∀ Q : H, modelReduce A M _ hM P ≠ modelReduce A M _ hM Q.val
  · exact oddKernelPointMap_smooth_of_noncollision_candidate E H n hkill A M hM hn hs hcard ho F hsep C hc P hP hout
  · push Not at hout
    obtain ⟨Q, hQ⟩ := hout
    exact (oddKernelPointMap_of_reduction_collision E H n hkill A M hM hn ho P Q hP (hs Q) hQ).1

private theorem pointEquiv_symm_of_model {L : Type*} [Field L] {W V : WeierstrassCurve L} (h : W = V) :
    WeierstrassVariableChange.pointEquivOfModelEq h.symm =
      (WeierstrassVariableChange.pointEquivOfModelEq h).symm := by
  subst V
  rfl

/-- [DkMath.Lib] 同じ商準同型の全零成分への制限。候補中心の一致を仮定として保持する。
零成分の各点を別の代表に置き換えず、既存の実点準同型を制限する。 -/
noncomputable def nodalCandidateZeroComponentHom :
    zeroComponentSubgroup M →+
      zeroComponentSubgroup (valuationKernelModel E H n hkill A M hM hn) := by
  let U := valuationKernelModel E H n hkill A M hM hn
  let hU := valuationKernelModel_map E H n hkill A M hM hn ho
  let f := (WeierstrassVariableChange.pointEquivOfModelEq hU.symm).toAddMonoidHom.comp
    ((oddKernelPointHom E H ho).comp
      (WeierstrassVariableChange.pointEquivOfModelEq hM).toAddMonoidHom)
  refine { toFun := fun P => ⟨f P.val, ?_⟩
           map_zero' := Subtype.ext (map_zero f)
           map_add' := fun P Q => Subtype.ext (map_add f P.val Q.val) }
  change HasSmoothReduction U _
  apply (smooth_pointEquiv_of_model A U _ hU _).mpr
  apply oddKernelPointMap_smooth_of_candidate E H n hkill A M hM hn hs hcard ho F hsep C hc
  apply (smooth_pointEquiv_of_model A M _ hM _).mp
  change HasSmoothReduction M ((WeierstrassVariableChange.pointEquivOfModelEq hM.symm)
    ((WeierstrassVariableChange.pointEquivOfModelEq hM) P.val))
  rw [pointEquiv_symm_of_model hM, AddEquiv.symm_apply_apply]
  exact P.property

/-- [DkMath.Lib] 制限準同型を同じ一般ファイバーに戻すと、既存商準同型そのものになる。 -/
theorem nodalCandidateZeroComponentHom_geometric (P : zeroComponentSubgroup M) :
    WeierstrassVariableChange.pointEquivOfModelEq
      (valuationKernelModel_map E H n hkill A M hM hn ho)
      (nodalCandidateZeroComponentHom E H n hkill A M hM hn hs hcard ho F hsep C hc P).val =
        oddKernelPointHom E H ho (WeierstrassVariableChange.pointEquivOfModelEq hM P.val) := by
  change WeierstrassVariableChange.pointEquivOfModelEq _
    (WeierstrassVariableChange.pointEquivOfModelEq _ _) = _
  rw [pointEquiv_symm_of_model (valuationKernelModel_map E H n hkill A M hM hn ho), AddEquiv.apply_symm_apply]
  rfl


/-- [DkMath.Lib] 制限準同型の零ファイバーは、同じ一般ファイバーの有限核Hとの交わり。
滑らかな核側では一般に制限は単射ではない。 -/
theorem nodalCandidateZeroComponentHom_eq_zero_iff (P : zeroComponentSubgroup M) :
    nodalCandidateZeroComponentHom E H n hkill A M hM hn hs hcard ho F hsep C hc P = 0 ↔
      WeierstrassVariableChange.pointEquivOfModelEq hM P.val ∈ H := by
  constructor
  · intro hz
    have he := congrArg (fun T : zeroComponentSubgroup (valuationKernelModel E H n hkill A M hM hn) =>
      WeierstrassVariableChange.pointEquivOfModelEq (valuationKernelModel_map E H n hkill A M hM hn ho) T.val) hz
    rw [nodalCandidateZeroComponentHom_geometric, AddSubgroup.coe_zero, map_zero] at he
    exact (oddKernelPointMap_eq_zero_iff E H ho _).mp he
  · intro hm
    have hzero : oddKernelPointHom E H ho (WeierstrassVariableChange.pointEquivOfModelEq hM P.val) = 0 := by
      apply AddMonoidHom.mem_ker.mp
      rw [oddKernelPointHom_ker]
      exact hm
    apply Subtype.ext
    apply (WeierstrassVariableChange.pointEquivOfModelEq
      (valuationKernelModel_map E H n hkill A M hM hn ho)).injective
    rw [nodalCandidateZeroComponentHom_geometric]
    simpa only [AddSubgroup.coe_zero, map_zero] using hzero

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
