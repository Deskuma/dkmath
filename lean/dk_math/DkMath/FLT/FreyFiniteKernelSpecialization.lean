/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFiniteKernelModel
import DkMath.Lib.NumberTheory.EllipticFiniteKernelSpecialization

#print "file: DkMath.FLT.FreyFiniteKernelSpecialization"

/-!
# 同じFrey Sourceの商座標を実点へ特殊化する

Source・直線L・実点核pointSubgroupを保って、有限座標の評価と標的方程式へ接続する。
標的のΔ≠0を入力する最後の全点写像は、関数としてのみ公開する。
加法性・isogeny・零成分輸送・hnoをこの特殊化から結論しない。
-/
namespace DkMath.FLT.Frey.Source
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 同じ直線の実点核の外で、同じX_Hの有限値を取る。 -/
noncomputable def residualKernelXAt (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1) (P : Points S.rationalCurve)
    (hP : P ∉ pointSubgroup S.rationalCurve p L) : AlgebraicClosure ℚ := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact kernelXAt S.rationalCurve (pointSubgroup S.rationalCurve p L) P hP

/-- 同じ核の外の同じ実点で、同じY_Hの有限値を取る。 -/
noncomputable def residualKernelYAt (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1) (P : Points S.rationalCurve)
    (hP : P ∉ pointSubgroup S.rationalCurve p L) : AlgebraicClosure ℚ := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact kernelYAt S.rationalCurve (pointSubgroup S.rationalCurve p L) P hP

/-- 同じSourceの実点に特殊化した値は、同じ標的モデルの方程式を満たす。 -/
theorem residual_kernel_at_equation (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1) (P : Points S.rationalCurve)
    (hP : P ∉ pointSubgroup S.rationalCurve p L) :
    (S.residualKernelModel L hline).toAffine.Equation
      (S.residualKernelXAt L hline P hP) (S.residualKernelYAt L hline P hP) := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact kernelAt_equation S.rationalCurve _ P hP

/-- 奇素数pの実点核には非零2捩れ点が入らない。
次の三根分離で必要な「核の外」を、同じpointSubgroupから内部供給する。 -/
theorem residual_twoTorsion_outside (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (P : Points S.rationalCurve)
    (hP : P ≠ 0) (hneg : -P = P) : P ∉ pointSubgroup S.rationalCurve p L := by
  intro hm
  have hpP := pointSubgroup_killed S.rationalCurve p L P hm
  have htwo : 2 • P = 0 := by
    rw [two_nsmul]
    simpa only [hneg] using add_neg_cancel P
  have hd := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hpP
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hd with h1 | heq
  · apply hP
    simpa only [h1, one_nsmul] using addOrderOf_nsmul_eq_zero P
  · have hd2 := addOrderOf_dvd_iff_nsmul_eq_zero.mpr htwo
    rw [heq] at hd2
    exact hp2 (le_antisymm (Nat.le_of_dvd (by decide : 0 < 2) hd2) (Fact.out : p.Prime).two_le)

/-- 同じSourceの反転固定点から、同じ標的の2捩れ三次式の根を得る。 -/
theorem residual_kernel_at_twoTorsion_root (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1) (P : Points S.rationalCurve)
    (hP : P ∉ pointSubgroup S.rationalCurve p L) (hneg : -P = P) :
    (S.residualKernelModel L hline).twoTorsionPolynomial.toPoly.eval
      (S.residualKernelXAt L hline P hP) = 0 := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact kernelAt_twoTorsion_root S.rationalCurve _ P hP hneg

/-- 同じ実点三つの特殊化値の分離から、同じSourceの標的Δ≠0へ接続する。
三値の分離は明示入力のままである。 -/
theorem residual_kernel_model_discriminant_of_separation
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (P : Fin 3 → Points S.rationalCurve) (hP : ∀ i, P i ∉ pointSubgroup S.rationalCurve p L)
    (hneg : ∀ i, -P i = P i)
    (hx : Function.Injective (fun i => S.residualKernelXAt L hline (P i) (hP i))) :
    (S.residualKernelModel L hline).Δ ≠ 0 := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact kernelModel_discriminant_of_twoTorsion_separation S.rationalCurve _ P hP hneg hx

/-- 同じSourceの全点写像。標的楕円性を入力し、群準同型はまだ主張しない。 -/
noncomputable def residualKernelPointMap (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1) [(S.residualKernelModel L hline).IsElliptic] :
    Points S.rationalCurve → (S.residualKernelModel L hline).toAffine.Point := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  let : (kernelModel S.rationalCurve (pointSubgroup S.rationalCurve p L)).IsElliptic :=
    (inferInstance : (S.residualKernelModel L hline).IsElliptic)
  exact kernelPointMap S.rationalCurve (pointSubgroup S.rationalCurve p L)

/-- 条件付き全点写像の零ファイバーは、同じ直線の実点核と一致する。 -/
theorem residual_kernel_pointMap_eq_zero_iff
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    [(S.residualKernelModel L hline).IsElliptic] (P : Points S.rationalCurve) :
    S.residualKernelPointMap L hline P = 0 ↔ P ∈ pointSubgroup S.rationalCurve p L := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  let : (kernelModel S.rationalCurve (pointSubgroup S.rationalCurve p L)).IsElliptic :=
    (inferInstance : (S.residualKernelModel L hline).IsElliptic)
  exact kernelPointMap_eq_zero_iff S.rationalCurve (pointSubgroup S.rationalCurve p L) P

end DkMath.FLT.Frey.Source
