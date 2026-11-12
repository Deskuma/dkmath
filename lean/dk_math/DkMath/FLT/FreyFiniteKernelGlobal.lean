/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFiniteKernelValuation
import DkMath.Lib.NumberTheory.EllipticFiniteKernelDivisor

#print "file: DkMath.FLT.FreyFiniteKernelGlobal"

/-!
# 同じSourceの全ファイバー・全射性・主因子輸送

同じ直線Lの実点核Hに対し、同じ全点関数の全射性と全ファイバーの位数pを供給する。
有限支持因子の押し出しは主因子を保存し、生成関数には同じ軌道積を使う。
点群の加法性と因子群の加法性を区別し、isogenyやhnoの結論は付け加えない。
-/
namespace DkMath.FLT.Frey.Source
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 同じ一次元残余核の位数pから、奇数条件を内部供給する。 -/
theorem residual_pointSubgroup_odd (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1) :
    Odd (Nat.card (pointSubgroup S.rationalCurve p L)) := by
  rw [card_pointSubgroup S.rationalCurve p L hline]
  exact (Fact.out : p.Prime).odd_of_ne_two hp2

/-- 同じ全点関数の任意の二点の像の一致は、差が同じHに入ることと同値。 -/
theorem residual_odd_kernel_pointMap_eq_iff_sub_mem (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (P R : Points S.rationalCurve) :
    S.residualOddKernelPointMap hp2 L hline P = S.residualOddKernelPointMap hp2 L hline R ↔
      R - P ∈ pointSubgroup S.rationalCurve p L := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact oddKernelPointMap_eq_iff_sub_mem S.rationalCurve _ (S.residual_pointSubgroup_odd hp2 L hline) P R

/-- 同じ標的の全点への全射性。追加の幾何学providerを要求しない。 -/
theorem residual_odd_kernel_pointMap_surjective (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1) :
    Function.Surjective (S.residualOddKernelPointMap hp2 L hline) := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact oddKernelPointMap_surjective S.rationalCurve _ (S.residual_pointSubgroup_odd hp2 L hline)

/-- 標的のどの点のファイバーも正確にp点。同じ点関数のファイバーである。 -/
theorem card_residual_odd_kernel_fiber (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (T : (S.residualKernelModel L hline).toAffine.Point) :
    Nat.card {P : Points S.rationalCurve // S.residualOddKernelPointMap hp2 L hline P = T} = p := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  have h := card_kernel_fiber S.rationalCurve _ (S.residual_pointSubgroup_odd hp2 L hline) T
  exact h.trans (card_pointSubgroup S.rationalCurve p L hline)

/-- 同じSourceの全点関数に沿う、実際の有限支持因子の押し出し。 -/
noncomputable def residualKernelDivisorPush (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1) :
    (Points S.rationalCurve →₀ ℤ) →+ ((S.residualKernelModel L hline).toAffine.Point →₀ ℤ) := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact kernelDivisorPush S.rationalCurve _ (S.residual_pointSubgroup_odd hp2 L hline)

/-- 同じSourceの主因子を同じ標的の主因子へ運ぶ。点群の準同型性を仮定しない。 -/
theorem residual_kernel_divisor_push_isPrincipal (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (D : Points S.rationalCurve →₀ ℤ) (hD : ValuationDivisor.IsPrincipal (pointValuation S.rationalCurve) D) :
    ValuationDivisor.IsPrincipal (S.residualKernelTargetValuation hp2 L hline)
      (S.residualKernelDivisorPush hp2 L hline D) := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact kernelDivisorPush_isPrincipal S.rationalCurve _ (S.residual_pointSubgroup_odd hp2 L hline) D hD

end DkMath.FLT.Frey.Source
