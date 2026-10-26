/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelDivisor
import DkMath.Lib.NumberTheory.EllipticWeilDivisor
import DkMathTest.Lib.NumberTheory.EllipticFiniteKernelValuation

#print "file: DkMathTest.Lib.NumberTheory.EllipticFiniteKernelGlobal"

/-!
同じy²=x³−x、位数9のE[3]、R=(−1,0)で検査する。
全射性・全ファイバーの位数9に加え、4点対4点の非零Weil主因子の輸送を調べる。
零因子だけの例で主因子保存を済ませず、標的でも係数1が残ることを確認する。
-/
namespace EllipticFiniteKernelGlobalTest
open WeierstrassCurve WeierstrassCurve.Affine WithZero Polynomial
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation EllipticFunctionField
open EllipticFiniteKernelTest EllipticFiniteKernelPolesTest EllipticFiniteKernelNonsingularTest
open EllipticFiniteKernelPointDescentTest
open scoped BigOperators
noncomputable section
local instance : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _
local instance : DecidableEq (Points curve) := Classical.decEq _
local instance : curve.IsElliptic := ⟨by rw [curve_discriminant]; norm_num⟩
local instance : Fintype fullThreeKernel := by
  let := finite_torsion_of_ne_zero curve 3 (by decide)
  exact Fintype.ofFinite (Torsion curve 3)

/-- 同じ9点核のX_Hは既約分子次数9・分母次数8を持つ。 -/
theorem actual_rational_degrees :
    ∃ r : RatFunc (AlgebraicClosure ℚ), r.num.natDegree = 9 ∧ r.denom.natDegree = 8 ∧
      veluX curve fullThreeKernel = aeval (genericX curve (AlgebraicClosure ℚ)) r.num /
        aeval (genericX curve (AlgebraicClosure ℚ)) r.denom := by
  obtain ⟨r, hd, hn, hr⟩ := exists_veluX_rational_at_infinity curve fullThreeKernel
  rw [fullThree_card.1] at hn
  exact ⟨r, hn, by omega, hr⟩

/-- 同じ標的上の全実点への全射性。 -/
theorem actual_surjective : Function.Surjective (oddKernelPointMap curve fullThreeKernel fullThree_card.2) :=
  oddKernelPointMap_surjective curve fullThreeKernel fullThree_card.2

/-- 任意の二点について、像の一致は同じ9点核の剰余類の一致である。 -/
theorem actual_fiber_relation (P U : Points curve) :
    oddKernelPointMap curve fullThreeKernel fullThree_card.2 P =
      oddKernelPointMap curve fullThreeKernel fullThree_card.2 U ↔ U - P ∈ fullThreeKernel :=
  oddKernelPointMap_eq_iff_sub_mem curve fullThreeKernel fullThree_card.2 P U

/-- Oも任意の有限点も、ファイバーの位数は正確に9となる。 -/
theorem actual_all_fiber_cards (T : (kernelModel curve fullThreeKernel).toAffine.Point) :
    Nat.card {P : Points curve // oddKernelPointMap curve fullThreeKernel fullThree_card.2 P = T} = 9 := by
  simpa only [fullThree_card.1] using card_kernel_fiber curve fullThreeKernel fullThree_card.2 T

/-- 既に降下した同じℚ係数標的の幾何学的点に対しても全射。 -/
theorem actual_descended_surjective : Function.Surjective image :=
  descendedKernelPointMap_surjective curve fullThreeKernel fullThree_card.2 fullThree_stable

/-- 同じ非零点Rは2捩れなので、[2]の二つのファイバーの差は主因子になる。 -/
theorem actual_R_two_torsion : 2 • R = 0 := by
  have h := (congrArg (fun T : Points curve => R + T) actual_R_fixed.symm).trans (add_neg_cancel R)
  simpa only [two_nsmul] using h

/-- 同じ[2]の二つのファイバーは、各々4点を持つ。 -/
theorem actual_weil_fiber_cards : Nat.card (fiberSet curve 2 R) = 4 ∧ Nat.card (fiberSet curve 2 0) = 4 := by
  constructor
  · simpa only [Nat.card_coe_set_eq, Nat.reducePow] using fiber_card curve 2 (by decide) R
  · simpa only [Nat.card_coe_set_eq, Nat.reducePow] using fiber_card curve 2 (by decide) 0

/-- 4点の零点と4点の極からなる、同じWeil関数の有限支持主因子。 -/
def sourceDivisor : Points curve →₀ ℤ := weilDivisor curve 2 (by decide) R

/-- 同じ実際のWeil関数がsourceDivisorを全点で実現する。 -/
theorem actual_source_principal : ValuationDivisor.IsPrincipal (pointValuation curve) sourceDivisor :=
  weilDivisor_isPrincipal curve 2 (by decide) R actual_R_two_torsion

/-- 非零の主因子を押し出しても、同じ標的で非零の主因子となる。
2捩れと奇数核の交わりがOだけであることを使い、標的係数1を内部検査する。 -/
theorem actual_nonzero_principal_push :
    ValuationDivisor.IsPrincipal (kernelTargetValuation curve fullThreeKernel fullThree_card.2)
      (kernelDivisorPush curve fullThreeKernel fullThree_card.2 sourceDivisor) ∧
      kernelDivisorPush curve fullThreeKernel fullThree_card.2 sourceDivisor ≠ 0 := by
  classical
  refine ⟨kernelDivisorPush_isPrincipal curve fullThreeKernel fullThree_card.2 sourceDivisor
    actual_source_principal, ?_⟩
  obtain ⟨P, hP⟩ := fiber_nonempty curve 2 (by decide) R
  change 2 • P = R at hP
  have hq (Q : fullThreeKernel) (hQ : 2 • Q.val = 0) : Q = 0 := by
    have hs : Q.val + Q.val = 0 := by simpa only [two_nsmul] using hQ
    exact Subtype.ext (eq_zero_of_mem_odd_kernel_fixed curve fullThreeKernel fullThree_card.2
      Q.val Q.property (neg_eq_of_add_eq_zero_left hs))
  have hR₀ : R ≠ 0 := Point.some_ne_zero _
  have hd (Q : fullThreeKernel) : sourceDivisor (P + Q.val) = if Q = 0 then 1 else 0 := by
    change (fiberDivisor curve 2 (by decide) R (P + Q.val) -
      fiberDivisor curve 2 (by decide) 0 (P + Q.val)) = _
    rw [fiberDivisor_apply, fiberDivisor_apply]
    have ht : 2 • (P + Q.val) = R + 2 • Q.val := by rw [smul_add, hP]
    have hp : 2 • (P + Q.val) = R ↔ Q = 0 := by
      rw [ht]
      constructor
      · intro he
        exact hq Q (add_left_cancel (he.trans (add_zero R).symm))
      · intro he; subst Q; simp
    have hn : 2 • (P + Q.val) ≠ 0 := by
      intro hz
      have he : R = -(2 • Q.val) := eq_neg_of_add_eq_zero_left (ht.symm.trans hz)
      exact actual_R_outside (he.symm ▸ fullThreeKernel.neg_mem (fullThreeKernel.nsmul_mem Q.property 2))
    simp only [hp, ite_eq_right hn, sub_zero]
  have hcoef : kernelDivisorPush curve fullThreeKernel fullThree_card.2 sourceDivisor
      (oddKernelPointMap curve fullThreeKernel fullThree_card.2 P) = 1 := by
    rw [kernelDivisorPush_apply_image]
    rw [Fintype.sum_eq_single (0 : fullThreeKernel) (fun Q hQ => by rw [hd, ite_eq_right hQ])]
    simpa using hd 0
  intro hz
  rw [hz, Finsupp.zero_apply] at hcoef
  exact zero_ne_one hcoef

end
end EllipticFiniteKernelGlobalTest
