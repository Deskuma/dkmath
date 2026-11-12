/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyWeilFunction
import DkMathTest.FLT.FreyWeilGeometry

#print "file: DkMathTest.FLT.FreyWeilFunction"

/-!
# NOTE-022: 実在するファイバー・生成元と、torsion条件の必要性

Source 2の曲線とその非零2-torsion点を使う。2倍ファイバーの四点の総和は零であり、
その点イデアルの積には非零生成元がある。一方、位数4の実際の点を目標にすると
総和は非零となり、ファイバーイデアルは主でない。torsion条件を消せないことも検査する。
37倍の零ファイバーと、指数1・目標点Oの境界も同じ一般定理で扱う。
-/
namespace FreyWeilFunctionTest
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open DkMath.Lib.NumberTheory.EllipticPrincipalPointIdeal
open FreyResidualRepresentationTest
local instance : sample.rationalCurve.IsElliptic := sample.rationalCurve_isElliptic

/-- 群が二元しかない場合、全元の総和は非零。四元2-torsionという仮定は必要である。 -/
theorem cyclic_two_sum_nonzero : (∑ i : ZMod 2, i) ≠ 0 := by decide

/-- 元の幾何学的点のまま、非零2-torsionを読む。 -/
theorem target_two_killed : 2 • (twoPoint.val : Points sample.rationalCurve) = 0 := twoPoint.property

/-- 非零torsionを目標にしても2倍写像のファイバーは非空。 -/
theorem actual_two_fiber_nonempty : (fiberSet sample.rationalCurve 2 twoPoint.val).Nonempty :=
  fiber_nonempty _ 2 (by decide) _

/-- 同じファイバーは四点からなる。 -/
theorem actual_two_fiber_card : (fiberSet sample.rationalCurve 2 twoPoint.val).ncard = 4 :=
  fiber_card _ 2 (by decide) _

/-- その四点の総和は零。仮想的なSource 37ではなく実在するSourceで検査する。 -/
theorem actual_two_fiber_sum :
    ∑ P ∈ (fiber_finite sample.rationalCurve 2 (by decide) twoPoint.val).toFinset, P = 0 :=
  sum_fiber_eq_zero _ 2 (by decide) _ target_two_killed

/-- 同じ四点のイデアルの積は主となる。 -/
theorem actual_two_fiber_principal :
    (fiberIdeal sample.rationalCurve 2 (by decide) twoPoint.val).IsPrincipal :=
  fiberIdeal_isPrincipal _ 2 (by decide) _ target_two_killed

/-- 選んだ分子が実際の積を生成し、零でないことを同時に確認する。 -/
theorem actual_two_generator :
    let f := weilNumerator sample.rationalCurve 2 (by decide) twoPoint.val target_two_killed
    f ≠ 0 ∧ Ideal.span {f} = fiberIdeal sample.rationalCurve 2 (by decide) twoPoint.val :=
  ⟨weilNumerator_ne_zero _ _ _ _ _, span_weilNumerator _ _ _ _ _⟩

/-- 同じSourceの公開入口から構成した商も非零。 -/
theorem actual_two_function_nonzero :
    sample.curve_weilFunction 2 (by decide) twoPoint.val target_two_killed ≠ 0 :=
  sample.curve_weilFunction_ne_zero _ _ _ _

/-- 37倍の零ファイバーには1369点ある。有限集合を計算展開してはいない。 -/
theorem actual_37_fiber_card : (fiberSet sample.rationalCurve 37 0).ncard = 1369 :=
  fiber_card _ 37 (by decide) _

/-- 37倍の零ファイバーにも総和零の定理を適用できる。 -/
theorem actual_37_fiber_sum :
    ∑ P ∈ (fiber_finite sample.rationalCurve 37 (by decide) 0).toFinset, P = 0 :=
  sum_fiber_eq_zero _ 37 (by decide) _ (smul_zero _)

/-- 指数1でも構成でき、零点の商は1に正規化される。 -/
theorem one_zero_function : weilFunction sample.rationalCurve 1 (by decide) 0 (smul_zero _) = 1 :=
  weilFunction_zero _ 1 (by decide)

/-- アフィン表示から除いたOには、積の単位元だけを割り当てる。 -/
theorem infinity_is_unit_ideal :
    pointIdeal (0 : Points sample.rationalCurve) = ⊤ := pointIdeal_zero

/-- 実際の非零点の点イデアルは主でない。点イデアルの積の主性とは区別する。 -/
theorem actual_point_ideal_not_principal : ¬ (pointIdeal twoPoint.val).IsPrincipal := by
  have h := isPrincipal_prod_pointIdeal_iff ({()} : Finset Unit) (fun _ => twoPoint.val)
  simp only [Finset.prod_singleton] at h
  exact fun hp => FreyWeilGeometryTest.shiftPoint_ne_zero (h.mp hp)

/-- 全射性から同じ点群内に実際の4-torsionの候補となる原像を選ぶ。 -/
noncomputable def fourPoint : Points sample.rationalCurve :=
  (multiplication_surjective sample.rationalCurve 2 (by decide) twoPoint.val).choose

/-- 選んだ同じ点の二倍は、元の非零2-torsion点である。 -/
theorem fourPoint_double : 2 • fourPoint = twoPoint.val :=
  (multiplication_surjective sample.rationalCurve 2 (by decide) twoPoint.val).choose_spec

/-- 従って二倍零ではない。ファイバー主性に必要な仮定の反例になる。 -/
theorem fourPoint_not_two_torsion : 2 • fourPoint ≠ 0 := by
  rw [fourPoint_double]
  exact FreyWeilGeometryTest.shiftPoint_ne_zero

/-- 二倍をもう一度取れば零となり、実際の4-torsionに属する。 -/
theorem fourPoint_four_killed : 4 • fourPoint = 0 := by
  change (2 * 2) • fourPoint = 0
  rw [mul_smul, fourPoint_double, target_two_killed]

/-- 目標点がE[2]に入らなければ、四点のファイバーでも総和は零にならない。 -/
theorem non_torsion_target_sum_nonzero :
    (∑ P ∈ (fiber_finite sample.rationalCurve 2 (by decide) fourPoint).toFinset, P) ≠ 0 := by
  rw [sum_fiber _ 2 (by decide)]
  exact fourPoint_not_two_torsion

/-- 同じ境界は主性にも現れる。有限性と四点という位数だけでは主性は従わない。 -/
theorem non_torsion_target_not_principal :
    ¬ (fiberIdeal sample.rationalCurve 2 (by decide) fourPoint).IsPrincipal :=
  fun h => fourPoint_not_two_torsion ((fiberIdeal_isPrincipal_iff _ 2 (by decide) _).mp h)

end FreyWeilFunctionTest
