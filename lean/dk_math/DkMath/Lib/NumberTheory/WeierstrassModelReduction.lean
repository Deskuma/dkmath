/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticSmoothReduction
import DkMath.Lib.NumberTheory.WeierstrassVariableChangeGalois

#print "file: DkMath.Lib.NumberTheory.WeierstrassModelReduction"

/-!
# 指定した同じ整モデルで一般ファイバーの実点を還元する

[DkMath.Lib] モデル等式による点の輸送を還元の前に明示する。
還元関数は全点で定義されるが、群準同型として使う場合は零成分へ制限する。
有限整点・非整点・Oを同じ入口で扱い、異なる剰余モデルの等式輸送とも可換にする。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassModelReduction
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open EllipticSmoothReduction EllipticGoodReductionSeparation WeierstrassVariableChange
noncomputable local instance instDecidableEqWeierstrassModelReduction {α : Type*} : DecidableEq α :=
  Classical.decEq _
variable {L : Type*} [Field L] [DecidableEq L] (A : ValuationSubring L)
  (M : WeierstrassCurve A) (V : WeierstrassCurve L) (hM : M.map A.subtype = V)

/-- [DkMath.Lib] 指定した同じ整モデルに沿う実点の還元。特異点分岐は既存関数のまま保持する。 -/
noncomputable def modelReduce : V.toAffine.Point → (M.map (residue A)).toAffine.Point :=
  fun P => reducePointSmooth M (pointEquivOfModelEq hM.symm P)

/-- [DkMath.Lib] Oは同じ剰余曲線のOへ還元する。 -/
theorem modelReduce_zero : modelReduce A M V hM 0 = 0 := by
  simp only [modelReduce, map_zero, reducePointSmooth_zero]

/-- [DkMath.Lib] 整な滑らかな有限点の還元は、同じ二座標の剰余である。 -/
theorem modelReduce_some {x y : L} (h : V.toAffine.Nonsingular x y) (hx : x ∈ A) {hy : y ∈ A}
    (hs : (M.map (residue A)).toAffine.Nonsingular (residue A ⟨x, hx⟩) (residue A ⟨y, hy⟩)) :
    modelReduce A M V hM (Point.some x y h) = Point.some _ _ hs := by
  unfold modelReduce
  rw [pointEquivOfModelEq_some]
  exact reducePointSmooth_some_of_mem M _ hx hs

/-- [DkMath.Lib] 非整なxを持つ有限点は、モデルの等式輸送を含めてOへ還元する。 -/
theorem modelReduce_some_not_mem {x y : L} (h : V.toAffine.Nonsingular x y) (hx : x ∉ A) :
    modelReduce A M V hM (Point.some x y h) = 0 := by
  unfold modelReduce
  rw [pointEquivOfModelEq_some]
  exact reducePointSmooth_some_of_notMem M _ hx

omit [DecidableEq L] in
/-- [DkMath.Lib] 同じ有限点で、座標の剰余値が等しければ剰余モデルの等式輸送も点を保つ。 -/
theorem residuePoint_eq {N : WeierstrassCurve A} (he : N.map (residue A) = M.map (residue A))
    {x y z w : ResidueField A} (hx : x = z) (hy : y = w)
    (h : (N.map (residue A)).toAffine.Nonsingular x y)
    (h' : (M.map (residue A)).toAffine.Nonsingular z w) :
    pointEquivOfModelEq he (Point.some x y h) = Point.some z w h' := by
  subst z
  subst w
  rw [pointEquivOfModelEq_some]

end DkMath.Lib.NumberTheory.WeierstrassModelReduction
