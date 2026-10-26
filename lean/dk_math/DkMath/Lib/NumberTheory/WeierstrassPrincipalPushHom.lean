/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.WeierstrassDivisorAbel

#print "file: DkMath.Lib.NumberTheory.WeierstrassPrincipalPushHom"

/-!
# Oを保つ主因子輸送から、点群の加法性へ

[DkMath.Lib] 点関数gがOを保ち、有限支持主因子を主因子へ押し出すとする。
[P]+[Q]−[P+Q]の点の総和はOなので、前段のアフィンAbel対応により
無限遠係数の補正を加えたものが実際の主因子になる。
その押し出しの点の総和もOである。補正項はg(O)=Oから消え、g(P+Q)=g(P)+g(Q)を得る。

点群とPic⁰の全同値や主因子の次数公式を追加仮定にせず、必要な加法性を導く。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassPrincipalPushHom
open WeierstrassCurve WeierstrassCurve.Affine
open WeierstrassFinitePlace WeierstrassDivisorAbel
noncomputable local instance instDecidableEqWeierstrassPrincipalPushHom {α : Type*} :
    DecidableEq α := Classical.decEq _
variable {k l : Type*} [Field k] [IsAlgClosed k] [Field l] [IsAlgClosed l]
  (W : WeierstrassCurve k) [W.IsElliptic] (V : WeierstrassCurve l) [V.IsElliptic]

/-- [DkMath.Lib] Oを保ち実際の主因子を保存する点関数は、実際の点加法を保存する。 -/
theorem map_add_of_principal_push (g : W.toAffine.Point → V.toAffine.Point) (hg0 : g 0 = 0)
    (hg : ∀ D : W.toAffine.Point →₀ ℤ,
      ValuationDivisor.IsPrincipal (modelPointValuation W) D →
      ValuationDivisor.IsPrincipal (modelPointValuation V) (Finsupp.mapDomain g D))
    (P Q : W.toAffine.Point) : g (P + Q) = g P + g Q := by
  classical
  let push : (W.toAffine.Point →₀ ℤ) →+ (V.toAffine.Point →₀ ℤ) :=
    Finsupp.mapDomain.addMonoidHom g
  have hs (R : W.toAffine.Point) (n : ℤ) : push (Finsupp.single R n) = Finsupp.single (g R) n :=
    Finsupp.mapDomain_single
  let D := Finsupp.single P (1 : ℤ) + Finsupp.single Q 1 - Finsupp.single (P + Q) 1
  have hD : pointSum W D = 0 := by
    simp only [D, map_sub, map_add, pointSum_single, one_zsmul, sub_self]
  obtain ⟨n, hn⟩ := exists_principal_correction W D hD
  have ht := pointSum_eq_zero_of_isPrincipal V _ (hg _ hn)
  change pointSum V (push (D + Finsupp.single 0 n)) = 0 at ht
  simp only [D, map_add, map_sub, hs, pointSum_single, one_zsmul, hg0, zsmul_zero, add_zero] at ht
  exact (sub_eq_zero.mp ht).symm

/-- [DkMath.Lib] 主因子輸送から得た準同型。点関数そのものをtoFunに保持する。 -/
noncomputable def pointHomOfPrincipalPush (g : W.toAffine.Point → V.toAffine.Point) (hg0 : g 0 = 0)
    (hg : ∀ D : W.toAffine.Point →₀ ℤ,
      ValuationDivisor.IsPrincipal (modelPointValuation W) D →
      ValuationDivisor.IsPrincipal (modelPointValuation V) (Finsupp.mapDomain g D)) :
    W.toAffine.Point →+ V.toAffine.Point where
  toFun := g
  map_zero' := hg0
  map_add' := map_add_of_principal_push W V g hg0 hg

/-- [DkMath.Lib] 主因子輸送による準同型の値は、元の同じ点関数の値である。 -/
theorem pointHomOfPrincipalPush_apply (g : W.toAffine.Point → V.toAffine.Point) (hg0 : g 0 = 0)
    (hg : ∀ D : W.toAffine.Point →₀ ℤ,
      ValuationDivisor.IsPrincipal (modelPointValuation W) D →
      ValuationDivisor.IsPrincipal (modelPointValuation V) (Finsupp.mapDomain g D)) (P : W.toAffine.Point) :
    pointHomOfPrincipalPush W V g hg0 hg P = g P := rfl

end DkMath.Lib.NumberTheory.WeierstrassPrincipalPushHom
