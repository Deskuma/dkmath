/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernel
import DkMath.Lib.NumberTheory.EllipticFunctionFieldGalois

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelGalois"

/-!
# NOTE-032-005C₂a: ガロア安定な有限核の正規化座標和

[DkMath.Lib] 核Hの各点が有理である必要はなく、ガロア元がHを置換すればよい。
同じ点群の作用とその逆からHの置換を構成し、係数作用と平行移動の交換則を
有限和へ延長する。正規化座標和の二つの補正定数にも同じ置換を使う。
これによりveluX,veluYは実際の関数体の係数ガロア作用で固定される。

これは関数体内の不変性であり、元の体上の有理関数としての表示、商曲線方程式、
写像の正則延長、加法性、核の一致を証明したとはしない。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open WeierstrassCurve WeierstrassCurve.Affine
open EllipticFunctionField EllipticTorsionRepresentation
open scoped BigOperators
variable {K : Type*} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]
noncomputable local instance : DecidableEq (AlgebraicClosure K) := Classical.decEq _

/-- [DkMath.Lib] 実点部分群のガロア安定性から、同じHの点の置換を構成する。
逆ガロア元もHを保存するという同じ大域条件を使う。 -/
noncomputable def kernelGaloisEquiv (H : AddSubgroup (Points E))
    (hH : ∀ σ P, P ∈ H → pointAction E σ P ∈ H) (σ : Field.absoluteGaloisGroup K) : H ≃ H where
  toFun Q := ⟨pointAction E σ Q.val, hH σ Q.val Q.property⟩
  invFun Q := ⟨pointAction E σ⁻¹ Q.val, hH σ⁻¹ Q.val Q.property⟩
  left_inv Q := Subtype.ext (by
    change pointAction E σ⁻¹ (pointAction E σ Q.val) = Q.val
    rw [← pointAction_mul, inv_mul_cancel, pointAction_one])
  right_inv Q := Subtype.ext (by
    change pointAction E σ (pointAction E σ⁻¹ Q.val) = Q.val
    rw [← pointAction_mul, mul_inv_cancel, pointAction_one])

/-- [DkMath.Lib] 係数ガロア作用は、同じ有限核の平行移動和と可換である。
各点の固定ではなく、同じHの置換と半線形交換則を使う。 -/
theorem kernelTrace_galois (H : AddSubgroup (Points E)) [Fintype H]
    (hH : ∀ σ P, P ∈ H → pointAction E σ P ∈ H) (σ : Field.absoluteGaloisGroup K)
    (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) :
    galFunctionFieldEquiv E σ (kernelTrace E H f) =
      kernelTrace E H (galFunctionFieldEquiv E σ f) := by
  unfold kernelTrace
  rw [map_sum]
  apply Fintype.sum_equiv (kernelGaloisEquiv E H hH σ)
  intro Q
  exact gal_transEquiv E σ Q.val f

omit [E.IsElliptic] in
/-- [DkMath.Lib] 同じ核のx座標の補正和はガロア作用で固定される。
Oの便宜的な座標0も座標作用の一般定理と整合する。 -/
theorem kernel_sum_xc_galois (H : AddSubgroup (Points E)) [Fintype H]
    (hH : ∀ σ P, P ∈ H → pointAction E σ P ∈ H) (σ : Field.absoluteGaloisGroup K) :
    σ.toAlgHom (∑ Q : H, Q.val.xc) = ∑ Q : H, Q.val.xc := by
  rw [map_sum]
  apply Fintype.sum_equiv (kernelGaloisEquiv E H hH σ)
  intro Q
  exact (point_xc_map σ.toAlgHom Q.val).symm

omit [E.IsElliptic] in
/-- [DkMath.Lib] 同じ核のy座標の補正和も、点の置換により固定される。 -/
theorem kernel_sum_yc_galois (H : AddSubgroup (Points E)) [Fintype H]
    (hH : ∀ σ P, P ∈ H → pointAction E σ P ∈ H) (σ : Field.absoluteGaloisGroup K) :
    σ.toAlgHom (∑ Q : H, Q.val.yc) = ∑ Q : H, Q.val.yc := by
  rw [map_sum]
  apply Fintype.sum_equiv (kernelGaloisEquiv E H hH σ)
  intro Q
  exact (point_yc_map σ.toAlgHom Q.val).symm

/-- [DkMath.Lib] 正規化x座標和は、同じ実際の関数体の係数ガロア作用で固定される。 -/
theorem veluX_galois (H : AddSubgroup (Points E)) [Fintype H]
    (hH : ∀ σ P, P ∈ H → pointAction E σ P ∈ H) (σ : Field.absoluteGaloisGroup K) :
    galFunctionFieldEquiv E σ (veluX E H) = veluX E H := by
  have hg : galFunctionFieldEquiv E σ (genericX E (AlgebraicClosure K)) =
      genericX E (AlgebraicClosure K) := gal_genericX E σ
  have hc : galFunctionFieldEquiv E σ
      (algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField
        (∑ Q : H, Q.val.xc)) =
      algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField
        (σ.toAlgHom (∑ Q : H, Q.val.xc)) := gal_algebraMap E σ _
  rw [veluX, map_sub, kernelTrace_galois E H hH, hg, hc, kernel_sum_xc_galois E H hH]

/-- [DkMath.Lib] 正規化y座標和も同じ係数ガロア作用で固定される。
この不変性だけから曲線方程式や点群の準同型を得たとはしない。 -/
theorem veluY_galois (H : AddSubgroup (Points E)) [Fintype H]
    (hH : ∀ σ P, P ∈ H → pointAction E σ P ∈ H) (σ : Field.absoluteGaloisGroup K) :
    galFunctionFieldEquiv E σ (veluY E H) = veluY E H := by
  have hg : galFunctionFieldEquiv E σ (genericY E (AlgebraicClosure K)) =
      genericY E (AlgebraicClosure K) := gal_genericY E σ
  have hc : galFunctionFieldEquiv E σ
      (algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField
        (∑ Q : H, Q.val.yc)) =
      algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField
        (σ.toAlgHom (∑ Q : H, Q.val.yc)) := gal_algebraMap E σ _
  rw [veluY, map_sub, kernelTrace_galois E H hH, hg, hc, kernel_sum_yc_galois E H hH]

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
