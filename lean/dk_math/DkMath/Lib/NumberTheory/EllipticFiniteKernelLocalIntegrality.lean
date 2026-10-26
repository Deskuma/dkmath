/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelHalf
import DkMath.Lib.NumberTheory.EllipticTorsionValuationIntegrality
import DkMath.Lib.NumberTheory.WeierstrassVeluPolynomial

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelLocalIntegrality"

/-!
# 同じ有限核の局所整性と、分母2を導入しない多項式係数候補

[DkMath.Lib] 同じ実点核Hをn倍で消すとき、nが付値単元なら全ての有限核座標は整である。
Oの便宜座標0も含めた定理を公開し、奇数核の半核を添字とするVélu型多項式候補へ運ぶ。
局所係数候補の整性と、既存kernelModelの係数の整性を区別する。
本所有者は方程式から同一性へ進む条件付きAPIを公開する。後続の
EllipticFiniteKernelVeluEquationでは、標数0・奇数核についてその方程式と一致を証明済み。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open WeierstrassCurve WeierstrassCurve.Affine EllipticTorsionRepresentation
open EllipticTorsionValuationIntegrality WeierstrassVeluPolynomial
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K)
noncomputable local instance instDecidableEqEllipticFiniteKernelLocalIntegrality {α : Type*} :
    DecidableEq α := Classical.decEq _

/-- [DkMath.Lib] 同じHの全点の両座標は、nが単元である整モデルの付値環へ入る。
Oの便宜座標は0なので、核の点を除去して定理を弱める必要はない。 -/
theorem kernel_coordinates_mem (H : AddSubgroup (Points E)) (n : ℕ)
    (hkill : ∀ P : H, n • P.val = 0) (A : ValuationSubring (AlgebraicClosure K))
    (M : WeierstrassCurve A) (hM : M.map A.subtype = E.map (algebraMap K (AlgebraicClosure K)))
    (hn : A.valuation (n : AlgebraicClosure K) = 1) (P : H) : P.val.xc ∈ A ∧ P.val.yc ∈ A := by
  by_cases hP : P.val = 0
  · rw [hP]
    exact ⟨A.zero_mem, A.zero_mem⟩
  · have hh := hkill P
    rw [Point.eq_some_xc_yc hP] at hh
    exact torsion_coordinates_mem A M _ hM hn (Point.nonsingular_xc_yc hP) hh

/-- [DkMath.Lib] 同じ半核の座標を使うVélu型多項式係数候補。
既存kernelModelと同一という定理はこの定義に含めない。 -/
noncomputable def halfKernelPolynomialModel (H : AddSubgroup (Points E)) [Fintype H] :
    WeierstrassCurve (AlgebraicClosure K) :=
  polynomialModel (E.map (algebraMap K (AlgebraicClosure K))) (halfKernel E H)
    (fun Q => Q.val.xc) (fun Q => Q.val.yc)

/-- [DkMath.Lib] 同じ整モデルと同じHの実点捩れ条件から、多項式係数候補の五係数の整性を供給する。
奇数性は半核が反転対を尽くすために必要であり、この多項式の整性自体には不要。 -/
theorem halfKernelPolynomialModel_coefficientsIn (H : AddSubgroup (Points E)) [Fintype H]
    (n : ℕ) (hkill : ∀ P : H, n • P.val = 0) (A : ValuationSubring (AlgebraicClosure K))
    (M : WeierstrassCurve A) (hM : M.map A.subtype = E.map (algebraMap K (AlgebraicClosure K)))
    (hn : A.valuation (n : AlgebraicClosure K) = 1) :
    CoefficientsIn A.toSubring (halfKernelPolynomialModel E H) := by
  apply polynomialModel_coefficientsIn
  · rw [← hM]
    exact ⟨M.a₁.property, M.a₂.property, M.a₃.property, M.a₄.property, M.a₆.property⟩
  · intro Q _
    exact kernel_coordinates_mem E H n hkill A M hM hn Q

/-- [DkMath.Lib] 同じX_H,Y_Hが多項式候補の方程式を満たすなら、候補は既存の同じkernelModelに等しい。
本定理では具体的な関数体恒等式を入力に取る。奇数核の場合は後続の
halfKernelPolynomialModel_equationがこの入力を内部供給する。 -/
theorem halfKernelPolynomialModel_eq_kernelModel_of_equation [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (he : ((halfKernelPolynomialModel E H).toAffine⁄(E.toAffine⁄(AlgebraicClosure K)).FunctionField).Equation (veluX E H) (veluY E H)) :
    halfKernelPolynomialModel E H = kernelModel E H :=
  kernelModel_unique E H (halfKernelPolynomialModel E H) rfl rfl he

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
