/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidualGL2
import DkMath.Lib.NumberTheory.EllipticTorsionWeilDeterminant
import DkMath.Lib.NumberTheory.EllipticMultiplicationSurjective
import DkMath.Lib.RepresentationTheory.StableLineMatrix

#print "file: DkMath.FLT.FreyResidualCyclotomic"

/-!
# 同じFrey Sourceの円分行列式への条件付き接続

円分指標そのものは根のガロア作用から無条件に構成済みである。
行列式との一致は、同じ曲線の実際のE[p]上のWeil対データを明示的に入力して得る。
このデータの存在を示す幾何学的providerはまだない。条件を定理名と引数に残すことで、
無条件の行列式公式やFrey表現の既約性を先取りしない。
付随して、前章のファイバー構成から倍写像の全射性を無条件に公開する。
-/
namespace DkMath.FLT.Frey.Source
open Module
open DkMath.Lib.NumberTheory EllipticTorsionRepresentation CyclotomicRootModule
open DkMath.Lib.RepresentationTheory
variable {p : ℕ} (S : Source p) [Fact p.Prime]

/-- 同じSourceの実際のねじれ点に対するWeil対の供給契約。存在定理ではない。 -/
abbrev ResidualWeilPairingData := WeilPairingData S.rationalCurve p

/-- Weil対を供給した場合、前章の基底不変な行列式指標は円分指標と一致する。 -/
theorem residual_determinant_eq_cyclotomic_of_pairing (w : S.ResidualWeilPairingData) :
    S.residualDeterminantCharacter = cyclotomicCharacter p :=
  RootPairing.determinant_eq_cyclotomic_of_pairing S.residualRepresentation S.residualBasis
    w.pairing w.equivariant

/-- 既定以外の基底にも同じ円分行列式を運べる。 -/
theorem residual_determinant_with_basis_of_pairing (w : S.ResidualWeilPairingData)
    (b : Basis (Fin 2) (ZMod p) S.ResidualSpace) :
    determinantCharacterWithBasis S.residualRepresentation b = cyclotomicCharacter p :=
  (determinantCharacterWithBasis_independent S.residualRepresentation b S.residualBasis).trans
    (S.residual_determinant_eq_cyclotomic_of_pairing w)

/-- 任意のp乗根への作用を、同じFrey残余作用素の行列式で記述する条件付き定理。 -/
theorem residual_apply_eq_pow_det_of_pairing (w : S.ResidualWeilPairingData)
    (σ : Field.absoluteGaloisGroup ℚ) (ζ : AlgebraicClosure ℚ) (hζ : ζ ^ p = 1) :
    σ.toAlgHom ζ = ζ ^ (LinearMap.det (S.residualRepresentation σ)).val := by
  have := S.rationalCurve_isElliptic
  exact torsion_apply_eq_pow_det_of_pairing S.rationalCurve p w σ ζ hζ

/-- 安定直線に適合する基底では、対角成分の積が円分指標になる。
対角成分の積の制約だけでは安定直線は排除できず、Mazur型の算術は別途必要である。 -/
theorem residual_stable_line_diagonal_product_of_pairing (w : S.ResidualWeilPairingData)
    (b : Basis (Fin 2) (ZMod p) S.ResidualSpace)
    (hstable : S.IsGaloisStable (Submodule.span (ZMod p) ({b 0} : Set S.ResidualSpace)))
    (σ : Field.absoluteGaloisGroup ℚ) :
    (S.residualGL2WithBasis b σ : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 *
      (S.residualGL2WithBasis b σ : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1 =
        (cyclotomicCharacter p σ : ZMod p) := by
  have hd := congrArg (fun χ : Field.absoluteGaloisGroup ℚ →* (ZMod p)ˣ => (χ σ : ZMod p))
    (S.residual_determinant_with_basis_of_pairing w b)
  rw [determinantCharacterWithBasis_val] at hd
  exact (stable_basis_line_diagonal_product S.residualRepresentation b hstable σ).trans hd

omit [Fact p.Prime] in
/-- 同じ有理曲線の代数閉包上では、非零自然数倍の写像は全射である。
これはWeil対を入力しない、独立の無条件な幾何学的結果。 -/
theorem residual_curve_multiplication_surjective (n : ℕ) (hn : n ≠ 0) :
    Function.Surjective (nsmulAddMonoidHom n : Points S.rationalCurve →+ Points S.rationalCurve) := by
  have := S.rationalCurve_isElliptic
  exact multiplication_surjective S.rationalCurve n hn

end DkMath.FLT.Frey.Source
