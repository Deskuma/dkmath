/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyWeilGalois
import DkMath.FLT.FreyResidualCyclotomic
import DkMath.Lib.NumberTheory.EllipticGeometricWeilPairing

#print "file: DkMath.FLT.FreyGeometricWeilPairing"

/-!
# 同じFrey Sourceの実際のWeil対と円分行列式

Sourceの同じ正規化曲線・同じtorsion作用・同じ移動固有値からデータを供給する。
非退化性は固定体・局所付値・点イデアルの主性による幾何学的証明であり、仮定ではない。
円分行列式は無条件になるが、Frey表現の既約性はなお別問題である。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory EllipticTorsionRepresentation CyclotomicRootModule
variable {p : ℕ} (S : Source p)

/-- 同じSourceの交代双指標の左非退化性。 -/
theorem curve_weilAlternatingBicharacter_nondegenerate (n : ℕ) (hn : n ≠ 0)
    (Q : Torsion S.rationalCurve n) (hQ : ∀ T, S.curve_weilAlternatingBicharacter n hn Q T = 1) : Q = 0 := by
  have := S.rationalCurve_isElliptic
  exact weilAlternatingBicharacter_nondegenerate_left S.rationalCurve n hn Q hQ

variable [Fact p.Prime]

/-- 既存の剰余Weil対データ契約を、同じ実際の曲線から満たす。 -/
noncomputable def residual_geometricWeilPairingData : S.ResidualWeilPairingData := by
  have := S.rationalCurve_isElliptic
  exact geometricWeilPairingData S.rationalCurve p (Fact.out : p.Prime).ne_zero

/-- 同じSourceの剰余表現の行列式は円分指標に一致する。対データの追加入力は不要。 -/
theorem residual_determinant_eq_cyclotomic : S.residualDeterminantCharacter = cyclotomicCharacter p :=
  S.residual_determinant_eq_cyclotomic_of_pairing S.residual_geometricWeilPairingData

/-- 任意のp乗根への作用を、同じSourceの実際の行列式の冪で記述する無条件の公式。 -/
theorem residual_apply_eq_pow_det (σ : Field.absoluteGaloisGroup ℚ) (ζ : AlgebraicClosure ℚ)
    (hζ : ζ ^ p = 1) : σ.toAlgHom ζ = ζ ^ (LinearMap.det (S.residualRepresentation σ)).val :=
  S.residual_apply_eq_pow_det_of_pairing S.residual_geometricWeilPairingData σ ζ hζ

end DkMath.FLT.Frey.Source
