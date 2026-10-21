/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyWeilBicharacter
import DkMath.FLT.FreyResidualRepresentation
import DkMath.Lib.NumberTheory.EllipticWeilGalois

#print "file: DkMath.FLT.FreyWeilGalois"

/-!
# Source の実際の双指標とガロア作用

同じ有理曲線のtorsion作用、同じWeil関数から得た比例定数、同じμₙ値を接続する。
構成済みの関数体作用は係数について半線形であり、選択された生成元は定数倍だけ変わる。
この章の結論はガロア同変性であり、非退化性と円分行列式の無条件化は次の課題である。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
variable {p : ℕ} (S : Source p)

/-- 同じSourceの平行移動比例定数は、実際のtorsion作用と係数作用に整合する。 -/
theorem curve_weilTranslationUnit_galois (n : ℕ) (hn : n ≠ 0)
    (σ : Field.absoluteGaloisGroup ℚ) (Q T : Torsion S.rationalCurve n) :
    S.curve_weilTranslationUnit n hn (torsionAction S.rationalCurve n σ T)
        (torsionAction S.rationalCurve n σ Q) =
      galoisUnitMap σ (S.curve_weilTranslationUnit n hn T Q) := by
  have := S.rationalCurve_isElliptic
  exact weilTranslationUnit_galois S.rationalCurve n hn σ Q T

/-- 同じμₙ値の交代的双指標にもガロア同変性を供給する。 -/
theorem curve_weilAlternatingBicharacter_galois (n : ℕ) (hn : n ≠ 0)
    (σ : Field.absoluteGaloisGroup ℚ) (Q T : Torsion S.rationalCurve n) :
    S.curve_weilAlternatingBicharacter n hn (torsionAction S.rationalCurve n σ Q)
        (torsionAction S.rationalCurve n σ T) =
      galoisRootMap n σ (S.curve_weilAlternatingBicharacter n hn Q T) := by
  have := S.rationalCurve_isElliptic
  exact weilAlternatingBicharacter_galois S.rationalCurve n hn σ Q T

/-- Sourceの既存の剰余表現へ直接渡せる同変性。
WeilPairingDataを仮定せず、非退化性を得たとも主張しない。 -/
theorem curve_weilAlternatingBicharacter_residual (hp : p ≠ 0)
    (σ : Field.absoluteGaloisGroup ℚ) (Q T : S.ResidualSpace) :
    S.curve_weilAlternatingBicharacter p hp (S.residualRepresentation σ Q)
        (S.residualRepresentation σ T) =
      galoisRootMap p σ (S.curve_weilAlternatingBicharacter p hp Q T) := by
  have := S.rationalCurve_isElliptic
  exact weilAlternatingBicharacter_representation S.rationalCurve p hp σ Q T

end DkMath.FLT.Frey.Source
