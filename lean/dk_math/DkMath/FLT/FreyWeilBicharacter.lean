/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyWeilCharacter
import DkMath.Lib.NumberTheory.EllipticWeilBicharacter

#print "file: DkMath.FLT.FreyWeilBicharacter"

/-!
# 同じSourceの実際の交代的双指標

前章の同じ比例定数に右加法性・交代性・反対称性を追加する。
二重のAddCharの外側は移動S、内側は目標Tであり、値は前章のc(S,T)のままである。
非退化性とガロア同変性はここで仮定も証明もしない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
variable {p : ℕ} (S : Source p)

/-- 同じSourceの比例定数の、目標を足す側の乗法性。 -/
theorem curve_weilTranslationUnit_add_right (n : ℕ) (hn : n ≠ 0)
    (Q T R : Torsion S.rationalCurve n) :
    S.curve_weilTranslationUnit n hn (T + R) Q =
      S.curve_weilTranslationUnit n hn T Q * S.curve_weilTranslationUnit n hn R Q := by
  have := S.rationalCurve_isElliptic
  exact weilTranslationUnit_add_right S.rationalCurve n hn Q T R

/-- 同じSourceの移動点と目標が一致する場合、固有値は1となる。 -/
theorem curve_weilTranslationUnit_self (n : ℕ) (hn : n ≠ 0) (T : Torsion S.rationalCurve n) :
    S.curve_weilTranslationUnit n hn T T = 1 := by
  have := S.rationalCurve_isElliptic
  exact weilTranslationUnit_self S.rationalCurve n hn T

/-- 同じSourceでも、移動と目標を交換すると比例定数は逆元となる。 -/
theorem curve_weilTranslationUnit_swap (n : ℕ) (hn : n ≠ 0) (Q T : Torsion S.rationalCurve n) :
    S.curve_weilTranslationUnit n hn T Q = (S.curve_weilTranslationUnit n hn Q T)⁻¹ := by
  have := S.rationalCurve_isElliptic
  exact weilTranslationUnit_swap S.rationalCurve n hn Q T

/-- 実際の曲線から構成した交代的双指標。WeilPairingDataは入力に取らない。 -/
noncomputable def curve_weilAlternatingBicharacter (n : ℕ) (hn : n ≠ 0) :
    AddChar (Torsion S.rationalCurve n)
      (AddChar (Torsion S.rationalCurve n) (rootsOfUnity n (AlgebraicClosure ℚ))) := by
  have := S.rationalCurve_isElliptic
  exact weilAlternatingBicharacter S.rationalCurve n hn

/-- Sourceの双指標の単元値は、前章の同じ移動比例定数である。 -/
theorem curve_weilAlternatingBicharacter_val (n : ℕ) (hn : n ≠ 0) (Q T : Torsion S.rationalCurve n) :
    (S.curve_weilAlternatingBicharacter n hn Q T).val = S.curve_weilTranslationUnit n hn T Q := rfl

end DkMath.FLT.Frey.Source
