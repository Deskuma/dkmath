/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticWeilAlternating

#print "file: DkMath.Lib.NumberTheory.EllipticWeilBicharacter"

/-!
# 同じμₙ値を持つ交代的な双指標

NOTE-025の値c(S,T)を変えず、右加法性と交代性を付け加える。
c(S+T,S+T)=1を両変数に展開するとc(S,T)c(T,S)=1となり、反対称性を得る。
固定したSの右指標を作り、さらに二重のAddCharにまとめる。
この段階で非退化性やガロア同変性は未証明であり、WeilPairingDataへはまだ接続しない。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]

/-- 交代性と両変数の加法性から、変数の交換は逆元を取ることに対応する。 -/
theorem weilTranslationUnit_swap (n : ℕ) (hn : n ≠ 0) (S T : Torsion E n) :
    weilTranslationUnit E n hn T S = (weilTranslationUnit E n hn S T)⁻¹ := by
  have h := weilTranslationUnit_self E n hn (T + S)
  rw [weilTranslationUnit_add_right, weilTranslationUnit_add, weilTranslationUnit_add,
    weilTranslationUnit_self, weilTranslationUnit_self, one_mul, mul_one] at h
  exact eq_inv_of_mul_eq_one_left h

/-- 既存の根値の指標は、右変数についても加法を乗法へ送る。 -/
theorem weilTranslationCharacter_add_right (n : ℕ) (hn : n ≠ 0) (S T R : Torsion E n) :
    weilTranslationCharacter E n hn (T + R) S =
      weilTranslationCharacter E n hn T S * weilTranslationCharacter E n hn R S :=
  Subtype.ext (weilTranslationUnit_add_right E n hn S T R)

/-- 交代性をμₙの型でも固定する。値はNOTE-025の同じ選択された単元のままである。 -/
theorem weilTranslationCharacter_self (n : ℕ) (hn : n ≠ 0) (T : Torsion E n) :
    weilTranslationCharacter E n hn T T = 1 := Subtype.ext (weilTranslationUnit_self E n hn T)

/-- μₙの中での反対称性。根を係数体へ埋め直す必要はない。 -/
theorem weilTranslationCharacter_swap (n : ℕ) (hn : n ≠ 0) (S T : Torsion E n) :
    weilTranslationCharacter E n hn T S = (weilTranslationCharacter E n hn S T)⁻¹ :=
  Subtype.ext (weilTranslationUnit_swap E n hn S T)

/-- 移動Sを固定し、目標Tを動かす右指標。引数は通常の対の順序S,Tである。 -/
noncomputable def weilTranslationRightCharacter (n : ℕ) (hn : n ≠ 0) (S : Torsion E n) :
    AddChar (Torsion E n) (rootsOfUnity n (AlgebraicClosure K)) where
  toFun T := weilTranslationCharacter E n hn T S
  map_zero_eq_one' := Subtype.ext (weilTranslationUnit_zero_target E n hn S)
  map_add_eq_mul' T R := weilTranslationCharacter_add_right E n hn S T R

/-- 両変数に加法的な実際の根値の対。外側Sが移動、内側Tが目標を表す。 -/
noncomputable def weilAlternatingBicharacter (n : ℕ) (hn : n ≠ 0) :
    AddChar (Torsion E n) (AddChar (Torsion E n) (rootsOfUnity n (AlgebraicClosure K))) where
  toFun := weilTranslationRightCharacter E n hn
  map_zero_eq_one' := by
    apply AddChar.ext
    intro T
    exact Subtype.ext (weilTranslationUnit_zero E n hn T)
  map_add_eq_mul' S R := by
    apply AddChar.ext
    intro T
    exact Subtype.ext (weilTranslationUnit_add E n hn T S R)

/-- 双指標の値は、前段の同じ移動指標の値に定義的に一致する。 -/
theorem weilAlternatingBicharacter_apply (n : ℕ) (hn : n ≠ 0) (S T : Torsion E n) :
    weilAlternatingBicharacter E n hn S T = weilTranslationCharacter E n hn T S := rfl

/-- 構成した双指標の対角上の値は1である。 -/
theorem weilAlternatingBicharacter_self (n : ℕ) (hn : n ≠ 0) (T : Torsion E n) :
    weilAlternatingBicharacter E n hn T T = 1 := weilTranslationCharacter_self E n hn T

/-- 構成した双指標は変数を交換すると逆元になる。 -/
theorem weilAlternatingBicharacter_swap (n : ℕ) (hn : n ≠ 0) (S T : Torsion E n) :
    weilAlternatingBicharacter E n hn S T = (weilAlternatingBicharacter E n hn T S)⁻¹ :=
  weilTranslationCharacter_swap E n hn S T

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
