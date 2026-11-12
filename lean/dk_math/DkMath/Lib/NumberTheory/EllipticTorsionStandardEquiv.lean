/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticTorsionGaloisStable

#print "file: DkMath.Lib.NumberTheory.EllipticTorsionStandardEquiv"

/-!
# n倍写像の核と標準torsionByの線形・ガロア同変な比較

`torsionByAddEquiv` は同じ点を保つ加法同型だった。nで消える加法群の間では
加法写像は自動的にZMod n線形なので、この同型を線形同型へ強化できる。
標準側の作用も体自己同型の座標作用を制限して独立に構成する。
したがって同変性は、人工的に選んだ作用との一致ではなく、同じ幾何学的な点への
二つの制限の一致を表す。素数性・有限性・次元2はここでは必要ない。

模範解答の `Definitions/Def_FLTPrelim_GaloisRep.lean` が使う整数torsion表示へ
命題を翻訳するアダプタであり、外部リポジトリの宣言をimportしているわけではない。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
variable {K : Type*} [Field K] (E : WeierstrassCurve K)

/-- 標準の整数torsion部分加群。元は同じ曲線の幾何学的な点である。 -/
noncomputable abbrev StandardTorsion (n : ℕ) :=
  Submodule.torsionBy ℤ (Points E) (n : ℤ)

/-- 標準整数torsionにも、nで消える群の標準ZMod n作用を入れる。 -/
noncomputable instance standardTorsionModule (n : ℕ) :
    Module (ZMod n) (StandardTorsion E n) :=
  AddCommGroup.zmodModule (by
    intro P
    apply Subtype.ext
    change n • P.val = 0
    have hP : (n : ℤ) • P.val = 0 := P.property
    simpa only [Nat.cast_smul_eq_nsmul ℤ] using hP)

/-- 同じ点を保持する線形同型。加法同型のZMod線形性は標準APIから得る。 -/
noncomputable def torsionByLinearEquiv (n : ℕ) :
    Torsion E n ≃ₗ[ZMod n] StandardTorsion E n :=
  { torsionByAddEquiv E n with map_smul' := ZMod.map_smul (torsionByAddEquiv E n) }

/-- 線形アダプタは元の加法アダプタをそのまま拡張する。 -/
theorem torsionByLinearEquiv_toAddEquiv (n : ℕ) :
    (torsionByLinearEquiv E n).toAddEquiv = torsionByAddEquiv E n := rfl

/-- 線形アダプタを通しても幾何学的な点の値は変わらない。 -/
theorem torsionByLinearEquiv_val (n : ℕ) (P : Torsion E n) :
    (torsionByLinearEquiv E n P).val = P.val := rfl

/-- 標準torsionByに対する、実際の座標作用の制限。 -/
noncomputable def standardTorsionAction (n : ℕ) (σ : Field.absoluteGaloisGroup K) :
    StandardTorsion E n →+ StandardTorsion E n where
  toFun P := ⟨pointAction E σ P.val, by
    change (n : ℤ) • pointAction E σ P.val = 0
    have hP : (n : ℤ) • P.val = 0 := P.property
    rw [← map_zsmul, hP, map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' P Q := Subtype.ext (map_add _ P.val Q.val)

/-- 標準整数torsion表示での同じガロア表現。 -/
noncomputable def standardRepresentation (n : ℕ) :
    Representation (ZMod n) (Field.absoluteGaloisGroup K) (StandardTorsion E n) where
  toFun σ := (standardTorsionAction E n σ).toZModLinearMap n
  map_one' := by
    apply LinearMap.ext
    intro P
    exact Subtype.ext (pointAction_one E P.val)
  map_mul' σ τ := by
    apply LinearMap.ext
    intro P
    exact Subtype.ext (pointAction_mul E σ τ P.val)

/-- 標準表現も、元の点の座標への作用そのものである。 -/
theorem standardRepresentation_val (n : ℕ) (σ : Field.absoluteGaloisGroup K)
    (P : StandardTorsion E n) :
    (standardRepresentation E n σ P).val = pointAction E σ P.val := rfl

/-- 二つの表示のガロア作用は線形アダプタと可換する。 -/
theorem torsionByLinearEquiv_equivariant (n : ℕ) (σ : Field.absoluteGaloisGroup K)
    (P : Torsion E n) :
    torsionByLinearEquiv E n (representation E n σ P) =
      standardRepresentation E n σ (torsionByLinearEquiv E n P) := rfl

/-- 部分加群の対応は順序同型であり、零・全体・包含を保つ。 -/
noncomputable def torsionSubmoduleEquiv (n : ℕ) :
    Submodule (ZMod n) (Torsion E n) ≃o Submodule (ZMod n) (StandardTorsion E n) :=
  Submodule.orderIsoMapComap (torsionByLinearEquiv E n)

/-- 標準表示への像が安定であることと、元のE[n]で安定であることは同値。 -/
theorem standard_isStable_iff (n : ℕ) (N : Submodule (ZMod n) (Torsion E n)) :
    DkMath.Lib.RepresentationTheory.IsStable (standardRepresentation E n)
      (torsionSubmoduleEquiv E n N) ↔ IsGaloisStable E n N :=
  DkMath.Lib.RepresentationTheory.isStable_map_iff _ _ _
    (torsionByLinearEquiv_equivariant E n) N

/-- 非零条件も含めて、実際の表現の既約性は標準表示の既約性と同値。 -/
theorem standard_isIrreducible_iff (n : ℕ) :
    IsIrreducible E n ↔
      DkMath.Lib.RepresentationTheory.IsIrreducible (standardRepresentation E n) :=
  DkMath.Lib.RepresentationTheory.isIrreducible_iff _ _ _
    (torsionByLinearEquiv_equivariant E n)

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
