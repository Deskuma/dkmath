/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.RepresentationTheory.Basic

#print "file: DkMath.Lib.NumberTheory.EllipticTorsionRepresentation"

/-!
# 楕円曲線の実際のn-torsion上のガロア表現

体K上の曲線Eを代数閉包へ基底変換し、実際の点群のn倍写像の核を取る。
ガロア元は座標へ作用し、Mathlibの `Affine.Point.map` が加法を保存するので
この核を保存する。nで消える加法群の標準ZMod n線形構造から表現を構成する。
座標空間Fₚ²を先に置いたり、作用を外部の仮定として渡したりする必要はない。

参考: anthropics/fermats-last-theorem, Definitions/Def_FLTPrelim_GaloisRep.lean。
そこでの点への作用・torsionへの制限という経路を、DkMathではn倍写像の核と
明示的な `Representation` で表す。曲線の非特異性は利用側で供給する。
ここでは滑らかな点群一般に構成できるので、E[n]の位数・次元2・非零性・
行列式・既約性・局所不分岐性の証明とは区別する。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open WeierstrassCurve
open scoped WeierstrassCurve.Affine
variable {K : Type*} [Field K] (E : WeierstrassCurve K)

/-- 同じ曲線の代数閉包上の実際の滑らかな点。無限遠点も含む。 -/
def Points := (E.toAffine⁄(AlgebraicClosure K)).Point

/-- Mathlibで証明された幾何学的な点の加法群。古典的等号判定をここで固定する。 -/
noncomputable instance pointsAddCommGroup : AddCommGroup (Points E) := by
  classical
  unfold Points
  infer_instance

/-- 絶対ガロア元の、元の曲線の点に対する座標作用。 -/
noncomputable def pointAction (σ : Field.absoluteGaloisGroup K) : Points E →+ Points E := by
  classical
  exact Affine.Point.map (W' := E.toAffine) (S := K) σ.toAlgHom

/-- 単位自己同型は点を動かさない。 -/
theorem pointAction_one (P : Points E) : pointAction E 1 P = P := by
  cases P <;> rfl

/-- 体の自己同型の合成と、点の写像の合成は同じ順序を持つ。 -/
theorem pointAction_mul (σ τ : Field.absoluteGaloisGroup K) (P : Points E) :
    pointAction E (σ * τ) P = pointAction E σ (pointAction E τ P) := by
  cases P <;> rfl

/-- n倍で零になる点の部分群。形式的な代替空間でなく、点群の実際の核である。 -/
noncomputable def torsionGroup (n : ℕ) : AddSubgroup (Points E) :=
  (nsmulAddMonoidHom n : Points E →+ Points E).ker

/-- 同じn-torsion部分群の型。 -/
noncomputable abbrev Torsion (n : ℕ) := torsionGroup E n

/-- 模範解答が使う標準のtorsionBy条件と、n倍写像の核の条件は同じである。 -/
theorem mem_torsionGroup_iff_torsionBy (n : ℕ) (P : Points E) :
    P ∈ torsionGroup E n ↔ P ∈ Submodule.torsionBy ℤ (Points E) (n : ℤ) := by
  change n • P = 0 ↔ (n : ℤ) • P = 0
  rw [Nat.cast_smul_eq_nsmul ℤ]

/-- 標準torsionBy部分加群との加法同型。元の点をそのまま保持する翻訳アダプタ。 -/
noncomputable def torsionByAddEquiv (n : ℕ) :
    Torsion E n ≃+ Submodule.torsionBy ℤ (Points E) (n : ℤ) where
  toFun P := ⟨P.val, (mem_torsionGroup_iff_torsionBy E n P.val).mp P.property⟩
  invFun P := ⟨P.val, (mem_torsionGroup_iff_torsionBy E n P.val).mpr P.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- アダプタで標準表示へ移しても、幾何学的な点の値は変わらない。 -/
theorem torsionByAddEquiv_val (n : ℕ) (P : Torsion E n) :
    (torsionByAddEquiv E n P).val = P.val := rfl

/-- 元の幾何学的な点へ戻す写像。 -/
noncomputable def underlying {n : ℕ} (P : Torsion E n) : Points E := P.val

/-- 記録した点はn倍で零になる。 -/
theorem underlying_killed {n : ℕ} (P : Torsion E n) : n • underlying E P = 0 := P.property

/-- 1-torsionは零点だけである。非零性を全てのnについて暗黙に仮定しない。 -/
theorem torsion_one_eq_zero (P : Torsion E 1) : P = 0 := by
  apply Subtype.ext
  change P.val = 0
  simpa only [one_nsmul, underlying] using underlying_killed E P

/-- 元の点を区別する単射。 -/
theorem underlying_injective {n : ℕ} : Function.Injective (underlying E (n := n)) :=
  Subtype.val_injective

/-- nで消える加法群に対する標準のZMod n線形構造。nが素数なら残余体上の空間。 -/
noncomputable instance torsionModule (n : ℕ) : Module (ZMod n) (Torsion E n) :=
  AddCommGroup.zmodModule (by
    intro P
    apply Subtype.ext
    exact underlying_killed E P)

/-- 座標作用はn倍を保つので、実際のtorsion部分群へ制限できる。 -/
noncomputable def torsionAction (n : ℕ) (σ : Field.absoluteGaloisGroup K) :
    Torsion E n →+ Torsion E n where
  toFun P := ⟨pointAction E σ P.val, by
    change n • pointAction E σ P.val = 0
    have hP : n • P.val = 0 := P.property
    rw [← map_nsmul, hP, map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' P Q := Subtype.ext (map_add _ P.val Q.val)

/-- 基底を選ばない、実際のn-torsion点群上のガロア表現。 -/
noncomputable def representation (n : ℕ) :
    Representation (ZMod n) (Field.absoluteGaloisGroup K) (Torsion E n) where
  toFun σ := (torsionAction E n σ).toZModLinearMap n
  map_one' := by
    apply LinearMap.ext
    intro P
    apply Subtype.ext
    exact pointAction_one E P.val
  map_mul' σ τ := by
    apply LinearMap.ext
    intro P
    apply Subtype.ext
    exact pointAction_mul E σ τ P.val

/-- 線形表現を幾何学的な点へ戻すと、同じ座標のガロア作用となる。 -/
theorem underlying_representation (n : ℕ) (σ : Field.absoluteGaloisGroup K) (P : Torsion E n) :
    underlying E (representation E n σ P) = pointAction E σ (underlying E P) := rfl

/-- 各ガロア元は可逆に作用する。零写像を形式的に表現と呼んだ構成ではない。 -/
theorem representation_inverse (n : ℕ) (σ : Field.absoluteGaloisGroup K) (P : Torsion E n) :
    representation E n σ⁻¹ (representation E n σ P) = P :=
  Representation.inv_self_apply _ σ P

/-- 線形表現と同じ作用を、連続群作用の標準APIにも渡す。 -/
noncomputable instance torsionGaloisAction (n : ℕ) :
    DistribMulAction (Field.absoluteGaloisGroup K) (Torsion E n) where
  smul σ P := representation E n σ P
  one_smul P := by
    change representation E n 1 P = P
    rw [map_one]
    rfl
  mul_smul σ τ P := by
    change representation E n (σ * τ) P = representation E n σ (representation E n τ P)
    rw [map_mul]
    rfl
  smul_zero σ := map_zero _
  smul_add σ P Q := map_add _ P Q

/-- 群作用記法は、構成済みの同じ線形表現を表す。 -/
theorem galois_smul_def (n : ℕ) (σ : Field.absoluteGaloisGroup K) (P : Torsion E n) :
    σ • P = representation E n σ P := rfl

/-- K有理点を同じ曲線の幾何学的な点へ写す。 -/
noncomputable def baseChangePoint (P : E.toAffine.Point) : Points E := by
  classical
  exact Affine.Point.baseChange (W' := E.toAffine) K (AlgebraicClosure K) P

/-- K有理点の基底変換は、全ての絶対ガロア元で固定される。 -/
theorem pointAction_baseChange (σ : Field.absoluteGaloisGroup K) (P : E.toAffine.Point) :
    pointAction E σ (baseChangePoint E P) = baseChangePoint E P := by
  classical
  exact Affine.Point.map_baseChange (W' := E.toAffine) σ.toAlgHom P

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
