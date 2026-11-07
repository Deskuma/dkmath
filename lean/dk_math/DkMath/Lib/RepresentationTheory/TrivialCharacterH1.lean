/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.Algebra.Group.TypeTags.Hom

#print "file: DkMath.Lib.RepresentationTheory.TrivialCharacterH1"

/-!
# 自明作用の係数への準同型が与える通常の H¹

Mathlib の通常の群コホモロジーを使う。位相や連続 H¹ の比較は主張しない。
-/
namespace DkMath.Lib.RepresentationTheory.TrivialCharacterH1
noncomputable section
variable {Γ V : Type} [Group Γ] [AddCommGroup V] (f : Γ →* Multiplicative V)

/-- 元の同じ加法群を係数とする、自明な整数線形表現。 -/
abbrev coefficient (Γ V : Type) [Group Γ] [AddCommGroup V] : Rep ℤ Γ := Rep.trivial ℤ Γ V

/-- 通常の乗法記法の準同型を、同じ値の加法的準同型へ翻訳する。 -/
def additive : Additive Γ →+ V where
  toFun g := Multiplicative.toAdd (f g.toMul)
  map_zero' := congrArg Multiplicative.toAdd f.map_one
  map_add' g h := congrArg Multiplicative.toAdd (f.map_mul g.toMul h.toMul)

/-- 同じ準同型の通常の 1-cocycle。 -/
def cocycle : groupCohomology.cocycles₁ (coefficient Γ V) :=
  (groupCohomology.cocycles₁IsoOfIsTrivial (coefficient Γ V)).inv (additive f)

/-- 代表 cocycle の値は、元の準同型の同じ値。 -/
theorem cocycle_apply (g : Γ) : cocycle f g = Multiplicative.toAdd (f g) := rfl

/-- 同じ代表から構成した Mathlib の通常の H¹ 類。 -/
def cohomologyClass : groupCohomology.H1 (coefficient Γ V) :=
  groupCohomology.H1π (coefficient Γ V) (cocycle f)

/-- 自明作用の H¹ と準同型の同型を通じて、同じ値を回収できる。 -/
theorem class_evaluate (g : Γ) :
    (groupCohomology.H1IsoOfIsTrivial (coefficient Γ V)).hom (cohomologyClass f)
      (Additive.ofMul g) = Multiplicative.toAdd (f g) :=
  groupCohomology.H1IsoOfIsTrivial_H1π_apply_apply (cocycle f) (Additive.ofMul g)

/-- 実際の非自明な値があれば、自明作用を係数とする通常の H¹ 類は非零。 -/
theorem class_ne_zero (hf : ∃ g, f g ≠ 1) : cohomologyClass f ≠ 0 := by
  intro hc
  obtain ⟨g, hg⟩ := hf
  have he := class_evaluate f g
  rw [hc, map_zero] at he
  exact hg (congrArg Multiplicative.ofAdd he.symm)

end
end DkMath.Lib.RepresentationTheory.TrivialCharacterH1
