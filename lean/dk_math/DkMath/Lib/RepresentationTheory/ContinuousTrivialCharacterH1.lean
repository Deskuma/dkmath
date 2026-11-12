/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.RepresentationTheory.TrivialCharacterH1
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Constructions

#print "file: DkMath.Lib.RepresentationTheory.ContinuousTrivialCharacterH1"

/-! # 自明係数の連続指標と同じ通常 H¹ 類
連続指標を保持し、通常 H¹ への忘却が同じ cocycle と値を保つことを証明する。
一般の連続群コホモロジー全体や大域 Selmer 比較を定義したとは主張しない。 -/
namespace DkMath.Lib.RepresentationTheory.ContinuousTrivialCharacterH1
noncomputable section
variable {Γ V : Type} [Group Γ] [AddCommGroup V] [TopologicalSpace Γ] [TopologicalSpace V]

/-- 通常 H¹ に使う cocycle と同じ代表。連続性を別の定理で保持する。 -/
def cocycle (f : ContinuousMonoidHom Γ (Multiplicative V)) :=
  TrivialCharacterH1.cocycle f.toMonoidHom

/-- 同じ cocycle は元の位相に関して連続。 -/
theorem cocycle_continuous (f : ContinuousMonoidHom Γ (Multiplicative V)) :
    Continuous (fun g : Γ => cocycle f g) :=
  continuous_toAdd.comp f.continuous

/-- 連続指標の同じ代表を通常 H¹ へ忘却する。 -/
def forgetClass (f : ContinuousMonoidHom Γ (Multiplicative V)) :=
  TrivialCharacterH1.cohomologyClass f.toMonoidHom

/-- 忘却後も元の指標と同じ値を回収する。 -/
theorem forgetClass_evaluate (f : ContinuousMonoidHom Γ (Multiplicative V)) (g : Γ) :
    (groupCohomology.H1IsoOfIsTrivial (TrivialCharacterH1.coefficient Γ V)).hom (forgetClass f)
      (Additive.ofMul g) = Multiplicative.toAdd (f g) :=
  TrivialCharacterH1.class_evaluate f.toMonoidHom g

/-- 自明作用では、連続指標から通常 H¹ への忘却は単射。 -/
theorem forgetClass_injective : Function.Injective (forgetClass (Γ := Γ) (V := V)) := by
  intro f g he
  apply ContinuousMonoidHom.ext
  intro σ
  apply Multiplicative.toAdd.injective
  rw [← forgetClass_evaluate f σ, ← forgetClass_evaluate g σ, he]

/-- 連続性を保持したまま、非自明な値が通常 H¹ の非零性を検出する。 -/
theorem forgetClass_ne_zero (f : ContinuousMonoidHom Γ (Multiplicative V))
    (hf : ∃ g, f g ≠ 1) : forgetClass f ≠ 0 :=
  TrivialCharacterH1.class_ne_zero f.toMonoidHom hf
end
end DkMath.Lib.RepresentationTheory.ContinuousTrivialCharacterH1

