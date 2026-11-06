/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Hom.End
import Mathlib.Algebra.Module.ZMod

#print "file: DkMath.Lib.Algebra.PrimePowerTateSequence"

/-!
# p 冪で消える互換な点列の加法群

第 n 成分の位数は p^(n+1) の約数、遷移は p 倍。
これは通常の Tate 点列の、法1の自明成分を除いた具体的なモデルである。
ここでは加法群・自然な単射・実際の作用を構成し、ℤₚ 加群構造や階数は主張しない。
-/

namespace DkMath.Lib.Algebra.PrimePowerTateSequence

variable (p : ℕ) (G : Type*) [AddCommGroup G]

/-- 実際の同じ群の点からなる、零化条件と遷移条件を満たす列。 -/
def sequences : AddSubgroup (ℕ → G) where
  carrier := {x | (∀ n, p ^ (n + 1) • x n = 0) ∧ (∀ n, p • x (n + 1) = x n)}
  zero_mem' := by simp
  add_mem' := by
    rintro x y ⟨hx, hxc⟩ ⟨hy, hyc⟩
    exact ⟨fun n => by simp only [Pi.add_apply, nsmul_add, hx n, hy n, add_zero],
      fun n => by simp only [Pi.add_apply, nsmul_add, hxc n, hyc n]⟩
  neg_mem' := by
    rintro x ⟨hx, hxc⟩
    exact ⟨fun n => by simp only [Pi.neg_apply, smul_neg, hx n, neg_zero],
      fun n => by simp only [Pi.neg_apply, smul_neg, hxc n]⟩

/-- 具体的な逆極限の加法群。素数性はこの定義自体には不要。 -/
abbrev Tate := sequences p G

variable {G} {p}

/-- 第 n 成分への評価は加法準同型。 -/
def evaluation (n : ℕ) : Tate p G →+ G where
  toFun x := x.val n
  map_zero' := rfl
  map_add' _ _ := rfl

/-- 同じ点列の実際の零化条件。 -/
theorem killed (x : Tate p G) (n : ℕ) : p ^ (n + 1) • evaluation n x = 0 := x.property.1 n

/-- 同じ点列の隣接遷移。 -/
theorem compatible (x : Tate p G) (n : ℕ) : p • evaluation (n + 1) x = evaluation n x :=
  x.property.2 n

/-- 点列の評価ごとの外延性。 -/
@[ext] theorem ext {x y : Tate p G} (h : ∀ n, evaluation n x = evaluation n y) : x = y :=
  Subtype.ext (funext h)

variable {H : Type*} [AddCommGroup H]

/-- 元の群の準同型を各成分へ適用する自然な写像。 -/
def map (f : G →+ H) : Tate p G →+ Tate p H where
  toFun x := ⟨fun n => f (evaluation n x),
    ⟨fun n => by rw [← map_nsmul, killed, map_zero],
      fun n => by rw [← map_nsmul, compatible]⟩⟩
  map_zero' := by apply ext; intro n; exact f.map_zero
  map_add' x y := by apply ext; intro n; exact f.map_add _ _

/-- 元の群の単射は、実際の互換点列上でも単射。 -/
theorem map_injective (f : G →+ H) (hf : Function.Injective f) : Function.Injective (map (p := p) f) := by
  intro x y h
  apply ext
  intro n
  exact hf (congrArg (evaluation n) h)

variable {Γ : Type*} [Group Γ]

/-- 元の群作用から、各成分に作用する同じ Tate 点列作用を構成する。 -/
def action (ρ : Γ →* AddMonoid.End G) : Γ →* AddMonoid.End (Tate p G) where
  toFun g := map (ρ g)
  map_one' := by
    apply AddMonoidHom.ext
    intro x
    apply ext
    intro n
    change ρ 1 (evaluation n x) = evaluation n x
    rw [map_one]
    rfl
  map_mul' g h := by
    apply AddMonoidHom.ext
    intro x
    apply ext
    intro n
    change ρ (g * h) (evaluation n x) = ρ g (ρ h (evaluation n x))
    rw [map_mul]
    rfl

/-- 作用の評価公式。各成分は元の同じ作用で動く。 -/
theorem evaluation_action (ρ : Γ →* AddMonoid.End G) (g : Γ) (x : Tate p G) (n : ℕ) :
    evaluation n (action ρ g x) = ρ g (evaluation n x) := rfl

end DkMath.Lib.Algebra.PrimePowerTateSequence
