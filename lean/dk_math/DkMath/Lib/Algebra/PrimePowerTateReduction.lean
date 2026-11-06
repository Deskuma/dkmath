/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.PrimePowerTateModule
import Mathlib.GroupTheory.QuotientGroup.Basic

#print "file: DkMath.Lib.Algebra.PrimePowerTateReduction"

/-!
# 標準 Tate 加群の第0成分と p 倍像

第0成分が零なら一段ずらした点列が p 倍逆像になる。
元の群の p 倍全射性があれば、実際の互換逆像列から第0評価の全射性も得る。
-/
namespace DkMath.Lib.Algebra.PrimePowerTateSequence
noncomputable section
variable {p : ℕ} {G : Type*} [AddCommGroup G]

/-- 第 n 成分の p^n 倍は、元の同じ第0成分。 -/
theorem evaluation_to_zero (x : Tate p G) (n : ℕ) :
    p ^ n • evaluation n x = evaluation 0 x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_nsmul', compatible, ih]

/-- 同じ点群の p 捩れへの第0評価。 -/
def reduction : Tate p G →+ (nsmulAddMonoidHom p : G →+ G).ker where
  toFun x := ⟨evaluation 0 x, by
    change p • evaluation 0 x = 0
    simpa only [Nat.zero_add, pow_one] using killed x 0⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- 第0成分が零なら、同じ点列を一段ずらすことができる。 -/
def shiftOfZero (x : Tate p G) (hx : reduction x = 0) : Tate p G :=
  ⟨fun n => evaluation (n + 1) x,
    ⟨fun n => (evaluation_to_zero x (n + 1)).trans (congrArg Subtype.val hx),
      fun n => compatible x (n + 1)⟩⟩

/-- 一段ずらした点列の実際の p 倍は元の点列。 -/
theorem nsmul_shiftOfZero (x : Tate p G) (hx : reduction x = 0) :
    p • shiftOfZero x hx = x := by
  apply ext; intro n
  change p • evaluation (n + 1) x = evaluation n x
  exact compatible x n

/-- 全 Tate 点列の p 倍写像は単射。第0成分だけの単射性ではない。 -/
theorem nsmul_injective : Function.Injective (nsmulAddMonoidHom p : Tate p G →+ Tate p G) := by
  intro x y h
  apply ext; intro n
  have he := congrArg (evaluation (n + 1)) h
  change p • evaluation (n + 1) x = p • evaluation (n + 1) y at he
  simpa only [compatible] using he

/-- 第0評価の核は同じ Tate 加群内の p 倍像。 -/
theorem range_nsmul_eq_reduction_ker :
    (nsmulAddMonoidHom p : Tate p G →+ Tate p G).range = (reduction (p := p) (G := G)).ker := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    apply Subtype.ext
    change p • evaluation 0 x = 0
    simpa only [Nat.zero_add, pow_one] using killed x 0
  · intro x hx
    exact ⟨shiftOfZero x hx, nsmul_shiftOfZero x hx⟩

variable (hdiv : Function.Surjective (nsmulAddMonoidHom p : G →+ G))

/-- 同じ群内の p 倍逆像を直前の点から順に選ぶ。 -/
def divisionSequence (a : (nsmulAddMonoidHom p : G →+ G).ker) : ℕ → G :=
  Nat.rec a.val (fun _ x => (hdiv x).choose)

theorem divisionSequence_step (a : (nsmulAddMonoidHom p : G →+ G).ker) (n : ℕ) :
    p • divisionSequence hdiv a (n + 1) = divisionSequence hdiv a n :=
  (hdiv (divisionSequence hdiv a n)).choose_spec

/-- 選んだ互換逆像は正確な段の p 冪で消える。 -/
theorem divisionSequence_killed (a : (nsmulAddMonoidHom p : G →+ G).ker) (n : ℕ) :
    p ^ (n + 1) • divisionSequence hdiv a n = 0 := by
  induction n with
  | zero =>
    change p ^ (0 + 1) • a.val = 0
    rw [Nat.zero_add, pow_one]
    exact a.property
  | succ n ih => rw [pow_succ, mul_nsmul', divisionSequence_step, ih]

include hdiv in
/-- p 倍全射性から、第0評価の全射性を実際の点列で証明する。 -/
theorem reduction_surjective : Function.Surjective (reduction (p := p) (G := G)) := by
  intro a
  exact ⟨⟨divisionSequence hdiv a, ⟨divisionSequence_killed hdiv a, divisionSequence_step hdiv a⟩⟩, rfl⟩

/-- 標準 Tate 加群の p 倍による商は、元の群の p 捩れと自然に加法同型。 -/
def quotientEquiv :
    Tate p G ⧸ (nsmulAddMonoidHom p : Tate p G →+ Tate p G).range ≃+
      (nsmulAddMonoidHom p : G →+ G).ker := by
  rw [range_nsmul_eq_reduction_ker]
  exact QuotientAddGroup.quotientKerEquivOfSurjective _ (reduction_surjective hdiv)

end
end DkMath.Lib.Algebra.PrimePowerTateSequence
