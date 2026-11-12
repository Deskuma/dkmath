/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.IrregularNorm37
import DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition

#print "file: DkMath.FLT.Kummer.IrregularCharacter37"

/-!
# IRR-009: State の障害を実際の指標成分へ送る

整数座標の State は、全障害が消える場合と、位相0だけが消え残り36位相が
全て非自明な場合に分かれる。後者の非零ベクトルを実際の37-torsion類群へ入れ、
少なくとも一つの非自明指標で観測する。全共役ノルムを再度課しても、
任意の類のノルムが1なので障害の存在を排除できない。
この有限線形分解は非零障害の存在、Bernoulli数との対応、単元の37乗化を供給しない。
-/
namespace DkMath.FLT.Kummer.IrregularPrime37
open DkMath.Lib.NumberTheory
open scoped NumberField
attribute [local instance] prime37 cyclotomic37

/-- 整数座標を保持した、全消滅／非零位相全残存の二分律。 -/
theorem observe_obstruction_dichotomy {m : ℕ} (E : RegularDescent.State phase37 (m + 1))
    (A B : ℤ) (hx : E.x = (A : 𝓞 Cyclotomic37)) (hy : E.y = (B : 𝓞 Cyclotomic37)) :
    (∀ i, (observe E).phases.obstruction i = 1) ∨
      ((observe E).phases.obstruction 0 = 1 ∧
        ∀ i, i ≠ 0 → (observe E).phases.obstruction i ≠ 1) := by
  have hz := observe_zero_obstruction_eq_one E A B hx hy
  by_cases h : (observe E).phases.obstruction 1 = 1
  · left
    intro i
    by_cases hi : i = 0
    · simpa only [hi] using hz
    · exact (observe_nonzero_trivial_iff E A B hx hy i hi).mpr h
  · exact Or.inr ⟨hz, fun i hi he => h ((observe_nonzero_trivial_iff E A B hx hy i hi).mp he)⟩

/-- 記録済みの同じイデアル類を、F₃₇線形空間に入れる。類や根を選び直さない。 -/
noncomputable def observeVector {m : ℕ} (E : RegularDescent.State phase37 (m + 1))
    (i : Fin 37) : Cyclotomic37CharacterDecomposition.Space Cyclotomic37 :=
  Additive.ofMul ⟨(observe E).phases.obstruction i, (observe E).phases.torsion i⟩

/-- ベクトル化しても元の障害をそのまま復元できる。 -/
theorem underlying_observeVector {m : ℕ} (E : RegularDescent.State phase37 (m + 1))
    (i : Fin 37) : Cyclotomic37CharacterDecomposition.underlying (observeVector E i) = (observe E).phases.obstruction i := rfl

/-- 非零障害という入力があれば、非自明指標への非零射影が存在する。
指標を特定したり、その入力となる非零類の存在を結論に足したりしない。 -/
theorem observe_nontrivial_character {m : ℕ} (E : RegularDescent.State phase37 (m + 1))
    (i : Fin 37) (hne : (observe E).phases.obstruction i ≠ 1) :
    ∃ a : (ZMod 37)ˣ, a ≠ 1 ∧ Cyclotomic37CharacterDecomposition.projector a (observeVector E i) ≠ 0 := by
  apply Cyclotomic37CharacterDecomposition.exists_nontrivial_component
  intro h
  exact hne (congrArg Cyclotomic37CharacterDecomposition.underlying h)

end DkMath.FLT.Kummer.IrregularPrime37
