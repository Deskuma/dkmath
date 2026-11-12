/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.AbsoluteInertiaGeneration
import DkMath.Lib.RepresentationTheory.LocalFixedCofixed

#print "file: DkMath.Lib.NumberTheory.AbsoluteInertiaRepresentation"

/-!
# NOTE-031-001B: 開核を持つ絶対ガロア表現の局所大域輸送

部分加群を点ごとに固定する群元と、全ての変化量が部分加群に入る群元は部分群をなす。
表現の核は両方の部分群に含まれるので、開核があればそれらも開く。
全ての有限素点の絶対慣性群が入るなら、実際に証明した開部分群=全群の定理を適用できる。

開核は明示入力であり、一般の無限加群表現から暗黙に得られるとはしない。
実際の楕円曲線の非零torsion表現では、幾何学的有限性と座標作用の連続性から供給する。
同じρ・同じNを両側で使い、安定性・一次元性をこの輸送に追加要求しない。
-/
namespace DkMath.Lib.NumberTheory.AbsoluteInertiaRepresentation
open ValuationInertia
open DkMath.Lib.RepresentationTheory LocalFixedCofixed
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
local notation "Γ" => Field.absoluteGaloisGroup ℚ

/-- 開核を持つ同じ表現で、Nを点ごとに固定する部分群も開く。 -/
theorem fixedSubgroup_isOpen (ρ : Representation R Γ V) (N : Submodule R V)
    (hopen : IsOpen (ρ.ker : Set Γ)) :
    IsOpen (fixedSubgroup ρ N : Set Γ) := by
  apply Subgroup.isOpen_mono (H₁ := ρ.ker) _ hopen
  intro g hg x _
  change ρ g = 1 at hg
  rw [hg]
  rfl

/-- 開核を持つ同じ表現で、商の変化量がNへ入る部分群も開く。 -/
theorem cofixedSubgroup_isOpen (ρ : Representation R Γ V) (N : Submodule R V)
    (hopen : IsOpen (ρ.ker : Set Γ)) :
    IsOpen (cofixedSubgroup ρ N : Set Γ) := by
  apply Subgroup.isOpen_mono (H₁ := ρ.ker) _ hopen
  intro g hg x
  change ρ g = 1 at hg
  rw [hg]
  simp

/-- 全てのq上の全ての付値環でNが慣性により点ごとに固定されれば、大域でもFixedとなる。
開核と全素点の条件を保持し、絶対慣性の生成性は算術証明から供給する。 -/
theorem isFixedOn_of_inertia (ρ : Representation R Γ V) (N : Submodule R V)
    (hopen : IsOpen (ρ.ker : Set Γ))
    (hlocal : ∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      LiesOverPrime A q → FixedOn ρ N (inertiaSubgroupIn A ℚ)) : IsFixedOn ρ N := by
  have ht := AbsoluteInertiaGeneration.subgroup_eq_top_of_inertia_le (fixedSubgroup ρ N)
    (fixedSubgroup_isOpen ρ N hopen) (fun q hq A hA => hlocal q hq A hA)
  intro g x hx
  have hg : g ∈ fixedSubgroup ρ N := ht ▸ Subgroup.mem_top g
  exact hg x hx

/-- 全てのq上の全ての付値環で商が慣性固定なら、大域でもCofixedとなる。
商の表現を新たに選ばず、同じV・Nの差の所属として結論する。 -/
theorem isCofixedOn_of_inertia (ρ : Representation R Γ V) (N : Submodule R V)
    (hopen : IsOpen (ρ.ker : Set Γ))
    (hlocal : ∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      LiesOverPrime A q → CofixedOn ρ N (inertiaSubgroupIn A ℚ)) : IsCofixedOn ρ N := by
  have ht := AbsoluteInertiaGeneration.subgroup_eq_top_of_inertia_le (cofixedSubgroup ρ N)
    (cofixedSubgroup_isOpen ρ N hopen) (fun q hq A hA => hlocal q hq A hA)
  intro g x
  have hg : g ∈ cofixedSubgroup ρ N := ht ▸ Subgroup.mem_top g
  exact hg x

/-- 全素点に共通の側を選んだ局所二択を、大域Fixed/Cofixedへ輸送する。
各素点で独立に選ぶ二択へ量化順序を変えない。 -/
theorem fixed_or_cofixed_of_inertia_common_side (ρ : Representation R Γ V) (N : Submodule R V)
    (hopen : IsOpen (ρ.ker : Set Γ))
    (hside :
      (∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
        LiesOverPrime A q → FixedOn ρ N (inertiaSubgroupIn A ℚ)) ∨
      (∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
        LiesOverPrime A q → CofixedOn ρ N (inertiaSubgroupIn A ℚ))) :
    IsFixedOn ρ N ∨ IsCofixedOn ρ N :=
  hside.elim (fun h => Or.inl (isFixedOn_of_inertia ρ N hopen h))
    (fun h => Or.inr (isCofixedOn_of_inertia ρ N hopen h))

end DkMath.Lib.NumberTheory.AbsoluteInertiaRepresentation
