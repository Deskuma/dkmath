/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.ValuationPlaceConjugacy
import DkMath.Lib.RepresentationTheory.ConjugateLocalConditions

#print "file: DkMath.Lib.NumberTheory.AbsoluteInertiaConjugacy"

/-!
# NOTE-031-004D: 一つの付値環で選んだ側を同じ素数上の全付値環へ運ぶ

付値環の共役推移性と、同時に共役される慣性群の等式を組み合わせる。
Nは全絶対ガロア群で安定な同じ部分加群のまま保つ。
結論の論理形は(∀A,Fixed)∨(∀A,Cofixed)である。各付値環で側を取り直す形へ弱めない。
局所二択そのものの数論的供給はこの輸送の入力であり、応用側で別に証明する。
-/
namespace DkMath.Lib.NumberTheory.AbsoluteInertiaConjugacy
open ValuationInertia ValuationPlaceConjugacy
open DkMath.Lib.RepresentationTheory LocalFixedCofixed ConjugateLocalConditions
variable {k V : Type*} [CommRing k] [AddCommGroup V] [Module k V]
local notation "G" => (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)

/-- 一つのq上の付値環でのFixed/Cofixed二択を、全付値環の同じ側の二択へ輸送する。 -/
theorem common_side_on_places (ρ : Representation k G V) (N : Submodule k V)
    (hN : IsStable ρ N) {q : ℕ} (hq : q.Prime)
    (A₀ : ValuationSubring (AlgebraicClosure ℚ)) (hA₀ : LiesOverPrime A₀ q)
    (h : FixedOn ρ N (inertiaSubgroupIn A₀ ℚ) ∨ CofixedOn ρ N (inertiaSubgroupIn A₀ ℚ)) :
    (∀ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A q →
      FixedOn ρ N (inertiaSubgroupIn A ℚ)) ∨
    (∀ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A q →
      CofixedOn ρ N (inertiaSubgroupIn A ℚ)) := by
  rcases h with hf | hc
  · left
    intro A hA
    obtain ⟨g, hg⟩ := exists_smul_eq hq hA₀ hA
    rw [← hg, inertia_smul]
    exact fixedOn_conjugate ρ N hN _ g hf
  · right
    intro A hA
    obtain ⟨g, hg⟩ := exists_smul_eq hq hA₀ hA
    rw [← hg, inertia_smul]
    exact cofixedOn_conjugate ρ N hN _ g hc

end DkMath.Lib.NumberTheory.AbsoluteInertiaConjugacy
