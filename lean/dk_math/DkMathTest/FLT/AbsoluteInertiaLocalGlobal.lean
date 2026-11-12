/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyInertiaTransport
import DkMathTest.FLT.InertiaLocalGlobal

#print "file: DkMathTest.FLT.AbsoluteInertiaLocalGlobal"

/-!
# NOTE-031-001B: 非自明性を保つ持ち上げと、局所で検出される大域の失敗

有限慣性元の非自明性は制限との可換性から持ち上げ先にも残る。
また、真の開部分群から外れる絶対慣性元が実際に存在することを、
開部分群=全群の算術定理の対偶で証明する。
同じSource 37の大域Fixed/Cofixedが失敗すれば、ある実際の付値環の慣性元で失敗する。
これは局所作用の自明性を供給したという主張ではない。Sourceの存在も仮定なしに主張しない。
-/
namespace AbsoluteInertiaLocalGlobalTest
open DkMath.Lib.NumberTheory ValuationInertia
open DkMath.Lib.RepresentationTheory LocalFixedCofixed
open scoped NumberField
local notation "Γ" => Field.absoluteGaloisGroup ℚ
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

/-- 非自明な有限慣性元の持ち上げは恒等元にはならず、同じq上の慣性に属する。 -/
theorem lift_preserves_nontriviality
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (Q : Ideal (𝓞 L)) [Q.IsMaximal] {q : ℕ} (hq : q.Prime) (hqQ : (q : 𝓞 L) ∈ Q)
    (τ : L ≃ₐ[ℚ] L) (hτ : τ ∈ Q.inertia (L ≃ₐ[ℚ] L)) (hne : τ ≠ 1) :
    ∃ σ : Γ, σ ≠ 1 ∧ AlgEquiv.restrictNormalHom L σ = τ ∧
      ∃ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A q ∧ σ ∈ inertiaSubgroupIn A ℚ := by
  obtain ⟨σ, hστ, A, hA, hσA⟩ :=
    AbsoluteInertiaGeneration.exists_lift_mem_valuation_inertia L Q hq hqQ τ hτ
  refine ⟨σ, ?_, hστ, A, hA, hσA⟩
  intro hσ
  apply hne
  change σ = (1 : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) at hσ
  rw [← hστ, hσ, map_one]

/-- 真の開部分群は、ある有限素点の実際の絶対慣性元を必ず取りこぼす。 -/
theorem proper_open_subgroup_has_local_witness (H : Subgroup Γ)
    (hopen : IsOpen (H : Set Γ)) (hne : H ≠ ⊤) :
    ∃ q : ℕ, q.Prime ∧ ∃ A : ValuationSubring (AlgebraicClosure ℚ),
      LiesOverPrime A q ∧ ∃ σ ∈ inertiaSubgroupIn A ℚ, σ ∉ H := by
  by_contra! h
  exact hne (AbsoluteInertiaGeneration.subgroup_eq_top_of_inertia_le H hopen h)

/-- 1は付値環の単元なので、素数上の住所の条件を満たさない。 -/
theorem not_liesOver_one (A : ValuationSubring (AlgebraicClosure ℚ)) : ¬ LiesOverPrime A 1 := by
  change ¬ (1 : AlgebraicClosure ℚ) ∈ A.nonunits
  rw [ValuationSubring.mem_nonunits_iff, map_one]
  exact lt_irrefl 1

/-- 単元分母の表示では分母が非零であり、分数へ戻す約分が正当化される。 -/
theorem integral_fraction_denominator_ne_zero (A : ValuationSubring (AlgebraicClosure ℚ))
    {q : ℕ} (hq : q.Prime) (hA : LiesOverPrime A q) (a : AlgebraicClosure ℚ) (ha : a ∈ A) :
    ∃ x s : integralClosure ℤ (AlgebraicClosure ℚ),
      (s : AlgebraicClosure ℚ) ≠ 0 ∧ (s : AlgebraicClosure ℚ) ∉ A.nonunits ∧ a * s = x := by
  obtain ⟨x, s, hs, hax⟩ :=
    ValuationInertiaLift.FractionRepresentation.exists_integral_fraction A hq hA a ha
  refine ⟨x, s, ?_, hs, hax⟩
  intro h
  apply hs
  rw [h, ValuationSubring.mem_nonunits_iff, map_zero]
  exact zero_lt_one

/-- 同じSource 37の局所Fixedを輸送する。開核・有限性を回帰の追加仮定に取らない。 -/
theorem source37_fixed (S : DkMath.FLT.Frey.Source 37) (N : Submodule (ZMod 37) S.ResidualSpace)
    (hlocal : ∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      LiesOverPrime A q → FixedOn S.residualRepresentation N (inertiaSubgroupIn A ℚ)) :
    IsFixedOn S.residualRepresentation N := S.residual_isFixedOn_of_inertia N hlocal

/-- 同じSource 37の商の局所固定を輸送する。Nを別の直線に選び直さない。 -/
theorem source37_cofixed (S : DkMath.FLT.Frey.Source 37) (N : Submodule (ZMod 37) S.ResidualSpace)
    (hlocal : ∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      LiesOverPrime A q → CofixedOn S.residualRepresentation N (inertiaSubgroupIn A ℚ)) :
    IsCofixedOn S.residualRepresentation N := S.residual_isCofixedOn_of_inertia N hlocal

/-- Source 37の共通側の二択はhsideを保持する条件付き接続である。 -/
theorem source37_common_side (S : DkMath.FLT.Frey.Source 37)
    (N : Submodule (ZMod 37) S.ResidualSpace)
    (hside :
      (∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
        LiesOverPrime A q → FixedOn S.residualRepresentation N (inertiaSubgroupIn A ℚ)) ∨
      (∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
        LiesOverPrime A q → CofixedOn S.residualRepresentation N (inertiaSubgroupIn A ℚ))) :
    IsFixedOn S.residualRepresentation N ∨ IsCofixedOn S.residualRepresentation N :=
  S.residual_fixed_or_cofixed_of_inertia_common_side N hside

/-- Source 37で大域Cofixedが失敗すれば、あるq上の実際の慣性元で差がNを外れる。 -/
theorem source37_cofixed_failure_local_witness (S : DkMath.FLT.Frey.Source 37)
    (N : Submodule (ZMod 37) S.ResidualSpace) (hbad : ¬ IsCofixedOn S.residualRepresentation N) :
    ∃ q : ℕ, q.Prime ∧ ∃ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A q ∧
      ∃ σ ∈ inertiaSubgroupIn A ℚ, ∃ x, S.residualRepresentation σ x - x ∉ N := by
  by_contra! h
  exact hbad (S.residual_isCofixedOn_of_inertia N h)

/-- 前回の安定直線の反例は引き続き有効で、各局所群で別々に選ぶ二択では足りない。 -/
theorem inconsistent_side_boundary :
    Module.finrank InertiaLocalGlobalTest.SideBoundary.k InertiaLocalGlobalTest.SideBoundary.line = 1 ∧
    ¬ (IsFixedOn InertiaLocalGlobalTest.SideBoundary.rho InertiaLocalGlobalTest.SideBoundary.line ∨
      IsCofixedOn InertiaLocalGlobalTest.SideBoundary.rho InertiaLocalGlobalTest.SideBoundary.line) :=
  ⟨InertiaLocalGlobalTest.SideBoundary.line_finrank,
    fun h => h.elim InertiaLocalGlobalTest.SideBoundary.not_global_fixed
      InertiaLocalGlobalTest.SideBoundary.not_global_cofixed⟩

end AbsoluteInertiaLocalGlobalTest
