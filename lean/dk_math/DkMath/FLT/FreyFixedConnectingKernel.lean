/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFixedConnectingInjective
import DkMath.FLT.FreyFixedQuotientTrivial

#print "file: DkMath.FLT.FreyFixedConnectingKernel"

/-!
# 同じ不変剰余類と実際の H¹ 係数写像の核の同型

実際の δ の単射性と長完全系列の正確性から、標準の核への整数線形同型を構成する。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
-- 核の部分加群構造は、元の H¹ から継承した構造を使う。
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))

/-- 元の F→Q の包含による実際の通常の H¹ 係数写像。 -/
abbrev ResidualCyclicStage.fixedH1CoefficientMap :=
  groupCohomology.map
    (A := TrivialCharacterH1.coefficient (inertiaSubgroupIn A ℚ) (T.inertiaFixedUpperQuotient A))
    (B := T.fullInertiaCoefficient A) (MonoidHom.id (inertiaSubgroupIn A ℚ)) (T.fixedCoefficientInclusion A) 1

/-- 同じ実際の係数写像の整数線形核。 -/
abbrev ResidualCyclicStage.fixedH1CoefficientKernel := LinearMap.ker (T.fixedH1CoefficientMap A).hom

/-- 同じ連結準同型の像は、同じ実際の係数写像の核。 -/
theorem ResidualCyclicStage.fixedConnecting_range :
    LinearMap.range (T.fixedConnecting A).hom = T.fixedH1CoefficientKernel A := by
  exact (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp
    (groupCohomology.mapShortComplex₁_exact (T.fixedCoefficientSequence_shortExact A) (i := 0) rfl)

/-- 同じ δ の値を同じ核の元として保持する。 -/
def ResidualCyclicStage.fixedConnectingToKernel :
    groupCohomology.H0 (T.fixedQuotientCoefficient A) →ₗ[ℤ] T.fixedH1CoefficientKernel A :=
  (T.fixedConnecting A).hom.codRestrict (T.fixedH1CoefficientKernel A) (by
    intro z
    rw [← T.fixedConnecting_range]
    exact ⟨z, rfl⟩)

/-- 実際の単射な δ が与える、H⁰(Q/F) と係数核の整数線形同型。 -/
def ResidualCyclicStage.fixedConnectingKernelEquiv :
    groupCohomology.H0 (T.fixedQuotientCoefficient A) ≃ₗ[ℤ] T.fixedH1CoefficientKernel A :=
  LinearEquiv.ofBijective (T.fixedConnectingToKernel A) ⟨by
    intro x y hxy
    exact T.fixedConnecting_injective A (congrArg Subtype.val hxy), by
    intro v
    have hv : v.val ∈ LinearMap.range (T.fixedConnecting A).hom := by
      rw [T.fixedConnecting_range]
      exact v.property
    obtain ⟨z, hz⟩ := hv
    exact ⟨z, Subtype.ext hz⟩⟩

/-- 同じ (Q/F)^I と実際の係数核の同型。 -/
def ResidualCyclicStage.invariantConnectingKernelEquiv :
    (T.fixedQuotientCoefficient A).ρ.invariants ≃ₗ[ℤ] T.fixedH1CoefficientKernel A :=
  (CategoryTheory.Iso.toLinearEquiv (groupCohomology.H0Iso (T.fixedQuotientCoefficient A)).symm).trans
    (T.fixedConnectingKernelEquiv A)

variable (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)

include hp5 hq hqp haddr hA in
/-- 同じ局所幾何の下では Q/F 全体が固定なので、同じ Q/F 自体が係数核と同型。 -/
def ResidualCyclicStage.quotientConnectingKernelEquiv :
    T.fixedQuotientCoefficient A ≃ₗ[ℤ] T.fixedH1CoefficientKernel A :=
  (T.fixedQuotientInvariantEquiv hp5 hq hqp haddr A hA).symm.trans
    (T.invariantConnectingKernelEquiv A)

end
end DkMath.FLT.Frey.Source
