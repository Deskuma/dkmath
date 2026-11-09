/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyKernelDecompositionEvaluation

#print "file: DkMath.FLT.FreyResidueDecompositionAction"

/-! # 同じ F・Q/F・K の作用を実際の D/I へ降ろす
ここで I は D 内の元の inertiaSubgroup。剰余群の巡回性や類の不変性は仮定しない。 -/
namespace DkMath.FLT.Frey.Source
/-- 分解群内の元の慣性は、実際の剰余作用の核として正規。 -/
instance inertiaNormalInDecomposition (A : ValuationSubring (AlgebraicClosure ℚ)) :
    (A.inertiaSubgroup ℚ).Normal := by
  delta ValuationSubring.inertiaSubgroup
  exact MonoidHom.normal_ker _
end DkMath.FLT.Frey.Source
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))

/-- 元の I⊆D の元は、同じ F 上で自明に作用する。 -/
theorem ResidualCyclicStage.inertia_le_fixedDecomposition_kernel :
    A.inertiaSubgroup ℚ ≤ (T.fixedDecompositionAction A).ker := by
  intro σ hσ
  apply AddMonoidHom.ext
  intro z
  apply Subtype.ext
  exact z.property σ.val ⟨σ, hσ, rfl⟩
variable (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 同じ Q/F の D 作用でも、元の慣性の作用は自明。 -/
theorem ResidualCyclicStage.inertia_le_quotientDecomposition_kernel :
    A.inertiaSubgroup ℚ ≤ (T.quotientDecompositionAction A).ker := by
  intro σ hσ
  apply LinearMap.ext
  intro z
  exact T.fixedQuotient_action_trivial hp5 hq hqp haddr A hA ⟨σ.val, ⟨σ, hσ, rfl⟩⟩ z

/-- 同じ K の D 作用も元の慣性で零化される。 -/
theorem ResidualCyclicStage.inertia_le_kernelDecomposition_kernel :
    A.inertiaSubgroup ℚ ≤ (T.kernelDecompositionAction A hp5 hq hqp haddr hA).ker := by
  intro σ hσ
  change (T.quotientConnectingKernelEquiv A hp5 hq hqp haddr hA).conjRingEquiv
    (T.quotientDecompositionAction A σ) = 1
  rw [show T.quotientDecompositionAction A σ = 1 from
    T.inertia_le_quotientDecomposition_kernel A hp5 hq hqp haddr hA hσ, map_one]

/-- 元の同じ F に対する D/I の作用。 -/
def ResidualCyclicStage.fixedResidueAction :
    ((A.decompositionSubgroup ℚ) ⧸ A.inertiaSubgroup ℚ) →* AddMonoid.End (T.inertiaFixedUpperQuotient A) :=
  QuotientGroup.lift _ (T.fixedDecompositionAction A) (T.inertia_le_fixedDecomposition_kernel A)

/-- 元の同じ Q/F に対する D/I の作用。 -/
def ResidualCyclicStage.quotientResidueAction :
    ((A.decompositionSubgroup ℚ) ⧸ A.inertiaSubgroup ℚ) →* Module.End ℤ (T.fixedQuotientCoefficient A) :=
  QuotientGroup.lift _ (T.quotientDecompositionAction A)
    (T.inertia_le_quotientDecomposition_kernel A hp5 hq hqp haddr hA)

/-- 元の同じ K に対する D/I の作用。 -/
def ResidualCyclicStage.kernelResidueAction :
    ((A.decompositionSubgroup ℚ) ⧸ A.inertiaSubgroup ℚ) →* Module.End ℤ (T.fixedH1CoefficientKernel A) :=
  QuotientGroup.lift _ (T.kernelDecompositionAction A hp5 hq hqp haddr hA)
    (T.inertia_le_kernelDecomposition_kernel A hp5 hq hqp haddr hA)

/-- 実際の剰余群上でも、以前の同じ連結同型が同変。 -/
theorem ResidualCyclicStage.quotientKernelEquiv_residue
    (s : (A.decompositionSubgroup ℚ) ⧸ A.inertiaSubgroup ℚ) (z : T.fixedQuotientCoefficient A) :
    T.kernelResidueAction A hp5 hq hqp haddr hA s (T.quotientConnectingKernelEquiv A hp5 hq hqp haddr hA z) =
    T.quotientConnectingKernelEquiv A hp5 hq hqp haddr hA (T.quotientResidueAction A hp5 hq hqp haddr hA s z) := by
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective s
  exact T.quotientKernelEquiv_decomposition A hp5 hq hqp haddr hA σ z
end
end DkMath.FLT.Frey.Source

