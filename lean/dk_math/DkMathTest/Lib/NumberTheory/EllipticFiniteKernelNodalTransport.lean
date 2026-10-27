/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelNodalTransport
import DkMath.Lib.NumberTheory.ValuationRationalPrimeSupport
import DkMathTest.Lib.NumberTheory.EllipticFiniteKernelReduction

#print "file: DkMathTest.Lib.NumberTheory.EllipticFiniteKernelNodalTransport"

/-! 実3点核を持つ曲線の47上で、中心一致を明示した全零成分輸送を確認する。 -/
namespace EllipticFiniteKernelNodalTransportTest
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open EllipticFiniteKernelReductionTest EllipticGoodReductionSeparation EllipticSmoothReduction
open EllipticCriticalCentre EllipticNodalTorsion.NodalTorsion
open ValuationInertia ValuationPrimeSupport ValuationRationalPrimeSupport
open scoped BigOperators
noncomputable section
local instance {α : Type*} : DecidableEq α := Classical.decEq _
local instance : sample.IsElliptic := ⟨by norm_num [sample, WeierstrassCurve.Δ, b₂, b₄, b₆, b₈]⟩
local instance : Fintype sampleKernel := Fintype.ofFinset {0, Q, -Q} (by
  intro P
  change P ∈ ({0, Q, -Q} : Finset (Points sample)) ↔ P = 0 ∨ P = Q ∨ P = -Q
  simp only [Finset.mem_insert, Finset.mem_singleton])
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private theorem three_unit (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 47) :
    A.valuation (3 : AlgebraicClosure ℚ) = 1 :=
  valuation_intCast_eq_one_of_not_dvd A (by decide : Nat.Prime 47)
    ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := 3) (by norm_num)

/-- 同じ実3点核の47上の全零成分。標的中心と候補の一致は仮定として保持する。 -/
theorem actual_zero_component_of_candidate (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : LiesOverPrime A 47) {x₀ y₀ α : ResidueField A}
    (F : Frame ((localSource A).map (residue A)) x₀ y₀ α)
    (hsep : α ≠ -((localSource A).map (residue A)).a₁ - α)
    (C : CriticalCentre A (kernelModel sample sampleKernel))
    (hc : residue A ⟨C.x, C.x_mem⟩ = (3 : ResidueField A) * x₀ -
      ∑ R : sampleKernel, (smoothKernelReduction sample sampleKernel A (localSource A)
        (localSource_map A) (sample_kernel_smooth_at_fortySeven A hA) R).xc)
    (P : Points sample) (hP : HasSmoothReduction (localSource A) P) :
    HasSmoothReduction (valuationKernelModel sample sampleKernel 3 sample_killed A (localSource A)
      (localSource_map A) (three_unit A hA))
      (oddKernelPointMap sample sampleKernel (sampleKernel_card ▸ (by decide : Odd 3)) P) := by
  exact oddKernelPointMap_smooth_of_candidate sample sampleKernel 3 sample_killed A (localSource A)
    (localSource_map A) (three_unit A hA) (sample_kernel_smooth_at_fortySeven A hA)
    sampleKernel_card _ F hsep C hc P hP

/-- 同じ実核のQが零成分であり、元の商準同型の核に実際に含まれる。 -/
theorem actual_nonzero_kernel_point : Q ≠ 0 ∧ oddKernelPointHom sample sampleKernel
    (sampleKernel_card ▸ (by decide : Odd 3)) Q = 0 := by
  constructor
  · exact Point.some_ne_zero _
  · let := kernelModel_isElliptic_of_odd_card sample sampleKernel
      (sampleKernel_card ▸ (by decide : Odd 3))
    exact kernelPointMap_of_mem sample sampleKernel Q (Or.inr (Or.inl rfl))

end
end EllipticFiniteKernelNodalTransportTest
