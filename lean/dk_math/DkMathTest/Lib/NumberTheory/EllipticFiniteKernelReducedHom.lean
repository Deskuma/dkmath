/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelReducedHom
import DkMath.Lib.NumberTheory.ValuationRationalPrimeSupport
import DkMathTest.Lib.NumberTheory.EllipticFiniteKernelReduction

#print "file: DkMathTest.Lib.NumberTheory.EllipticFiniteKernelReducedHom"

/-! 実3点核の47上で還元像への降下と、実際の非零核点の消滅を検査する。 -/
namespace EllipticFiniteKernelReducedHomTest
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open EllipticFiniteKernelReductionTest EllipticGoodReductionSeparation EllipticSmoothReduction
open EllipticNodalTorsion.NodalTorsion ValuationInertia ValuationPrimeSupport ValuationRationalPrimeSupport
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

/-- 47上の任意の実零成分点で、同じ3点核の商と同じ還元像上の準同型が可換。 -/
theorem actual_reduction_commutes (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 47)
    {x₀ y₀ α : ResidueField A} (F : Frame ((localSource A).map (residue A)) x₀ y₀ α)
    (hsep : α ≠ -((localSource A).map (residue A)).a₁ - α)
    (P : zeroComponentSubgroup (localSource A)) :
    nodalReducedHom sample sampleKernel 3 sampleKernel_card (by decide) sample_killed A (localSource A)
      (localSource_map A) (three_unit A hA) (sample_kernel_smooth_at_fortySeven A hA) F hsep
      ⟨zeroComponentReduction (localSource A) P, ⟨P, rfl⟩⟩ =
    zeroComponentReduction (valuationKernelModel sample sampleKernel 3 sample_killed A (localSource A)
      (localSource_map A) (three_unit A hA))
      (nodalZeroComponentHom sample sampleKernel 3 sampleKernel_card (by decide) sample_killed A (localSource A)
        (localSource_map A) (three_unit A hA) (sample_kernel_smooth_at_fortySeven A hA) F hsep P) :=
  nodalReducedHom_commutes sample sampleKernel 3 sampleKernel_card (by decide) sample_killed A (localSource A)
    (localSource_map A) (three_unit A hA) (sample_kernel_smooth_at_fortySeven A hA) F hsep P

/-- 非零実核点Qの同じ還元像も、実際の商の還元準同型ではOとなる。 -/
theorem actual_kernel_reduces_to_zero (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 47)
    {x₀ y₀ α : ResidueField A} (F : Frame ((localSource A).map (residue A)) x₀ y₀ α)
    (hsep : α ≠ -((localSource A).map (residue A)).a₁ - α) :
    let R : sampleKernel := ⟨Q, Or.inr (Or.inl rfl)⟩
    let P : zeroComponentSubgroup (localSource A) := ⟨kernelIntegralPointHom sample sampleKernel A
      (localSource A) (localSource_map A) R,
      (smooth_pointEquiv_of_model A (localSource A) _ (localSource_map A) R.val).mpr
        (sample_kernel_smooth_at_fortySeven A hA R)⟩
    nodalReducedHom sample sampleKernel 3 sampleKernel_card (by decide) sample_killed A (localSource A)
      (localSource_map A) (three_unit A hA) (sample_kernel_smooth_at_fortySeven A hA) F hsep
      ⟨smoothKernelReduction sample sampleKernel A (localSource A) (localSource_map A)
        (sample_kernel_smooth_at_fortySeven A hA) R, ⟨P, rfl⟩⟩ = 0 :=
  nodalReducedHom_kills_kernel sample sampleKernel 3 sampleKernel_card (by decide) sample_killed A (localSource A)
    (localSource_map A) (three_unit A hA) (sample_kernel_smooth_at_fortySeven A hA) F hsep ⟨Q, Or.inr (Or.inl rfl)⟩

/-- 同じ実非零3捩れ点は、源の還元像でも非零であり、核の埋め込みは潰れない。 -/
theorem actual_reduced_kernel_nonzero (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 47) :
    reducedKernelIntoRange sample sampleKernel A (localSource A) (localSource_map A)
      (sample_kernel_smooth_at_fortySeven A hA) ⟨Q, Or.inr (Or.inl rfl)⟩ ≠ 0 := by
  have hi := reducedKernelIntoRange_injective sample sampleKernel 3 sample_killed A (localSource A)
    (localSource_map A) (three_unit A hA) (sample_kernel_smooth_at_fortySeven A hA)
  intro hz
  have he : (⟨Q, Or.inr (Or.inl rfl)⟩ : sampleKernel) = 0 := by
    apply hi
    simpa only [map_zero] using hz
  exact Point.some_ne_zero _ (congrArg Subtype.val he)

/-- 同じ実際の還元像の剰余類を送ると、同じ還元準同型の値になる。 -/
theorem actual_quotient_map (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 47)
    {x₀ y₀ α : ResidueField A} (F : Frame ((localSource A).map (residue A)) x₀ y₀ α)
    (hsep : α ≠ -((localSource A).map (residue A)).a₁ - α)
    (R : (zeroComponentReduction (localSource A)).range) :
    nodalReducedQuotientHom sample sampleKernel 3 sampleKernel_card (by decide) sample_killed A (localSource A)
      (localSource_map A) (three_unit A hA) (sample_kernel_smooth_at_fortySeven A hA) F hsep
      (QuotientAddGroup.mk R) =
    nodalReducedHom sample sampleKernel 3 sampleKernel_card (by decide) sample_killed A (localSource A)
      (localSource_map A) (three_unit A hA) (sample_kernel_smooth_at_fortySeven A hA) F hsep R :=
  nodalReducedQuotientHom_mk sample sampleKernel 3 sampleKernel_card (by decide) sample_killed A (localSource A)
    (localSource_map A) (three_unit A hA) (sample_kernel_smooth_at_fortySeven A hA) F hsep R

end
end EllipticFiniteKernelReducedHomTest
