/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelNodalCenterAll
import DkMath.Lib.NumberTheory.ValuationRationalPrimeSupport
import DkMathTest.Lib.NumberTheory.EllipticFiniteKernelNoncollision
import DkMathTest.Lib.NumberTheory.WeierstrassNodalDistance

#print "file: DkMathTest.Lib.NumberTheory.EllipticFiniteKernelNodalCenter"

/-! 実3点核の47上の全零成分を、中心一致を仮定せず同じ商標的へ輸送する。
源の節点Frameと分離条件は、この例でも明示している。 -/
namespace EllipticFiniteKernelNodalCenterTest
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open EllipticFiniteKernelReductionTest EllipticFiniteKernelNoncollisionTest
open EllipticFiniteKernelZeroComponentTest EllipticGoodReductionSeparation
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

/-- 同じ実3点核の47上で、源Frameから同じ標的の中心を内部構成し全零成分を輸送する。 -/
theorem actual_all_smooth_at_47 (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : LiesOverPrime A 47) {x₀ y₀ α : ResidueField A}
    (F : Frame ((localSource A).map (residue A)) x₀ y₀ α)
    (hsep : α ≠ -((localSource A).map (residue A)).a₁ - α)
    (P : Points sample) (hP : HasSmoothReduction (localSource A) P) :
    HasSmoothReduction (valuationKernelModel sample sampleKernel 3 sample_killed A (localSource A)
      (localSource_map A) (three_unit A hA))
      (oddKernelPointMap sample sampleKernel (sampleKernel_card ▸ (by decide : Odd 3)) P) := by
  obtain ⟨C⟩ := exists_nodal_kernel_criticalCentre sample sampleKernel 3 sampleKernel_card (by decide)
    sample_killed A (localSource A) (localSource_map A) (three_unit A hA)
    (sample_kernel_smooth_at_fortySeven A hA) F hsep
  exact oddKernelPointMap_smooth_of_nodal_all sample sampleKernel 3 sampleKernel_card (by decide)
    sample_killed A (localSource A) (localSource_map A) (three_unit A hA)
    (sample_kernel_smooth_at_fortySeven A hA) F hsep C P hP

/-- 実際に存在するx=1の非零点も、同じ標的で滑らかに還元する。 -/
theorem exists_actual_nonzero_smooth_image (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : LiesOverPrime A 47) {x₀ y₀ α : ResidueField A}
    (F : Frame ((localSource A).map (residue A)) x₀ y₀ α)
    (hsep : α ≠ -((localSource A).map (residue A)).a₁ - α) :
    ∃ P : Points sample, P ≠ 0 ∧ P.xc = 1 ∧
      HasSmoothReduction (valuationKernelModel sample sampleKernel 3 sample_killed A (localSource A)
        (localSource_map A) (three_unit A hA))
        (oddKernelPointMap sample sampleKernel (sampleKernel_card ▸ (by decide : Odd 3)) P) := by
  obtain ⟨P, hp, hx⟩ := exists_nonzero_point_x_one
  exact ⟨P, hp, hx, actual_all_smooth_at_47 A hA F hsep P (smooth_at_fortySeven_of_x_one A hA P hx)⟩


end
end EllipticFiniteKernelNodalCenterTest
