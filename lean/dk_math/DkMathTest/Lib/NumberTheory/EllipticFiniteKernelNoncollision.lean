/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelNoncollision
import DkMath.Lib.NumberTheory.ValuationRationalPrimeSupport
import DkMathTest.Lib.NumberTheory.EllipticFiniteKernelZeroComponent

#print "file: DkMathTest.Lib.NumberTheory.EllipticFiniteKernelNoncollision"

/-! 既存の実3点核とx=1の実点を47上で再利用する。
その還元は滑らかで、核の全還元像から離れることを確認する。 -/
namespace EllipticFiniteKernelNoncollisionTest
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open EllipticFiniteKernelReductionTest EllipticFiniteKernelZeroComponentTest
open EllipticGoodReductionSeparation WeierstrassModelReduction
open ValuationInertia ValuationPrimeSupport ValuationRationalPrimeSupport
noncomputable section
local instance {α : Type*} : DecidableEq α := Classical.decEq _
local instance : sample.IsElliptic := ⟨by norm_num [sample, WeierstrassCurve.Δ, b₂, b₄, b₆, b₈]⟩
local instance : Fintype sampleKernel := Fintype.ofFinset {0, Q, -Q} (by
  intro P
  change P ∈ ({0, Q, -Q} : Finset (Points sample)) ↔ P = 0 ∨ P = Q ∨ P = -Q
  simp only [Finset.mem_insert, Finset.mem_singleton])

private theorem three_unit (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 47) :
    A.valuation (3 : AlgebraicClosure ℚ) = 1 :=
  valuation_intCast_eq_one_of_not_dvd A (by decide : Nat.Prime 47)
    ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := 3) (by norm_num)

/-- x=1の実点は47上で滑らか。特異と仮定すると源方程式から32=0となる。 -/
theorem smooth_at_fortySeven_of_x_one (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : LiesOverPrime A 47) (P : Points sample) (hx : P.xc = 1) :
    HasSmoothReduction (localSource A) P := by
  have hp : P ≠ 0 := by intro he; rw [he] at hx; exact zero_ne_one hx
  rw [Point.eq_some_xc_yc hp, hasSmoothReduction_some_iff]
  intro hxi hyi
  have h32 : (32 : ResidueField A) ≠ 0 := by
    have hv := valuation_intCast_eq_one_of_not_dvd A (by decide : Nat.Prime 47)
      ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := 32) (by norm_num)
    have hr := (WeierstrassResidueModel.residue_ne_zero_iff A (32 : A)).mpr hv
    simpa only [map_ofNat] using hr
  have hxr : residue A ⟨P.xc, hxi⟩ = 1 := by
    have he : (⟨P.xc, hxi⟩ : A) = 1 := Subtype.ext hx
    rw [he, map_one]
  have he := equation_residue (localSource A) (x := ⟨P.xc, hxi⟩) (y := ⟨P.yc, hyi⟩)
    ((localSource_map A).symm ▸ (Point.nonsingular_xc_yc hp).1)
  rw [nonsingular_iff']
  refine ⟨he, Or.inl ?_⟩
  intro hd
  have hy3 : residue A ⟨P.yc, hyi⟩ = 3 := by
    simp only [localSource, WeierstrassCurve.map, map_one, map_zero, map_ofNat, hxr] at hd
    linear_combination hd
  rw [equation_iff] at he
  simp only [localSource, WeierstrassCurve.map, map_one, map_zero, map_ofNat, hxr, hy3] at he
  apply h32
  linear_combination he

/-- x=1の点は47上で、同じ3点核のどの還元像にも衝突しない。 -/
theorem noncollision_of_x_one (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : LiesOverPrime A 47) (P : Points sample) (hx : P.xc = 1) :
    ∀ R : sampleKernel, modelReduce A (localSource A) _ (localSource_map A) P ≠
      modelReduce A (localSource A) _ (localSource_map A) R.val := by
  have hs := smooth_at_fortySeven_of_x_one A hA P hx
  have hx' : (P : (sample.map (algebraMap ℚ (AlgebraicClosure ℚ))).toAffine.Point).xc = 1 := hx
  have hr : modelReduce A (localSource A) _ (localSource_map A) P ≠ 0 := by
    intro hz
    rcases (modelReduce_eq_zero_iff A (localSource A) _ (localSource_map A) hs).mp hz with hp | hi
    · rw [hp] at hx; exact zero_ne_one hx
    · exact hi (hx' ▸ A.one_mem)
  obtain ⟨hxi, _, hxr, _⟩ := modelReduce_coordinates_of_ne_zero A (localSource A) _
    (localSource_map A) P hs hr
  have hx1 : (modelReduce A (localSource A) _ (localSource_map A) P).xc = 1 := by
    have he : (⟨(P : (sample.map (algebraMap ℚ (AlgebraicClosure ℚ))).toAffine.Point).xc, hxi⟩ : A) = 1 :=
      Subtype.ext hx'
    exact hxr.trans ((congrArg (residue A) he).trans (map_one _))
  intro R heq
  have hrx : R.val.xc = 0 := by
    rcases R.property with h | h | h
    · rw [h]; rfl
    · rw [h]; exact sample_kernel_coordinates.1
    · rw [h]; exact sample_kernel_coordinates.2.2.1
  have hk : (modelReduce A (localSource A) _ (localSource_map A) R.val).xc = 0 := by
    change (smoothKernelReduction sample sampleKernel A (localSource A) (localSource_map A)
      (sample_kernel_smooth_at_fortySeven A hA) R).xc = 0
    rw [(smoothKernelReduction_coordinates sample sampleKernel A (localSource A) (localSource_map A)
      (sample_kernel_smooth_at_fortySeven A hA) 3 sample_killed (three_unit A hA) R).1]
    have he : (⟨R.val.xc, (kernel_coordinates_mem sample sampleKernel 3 sample_killed A
      (localSource A) (localSource_map A) (three_unit A hA) R).1⟩ : A) = 0 := Subtype.ext hrx
    rw [he, map_zero]
  have hh := congrArg Point.xc heq
  rw [hx1, hk] at hh
  exact one_ne_zero hh

/-- 実際のx=1の非衝突点について、同じ商のX,Yはともに47上で整。 -/
theorem actual_noncollision_coordinates (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : LiesOverPrime A 47) : ∃ P : Points sample,
    ∃ hp : P ∉ sampleKernel, P.xc = 1 ∧ kernelXAt sample sampleKernel P hp ∈ A ∧
      kernelYAt sample sampleKernel P hp ∈ A := by
  obtain ⟨P, _, hx⟩ := exists_nonzero_point_x_one
  have hs := smooth_at_fortySeven_of_x_one A hA P hx
  have hout := noncollision_of_x_one A hA P hx
  have hp := not_mem_of_reduction_noncollision sample sampleKernel A (localSource A) (localSource_map A) P hout
  have hc := kernelAt_coordinates_mem sample sampleKernel 3 sample_killed A (localSource A)
    (localSource_map A) (three_unit A hA) (sample_kernel_smooth_at_fortySeven A hA) P hs hout
  exact ⟨P, hp, hx, hc⟩

/-- x=1の実点で、同じ商X,Yの剰余は同じ3点還元核による正規化和に等しい。 -/
theorem actual_noncollision_residue (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : LiesOverPrime A 47) (P : Points sample) (hx : P.xc = 1) :
    let hs := sample_kernel_smooth_at_fortySeven A hA
    let hp := smooth_at_fortySeven_of_x_one A hA P hx
    let hout := noncollision_of_x_one A hA P hx
    let hn := three_unit A hA
    let hmem := not_mem_of_reduction_noncollision sample sampleKernel A (localSource A) (localSource_map A) P hout
    let hxy := kernelAt_coordinates_mem sample sampleKernel 3 sample_killed A (localSource A)
      (localSource_map A) hn hs P hp hout
    residue A ⟨kernelXAt sample sampleKernel P hmem, hxy.1⟩ =
      (∑ Q : sampleKernel, (modelReduce A (localSource A) _ (localSource_map A) P +
        smoothKernelReduction sample sampleKernel A (localSource A) (localSource_map A) hs Q).xc) -
        ∑ Q : sampleKernel, (smoothKernelReduction sample sampleKernel A (localSource A) (localSource_map A) hs Q).xc ∧
    residue A ⟨kernelYAt sample sampleKernel P hmem, hxy.2⟩ =
      (∑ Q : sampleKernel, (modelReduce A (localSource A) _ (localSource_map A) P +
        smoothKernelReduction sample sampleKernel A (localSource A) (localSource_map A) hs Q).yc) -
        ∑ Q : sampleKernel, (smoothKernelReduction sample sampleKernel A (localSource A) (localSource_map A) hs Q).yc :=
  kernelAt_coordinates_residue sample sampleKernel 3 sample_killed A (localSource A)
    (localSource_map A) (three_unit A hA) (sample_kernel_smooth_at_fortySeven A hA) P
    (smooth_at_fortySeven_of_x_one A hA P hx) (noncollision_of_x_one A hA P hx)

end
end EllipticFiniteKernelNoncollisionTest
