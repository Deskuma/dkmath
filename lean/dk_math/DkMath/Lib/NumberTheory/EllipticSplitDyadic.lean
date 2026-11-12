/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Reconstructed from DkMath EllipticNodalInertia (upstream blob
4671d1857e26c4967080e5f48c4ce2fbe56484ee) and EllipticFrobeniusBranchSwap.
Modified: split residue quadratic; full decomposition group instead of inertia;
retain the same centre, directions, model and actual point difference.
-/

import DkMath.Lib.NumberTheory.EllipticFrobeniusBranchSwap
import DkMath.Lib.NumberTheory.EllipticNodalInertia
import DkMath.Lib.NumberTheory.ValuationSplitQuadratic

#print "file: DkMath.Lib.NumberTheory.EllipticSplitDyadic"

/-!
# NOTE-032-005A: 分裂接錐では分解群が商を固定する

[DkMath.Lib] 剰余a₁=1,a₂=0,x₀=0の接錐の根は0,1である。
分解群は剰余体の0,1を固定するので、分離した実際の方向も個別に固定する。
浅い点の中心傾きの剰余も0,1であり、分解群による傾きの差は非単元となる。
同じ深さ・同じ枝の比較からσP−Pは滑らかに還元する。
臨界側は既存の二点の和の定理、滑らかな側は加法閉性で補い、全ての実点で結論する。

点そのものの固定や、全ガロア群の商作用の自明性は主張しない。
分解群での+1作用は3側の−1作用と異なり、Cofixed条件と矛盾しない。
-/
namespace DkMath.Lib.NumberTheory.EllipticSplitDyadic
open WeierstrassCurve IsLocalRing ValuationInertia ValuationPrimeSupport
open EllipticCriticalCentre EllipticTangentDirections EllipticCriticalCentreAlgebra
open EllipticGoodReductionSeparation EllipticShallowSlope ValuationTameCharacter.TameCharacter

/-- [DkMath.Lib] 同じモデルの小さい接錐値を分裂式z²+z=0へ写す。 -/
theorem quadratic_residue_eq_zero {L : Type*} [Field L] {A : ValuationSubring L}
    (M : WeierstrassCurve A) (V : WeierstrassCurve L) (hm : M.map A.subtype = V)
    (C : CriticalCentre A V)
    (ha₁ : (M.map (residue A)).a₁ = 1) (ha₂ : (M.map (residue A)).a₂ = 0)
    (hx₀ : residue A (⟨C.x, C.x_mem⟩ : A) = 0)
    {z : L} (hz : z ∈ A)
    (hsmall : A.valuation (z ^ 2 + V.a₁ * z - (V.a₂ + 3 * C.x)) < 1) :
    residue A (⟨z, hz⟩ : A) ^ 2 + residue A (⟨z, hz⟩ : A) = 0 := by
  subst V
  let x₀ : A := ⟨C.x, C.x_mem⟩
  let t : A := ⟨z, hz⟩
  let f : A := t ^ 2 + M.a₁ * t - (M.a₂ + 3 * x₀)
  have hf : residue A f = 0 := by
    apply (ValuationResidue.coe_mem_nonunits_iff_residue_eq_zero A f).mp
    rw [ValuationSubring.mem_nonunits_iff]
    exact hsmall
  change residue A M.a₁ = 1 at ha₁
  change residue A M.a₂ = 0 at ha₂
  change residue A x₀ = 0 at hx₀
  simpa only [f, map_sub, map_add, map_pow, map_mul, map_ofNat,
    ha₁, ha₂, hx₀, mul_zero, add_zero, one_mul, sub_zero] using hf

/-- [DkMath.Lib] 分裂接錐の同じ分離方向は、分解群全体で個別に固定される。
剰余合同と同じ二次式の因数分解を併用して、剰余固定から実際の根の固定へ戻す。 -/
theorem directions_decomposition_fixed (E : WeierstrassCurve ℚ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (M : WeierstrassCurve A) (hm : M.map A.subtype = E.baseChange (AlgebraicClosure ℚ))
    (C : CriticalCentre A (E.baseChange (AlgebraicClosure ℚ))) (D : TangentDirections C)
    (ha₁ : (M.map (residue A)).a₁ = 1) (ha₂ : (M.map (residue A)).a₂ = 0)
    (hx₀ : residue A (⟨C.x, C.x_mem⟩ : A) = 0)
    {σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)}
    (hσ : σ ∈ A.decompositionSubgroup ℚ) : σ D.α = D.α ∧ σ D.β = D.β := by
  have : CharP (ResidueField A) 2 := charP_residueField A Nat.prime_two hA
  have hfix := EllipticDyadicGeometry.decomposition_fixed E A C
    ((ValuationSubring.mem_nonunits_iff _).mp hA) σ hσ
  have hroot := quadratic_residue_eq_zero M _ hm C ha₁ ha₂ hx₀ D.α_mem
    (by rw [D.roots.1, map_zero]; exact zero_lt_one)
  have hnear := (ValuationSubring.mem_nonunits_iff A).mp
    (ValuationSplitQuadratic.apply_sub_mem_nonunits A hσ D.α_mem hroot)
  have hr : (σ D.α) ^ 2 + (E.baseChange (AlgebraicClosure ℚ)).a₁ * σ D.α -
      ((E.baseChange (AlgebraicClosure ℚ)).a₂ + 3 * C.x) = 0 := by
    simpa [WeierstrassCurve.baseChange, map_ofNat, hfix.1] using congrArg σ D.roots.1
  have hfac : (σ D.α - D.α) * (σ D.α - D.β) = 0 := by
    linear_combination hr - σ D.α * D.sum_eq + D.product_eq
  have hα : σ D.α = D.α := by
    rcases mul_eq_zero.mp hfac with h | h
    · exact sub_eq_zero.mp h
    · rw [sub_eq_zero.mp h, Valuation.map_sub_swap, D.separated] at hnear
      exact (lt_irrefl _ hnear).elim
  have hsum := congrArg σ D.sum_eq
  have e₁ : σ (E.baseChange (AlgebraicClosure ℚ)).a₁ = (E.baseChange (AlgebraicClosure ℚ)).a₁ := by
    simp [WeierstrassCurve.baseChange]
  simp only [map_add, map_neg, e₁, hα] at hsum
  exact ⟨hα, by linear_combination hsum - D.sum_eq⟩

/-- [DkMath.Lib] 分裂接錐の浅い点では、中心傾きの分解群変化量は非単元となる。
浅さは明示し、臨界側へこの傾き計算を拡張しない。 -/
theorem slope_difference_small (E : WeierstrassCurve ℚ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (M : WeierstrassCurve A) (hm : M.map A.subtype = E.baseChange (AlgebraicClosure ℚ))
    (C : CriticalCentre A (E.baseChange (AlgebraicClosure ℚ))) (D : TangentDirections C)
    (ha₁ : (M.map (residue A)).a₁ = 1) (ha₂ : (M.map (residue A)).a₂ = 0)
    (hx₀ : residue A (⟨C.x, C.x_mem⟩ : A) = 0)
    {σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)}
    (hσ : σ ∈ A.decompositionSubgroup ℚ)
    {x y : AlgebraicClosure ℚ} (h : (E.baseChange (AlgebraicClosure ℚ)).toAffine.Equation x y)
    (hX : A.valuation (x - C.x) < 1)
    (hsh : A.valuation (equationDefect (E.baseChange (AlgebraicClosure ℚ)) C.x C.y) <
      A.valuation (x - C.x) ^ 2) :
    A.valuation (σ (centreSlope C x y) - centreSlope C x y) < 1 := by
  have : CharP (ResidueField A) 2 := charP_residueField A Nat.prime_two hA
  have hz := (slope_mem_and_branches_of_shallow D h hX hsh).1
  apply (ValuationSubring.mem_nonunits_iff A).mp
  exact ValuationSplitQuadratic.apply_sub_mem_nonunits A hσ hz
    (quadratic_residue_eq_zero M _ hm C ha₁ ha₂ hx₀ hz (quadratic_small_of_shallow C h hX hsh))

/-- [DkMath.Lib] 分裂接錐では全ての実点の分解群変化量が零成分へ入る。
浅い点は同じ枝の差、臨界側は二点の和、滑らかな点は加法閉性で扱う。
捩れ位数・素数性を仮定せず、点そのものの固定も主張しない。 -/
theorem decomposition_difference_smooth [DecidableEq (AlgebraicClosure ℚ)]
    (E : WeierstrassCurve ℚ) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (M : WeierstrassCurve A) (hm : M.map A.subtype = E.baseChange (AlgebraicClosure ℚ))
    (C : CriticalCentre A (E.baseChange (AlgebraicClosure ℚ))) (D : TangentDirections C)
    (ha₁ : (M.map (residue A)).a₁ = 1) (ha₂ : (M.map (residue A)).a₂ = 0)
    (hx₀ : residue A (⟨C.x, C.x_mem⟩ : A) = 0)
    {σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)}
    (hσ : σ ∈ A.decompositionSubgroup ℚ)
    (P : (E.baseChange (AlgebraicClosure ℚ)).toAffine.Point) :
    HasSmoothReduction M (Affine.Point.map σ.toAlgHom P - P) := by
  classical
  have hfix := EllipticDyadicGeometry.decomposition_fixed E A C
    ((ValuationSubring.mem_nonunits_iff _).mp hA) σ hσ
  cases P with
  | zero =>
    change HasSmoothReduction M (0 - 0 : (E.baseChange (AlgebraicClosure ℚ)).toAffine.Point)
    rw [sub_self]
    exact hasSmoothReduction_zero M _
  | some x y h =>
    rw [Affine.Point.map_some]
    have h' := (E.toAffine.baseChange_nonsingular σ.toAlgHom.injective x y).mpr h
    have hlev : A.valuation (σ x - C.x) = A.valuation (x - C.x) := by
      rw [show σ x - C.x = σ (x - C.x) by rw [map_sub, hfix.1]]
      exact valuation_apply_eq hσ _
    by_cases hP : HasSmoothReduction M (Affine.Point.some x y h)
    · apply EllipticNodalInertia.smooth_sub_of_model M _ hm ?_ hP
      by_contra hbad
      have hc := (EllipticNodalReduction.not_hasSmoothReduction_some_iff_of_model M _ hm C h').mp hbad
      change A.valuation (σ x - C.x) < 1 at hc
      rw [hlev] at hc
      exact ((EllipticNodalReduction.not_hasSmoothReduction_some_iff_of_model M _ hm C h).mpr hc) hP
    · have hX := (EllipticNodalReduction.not_hasSmoothReduction_some_iff_of_model M _ hm C h).mp hP
      have hX' : A.valuation (σ x - C.x) < 1 := hlev ▸ hX
      by_cases hsh : A.valuation (equationDefect (E.baseChange (AlgebraicClosure ℚ)) C.x C.y) <
          A.valuation (x - C.x) ^ 2
      · have he : σ (centreSlope C x y) = centreSlope C (σ x) (σ y) := by
          simp only [centreSlope, map_div₀, map_sub, hfix.1, hfix.2]
        have hbr : A.valuation (centreSlope C (σ x) (σ y) - centreSlope C x y) < 1 := by
          rw [← he]
          exact slope_difference_small E A hA M hm C D ha₁ ha₂ hx₀ hσ h.1 hX hsh
        exact (EllipticBranchComparison.sub_of_same_branch_of_model M _ hm C D h' h hX' hX hlev
          (by change A.valuation (equationDefect _ C.x C.y) < A.valuation (σ x - C.x) ^ 2; rwa [hlev]) hbr).1
      · rw [sub_eq_add_neg, Affine.Point.neg_some]
        exact EllipticNodalInertia.critical_pair_smooth_of_model M _ hm C D h'
          ((Affine.nonsingular_neg ..).mpr h) hX' (by
            change A.valuation (σ x - C.x) ^ 2 ≤ A.valuation (equationDefect _ C.x C.y)
            rw [hlev]
            exact not_lt.mp hsh) hX (not_lt.mp hsh)

end DkMath.Lib.NumberTheory.EllipticSplitDyadic
