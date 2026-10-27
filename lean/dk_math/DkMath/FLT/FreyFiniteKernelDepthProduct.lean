/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/
import DkMath.FLT.FreyFiniteKernelSingularInverse
import DkMath.Lib.NumberTheory.EllipticFiniteKernelDepthProduct

#print "file: DkMath.FLT.FreyFiniteKernelDepthProduct"

/-!
# 同じ Frey 商の判別式深さ：一般積公式を入力とする接続

同じ Source と一次元核 L の特異核側では、源の節点中心と二方向を悪い住所から
内部供給する。Vélu の一般判別式積公式は明示的な仮定であり、この章では証明しない。
-/
namespace DkMath.FLT.Frey.Source
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open EllipticGoodReductionSeparation ValuationInertia ValuationPrimeSupport ValuationRationalPrimeSupport
open DkMath.Lib.RepresentationTheory
noncomputable local instance instDecidableEqFreyFiniteKernelDepthProduct {α : Type*} : DecidableEq α := Classical.decEq _
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 同じ Frey Source と同じ L の特異核側で、一般判別式積公式から源と商の付値関係を得る。
源の節点中心と二方向は q=2 を含む悪い住所から構成し、積公式の仮定は隠さない。 -/
theorem residual_singular_discriminant_value_of_product_identity (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    {q : ℕ} [Fact q.Prime] (hqp : q ≠ p) (hbad : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hd : Disjoint L (S.residualZeroComponent A))
    (hprod :
      letI := S.finite_residualPointSubgroup L hl
      letI := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
      (S.residualKernelModel L hl).Δ *
        (∏ Q : halfKernel S.rationalCurve (pointSubgroup S.rationalCurve p L),
          (2 * Q.val.val.yc + (S.rationalCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).a₁ * Q.val.val.xc +
            (S.rationalCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).a₃) ^ 2) ^ 4 =
        (S.rationalCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).Δ ^ p) :
    A.valuation (S.residualKernelModel L hl).Δ ^ p =
      A.valuation (S.rationalCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).Δ := by
  let := S.finite_residualPointSubgroup L hl
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  have hp : A.valuation (p : AlgebraicClosure ℚ) = 1 := by
    simpa only [pow_one] using prime_power_value_one A (Fact.out : p.Prime) Fact.out
      ((ValuationSubring.mem_nonunits_iff _).mp hA) hqp 1
  by_cases hq2 : q = 2
  · subst q
    obtain ⟨C, D, -, -⟩ := S.exists_dyadic_geometry hp5 A hA
    exact singular_discriminant_value_of_product_identity S.rationalCurve (pointSubgroup S.rationalCurve p L) p
      (card_pointSubgroup S.rationalCurve p L hl) (by omega) (S.residual_kernel_killed L) A
      (S.valuationModel A) (S.valuationModel_map A) hp C D
      (S.residual_kernel_not_smooth_of_disjoint L A hd) hprod
  · obtain ⟨C, D, -, -⟩ := S.exists_criticalCentre_directions_at_bad_prime
      (Fact.out : p.Prime).pos hq2 (hbad.resolve_left hq2) A hA
    exact singular_discriminant_value_of_product_identity S.rationalCurve (pointSubgroup S.rationalCurve p L) p
      (card_pointSubgroup S.rationalCurve p L hl) (by omega) (S.residual_kernel_killed L) A
      (S.valuationModel A) (S.valuationModel_map A) hp C D
      (S.residual_kernel_not_smooth_of_disjoint L A hd) hprod

/-- 同じ Frey Source と同じ L の滑らかな核側で、一般判別式積公式から商の付値は源の p 乗。
源の還元型は要求しない。積公式の成立は別の仮定である。 -/
theorem residual_smooth_discriminant_value_of_product_identity (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hle : L ≤ S.residualZeroComponent A)
    (hprod :
      letI := S.finite_residualPointSubgroup L hl
      letI := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
      (S.residualKernelModel L hl).Δ *
        (∏ Q : halfKernel S.rationalCurve (pointSubgroup S.rationalCurve p L),
          (2 * Q.val.val.yc + (S.rationalCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).a₁ * Q.val.val.xc +
            (S.rationalCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).a₃) ^ 2) ^ 4 =
        (S.rationalCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).Δ ^ p) :
    A.valuation (S.residualKernelModel L hl).Δ =
      A.valuation (S.rationalCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).Δ ^ p := by
  let := S.finite_residualPointSubgroup L hl
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  have hp : A.valuation (p : AlgebraicClosure ℚ) = 1 := by
    simpa only [pow_one] using prime_power_value_one A (Fact.out : p.Prime) hq
      ((ValuationSubring.mem_nonunits_iff _).mp hA) hqp 1
  have hc := card_pointSubgroup S.rationalCurve p L hl
  change (kernelModel S.rationalCurve (pointSubgroup S.rationalCurve p L)).Δ *
    (∏ Q : halfKernel S.rationalCurve (pointSubgroup S.rationalCurve p L),
      (2 * Q.val.val.yc + (S.rationalCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).a₁ * Q.val.val.xc +
        (S.rationalCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).a₃) ^ 2) ^ 4 =
    (S.rationalCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).Δ ^ p at hprod
  change A.valuation (kernelModel S.rationalCurve (pointSubgroup S.rationalCurve p L)).Δ = _
  have he := smooth_discriminant_value_of_product_identity S.rationalCurve (pointSubgroup S.rationalCurve p L)
    p (S.residual_kernel_killed L) A (S.valuationModel A) (S.valuationModel_map A) hp
    (S.residual_pointSubgroup_odd hp2 L hl) (S.residual_kernel_smooth_of_le L A hle) (by simpa only [hc] using hprod)
  simpa only [hc] using he

end DkMath.FLT.Frey.Source
