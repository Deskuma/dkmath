/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFiniteKernelNodalTransport
import DkMath.FLT.FreyFiniteKernelNodalReduction
import DkMath.Lib.NumberTheory.EllipticFiniteKernelNodalCenterAll

#print "file: DkMath.FLT.FreyFiniteKernelNodalAll"

/-!
# 2・3を含む悪い住所の全零成分輸送

同じSource・一次元L・同じ実核を保ち、同じ商準同型の全零成分像を標的へ送る。
源・標的の節点中心と接方向を内部供給し、滑らかな核と特異核の分岐を統合する。
p≥5、q≠p、悪い住所、源の滑らかさを保持する。
-/
namespace DkMath.FLT.Frey.Source
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open EllipticGoodReductionSeparation WeierstrassRationalIntegralModel
open ValuationInertia ValuationPrimeSupport ValuationRationalPrimeSupport
open DkMath.Lib.RepresentationTheory EllipticNodalTorsion.NodalTorsion
noncomputable local instance instDecidableEqFreyFiniteKernelNodalAll {α : Type*} : DecidableEq α :=
  Classical.decEq _
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 源のFrameと標的中心が与えられた同じ滑らかな核側で、任意標数の全零成分を輸送する。 -/
theorem residual_pointHom_smooth_of_nodal_all (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hle : L ≤ S.residualZeroComponent A) {x₀ y₀ α : IsLocalRing.ResidueField A}
    (F : Frame ((S.valuationModel A).map (IsLocalRing.residue A)) x₀ y₀ α)
    (hsep : α ≠ -((S.valuationModel A).map (IsLocalRing.residue A)).a₁ - α)
    (C : EllipticCriticalCentre.CriticalCentre A (S.residualKernelModel L hl))
    (P : Points S.rationalCurve) (hP : HasSmoothReduction (S.valuationModel A) P) :
    HasSmoothReduction (S.residualValuationKernelModel L hl hq hqp A hA)
      (S.residualOddKernelPointHom hp2 L hl P) := by
  let := S.finite_residualPointSubgroup L hl
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  have hunit : A.valuation (p : AlgebraicClosure ℚ) = 1 := by
    simpa only [pow_one] using prime_power_value_one A (Fact.out : p.Prime) hq
      ((ValuationSubring.mem_nonunits_iff _).mp hA) hqp 1
  exact oddKernelPointMap_smooth_of_nodal_all S.rationalCurve _ p
    (card_pointSubgroup S.rationalCurve p L hl) hp2 (S.residual_kernel_killed L) A
    (S.valuationModel A) (S.valuationModel_map A) hunit (S.residual_kernel_smooth_of_le L A hle)
    F hsep C P hP

/-- p≥5で2を含む悪い住所q≠pの滑らかな核側から、同じ付値環商標的へ全零成分を送る。
源・標的の中心と接方向を内部供給する。L≤E₀[p]と源点の滑らかさを保持する。 -/
theorem residual_pointHom_smooth_at_bad_place_of_le (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    {q : ℕ} [Fact q.Prime] (hqp : q ≠ p) (hbad : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hle : L ≤ S.residualZeroComponent A) (P : Points S.rationalCurve)
    (hP : HasSmoothReduction (S.valuationModel A) P) :
    HasSmoothReduction (S.residualValuationKernelModel L hl Fact.out hqp A hA)
      (S.residualOddKernelPointHom (by omega) L hl P) := by
  let := S.finite_residualPointSubgroup L hl
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  have hunit : A.valuation (p : AlgebraicClosure ℚ) = 1 := by
    simpa only [pow_one] using prime_power_value_one A (Fact.out : p.Prime) Fact.out
      ((ValuationSubring.mem_nonunits_iff _).mp hA) hqp 1
  by_cases hq2 : q = 2
  · subst q
    obtain ⟨C, D, -, -⟩ := S.exists_dyadic_geometry hp5 A hA
    obtain ⟨F, hsep⟩ := WeierstrassNodalFrame.residue_frame_of_model A (S.valuationModel A) _
      (S.valuationModel_map A) C D
    obtain ⟨T⟩ := exists_nodal_kernel_criticalCentre S.rationalCurve (pointSubgroup S.rationalCurve p L) p
      (card_pointSubgroup S.rationalCurve p L hl) (by omega) (S.residual_kernel_killed L) A
      (S.valuationModel A) (S.valuationModel_map A) hunit (S.residual_kernel_smooth_of_le L A hle) F hsep
    exact S.residual_pointHom_smooth_of_nodal_all (by omega) L hl Fact.out hqp A hA hle F hsep T P hP
  · obtain ⟨C, D, -, -⟩ := S.exists_criticalCentre_directions_at_bad_prime
      (Fact.out : p.Prime).pos hq2 (hbad.resolve_left hq2) A hA
    obtain ⟨F, hsep⟩ := WeierstrassNodalFrame.residue_frame_of_model A (S.valuationModel A) _
      (S.valuationModel_map A) C D
    obtain ⟨T⟩ := exists_nodal_kernel_criticalCentre S.rationalCurve (pointSubgroup S.rationalCurve p L) p
      (card_pointSubgroup S.rationalCurve p L hl) (by omega) (S.residual_kernel_killed L) A
      (S.valuationModel A) (S.valuationModel_map A) hunit (S.residual_kernel_smooth_of_le L A hle) F hsep
    exact S.residual_pointHom_smooth_of_nodal_all (by omega) L hl Fact.out hqp A hA hle F hsep T P hP

/-- 2・3を含む悪い住所q≠pで、同じ一次元Lの局所核の分岐に依らない全零成分輸送。 -/
theorem residual_pointHom_smooth_at_bad_place (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    {q : ℕ} [Fact q.Prime] (hqp : q ≠ p) (hbad : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (P : Points S.rationalCurve) (hP : HasSmoothReduction (S.valuationModel A) P) :
    HasSmoothReduction (S.residualValuationKernelModel L hl Fact.out hqp A hA)
      (S.residualOddKernelPointHom (by omega) L hl P) := by
  rcases S.residual_line_smooth_or_disjoint L hl A with hle | hd
  · exact S.residual_pointHom_smooth_at_bad_place_of_le hp5 L hl hqp hbad A hA hle P hP
  · by_cases hq2 : q = 2
    · subst q
      exact S.residual_pointHom_smooth_at_two_of_disjoint hp5 L hl A hA hd P hP
    · exact S.residual_pointHom_smooth_at_bad_prime_of_disjoint (by omega) L hl hq2 hqp
        (hbad.resolve_left hq2) A hA hd P hP

/-- 同じ安定Lの既存整数標的への、2・3を含む全零成分輸送。 -/
theorem residual_integer_pointHom_smooth_at_bad_place (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    (hst : IsStable S.residualRepresentation L) {q : ℕ} [Fact q.Prime]
    (hqp : q ≠ p) (hbad : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (P : Points S.rationalCurve) (hP : HasSmoothReduction (S.valuationModel A) P) :
    HasSmoothReduction (integerValuationModel A (S.residualIntegerKernelModel L hl hst))
      (S.residualIntegerKernelPointHom (by omega) L hl hst P) :=
  (S.residual_integer_pointHom_smooth_iff (by omega) L hl hst Fact.out hqp A hA P).mpr
    (S.residual_pointHom_smooth_at_bad_place hp5 L hl hqp hbad A hA P hP)

end DkMath.FLT.Frey.Source
