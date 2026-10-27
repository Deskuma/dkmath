/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFiniteKernelNodalAll
import DkMath.Lib.NumberTheory.EllipticFiniteKernelReducedHom

#print "file: DkMath.FLT.FreyFiniteKernelReducedHom"

/-!
# 同じSourceの還元像上の商準同型

同じ一次元Lが零成分に入る側で、同じ実際の商準同型を源の実際の還元像へ降ろす。
その可換性は同じ付値環標的で成立する。源のFrameと方向分離を保持する。
剰余点群全体への持上げ、明示的な冪写像との一致と逆像判定は別に残る。
-/
namespace DkMath.FLT.Frey.Source
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open EllipticGoodReductionSeparation EllipticSmoothReduction
open ValuationInertia ValuationPrimeSupport ValuationRationalPrimeSupport
open DkMath.Lib.RepresentationTheory EllipticNodalTorsion.NodalTorsion
noncomputable local instance instDecidableEqFreyFiniteKernelReducedHom {α : Type*} : DecidableEq α :=
  Classical.decEq _
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 同じSource・L・源モデルの実際の還元像上に、同じ商標的の剰余点群への準同型を構成する。
源の全剰余点の持上げは要求しない。 -/
noncomputable def residualNodalReducedHom (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hle : L ≤ S.residualZeroComponent A) {x₀ y₀ α : ResidueField A}
    (F : Frame ((S.valuationModel A).map (residue A)) x₀ y₀ α)
    (hsep : α ≠ -((S.valuationModel A).map (residue A)).a₁ - α) :
    (zeroComponentReduction (S.valuationModel A)).range →+
      ((S.residualValuationKernelModel L hl hq hqp A hA).map (residue A)).toAffine.Point := by
  let := S.finite_residualPointSubgroup L hl
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  have hunit : A.valuation (p : AlgebraicClosure ℚ) = 1 := by
    simpa only [pow_one] using prime_power_value_one A (Fact.out : p.Prime) hq
      ((ValuationSubring.mem_nonunits_iff _).mp hA) hqp 1
  exact nodalReducedHom S.rationalCurve (pointSubgroup S.rationalCurve p L) p
    (card_pointSubgroup S.rationalCurve p L hl) hp2 (S.residual_kernel_killed L) A
    (S.valuationModel A) (S.valuationModel_map A) hunit (S.residual_kernel_smooth_of_le L A hle) F hsep

/-- 同じSourceの任意の零成分点で、実際の商準同型と実際の還元が可換となる。
左の還元像の代表と右の商標的は、同じL・同じ付値環モデルを使用する。 -/
theorem residualNodalReducedHom_commutes (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hle : L ≤ S.residualZeroComponent A) {x₀ y₀ α : ResidueField A}
    (F : Frame ((S.valuationModel A).map (residue A)) x₀ y₀ α)
    (hsep : α ≠ -((S.valuationModel A).map (residue A)).a₁ - α)
    (P : zeroComponentSubgroup (S.valuationModel A)) :
    S.residualNodalReducedHom hp2 L hl hq hqp A hA hle F hsep
        ⟨zeroComponentReduction (S.valuationModel A) P, ⟨P, rfl⟩⟩ =
      letI := S.finite_residualPointSubgroup L hl
      letI := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
      let hn : A.valuation (p : AlgebraicClosure ℚ) = 1 := by
        simpa only [pow_one] using prime_power_value_one A (Fact.out : p.Prime) hq
          ((ValuationSubring.mem_nonunits_iff _).mp hA) hqp 1
      zeroComponentReduction (S.residualValuationKernelModel L hl hq hqp A hA)
        (nodalZeroComponentHom S.rationalCurve (pointSubgroup S.rationalCurve p L) p
          (card_pointSubgroup S.rationalCurve p L hl) hp2 (S.residual_kernel_killed L) A
          (S.valuationModel A) (S.valuationModel_map A) hn (S.residual_kernel_smooth_of_le L A hle) F hsep P) := by
  let := S.finite_residualPointSubgroup L hl
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  have hn : A.valuation (p : AlgebraicClosure ℚ) = 1 := by
    simpa only [pow_one] using prime_power_value_one A (Fact.out : p.Prime) hq
      ((ValuationSubring.mem_nonunits_iff _).mp hA) hqp 1
  exact nodalReducedHom_commutes S.rationalCurve (pointSubgroup S.rationalCurve p L) p
    (card_pointSubgroup S.rationalCurve p L hl) hp2 (S.residual_kernel_killed L) A
    (S.valuationModel A) (S.valuationModel_map A) hn (S.residual_kernel_smooth_of_le L A hle) F hsep P

/-- 同じSourceの可換図式を、元の実点商準同型と同じ付値環モデルでの還元で表示する。
零成分制限を構成する内部の中心選択は右辺に現れない。 -/
theorem residualNodalReducedHom_commutes_model (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hle : L ≤ S.residualZeroComponent A) {x₀ y₀ α : ResidueField A}
    (F : Frame ((S.valuationModel A).map (residue A)) x₀ y₀ α)
    (hsep : α ≠ -((S.valuationModel A).map (residue A)).a₁ - α)
    (P : zeroComponentSubgroup (S.valuationModel A)) :
    S.residualNodalReducedHom hp2 L hl hq hqp A hA hle F hsep
        ⟨zeroComponentReduction (S.valuationModel A) P, ⟨P, rfl⟩⟩ =
      WeierstrassModelReduction.modelReduce A (S.residualValuationKernelModel L hl hq hqp A hA)
        (S.residualKernelModel L hl) (S.residual_valuation_kernel_model_map hp2 L hl hq hqp A hA)
        (S.residualOddKernelPointHom hp2 L hl (WeierstrassVariableChange.pointEquivOfModelEq
          (S.valuationModel_map A) P.val)) := by
  let := S.finite_residualPointSubgroup L hl
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  have hn : A.valuation (p : AlgebraicClosure ℚ) = 1 := by
    simpa only [pow_one] using prime_power_value_one A (Fact.out : p.Prime) hq
      ((ValuationSubring.mem_nonunits_iff _).mp hA) hqp 1
  exact nodalReducedHom_commutes_model S.rationalCurve (pointSubgroup S.rationalCurve p L) p
    (card_pointSubgroup S.rationalCurve p L hl) hp2 (S.residual_kernel_killed L) A
    (S.valuationModel A) (S.valuationModel_map A) hn (S.residual_kernel_smooth_of_le L A hle) F hsep P

/-- 悪い住所q≠pの滑らかな核側で、同じSourceの実際の還元像上の準同型を内部構成する。
2進・奇素数の源Frameと方向分離を内部供給し、全零成分点に対する同じ実点商写像との可換図式を得る。
定義域は源の実際の還元像であり、全剰余点の持上げは結論しない。 -/
theorem exists_residualNodalReducedHom_at_bad_place (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    {q : ℕ} [Fact q.Prime] (hqp : q ≠ p) (hbad : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hle : L ≤ S.residualZeroComponent A) :
    ∃ ψ : (zeroComponentReduction (S.valuationModel A)).range →+
        ((S.residualValuationKernelModel L hl Fact.out hqp A hA).map (residue A)).toAffine.Point,
      ∀ P : zeroComponentSubgroup (S.valuationModel A),
        ψ ⟨zeroComponentReduction (S.valuationModel A) P, ⟨P, rfl⟩⟩ =
          WeierstrassModelReduction.modelReduce A (S.residualValuationKernelModel L hl Fact.out hqp A hA)
            (S.residualKernelModel L hl) (S.residual_valuation_kernel_model_map (by omega) L hl Fact.out hqp A hA)
            (S.residualOddKernelPointHom (by omega) L hl (WeierstrassVariableChange.pointEquivOfModelEq
              (S.valuationModel_map A) P.val)) := by
  by_cases hq2 : q = 2
  · subst q
    obtain ⟨C, D, -, -⟩ := S.exists_dyadic_geometry hp5 A hA
    obtain ⟨F, hsep⟩ := WeierstrassNodalFrame.residue_frame_of_model A (S.valuationModel A) _
      (S.valuationModel_map A) C D
    refine ⟨S.residualNodalReducedHom (by omega) L hl Fact.out hqp A hA hle F hsep, ?_⟩
    intro P
    exact S.residualNodalReducedHom_commutes_model (by omega) L hl Fact.out hqp A hA hle F hsep P
  · obtain ⟨C, D, -, -⟩ := S.exists_criticalCentre_directions_at_bad_prime
      (Fact.out : p.Prime).pos hq2 (hbad.resolve_left hq2) A hA
    obtain ⟨F, hsep⟩ := WeierstrassNodalFrame.residue_frame_of_model A (S.valuationModel A) _
      (S.valuationModel_map A) C D
    refine ⟨S.residualNodalReducedHom (by omega) L hl Fact.out hqp A hA hle F hsep, ?_⟩
    intro P
    exact S.residualNodalReducedHom_commutes_model (by omega) L hl Fact.out hqp A hA hle F hsep P

end DkMath.FLT.Frey.Source
