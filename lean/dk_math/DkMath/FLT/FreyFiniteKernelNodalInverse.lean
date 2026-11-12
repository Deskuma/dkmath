/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFiniteKernelNodalAll
import DkMath.Lib.NumberTheory.EllipticFiniteKernelNodalInverse

#print "file: DkMath.FLT.FreyFiniteKernelNodalInverse"

/-!
# Frey の滑らかな核側における零成分の逆像

同じ Source、一次元核、付値環モデルと実点商準同型を保つ。
悪い素点の源中心・接方向を内部供給して零成分所属の必要十分条件を得る。
特異核側では非零核点そのものが逆方向の反例となる。
-/
namespace DkMath.FLT.Frey.Source
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open EllipticGoodReductionSeparation WeierstrassRationalIntegralModel
open ValuationInertia ValuationPrimeSupport ValuationRationalPrimeSupport
open DkMath.Lib.RepresentationTheory
noncomputable local instance {α : Type*} : DecidableEq α := Classical.decEq _
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 悪い住所の滑らかな核側では、同じ商像が零成分に入ることは源点が零成分に入ることと同値。
2・3を含み、源の中心と接方向を内部供給する。 -/
theorem residual_pointHom_smooth_iff_at_bad_place_of_le (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    {q : ℕ} [Fact q.Prime] (hqp : q ≠ p) (hbad : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hle : L ≤ S.residualZeroComponent A) (P : Points S.rationalCurve) :
    HasSmoothReduction (S.residualValuationKernelModel L hl Fact.out hqp A hA)
      (S.residualOddKernelPointHom (by omega) L hl P) ↔
      HasSmoothReduction (S.valuationModel A) P := by
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
    exact oddKernelPointMap_smooth_iff S.rationalCurve (pointSubgroup S.rationalCurve p L) p
      (card_pointSubgroup S.rationalCurve p L hl) (by omega) (S.residual_kernel_killed L) A
      (S.valuationModel A) (S.valuationModel_map A) hunit (S.residual_kernel_smooth_of_le L A hle)
      C F hsep rfl P
  · obtain ⟨C, D, -, -⟩ := S.exists_criticalCentre_directions_at_bad_prime
      (Fact.out : p.Prime).pos hq2 (hbad.resolve_left hq2) A hA
    obtain ⟨F, hsep⟩ := WeierstrassNodalFrame.residue_frame_of_model A (S.valuationModel A) _
      (S.valuationModel_map A) C D
    exact oddKernelPointMap_smooth_iff S.rationalCurve (pointSubgroup S.rationalCurve p L) p
      (card_pointSubgroup S.rationalCurve p L hl) (by omega) (S.residual_kernel_killed L) A
      (S.valuationModel A) (S.valuationModel_map A) hunit (S.residual_kernel_smooth_of_le L A hle)
      C F hsep rfl P

/-- 安定な同じ核 L の既存整数標的でも、滑らかな核側の零成分所属は同値。
既存の整数化点同型と p 以外での単元性を使い、標的や点を選び直さない。 -/
theorem residual_integer_pointHom_smooth_iff_at_bad_place_of_le (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    (hst : IsStable S.residualRepresentation L) {q : ℕ} [Fact q.Prime]
    (hqp : q ≠ p) (hbad : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hle : L ≤ S.residualZeroComponent A) (P : Points S.rationalCurve) :
    HasSmoothReduction (integerValuationModel A (S.residualIntegerKernelModel L hl hst))
      (S.residualIntegerKernelPointHom (by omega) L hl hst P) ↔
      HasSmoothReduction (S.valuationModel A) P :=
  (S.residual_integer_pointHom_smooth_iff (by omega) L hl hst Fact.out hqp A hA P).trans
    (S.residual_pointHom_smooth_iff_at_bad_place_of_le hp5 L hl hqp hbad A hA hle P)

/-- 特異核側の非零核点は、零成分の逆像判定の反例である。
その実点は特異に還元するが、同じ商で O に送られる。 -/
theorem residual_disjoint_kernel_counterexample (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hd : Disjoint L (S.residualZeroComponent A))
    (Q : pointSubgroup S.rationalCurve p L) (hQ : Q.val ≠ 0) :
    HasSmoothReduction (S.residualValuationKernelModel L hl hq hqp A hA)
      (S.residualOddKernelPointHom hp2 L hl Q.val) ∧
      ¬ HasSmoothReduction (S.valuationModel A) Q.val := by
  let := S.finite_residualPointSubgroup L hl
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  have hunit : A.valuation (p : AlgebraicClosure ℚ) = 1 := by
    simpa only [pow_one] using prime_power_value_one A (Fact.out : p.Prime) hq
      ((ValuationSubring.mem_nonunits_iff _).mp hA) hqp 1
  exact nonsmooth_kernel_point_counterexample S.rationalCurve (pointSubgroup S.rationalCurve p L) p
    (S.residual_kernel_killed L) A (S.valuationModel A) (S.valuationModel_map A) hunit
    (S.residual_pointSubgroup_odd hp2 L hl) Q (S.residual_kernel_not_smooth_of_disjoint L A hd Q hQ)

/-- 一次元の特異核は実際に非零点を持つので、逆像同値の反例が存在する。
位数 p の核を同じ L から供給し、その非零点を取り直す。 -/
theorem exists_residual_disjoint_counterexample (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hd : Disjoint L (S.residualZeroComponent A)) :
    ∃ P : Points S.rationalCurve,
      HasSmoothReduction (S.residualValuationKernelModel L hl hq hqp A hA)
        (S.residualOddKernelPointHom hp2 L hl P) ∧ ¬ HasSmoothReduction (S.valuationModel A) P := by
  let := S.finite_residualPointSubgroup L hl
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  let : Nontrivial (pointSubgroup S.rationalCurve p L) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [card_pointSubgroup S.rationalCurve p L hl]
    exact (Fact.out : p.Prime).one_lt)
  obtain ⟨Q, hQ⟩ := exists_ne (0 : pointSubgroup S.rationalCurve p L)
  have hQ' : Q.val ≠ 0 := fun h => hQ (Subtype.ext h)
  exact ⟨Q.val, S.residual_disjoint_kernel_counterexample hp2 L hl hq hqp A hA hd Q hQ'⟩

end DkMath.FLT.Frey.Source
