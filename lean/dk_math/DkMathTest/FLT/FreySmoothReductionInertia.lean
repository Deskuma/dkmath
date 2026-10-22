/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreySmoothReductionInertia
import DkMathTest.FLT.FreyGoodReductionInertia

#print "file: DkMathTest.FLT.FreySmoothReductionInertia"

/-!
# NOTE-031-002C1: 同じ特異な剰余曲線で、滑らかな点と特異点を区別する

曲線y²+xy=x³+4x²+xの判別式は225である。3上の剰余曲線は特異だが、
(0,0)は滑らかで、元の曲線の非零2-torsion点として新定理を適用できる。
一方、前章で重なった二点の剰余点(2,2)は特異であり、今回の仮定から除外される。
曲線全体の良還元を要求しないことと、一点の滑らかさを除けないことを同時に検査する。
-/
namespace FreySmoothReductionInertiaTest
open DkMath.Lib.NumberTheory ValuationInertia ValuationPrimeSupport
open EllipticGoodReductionSeparation EllipticTorsionRepresentation
open WeierstrassCurve IsLocalRing FreyValuationArithmeticTest
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

/-- 同じ剰余曲線は特異であるが、(0,0)は滑らかであり、(2,2)は曲線上の特異点である。 -/
theorem residue_geometry :
    let V := curveInt.map (Int.castRingHom (ZMod 3))
    V.Δ = 0 ∧ V.c₄ ≠ 0 ∧ V.toAffine.Nonsingular 0 0 ∧
      V.toAffine.Equation 2 2 ∧ ¬ V.toAffine.Nonsingular 2 2 := by
  norm_num [curveInt, Δ, c₄, b₂, b₄, b₆, b₈, Affine.nonsingular_iff, Affine.equation_iff]
  decide

/-- 同じ有理曲線の代数閉包上の点(0,0)は非特異である。 -/
theorem origin_nonsingular : (curve.baseChange (AlgebraicClosure ℚ)).toAffine.Nonsingular 0 0 := by
  norm_num [curve, curveInt, baseChange, Affine.nonsingular_iff, Affine.equation_iff]

/-- 実際のE[2]の非零点(0,0)。負号が同じ座標を与えるので2倍零となる。 -/
noncomputable def smoothTorsion : Torsion curve 2 := by
  classical
  refine ⟨Affine.Point.some 0 0 origin_nonsingular, ?_⟩
  change 2 • (Affine.Point.some 0 0 origin_nonsingular : (curve.baseChange (AlgebraicClosure ℚ)).toAffine.Point) = 0
  have hn : -(Affine.Point.some 0 0 origin_nonsingular) = Affine.Point.some 0 0 origin_nonsingular := by
    rw [Affine.Point.neg_some, Affine.Point.some.injEq]
    norm_num [Affine.negY, curve, curveInt, baseChange]
  rw [two_nsmul]
  calc _ = -Affine.Point.some 0 0 origin_nonsingular + Affine.Point.some 0 0 origin_nonsingular :=
      congrArg (fun T => T + Affine.Point.some 0 0 origin_nonsingular) hn.symm
    _ = 0 := neg_add_cancel _

/-- 回帰の点は零でない。空のtorsion群や無限遠点だけの検査ではない。 -/
theorem smoothTorsion_ne_zero : smoothTorsion ≠ 0 := by
  intro he
  exact Affine.Point.some_ne_zero origin_nonsingular (congrArg Subtype.val he)

/-- どの付値環モデルでもこの同じ点の剰余偏微分の一つは−1となり、滑らかである。 -/
theorem smoothTorsion_hasSmoothReduction (A : ValuationSubring (AlgebraicClosure ℚ)) :
    HasSmoothReduction (curveInt.map (Int.castRingHom A)) smoothTorsion.val := by
  rw [smoothTorsion, hasSmoothReduction_some_iff]
  intro hx hy
  have hx0 : (⟨0, hx⟩ : A) = 0 := rfl
  simp [hx0, curveInt, Affine.nonsingular_iff, Affine.equation_iff]

/-- 悪い素数3の全慣性元でも、同じ実際の非零2-torsion点が固定される。
全点の固定をここから主張せず、滑らかな還元を持つ当該点に新定理を適用する。 -/
theorem smooth_fixed_at_bad_three
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 3)
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : σ ∈ inertiaSubgroupIn A ℚ) :
    smoothTorsion ≠ 0 ∧ representation curve 2 σ smoothTorsion = smoothTorsion := by
  refine ⟨smoothTorsion_ne_zero, ?_⟩
  let W := curveInt.map (Int.castRingHom A)
  have hm : W.map A.subtype = curve.baseChange (AlgebraicClosure ℚ) := by
    simp only [W, curve, baseChange, map_map]
    congr 1
  have hn : A.valuation (2 : AlgebraicClosure ℚ) = 1 :=
    valuation_intCast_eq_one_of_not_dvd A (by decide)
      ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := 2) (by norm_num)
  exact EllipticSmoothReductionInertia.fixed_of_inertia_of_smooth_reduction curve 2 A W hm hn σ hσ
    smoothTorsion (smoothTorsion_hasSmoothReduction A)

/-- 前章の衝突点Q=(−4,2)は、3上では滑らかな還元条件を満たさない。
特異点へ落ちる枝を新しい単射性の仮定に紛れ込ませない。 -/
theorem singular_coordinates_excluded
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 3) :
    ¬ SmoothCoordinates (curveInt.map (Int.castRingHom A)) (-4) 2 := by
  have := charP_residueField A (by decide) hA
  intro hs
  have hx : (-4 : AlgebraicClosure ℚ) ∈ A := by simpa only [Int.cast_neg, Int.cast_ofNat] using intCast_mem A (-4)
  have hy : (2 : AlgebraicClosure ℚ) ∈ A := by simpa only [Int.cast_ofNat] using intCast_mem A 2
  have h := hs hx hy
  change (curveInt.map (Int.castRingHom A) |>.map (residue A)).toAffine.Nonsingular
    (residue A (-4)) (residue A 2) at h
  have h3 : (3 : ResidueField A) = 0 := CharP.cast_eq_zero _ 3
  norm_num [curveInt, Affine.nonsingular_iff, Affine.equation_iff] at h
  simp only [map_ofNat] at h
  rcases h.2 with hX | hY
  · apply hX
    linear_combination -5 * h3
  · apply hY
    ring

/-- 同じSource 37の悪い素数3でも、滑らかに還元する同じ残余点は固定される。
hdは悪い素数を指定する。特異点側を含む全点固定の結論には強めない。 -/
theorem source37_bad_smooth_fixed (S : DkMath.FLT.Frey.Source 37) (hd : (3 : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 3)
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : σ ∈ inertiaSubgroupIn A ℚ)
    (P : S.ResidualSpace) (hs : HasSmoothReduction (S.valuationModel A) P.val) :
    A.valuation (S.curve.c₄ : AlgebraicClosure ℚ) = 1 ∧ S.residualRepresentation σ P = P := by
  exact ⟨S.valuation_c4_eq_one (by decide) (by decide) hd A hA,
    S.residual_fixed_of_smooth_reduction (by decide) (by decide) A hA σ hσ P hs⟩

end FreySmoothReductionInertiaTest
