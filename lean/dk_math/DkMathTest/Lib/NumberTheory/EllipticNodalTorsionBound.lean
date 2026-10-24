/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticNodalTorsionBound
import DkMath.Lib.NumberTheory.ValuationPrimeSupport
import DkMath.Lib.NumberTheory.EllipticDyadicGeometry
import DkMath.Lib.NumberTheory.EllipticTorsionRegularFiber

#print "file: DkMathTest.Lib.NumberTheory.EllipticNodalTorsionBound"

/-!
NOTE-032-003Bの境界例。2上で位数2は単元でなく、良還元でも非零の2捩れが還元核へ入る。
明示座標(−1/4,1/8)で、捩れ還元の単射性に必要な単元条件を確認する。
-/
namespace EllipticNodalTorsionBoundTest
open DkMath.Lib.NumberTheory ValuationInertia ValuationPrimeSupport
open EllipticGoodReductionSeparation EllipticSmoothReduction
open WeierstrassCurve
open EllipticCriticalCentre EllipticTangentDirections EllipticTorsionRepresentation
local notation "ℚ̄" => AlgebraicClosure ℚ
noncomputable local instance : DecidableEq ℚ̄ := Classical.decEq _

/-- y²+xy=x³+4x²+xは判別式225を持つ整数モデル。 -/
def poleCurve : WeierstrassCurve ℤ := ⟨1, 4, 0, 1, 0⟩

/-- 判別式は2で単元なので、この例は良還元でも起こる。 -/
theorem poleCurve_discriminant : poleCurve.Δ = 225 := by
  norm_num [poleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- 単元条件を落とすと、非零の滑らかな捩れ点でも零へ還元する。
P=(−1/4,1/8)は−P=Pで、2P=0。x座標は2上で極を持つので零へ還元する。 -/
theorem nonunit_order_boundary (A : ValuationSubring ℚ̄) (hA : LiesOverPrime A 2) :
    let W := poleCurve.map (Int.castRingHom A)
    ∃ P : (W.map A.subtype).toAffine.Point,
      HasSmoothReduction W P ∧ 2 • P = 0 ∧ reducePointSmooth W P = 0 ∧ P ≠ 0 := by
  classical
  let W := poleCurve.map (Int.castRingHom A)
  let E := W.map A.subtype
  have h : E.toAffine.Nonsingular (-1 / 4) (1 / 8) := by
    norm_num [Affine.nonsingular_iff', Affine.equation_iff, E, W, poleCurve, map_ofNat]
  let P := Affine.Point.some (-1 / 4) (1 / 8) h
  have hneg : -P = P := by
    dsimp only [P]
    rw [Affine.Point.neg_some]
    congr 1
    norm_num [Affine.negY, E, W, poleCurve]
  have h2 := (ValuationSubring.mem_nonunits_iff A).mp hA
  have h4 : A.valuation (4 : ℚ̄) < 1 := by
    simpa using valuation_intCast_lt_one_of_dvd A h2 (z := 4) (by norm_num)
  have hx : (-1 / 4 : ℚ̄) ∉ A := by
    intro hx
    have hsmall : A.valuation ((4 : ℚ̄) * (-1 / 4)) < 1 := by
      rw [map_mul]
      exact (mul_le_of_le_one_right' ((A.valuation_le_one_iff _).mpr hx)).trans_lt h4
    norm_num at hsmall
  refine ⟨P, hasSmoothReduction_of_notMem W h hx, ?_, reducePointSmooth_some_of_notMem W h hx, ?_⟩
  · rw [two_nsmul]
    simpa only [hneg] using neg_add_cancel P
  · exact Affine.Point.some_ne_zero h


/-- 2上で節点還元する実際の整数曲線。Frey Sourceの存在を仮定しない。 -/
def nodalCurve : WeierstrassCurve ℤ := ⟨1, 1, 0, 2, 0⟩

/-- 判別式とc₄の値は整数環でkernel検証する。 -/
theorem nodalCurve_invariants : nodalCurve.Δ = -412 ∧ nodalCurve.c₄ = -71 := by
  norm_num [nodalCurve, WeierstrassCurve.Δ, WeierstrassCurve.c₄, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- 実際の楕円曲線の3捩れ9個と、滑らかな還元の上界3を比較して外側の点を構成する。
中心・方向・零成分外の点の存在は追加入力に置かない。 -/
theorem nodalCurve_exists_outside_three (A : ValuationSubring ℚ̄) (hA : LiesOverPrime A 2) :
    let W := nodalCurve.map (Int.castRingHom A)
    let E := nodalCurve.map (Int.castRingHom ℚ)
    ∃ P : Torsion E 3, ¬ HasSmoothReduction W P.val := by
  classical
  let W := nodalCurve.map (Int.castRingHom A)
  let E := nodalCurve.map (Int.castRingHom ℚ)
  let V := E.baseChange ℚ̄
  change ∃ P : Torsion E 3, ¬ HasSmoothReduction W P.val
  have hm : W.map A.subtype = V := by
    ext <;> simp [W, V, E, WeierstrassCurve.baseChange, nodalCurve, map_ofNat]
  have hΔ : V.Δ = (-412 : ℚ̄) := by
    simp [V, E, WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ, nodalCurve_invariants.1]
  have hc : V.c₄ = (-71 : ℚ̄) := by
    simp [V, E, WeierstrassCurve.baseChange, WeierstrassCurve.map_c₄, nodalCurve_invariants.2]
  have : E.IsElliptic := ⟨by
    rw [isUnit_iff_ne_zero]
    simp [E, WeierstrassCurve.map_Δ, nodalCurve_invariants.1]⟩
  have h2 := (ValuationSubring.mem_nonunits_iff A).mp hA
  have hΔsmall : A.valuation V.Δ < 1 := by
    rw [hΔ]
    simpa using valuation_intCast_lt_one_of_dvd A h2 (z := -412) (by norm_num)
  have hcunit : A.valuation V.c₄ = 1 := by
    rw [hc]
    simpa using valuation_intCast_eq_one_of_not_dvd A Nat.prime_two h2 (z := -71) (by norm_num)
  obtain ⟨C⟩ := EllipticCriticalCentre.exists_criticalCentre A V
    (by rw [← hm, WeierstrassCurve.map_a₁]; exact W.a₁.property)
    (by rw [← hm, WeierstrassCurve.map_a₂]; exact W.a₂.property)
    (by rw [← hm, WeierstrassCurve.map_a₃]; exact W.a₃.property)
    (by rw [← hm, WeierstrassCurve.map_a₄]; exact W.a₄.property)
    (by rw [← hm, WeierstrassCurve.map_a₆]; exact W.a₆.property)
    (by rw [hΔ]; norm_num) hΔsmall hcunit
  obtain ⟨D⟩ := EllipticDyadicGeometry.exists_tangentDirections A V C
    (by rw [← hm, WeierstrassCurve.map_a₁]; exact W.a₁.property)
    (by rw [← hm, WeierstrassCurve.map_a₂]; exact W.a₂.property)
  have h3 : A.valuation (3 : ℚ̄) = 1 := by
    simpa using valuation_intCast_eq_one_of_not_dvd A Nat.prime_two h2 (z := 3) (by norm_num)
  by_contra! hall
  have hbound : Nat.card (Torsion E 3) ≤ 3 :=
    EllipticNodalTorsionBound.card_le_of_injective_smooth_torsion W V hm C D (by decide) h3
      (fun P : Torsion E 3 => P.val) Subtype.val_injective hall (fun P => P.property)
  rw [card_torsion_prime_sq E 3] at hbound
  norm_num at hbound

end EllipticNodalTorsionBoundTest
