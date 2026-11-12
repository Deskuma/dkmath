/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidualRepresentation
import DkMath.Lib.NumberTheory.ValuationPrimeSupport
import DkMath.Lib.NumberTheory.EllipticTorsionValuationIntegrality

#print "file: DkMath.FLT.FreyValuationArithmetic"

/-!
# NOTE-031-002A: 同じFrey Sourceを絶対ガロア群の付値環から観測する

整数モデルを任意のq上の付値環Aへ写し、同じ有理曲線の代数閉包上のモデルと一致させる。
q≠2では整数判別式の指数2pをそのままAの値群へ輸送できる。
abcを割らない場合の剰余曲線の非特異性と、割る場合のc₄の単元性も供給する。
さらにp≠qを使い、実際のp-torsion点の両座標がAに入ることを証明する。

慣性元はこれらの座標を剰余体で固定するが、合同から元の点の固定はまだ結論しない。
良還元の還元写像とその核、乗法的還元の零成分に関する幾何学が次の接続である。
Sourceの共通因子・向き付け・曲線・点は変更しない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory ValuationInertia ValuationPrimeSupport
open GNFreyDiscriminant FreyPrimeValuation WeierstrassCurve
noncomputable local instance instDecidableEqFreyValuationArithmetic :
    DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _
variable {p : ℕ} (S : Source p)

/-- 同じ整係数モデルをAへ写す。局所座標変換やSourceの選び直しは行わない。 -/
noncomputable def valuationModel (A : ValuationSubring (AlgebraicClosure ℚ)) : WeierstrassCurve A :=
  S.curve.map (Int.castRingHom A)

/-- 付値環モデルの一般ファイバーは、同じ有理曲線の元の基底変換と一致する。 -/
theorem valuationModel_map (A : ValuationSubring (AlgebraicClosure ℚ)) :
    (S.valuationModel A).map A.subtype = S.rationalCurve.baseChange (AlgebraicClosure ℚ) := by
  rw [valuationModel, ← S.curve_map, baseChange, map_map, map_map]
  congr 1

/-- 整数判別式は非零である。padicValIntの零デフォルトを排除する実際の証拠。 -/
theorem curve_discriminant_ne_zero : S.curve.Δ ≠ 0 := by
  have hd := integral_discriminant_of_solution S.normalization S.equation
  change 256 * S.curve.Δ = (S.a * S.b * S.c) ^ (2 * p) at hd
  intro hz
  rw [hz, mul_zero] at hd
  exact pow_ne_zero _ S.product_ne_zero hd.symm

/-- q≠2で、整数判別式の指数2pをAの実際の値群へ輸送する。
Aの付値を整数の正規化付値へ同一視しない。q=pでも算術等式は有効である。 -/
theorem valuation_discriminant_eq {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q) :
    A.valuation (S.curve.Δ : AlgebraicClosure ℚ) =
      A.valuation (q : AlgebraicClosure ℚ) ^ (2 * p * padicValInt q (S.a * S.b * S.c)) := by
  rw [valuation_intCast_eq_pow_padicValInt A Fact.out
    ((ValuationSubring.mem_nonunits_iff _).mp hA) S.curve_discriminant_ne_zero]
  rw [show padicValInt q S.curve.Δ = 2 * p * padicValInt q (S.a * S.b * S.c) from
    integral_valuation_of_solution hq2 S.normalization S.equation S.product_ne_zero]

/-- 同じ判別式の付値は実際にp乗となる。ただしこれだけで慣性作用の自明性とはしない。 -/
theorem valuation_discriminant_pth_power {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q) :
    A.valuation (S.curve.Δ : AlgebraicClosure ℚ) =
      (A.valuation (q : AlgebraicClosure ℚ) ^ (2 * padicValInt q (S.a * S.b * S.c))) ^ p := by
  rw [S.valuation_discriminant_eq hq2 A hA, ← pow_mul]
  congr 1
  ring

/-- abcを割る奇素数では、同じ整数モデルのc₄はAの単元付値1となる。 -/
theorem valuation_c4_eq_one (hp : 0 < p) {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2)
    (hd : (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q) :
    A.valuation (S.curve.c₄ : AlgebraicClosure ℚ) = 1 :=
  valuation_intCast_eq_one_of_not_dvd A Fact.out ((ValuationSubring.mem_nonunits_iff _).mp hA)
    (S.local_arithmetic hp hq2 hd).2.1

/-- abcを割らない奇素数の全付値環で、同じモデルの剰余曲線は楕円曲線となる。
点の還元写像の構成・単射性まではこの係数の定理に含めない。 -/
theorem valuation_reduction_isElliptic (hp : 0 < p) {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2)
    (hd : ¬ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q) :
    ((S.valuationModel A).map (IsLocalRing.residue A)).IsElliptic := by
  have hv : A.valuation (S.curve.Δ : AlgebraicClosure ℚ) = 1 :=
    valuation_intCast_eq_one_of_not_dvd A Fact.out ((ValuationSubring.mem_nonunits_iff _).mp hA)
      (fun h => hd ((prime_dvd_integral_discriminant_iff hp hq2
        S.normalization S.equation).mp h))
  constructor
  rw [isUnit_iff_ne_zero, map_Δ]
  intro hz
  have hm := (IsLocalRing.residue_eq_zero_iff _).mp hz
  have hlt := (ValuationSubring.mem_nonunits_iff A).mp (ValuationSubring.coe_mem_nonunits_iff.mpr hm)
  have hmodel : ((S.valuationModel A).Δ : AlgebraicClosure ℚ) = (S.curve.Δ : AlgebraicClosure ℚ) := by
    simp [valuationModel, eq_intCast]
  rw [hmodel, hv] at hlt
  exact lt_irrefl 1 hlt

/-- p≠qでの実際のp-torsion点の両座標は、q上の全ての付値環に入る。
良還元・乗法的還元の区別もq≠2もこの整性には不要である。 -/
theorem residual_coordinates_mem [Fact p.Prime] {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    {x y : AlgebraicClosure ℚ} (h : (S.rationalCurve.baseChange (AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (hkill : p • (Affine.Point.some x y h) = 0) : x ∈ A ∧ y ∈ A := by
  have hunit : A.valuation (p : AlgebraicClosure ℚ) = 1 := by
    apply valuation_intCast_eq_one_of_not_dvd A hq ((ValuationSubring.mem_nonunits_iff _).mp hA)
      (z := (p : ℤ))
    intro hd
    have hd' : q ∣ p := by exact_mod_cast hd
    exact hqp ((Nat.prime_dvd_prime_iff_eq hq Fact.out).mp hd')
  exact EllipticTorsionValuationIntegrality.torsion_coordinates_mem A (S.valuationModel A)
    (S.rationalCurve.baseChange (AlgebraicClosure ℚ)) (S.valuationModel_map A) hunit h hkill

/-- 同じ実際のtorsion点の座標の慣性による変化量はAの非単元となる。
差が零であるという不分岐性は、還元幾何学を追加して証明する次の課題である。 -/
theorem residual_inertia_coordinate_congruence [Fact p.Prime] {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : σ ∈ inertiaSubgroupIn A ℚ)
    {x y : AlgebraicClosure ℚ} (h : (S.rationalCurve.baseChange (AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (hkill : p • (Affine.Point.some x y h) = 0) :
    σ x - x ∈ A.nonunits ∧ σ y - y ∈ A.nonunits := by
  obtain ⟨hx, hy⟩ := S.residual_coordinates_mem hq hqp A hA h hkill
  exact ⟨inertia_apply_sub_mem_nonunits A ℚ σ hσ hx, inertia_apply_sub_mem_nonunits A ℚ σ hσ hy⟩

end DkMath.FLT.Frey.Source
