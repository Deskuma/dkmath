/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFunctionFieldConstants
import DkMath.Lib.NumberTheory.EllipticWeilTransport

#print "file: DkMath.Lib.NumberTheory.EllipticFunctionEigenvalue"

/-!
# 同じ位数を持つ関数の比と平行移動の固有値

位数の一致から乗法的付値の一致を復元し、商の全有限付値が1となることを示す。
定数判定を商に適用すると、非零関数f,gに対しf=cgとなる一意な非零定数cが得られる。
最後に平行移動が係数体を固定することを用い、固有値が関数の非零定数倍で変わらないことを示す。
この章は任意の非零関数を対象とし、Weil関数やねじれ点の仮定を必要としない。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open WeierstrassCurve WeierstrassCurve.Affine WithZero
open EllipticFunctionField
variable {K : Type*} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]
attribute [local instance] geometricCoordinateRing_isDedekindDomain

/-- 非零関数では、整数位数の一致から実際の乗法的付値の一致を復元できる。 -/
theorem pointValuation_eq_of_pointOrder_eq (P : Points E)
    (f g : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) (hf : f ≠ 0) (hg : g ≠ 0)
    (h : pointOrder E P f hf = pointOrder E P g hg) :
    pointValuation E P f = pointValuation E P g := by
  rw [pointOrder_eq_neg_log, pointOrder_eq_neg_log] at h
  have hl : log (pointValuation E P f) = log (pointValuation E P g) := by omega
  exact (exp_log ((pointValuation E P).ne_zero_iff.mpr hf)).symm.trans
    ((congrArg exp hl).trans (exp_log ((pointValuation E P).ne_zero_iff.mpr hg)))

omit [E.IsElliptic] in
/-- 非零関数を掛けた二つの定数が一致すれば、その係数体の単元も一致する。 -/
theorem function_scalar_unique (g : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) (hg : g ≠ 0)
    {c d : (AlgebraicClosure K)ˣ}
    (h : algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField (c : AlgebraicClosure K) * g =
      algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField (d : AlgebraicClosure K) * g) :
    c = d := by
  apply Units.ext
  apply (algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField).injective
  exact mul_right_cancel₀ hg h

/-- 全点で位数が同じ非零関数の比は、一意な非零定数である。
実際には有限点の一致だけを定数判定へ渡す。Oの一致を再び例外処理する必要はない。 -/
theorem existsUnique_scalar_of_pointOrder_eq
    (f g : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) (hf : f ≠ 0) (hg : g ≠ 0)
    (h : ∀ P : Points E, pointOrder E P f hf = pointOrder E P g hg) :
    ∃! c : (AlgebraicClosure K)ˣ,
      f = algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField
        (c : AlgebraicClosure K) * g := by
  classical
  have hv : ∀ v : IsDedekindDomain.HeightOneSpectrum (E.toAffine⁄(AlgebraicClosure K)).CoordinateRing,
      v.valuation (E.toAffine⁄(AlgebraicClosure K)).FunctionField (f / g) = 1 := by
    intro v
    obtain ⟨P, hP, rfl⟩ := placeOf_surjective E (AlgebraicClosure K) v
    have he := pointValuation_eq_of_pointOrder_eq E P f g hf hg (h P)
    have he' : finitePointValuation E P hP f = finitePointValuation E P hP g := by
      simpa only [pointValuation, dite_eq_right hP] using he
    change (placeOf E (AlgebraicClosure K) P hP).valuation _ f =
      (placeOf E (AlgebraicClosure K) P hP).valuation _ g at he'
    rw [map_div₀, he', div_self (((placeOf E (AlgebraicClosure K) P hP).valuation _).ne_zero_iff.mpr hg)]
  obtain ⟨c, hc, -⟩ := EllipticFunctionFieldConstants.existsUnique_unit_of_valuation_eq_one
    (E.baseChange (AlgebraicClosure K)) (div_ne_zero hf hg) hv
  have he : f = algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField
      (c : AlgebraicClosure K) * g := (div_eq_iff hg).mp hc
  refine ⟨c, he, ?_⟩
  intro d hd
  exact function_scalar_unique E g hg (hd.symm.trans he)

open Classical in
/-- 係数体は平行移動で固定されるので、固有関数を非零定数倍しても固有値は同じ。
存在を仮定するのは任意関数のこの一つの固有方程式だけであり、Weil関数の場合は次章で構成する。 -/
theorem transEquiv_const_mul_eigenfunction (S : Points E)
    (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) (a c : (AlgebraicClosure K)ˣ)
    (h : transEquiv E (AlgebraicClosure K) S f =
      algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField (c : AlgebraicClosure K) * f) :
    transEquiv E (AlgebraicClosure K) S
      (algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField (a : AlgebraicClosure K) * f) =
      algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField (c : AlgebraicClosure K) *
        (algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField (a : AlgebraicClosure K) * f) := by
  rw [map_mul, AlgEquiv.commutes, h]
  ring

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
