/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_WeierstrassCurve_Affine_FunctionField_exists_eq_algebraMap_of_valuation_eq_one.lean.
Upstream blob: e6ef120f499a0d3a9b80eb48feb216ea8fbbd539
Modified for DkMath: reuse NOTE-024 norm degrees, require nonzero function explicitly,
and state uniqueness as a unit of the coefficient field.
-/

import DkMath.Lib.NumberTheory.EllipticInfinityClassification
import DkMath.Lib.NumberTheory.EllipticFunctionFieldPlaces
import Mathlib.RingTheory.DedekindDomain.AdicValuation

#print "file: DkMath.Lib.NumberTheory.EllipticFunctionFieldConstants"

/-!
# 有限場所の付値から定数を復元する

全有限場所で付値1の非零有理関数gは、gとg⁻¹の両方が座標環に入るので単元となる。
単元のノルムも単元だから次数0である。二元基底p(x)+q(x)yでは、q≠0なら
ノルム次数が少なくとも3となり矛盾する。残るp(x)も次数0で、gは非零定数である。
無限遠点の輸送やWeil対の存在をこの定数判定に仮定しない。
-/
namespace DkMath.Lib.NumberTheory.EllipticFunctionFieldConstants
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open IsDedekindDomain
open scoped Polynomial.Bivariate
variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- 座標環の単元は非零定数に限る。Y成分の次数3と、X成分の二倍の次数を使う。 -/
theorem isUnit_iff_eq_algebraMap (f : W.toAffine.CoordinateRing) :
    IsUnit f ↔ ∃ c : F, c ≠ 0 ∧ f = algebraMap F W.toAffine.CoordinateRing c := by
  constructor
  · intro hf
    obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq f
    have hnu : IsUnit (Algebra.norm F[X] (p • (1 : W.toAffine.CoordinateRing) +
        q • CoordinateRing.mk W.toAffine Y)) := hf.map _
    have hd := natDegree_eq_zero_of_isUnit hnu
    have hq : q = 0 := by
      by_contra hq
      rw [EllipticInfinityValuation.CoordinateRing.natDegree_norm_smul_basis_of_ne_zero _ _ _ hq] at hd
      omega
    subst q
    rw [zero_smul, add_zero] at hnu ⊢
    have hnp : Algebra.norm F[X] (p • (1 : W.toAffine.CoordinateRing)) = p ^ 2 := by
      have h := CoordinateRing.norm_smul_basis (W' := W.toAffine) p 0
      rw [zero_smul, add_zero] at h
      rw [h]
      ring
    rw [hnp, isUnit_pow_iff two_ne_zero, Polynomial.isUnit_iff] at hnu
    obtain ⟨c, hc, rfl⟩ := hnu
    refine ⟨c, hc.ne_zero, ?_⟩
    rw [CoordinateRing.smul, mul_one]
    rfl
  · rintro ⟨c, hc, rfl⟩
    exact (IsUnit.mk0 c hc).map _

/-- Dedekind付値の整性判定をgとg⁻¹に適用し、同じ関数体内の非零定数を取り出す。
f≠0を明示するので、有限場所の非空性を別途仮定する必要もない。 -/
theorem exists_eq_algebraMap_of_valuation_eq_one [IsDedekindDomain W.toAffine.CoordinateRing]
    {f : W.toAffine.FunctionField} (hf0 : f ≠ 0)
    (hf : ∀ v : HeightOneSpectrum W.toAffine.CoordinateRing, v.valuation W.toAffine.FunctionField f = 1) :
    ∃ c : F, c ≠ 0 ∧ f = algebraMap F W.toAffine.FunctionField c := by
  obtain ⟨g, hg⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one
    W.toAffine.FunctionField f (fun v => (hf v).le)
  obtain ⟨g', hg'⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one
    W.toAffine.FunctionField f⁻¹ (fun v => by rw [map_inv₀, hf v, inv_one])
  have hgg' : g * g' = 1 := by
    apply IsFractionRing.injective W.toAffine.CoordinateRing W.toAffine.FunctionField
    rw [map_mul, hg, hg', map_one, mul_inv_cancel₀ hf0]
  obtain ⟨c, hc, hgc⟩ := (isUnit_iff_eq_algebraMap W g).mp (IsUnit.of_mul_eq_one g' hgg')
  refine ⟨c, hc, ?_⟩
  rw [← hg, hgc, ← IsScalarTower.algebraMap_apply]

/-- 定数体の埋め込みの単射性により、復元された非零定数は単元としても一意である。 -/
theorem existsUnique_unit_of_valuation_eq_one [IsDedekindDomain W.toAffine.CoordinateRing]
    {f : W.toAffine.FunctionField} (hf0 : f ≠ 0)
    (hf : ∀ v : HeightOneSpectrum W.toAffine.CoordinateRing, v.valuation W.toAffine.FunctionField f = 1) :
    ∃! c : Fˣ, f = algebraMap F W.toAffine.FunctionField (c : F) := by
  obtain ⟨c, hc, he⟩ := exists_eq_algebraMap_of_valuation_eq_one W hf0 hf
  refine ⟨Units.mk0 c hc, he, ?_⟩
  intro d hd
  apply Units.ext
  exact (algebraMap F W.toAffine.FunctionField).injective (hd.symm.trans he)

end DkMath.Lib.NumberTheory.EllipticFunctionFieldConstants
