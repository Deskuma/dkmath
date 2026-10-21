/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_WeierstrassCurve_Affine_FunctionField_exists_valuation_eq_exp_natDegree_norm.lean.
Upstream blob: bee7e29c4b6a040b634b7ba3d71e99df35d5ec15
Modified for DkMath: isolated namespace and textbook description of the actual infinity valuation.
-/

import DkMath.Lib.NumberTheory.EllipticFunctionField
import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.RingTheory.Norm.Basic

#print "file: DkMath.Lib.NumberTheory.EllipticInfinityValuation"

/-!
# ノルム次数から無限遠点の付値を構成する

座標環の二元基底p+qYのノルム次数は、q≠0ならmax(2 deg p, 2 deg q+3)、
q=0なら2 deg pとなる。零元の付値は次数とは別に0と定義する。
この次数の指数を用いて座標環上の付値を構成し、その実際の分数体へ延長する。
単なる次数差の台帳ではなく、乗法性と和の不等式を持つValuationである。
-/
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate WithZero nonZeroDivisors
namespace DkMath.Lib.NumberTheory.EllipticInfinityValuation

variable {K : Type*} [Field K] (W : Affine K)

namespace CoordinateRing

/-- 非零座標環元のノルムは非零。二元自由加群の基底を使う。 -/
lemma norm_ne_zero {f : W.CoordinateRing} (hf : f ≠ 0) : Algebra.norm K[X] f ≠ 0 :=
  (Algebra.norm_ne_zero_iff_of_basis (CoordinateRing.basis W)).mpr hf

open Classical in
/-- 零元の値を0、非零元の値をノルム次数の指数とする。 -/
noncomputable def valuationInftyDef (f : W.CoordinateRing) : ℤᵐ⁰ :=
  if f = 0 then 0 else WithZero.exp ((Algebra.norm K[X] f).natDegree : ℤ)

/-- 二元基底p+qYの次数公式から、和の次数の非Archimedes不等式を示す。 -/
lemma degree_norm_add_le (f g : W.CoordinateRing) :
    (Algebra.norm K[X] (f + g)).degree ≤
      max (Algebra.norm K[X] f).degree (Algebra.norm K[X] g).degree := by
  obtain ⟨p, q, rfl⟩  := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq f
  obtain ⟨p', q', rfl⟩  := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq g
  have : p • (1 : W.CoordinateRing) + q • WeierstrassCurve.Affine.CoordinateRing.mk W Y + (p' • 1 + q' • WeierstrassCurve.Affine.CoordinateRing.mk W Y) =
      (p + p') • 1 + (q + q') • WeierstrassCurve.Affine.CoordinateRing.mk W Y := by
    rw [add_smul, add_smul]; abel
  rw [this, WeierstrassCurve.Affine.CoordinateRing.degree_norm_smul_basis, WeierstrassCurve.Affine.CoordinateRing.degree_norm_smul_basis, WeierstrassCurve.Affine.CoordinateRing.degree_norm_smul_basis]
  refine max_le ?_ ?_
  · rcases le_max_iff.mp (degree_add_le p p') with h | h
    · exact le_max_of_le_left (le_max_of_le_left (nsmul_le_nsmul_right h 2))
    · exact le_max_of_le_right (le_max_of_le_left (nsmul_le_nsmul_right h 2))
  · rcases le_max_iff.mp (degree_add_le q q') with h | h
    · exact le_max_of_le_left (le_max_of_le_right
        (add_le_add_left (nsmul_le_nsmul_right h 2) 3))
    · exact le_max_of_le_right (le_max_of_le_right
        (add_le_add_left (nsmul_le_nsmul_right h 2) 3))

/-- ノルム次数は乗法的で、和には最大値の上界を持つので実際の付値になる。 -/
noncomputable def valuationInftyInt : Valuation W.CoordinateRing ℤᵐ⁰ where
  toFun := valuationInftyDef W
  map_zero' := ite_eq_left rfl
  map_one' := by
    simp [valuationInftyDef]
  map_mul' f g := by
    classical
    by_cases hf : f = 0
    · simp [valuationInftyDef, hf]
    by_cases hg : g = 0
    · simp [valuationInftyDef, hg]
    simp only [valuationInftyDef, ite_eq_right hf, ite_eq_right hg, ite_eq_right (mul_ne_zero hf hg), map_mul,
      natDegree_mul (norm_ne_zero W hf) (norm_ne_zero W hg), Nat.cast_add, WithZero.exp_add]
  map_add_le_max' f g := by
    classical
    by_cases hfg : f + g = 0
    · simp [valuationInftyDef, hfg]
    by_cases hf : f = 0
    · simp [valuationInftyDef, hf]
    by_cases hg : g = 0
    · simp [valuationInftyDef, hg]
    simp only [valuationInftyDef, ite_eq_right hf, ite_eq_right hg, ite_eq_right hfg, le_max_iff,
      WithZero.exp_le_exp, Nat.cast_le]
    have h := degree_norm_add_le W f g
    rw [degree_eq_natDegree (norm_ne_zero W hfg), degree_eq_natDegree (norm_ne_zero W hf),
      degree_eq_natDegree (norm_ne_zero W hg)] at h
    rcases le_max_iff.mp h with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h)

/-- 座標環上の付値の定義式。 -/
lemma valuationInftyInt_apply (f : W.CoordinateRing) :
    valuationInftyInt W f = valuationInftyDef W f := rfl

/-- 非零分母を付値の台から除き、分数体への延長を保証する。 -/
lemma nonZeroDivisors_le_supp_primeCompl :
    W.CoordinateRing⁰ ≤ (valuationInftyInt W).supp.primeCompl := fun _ hs => by
  simp [valuationInftyInt_apply, valuationInftyDef, nonZeroDivisors.ne_zero hs]

end CoordinateRing

/-- ノルム次数の付値を実際の関数体へ延長する。無限遠点の付値として用いる。 -/
noncomputable def valuationInfty : Valuation W.FunctionField ℤᵐ⁰ :=
  (CoordinateRing.valuationInftyInt W).extendToLocalization
    (CoordinateRing.nonZeroDivisors_le_supp_primeCompl W) W.FunctionField

/-- 関数体の付値は座標環上で元の次数付値に一致する。 -/
lemma valuationInfty_algebraMap (f : W.CoordinateRing) :
    valuationInfty W (algebraMap W.CoordinateRing W.FunctionField f) =
      CoordinateRing.valuationInftyDef W f :=
  Valuation.extendToLocalization_apply_map_apply ..

/-- 非零座標環元の無限遠点付値はexp(deg Norm)であり、位数は次数の負となる。 -/
lemma valuationInfty_algebraMap_of_ne_zero {f : W.CoordinateRing} (hf : f ≠ 0) :
    valuationInfty W (algebraMap W.CoordinateRing W.FunctionField f) =
      WithZero.exp ((Algebra.norm K[X] f).natDegree : ℤ) := by
  rw [valuationInfty_algebraMap, CoordinateRing.valuationInftyDef, ite_eq_right hf]

end DkMath.Lib.NumberTheory.EllipticInfinityValuation
