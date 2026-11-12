/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_WeierstrassCurve_Affine_valuation_placeOf_neg_transEquiv_algebraMap.lean.
Upstream blob: 0d75c45594a92350089fb4b7551926c1261e0e6b
Modified for DkMath: reuse constructed infinity valuation and rigidity, remove export macros.
-/

import DkMath.Lib.NumberTheory.EllipticTranslationValuation
import DkMath.Lib.NumberTheory.EllipticInfinityClassification

#print "file: DkMath.Lib.NumberTheory.EllipticTranslationInfinity"

/-!
# 平行移動の例外点は無限遠点に一致する
有限点−Sで引き戻したxは極を持つ。この事実から付値環を同定する。
xとyのノルム次数2と3を組み合わせると、付値の値群への全射性も証明できる。
従って付値環だけでなく、整数値群で正規化した実際の付値が一致する。
-/
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped Polynomial.Bivariate
namespace DkMath.Lib.NumberTheory.EllipticFunctionField
namespace InfinityCoordinateRing
open WeierstrassCurve.Affine.CoordinateRing
open DkMath.Lib.NumberTheory.EllipticInfinityValuation.CoordinateRing

variable {K : Type*} [Field K] (W : Affine K)

/-- X多項式のノルム次数は二倍。 -/
lemma natDegree_norm_mk_C' (p : K[X]) :
    (Algebra.norm K[X] (mk W (C p))).natDegree = 2 * p.natDegree := by
  rw [← natDegree_norm_smul_basis_of_eq_zero W p, CoordinateRing.smul, zero_smul, add_zero,
    mul_one]
/-- yのノルム次数は3であり、xの次数2との差から正規化を得る。 -/
lemma natDegree_norm_mk_Y' : (Algebra.norm K[X] (mk W Y)).natDegree = 3 := by
  have := natDegree_norm_smul_basis_of_ne_zero W 0 1 one_ne_zero
  rw [zero_smul, one_smul, zero_add] at this
  rw [this]
  norm_num
/-- y座標の座標環内での非零性。 -/
lemma mk_Y_ne_zero' : mk W Y ≠ 0 := by
  simpa [YClass] using YClass_ne_zero (W' := W) 0
/-- x座標の座標環内での非零性。 -/
lemma mk_C_X_ne_zero' : mk W (C X) ≠ 0 := by
  simpa [XClass] using XClass_ne_zero (W' := W) 0
end InfinityCoordinateRing

section PlaceNegS

variable {F : Type*} [Field F] (W : WeierstrassCurve F) (K : Type*) [Field K] [Algebra F K]
  [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing]
omit [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] in
/-- 移動元−Sでは、割線の分母x−x(S)の付値が分子y−y(S)より小さい。二重接点でも非特異性から厳密不等式を得る。 -/
theorem valuation_XClass_lt_valuation_YClass {x_S y_S : K} (hxy : (W⁄K).Nonsingular x_S y_S)
    (hS' : -(Point.some x_S y_S hxy) ≠ 0) :
    (placeOf W K (-(Point.some x_S y_S hxy)) hS').valuation (W⁄K).FunctionField
        (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.XClass (W⁄K) x_S)) <
      (placeOf W K (-(Point.some x_S y_S hxy)) hS').valuation (W⁄K).FunctionField
        (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField
          (CoordinateRing.YClass (W⁄K) (C y_S))) := by
  classical
  set v := (placeOf W K (-(Point.some x_S y_S hxy)) hS').valuation (W⁄K).FunctionField with hv
  set ι := algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField with hι
  set 𝔪 := (placeOf W K (-(Point.some x_S y_S hxy)) hS').asIdeal with h𝔪def
  have h𝔪 : 𝔪 = CoordinateRing.XYIdeal (W⁄K) x_S (C ((W⁄K).negY x_S y_S)) := rfl
  set u₀ := CoordinateRing.XClass (W⁄K) x_S with hu₀
  set t₀ := CoordinateRing.YClass (W⁄K) (C y_S) with ht₀
  have hu_mem : u₀ ∈ 𝔪 := h𝔪 ▸ Ideal.subset_span (Set.mem_insert _ _)
  have hneg_mem : CoordinateRing.YClass (W⁄K) (C ((W⁄K).negY x_S y_S)) ∈ 𝔪 :=
    h𝔪 ▸ Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hconst : ∀ c : K, CoordinateRing.mk (W⁄K) (C (C c)) ∈ 𝔪 → c = 0 := by
    intro c hc
    by_contra h0
    have hunit : IsUnit (CoordinateRing.mk (W⁄K) (C (C c))) :=
      (((IsUnit.mk0 c h0).map C).map C).map _
    exact (placeOf W K _ hS').isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hc hunit)
  have hu_lt : v (ι u₀) < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).mpr hu_mem
  have ht0 : v (ι t₀) ≠ 0 := (Valuation.ne_zero_iff v).mpr
    ((map_ne_zero_iff ι (IsFractionRing.injective (W⁄K).CoordinateRing (W⁄K).FunctionField)).mpr
      (CoordinateRing.YClass_ne_zero (W' := W⁄K) _))
  by_cases ht : t₀ ∈ 𝔪
  · have he : (W⁄K).negY x_S y_S - y_S = 0 := by
      apply hconst
      have key : t₀ - CoordinateRing.YClass (W⁄K) (C ((W⁄K).negY x_S y_S)) =
          CoordinateRing.mk (W⁄K) (C (C ((W⁄K).negY x_S y_S - y_S))) := by
        rw [ht₀, CoordinateRing.YClass, CoordinateRing.YClass, ← map_sub]
        congr 1
        simp only [map_sub]
        ring
      exact key ▸ sub_mem ht hneg_mem
    have he2 : 2 * y_S + (W⁄K).a₁ * x_S + (W⁄K).a₃ = 0 := by
      simp only [negY] at he
      linear_combination -he
    have hc1 : 3 * x_S ^ 2 + 2 * (W⁄K).a₂ * x_S + (W⁄K).a₄ - (W⁄K).a₁ * y_S ≠ 0 := by
      have h := ((nonsingular_iff' _ _).mp hxy).2.resolve_right (not_not.mpr he2)
      intro h0
      apply h
      linear_combination -h0
    have hγ : CoordinateRing.mk (W⁄K) (Y ^ 2 + C (C (W⁄K).a₁ * X + C (W⁄K).a₃) * Y -
        C (X ^ 3 + C (W⁄K).a₂ * X ^ 2 + C (W⁄K).a₄ * X + C (W⁄K).a₆)) = 0 := AdjoinRoot.mk_self
    simp only [map_sub, map_add, map_mul, map_pow] at hγ
    have hS := congrArg (fun z : K => CoordinateRing.mk (W⁄K) (C (C z)))
      (((equation_iff _ _).mp hxy.1))
    simp only [map_add, map_mul, map_pow] at hS
    have he2' := congrArg (fun z : K => CoordinateRing.mk (W⁄K) (C (C z))) he2
    simp only [map_add, map_mul, map_ofNat, map_zero] at he2'
    have hrel : t₀ * (t₀ + CoordinateRing.mk (W⁄K) (C (C (W⁄K).a₁)) * u₀) =
        u₀ * (u₀ ^ 2 + CoordinateRing.mk (W⁄K) (C (C (3 * x_S + (W⁄K).a₂))) * u₀ +
          CoordinateRing.mk (W⁄K) (C (C (3 * x_S ^ 2 + 2 * (W⁄K).a₂ * x_S + (W⁄K).a₄ -
            (W⁄K).a₁ * y_S)))) := by
      simp only [map_add, map_mul, map_sub, map_pow, map_ofNat]
      rw [ht₀, hu₀, CoordinateRing.YClass, CoordinateRing.XClass]
      simp only [map_sub]
      linear_combination hγ - hS - (CoordinateRing.mk (W⁄K) Y -
        CoordinateRing.mk (W⁄K) (C (C y_S))) * he2'
    have hq : v (ι (u₀ ^ 2 + CoordinateRing.mk (W⁄K) (C (C (3 * x_S + (W⁄K).a₂))) * u₀ +
        CoordinateRing.mk (W⁄K) (C (C (3 * x_S ^ 2 + 2 * (W⁄K).a₂ * x_S + (W⁄K).a₄ -
          (W⁄K).a₁ * y_S))))) = 1 := by
      rw [hι, HeightOneSpectrum.valuation_eq_one_iff_notMem]
      intro hmem
      apply hc1
      apply hconst
      have : CoordinateRing.mk (W⁄K) (C (C (3 * x_S ^ 2 + 2 * (W⁄K).a₂ * x_S + (W⁄K).a₄ -
          (W⁄K).a₁ * y_S))) = (u₀ ^ 2 + CoordinateRing.mk (W⁄K) (C (C (3 * x_S + (W⁄K).a₂))) * u₀ +
            CoordinateRing.mk (W⁄K) (C (C (3 * x_S ^ 2 + 2 * (W⁄K).a₂ * x_S + (W⁄K).a₄ -
              (W⁄K).a₁ * y_S)))) -
          u₀ * (u₀ + CoordinateRing.mk (W⁄K) (C (C (3 * x_S + (W⁄K).a₂)))) := by ring
      rw [this]
      exact sub_mem hmem (Ideal.mul_mem_right _ _ hu_mem)
    have hs : v (ι (t₀ + CoordinateRing.mk (W⁄K) (C (C (W⁄K).a₁)) * u₀)) < 1 :=
      (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).mpr (add_mem ht (Ideal.mul_mem_left _ _ hu_mem))
    have hmul := congrArg (fun z => v (ι z)) hrel
    simp only [map_mul] at hmul
    rw [hq, mul_one] at hmul
    rw [← hmul]
    exact mul_lt_of_lt_one_right (zero_lt_iff.mpr ht0) hs
  · have ht1 : v (ι t₀) = 1 := by rw [hι, HeightOneSpectrum.valuation_eq_one_iff_notMem]; exact ht
    rw [ht1]
    exact hu_lt
/-- −Sにおいて移動後のxは極を持つ。割線の傾きの二乗が他の項を支配する。 -/
theorem one_lt_valuation_transEquiv_genericX {x_S y_S : K} (hxy : (W⁄K).Nonsingular x_S y_S)
    (hS' : -(Point.some x_S y_S hxy) ≠ 0) :
    1 < (placeOf W K (-(Point.some x_S y_S hxy)) hS').valuation (W⁄K).FunctionField
      (transEquiv W K (Point.some x_S y_S hxy) (genericX W K)) := by
  classical
  set v := (placeOf W K (-(Point.some x_S y_S hxy)) hS').valuation (W⁄K).FunctionField with hv
  set ι := algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField with hι
  have hKconst : ∀ c : K, algebraMap K (W⁄K).FunctionField c =
      ι (CoordinateRing.mk (W⁄K) (C (C c))) := fun c =>
    IsScalarTower.algebraMap_apply K (W⁄K).CoordinateRing (W⁄K).FunctionField c
  have hx : genericX W K ≠ (Algebra.ofId K (W⁄K).FunctionField) x_S := by
    intro h
    apply CoordinateRing.XClass_ne_zero (W' := W⁄K) x_S
    apply IsFractionRing.injective (W⁄K).CoordinateRing (W⁄K).FunctionField
    rw [CoordinateRing.XClass, map_sub, map_sub, map_sub, _root_.map_zero, ← hι,
      show ι (CoordinateRing.mk (W⁄K) (C X)) = genericX W K from rfl, ← hKconst, h, sub_eq_zero]
    rfl
  have hu0 : v (ι (CoordinateRing.XClass (W⁄K) x_S)) ≠ 0 := (Valuation.ne_zero_iff v).mpr
    ((map_ne_zero_iff ι (IsFractionRing.injective (W⁄K).CoordinateRing (W⁄K).FunctionField)).mpr
      (CoordinateRing.XClass_ne_zero (W' := W⁄K) _))
  have ht' : genericY W K - (Algebra.ofId K (W⁄K).FunctionField) y_S =
      ι (CoordinateRing.YClass (W⁄K) (C y_S)) := by
    rw [CoordinateRing.YClass, map_sub, map_sub, Algebra.ofId_apply, hKconst]
    rfl
  have hu' : genericX W K - (Algebra.ofId K (W⁄K).FunctionField) x_S =
      ι (CoordinateRing.XClass (W⁄K) x_S) := by
    rw [CoordinateRing.XClass, map_sub, map_sub, map_sub, Algebra.ofId_apply, hKconst]
    rfl
  have hlt := valuation_XClass_lt_valuation_YClass W K hxy hS'
  rw [transEquiv_genericX, genericPoint, Point.baseChange, Point.map_some, Point.add_of_X_ne hx,
    Point.xc_some, slope_of_X_ne hx]
  simp only [addX]
  set ℓ := (genericY W K - (Algebra.ofId K (W⁄K).FunctionField) y_S) /
    (genericX W K - (Algebra.ofId K (W⁄K).FunctionField) x_S) with hℓ
  have hℓ1 : 1 < v ℓ := by
    rw [hℓ, ht', hu', map_div₀, one_lt_div₀ (zero_lt_iff.mpr hu0)]
    exact hlt
  have hℓ0 : 0 < v ℓ := lt_trans zero_lt_one hℓ1
  have ha1 : (W⁄(W⁄K).FunctionField).a₁ = algebraMap F (W⁄K).FunctionField W.a₁ := rfl
  have ha2 : (W⁄(W⁄K).FunctionField).a₂ = algebraMap F (W⁄K).FunctionField W.a₂ := rfl
  have hF : ∀ r : F, v (algebraMap F (W⁄K).FunctionField r) ≤ 1 := fun r => by
    rw [IsScalarTower.algebraMap_apply F (W⁄K).CoordinateRing (W⁄K).FunctionField]
    exact HeightOneSpectrum.valuation_le_one _ _
  have hrest : v ((W⁄(W⁄K).FunctionField).a₁ * ℓ - (W⁄(W⁄K).FunctionField).a₂ - genericX W K -
      (Algebra.ofId K (W⁄K).FunctionField) x_S) ≤ v ℓ := by
    refine Valuation.map_sub_le _ (Valuation.map_sub_le _ (Valuation.map_sub_le _ ?_ ?_) ?_) ?_
    · rw [map_mul, ha1]
      exact mul_le_of_le_one_left zero_le (hF _)
    · rw [ha2]; exact (hF _).trans hℓ1.le
    · exact (HeightOneSpectrum.valuation_le_one _ _).trans hℓ1.le
    · rw [Algebra.ofId_apply, hKconst]
      exact (HeightOneSpectrum.valuation_le_one _ _).trans hℓ1.le
  have hexp : ℓ ^ 2 + (W⁄(W⁄K).FunctionField).a₁ * ℓ - (W⁄(W⁄K).FunctionField).a₂ - genericX W K -
      (Algebra.ofId K (W⁄K).FunctionField) x_S = ℓ ^ 2 + ((W⁄(W⁄K).FunctionField).a₁ * ℓ -
        (W⁄(W⁄K).FunctionField).a₂ - genericX W K - (Algebra.ofId K (W⁄K).FunctionField) x_S) := by
    ring
  have hsq : v ℓ < v (ℓ ^ 2) := by
    rw [map_pow, sq]
    exact lt_mul_of_one_lt_left hℓ0 hℓ1
  rw [hexp, v.map_add_eq_of_lt_left (lt_of_le_of_lt hrest hsq)]
  exact lt_trans hℓ1 hsq
/-- P+S=Oの例外輸送。付値環を無限遠点と同定し、y/xの値exp(1)による全射性から正規化まで一致させる。 -/
theorem valuation_placeOf_neg_transEquiv_algebraMap_aux (S : (W⁄K).Point) (hS : S ≠ 0)
    (hS' : -S ≠ 0) {a : (W⁄K).CoordinateRing} (ha : a ≠ 0) :
    (placeOf W K (-S) hS').valuation (W⁄K).FunctionField
        (transEquiv W K S (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField a)) =
      WithZero.exp ((Algebra.norm (Polynomial K) a).natDegree : ℤ) := by
  rcases S with _ | ⟨x_S, y_S, hxy⟩
  · exact absurd rfl hS
  set v := (placeOf W K (-(Point.some x_S y_S hxy)) hS').valuation (W⁄K).FunctionField with hv
  set ι := algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField with hι
  let vinf := EllipticInfinityValuation.valuationInfty (W⁄K)
  have hvinf : ∀ f : (W⁄K).CoordinateRing, f ≠ 0 →
      vinf (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField f) =
        exp ((Algebra.norm K[X] f).natDegree : ℤ) :=
    fun _ hf => EllipticInfinityValuation.valuationInfty_algebraMap_of_ne_zero (W⁄K) hf
  set τ : (W⁄K).FunctionField →+* (W⁄K).FunctionField :=
    (transEquiv W K (Point.some x_S y_S hxy)).toAlgHom.toRingHom with hτ
  have hτapp : ∀ h, v.comap τ h = v (transEquiv W K (Point.some x_S y_S hxy) h) := fun _ => rfl
  have hO : (v.comap τ).valuationSubring = vinf.valuationSubring := by
    refine EllipticInfinityValuation.FunctionField.eq_valuationSubring_of_X_not_mem_aux (W.baseChange K) _
      (fun c => ?_) ?_ vinf hvinf
    · rw [Valuation.mem_valuationSubring_iff, hτapp, AlgEquiv.commutes]
      exact valuation_algebraMap_le_one W K _ hS' c
    · rw [Valuation.mem_valuationSubring_iff, hτapp, not_le]
      exact one_lt_valuation_transEquiv_genericX W K hxy hS'
  have hsτ : Function.Surjective (v.comap τ) := fun γ => by
    obtain ⟨h, hh⟩ := HeightOneSpectrum.valuation_surjective
      (placeOf W K (-(Point.some x_S y_S hxy)) hS') (K := (W⁄K).FunctionField) γ
    exact ⟨(transEquiv W K (Point.some x_S y_S hxy)).symm h, by
      rw [hτapp, AlgEquiv.apply_symm_apply]; exact hh⟩
  have hsinf : Function.Surjective vinf := by
    intro γ
    rcases eq_or_ne γ 0 with rfl | hγ
    · exact ⟨0, map_zero _⟩
    · have hY : vinf (ι (CoordinateRing.mk (W⁄K) Y)) = WithZero.exp 3 := by
        rw [hι, hvinf _ (InfinityCoordinateRing.mk_Y_ne_zero' (W⁄K)), InfinityCoordinateRing.natDegree_norm_mk_Y']
        rfl
      have hX : vinf (ι (CoordinateRing.mk (W⁄K) (C X))) = WithZero.exp 2 := by
        rw [hι, hvinf _ (InfinityCoordinateRing.mk_C_X_ne_zero' (W⁄K)), InfinityCoordinateRing.natDegree_norm_mk_C',
          natDegree_X]
        rfl
      refine ⟨(ι (CoordinateRing.mk (W⁄K) Y) / ι (CoordinateRing.mk (W⁄K) (C X))) ^ WithZero.log γ, ?_⟩
      rw [map_zpow₀, map_div₀, hY, hX, ← WithZero.exp_sub, ← WithZero.exp_zsmul, smul_eq_mul]
      norm_num
      exact WithZero.exp_log hγ
  have heqv := Valuation.eq_of_valuationSubring_eq_aux _ _ hsτ hsinf hO
  have key := DFunLike.congr_fun heqv (ι a)
  rw [hτapp] at key
  rw [key, hι, hvinf a ha]
end PlaceNegS
variable {F : Type*} [Field F] (W : WeierstrassCurve F) (K : Type*) [Field K] [Algebra F K]
  [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing]

/-- 例外点の一致を座標環の元から任意の有理関数へ拡張する。分子・分母の表示を使う。 -/
theorem valuation_placeOf_neg_transEquiv (S : (W⁄K).Point) (hS : S ≠ 0)
    (f : (W⁄K).FunctionField) :
    (placeOf W K (-S) (neg_ne_zero.mpr hS)).valuation (W⁄K).FunctionField
      (transEquiv W K S f) = EllipticInfinityValuation.valuationInfty (W⁄K) f := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := (W⁄K).CoordinateRing) f
  by_cases ha : a = 0
  · simp [ha]
  have hb0 := nonZeroDivisors.ne_zero hb
  rw [map_div₀, map_div₀, map_div₀,
    valuation_placeOf_neg_transEquiv_algebraMap_aux W K S hS _ ha,
    valuation_placeOf_neg_transEquiv_algebraMap_aux W K S hS _ hb0,
    EllipticInfinityValuation.valuationInfty_algebraMap_of_ne_zero _ ha,
    EllipticInfinityValuation.valuationInfty_algebraMap_of_ne_zero _ hb0]

end DkMath.Lib.NumberTheory.EllipticFunctionField
