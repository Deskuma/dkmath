/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/
import DkMath.Lib.NumberTheory.EllipticFiniteKernelVeluEquation
import DkMath.Lib.NumberTheory.EllipticFiniteKernelFormal
import DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation
import DkMath.Lib.NumberTheory.WeierstrassVeluPolynomial
import Mathlib.RingTheory.Valuation.ValuationSubring

#print "file: DkMath.Lib.NumberTheory.EllipticThreeKernelDiscriminant"

/-!
# 3点核を持つ Tate 型曲線の判別式

[DkMath.Lib] y²+a xy+b y=x³ と原点 (0,0) の反転対を使う。
Vélu 多項式の判別式を整数係数の恒等式として計算し、同じ実点核の商に接続する。
三次の場合を一般指数の積公式に読み替えず、係数と仮定を明示する。
-/
namespace DkMath.Lib.NumberTheory.EllipticThreeKernelDiscriminant
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassVeluPolynomial
open scoped BigOperators

/-- [DkMath.Lib] 3捩れ点を原点に置いた Tate 型の Weierstrass 曲線。 -/
def source {R : Type*} [CommRing R] (a b : R) : WeierstrassCurve R := ⟨a, 0, b, 0, 0⟩

/-- [DkMath.Lib] 原点を半核代表とする Vélu 型多項式モデル。 -/
def quotient {R : Type*} [CommRing R] (a b : R) : WeierstrassCurve R :=
  polynomialModel (source a b) ({()} : Finset Unit) (fun _ => 0) (fun _ => 0)

/-- [DkMath.Lib] 同じ3点核の多項式商の係数。整数係数のため標数2・3でも成立する。 -/
theorem quotient_eq {R : Type*} [CommRing R] (a b : R) :
    quotient a b = ⟨a, 0, b, -5 * a * b, -(a ^ 3 * b) - 7 * b ^ 2⟩ := by
  ext <;> simp [quotient, source, polynomialModel, momentT, momentW, b₂, b₄] <;> ring

/-- [DkMath.Lib] 源の判別式は b³(a³−27b)。 -/
theorem source_discriminant {R : Type*} [CommRing R] (a b : R) :
    (source a b).Δ = b ^ 3 * (a ^ 3 - 27 * b) := by
  simp only [source, WeierstrassCurve.Δ, b₂, b₄, b₆, b₈]
  ring

/-- [DkMath.Lib] 多項式商の判別式は b(a³−27b)³。
二つの素因子の指数が 3:1 から 1:3 へ交換する。 -/
theorem quotient_discriminant {R : Type*} [CommRing R] (a b : R) :
    (quotient a b).Δ = b * (a ^ 3 - 27 * b) ^ 3 := by
  rw [quotient_eq]
  simp only [WeierstrassCurve.Δ, b₂, b₄, b₆, b₈]
  ring

/-- [DkMath.Lib] 三次の場合の Vélu 判別式積恒等式。
原点の接線分母の平方は b² なので、その四乗 b⁸ を商判別式に掛ける。 -/
theorem discriminant_product_identity {R : Type*} [CommRing R] (a b : R) :
    (quotient a b).Δ * (b ^ 2) ^ 4 = (source a b).Δ ^ 3 := by
  rw [quotient_discriminant, source_discriminant]
  ring

/-- [DkMath.Lib] 任意の付値で、源と商の判別式の値を二つの因子の付値で表す。
付値の規格化や離散性を要しない。 -/
theorem discriminant_values {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation F Γ₀) (a b : F) :
    v (source a b).Δ = v b ^ 3 * v (a ^ 3 - 27 * b) ∧
    v (quotient a b).Δ = v b * v (a ^ 3 - 27 * b) ^ 3 := by
  rw [source_discriminant, quotient_discriminant, map_mul, map_pow, map_mul, map_pow]
  exact ⟨rfl, rfl⟩

/-- [DkMath.Lib] b が付値1なら、商判別式の付値は源判別式の付値の3乗。 -/
theorem quotient_value_of_b_unit {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation F Γ₀) (a b : F) (hb : v b = 1) :
    v (quotient a b).Δ = v (source a b).Δ ^ 3 := by
  obtain ⟨hs, ht⟩ := discriminant_values v a b
  rw [hs, ht, hb]
  simp

/-- [DkMath.Lib] a³−27b が付値1なら、源判別式の付値は商判別式の付値の3乗。 -/
theorem source_value_of_complement_unit {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation F Γ₀) (a b : F) (hc : v (a ^ 3 - 27 * b) = 1) :
    v (source a b).Δ = v (quotient a b).Δ ^ 3 := by
  obtain ⟨hs, ht⟩ := discriminant_values v a b
  rw [hs, ht, hc]
  simp

/-- [DkMath.Lib] a,b が整で b が非単元、c₄ が単元なら、a³−27b は単元。
特異核側でどちらの因子が深さを担うかを、標数に依らない付値計算で決定する。 -/
theorem complement_unit_of_c4_unit {F : Type*} [Field F] (A : ValuationSubring F)
    (a b : F) (ha : a ∈ A) (hb : A.valuation b < 1)
    (hc4 : A.valuation (source a b).c₄ = 1) : A.valuation (a ^ 3 - 27 * b) = 1 := by
  have ha1 : A.valuation a ≤ 1 := (A.valuation_le_one_iff _).mpr ha
  have h24 : A.valuation (24 : F) ≤ 1 := (A.valuation_le_one_iff _).mpr (ofNat_mem A 24)
  have h27 : A.valuation (27 : F) ≤ 1 := (A.valuation_le_one_iff _).mpr (ofNat_mem A 27)
  have hsmall : A.valuation (24 * a * b) < 1 := by
    rw [map_mul, map_mul]
    exact (mul_le_of_le_one_left' (mul_le_one' h24 ha1)).trans_lt hb
  have hc4eq : (source a b).c₄ = a ^ 4 - 24 * a * b := by
    simp only [source, c₄, b₂, b₄]
    ring
  rw [hc4eq] at hc4
  have hpow : A.valuation (a ^ 4) = 1 := by
    have he : a ^ 4 = (a ^ 4 - 24 * a * b) + 24 * a * b := by ring
    rw [he, Valuation.map_add_eq_of_lt_left _ (by rw [hc4]; exact hsmall), hc4]
  have haunit : A.valuation a = 1 := by
    apply (pow_eq_one_iff_left (by decide : (4 : ℕ) ≠ 0)).mp
    simpa only [map_pow] using hpow
  have hsmall27 : A.valuation (27 * b) < 1 := by
    rw [map_mul]
    exact (mul_le_of_le_one_left' h27).trans_lt hb
  rw [Valuation.map_sub_eq_of_lt_left _ (by rw [map_pow, haunit, one_pow]; exact hsmall27),
    map_pow, haunit, one_pow]

end DkMath.Lib.NumberTheory.EllipticThreeKernelDiscriminant

namespace DkMath.Lib.NumberTheory.EllipticThreeKernelDiscriminant
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassVeluPolynomial
open EllipticTorsionRepresentation EllipticFiniteKernel EllipticGoodReductionSeparation
open WeierstrassResidueModel IsLocalRing
noncomputable local instance instDecidableEqEllipticThreeKernelDiscriminant {α : Type*} : DecidableEq α := Classical.decEq _
variable {K : Type*} [Field K] [CharZero K] (a b : K)
variable [(source a b).IsElliptic] (H : AddSubgroup (Points (source a b))) [Fintype H]
  (hcard : Nat.card H = 3) (Q : H) (hQ0 : Q.val ≠ 0)
  (hQx : Q.val.xc = 0) (hQy : Q.val.yc = 0)

include hcard Q hQ0 in
omit [CharZero K] [(source a b).IsElliptic] in
set_option linter.unusedFintypeInType false in
/-- [DkMath.Lib] 点数3の同じ核は、任意の非零点 Q とその反対点、無限遠から尽きる。 -/
theorem three_kernel_cover (R : H) : R.val = 0 ∨ R.val = Q.val ∨ R.val = -Q.val := by
  classical
  have ho : Odd (Nat.card H) := hcard ▸ (by decide : Odd 3)
  have hQ : Q ≠ 0 := fun hh => hQ0 (congrArg Subtype.val hh)
  have hn : -Q ≠ Q := neg_ne_self_of_odd_kernel (source a b) H ho Q hQ
  have hc : ({0, Q, -Q} : Finset H).card = 3 := by
    have h1 : (0 : H) ∉ ({Q, -Q} : Finset H) := by simp [hQ, Ne.symm hQ]
    have h2 : Q ∉ ({-Q} : Finset H) := by simp [Ne.symm hn]
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2, Finset.card_singleton]
  have hu : ({0, Q, -Q} : Finset H) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, Fintype.card_eq_nat_card, hcard, hc]
  have hr : R ∈ ({0, Q, -Q} : Finset H) := hu.symm ▸ Finset.mem_univ R
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with h | h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (Or.inl (congrArg Subtype.val h))
  · exact Or.inr (Or.inr (congrArg Subtype.val h))

include hcard Q hQ0 hQx hQy in
/-- [DkMath.Lib] 反転対のどちらを半核に選んでも、同じ実3点核の商標的は
Tate 型の原点を用いた多項式商に等しい。核点が 0,Q,−Q からなることを保持する。 -/
theorem kernelModel_eq_quotient :
    kernelModel (source a b) H = quotient (algebraMap K (AlgebraicClosure K) a) (algebraMap K (AlgebraicClosure K) b) := by
  have ho : Odd (Nat.card H) := hcard ▸ (by decide : Odd 3)
  rw [← halfKernelPolynomialModel_eq_kernelModel (source a b) H ho]
  have hc := card_halfKernel (source a b) H ho
  rw [hcard] at hc
  have hs : (halfKernel (source a b) H).card = 1 := by omega
  obtain ⟨R, hR⟩ := Finset.card_eq_one.mp hs
  have hr : R ∈ halfKernel (source a b) H := by rw [hR]; exact Finset.mem_singleton_self _
  have hn : R.val ≠ 0 := fun he => (mem_halfKernel (source a b) H R).mp hr |>.1 <| Subtype.ext he
  have hd : R.val = Q.val ∨ R.val = -Q.val := by
    rcases three_kernel_cover a b H hcard Q hQ0 R with hz | hq | hq
    · exact (hn hz).elim
    · exact Or.inl hq
    · exact Or.inr hq
  have hnegx : (-Q.val).xc = 0 := by
    have hh : ∀ P : Points (source a b), (-P).xc = P.xc := by
      intro P
      cases P <;> rfl
    rw [hh, hQx]
  have hnegy : (-Q.val).yc = -algebraMap K (AlgebraicClosure K) b := by
    have hh : ∀ P : Points (source a b), P ≠ 0 →
        (-P).yc = -P.yc - algebraMap K (AlgebraicClosure K) a * P.xc - algebraMap K (AlgebraicClosure K) b := by
      intro P hP
      cases P with
      | zero => exact (hP rfl).elim
      | some x y h => rfl
    rw [hh Q.val hQ0, hQx, hQy]
    ring
  unfold halfKernelPolynomialModel
  rw [hR]
  rw [quotient_eq]
  rcases hd with hd | hd
  · simp only [polynomialModel, Finset.sum_singleton, hd]
    ext <;> simp only [momentT, momentW, hQx, hQy] <;>
      simp [source, WeierstrassCurve.map, b₂, b₄] <;> ring
  · simp only [polynomialModel, Finset.sum_singleton, hd]
    ext <;> simp only [momentT, momentW, hnegx, hnegy] <;>
      simp [source, WeierstrassCurve.map, b₂, b₄] <;> ring

include hcard Q hQ0 hQx hQy in
/-- [DkMath.Lib] 同じ実3点核の商標的について、源と商の判別式の正確な値。
半核を固定の点に選び直さず、同じ標的への一致を前の定理から使用する。 -/
theorem kernelModel_discriminant :
    (kernelModel (source a b) H).Δ = (algebraMap K (AlgebraicClosure K) b) *
      ((algebraMap K (AlgebraicClosure K) a) ^ 3 - 27 * algebraMap K (AlgebraicClosure K) b) ^ 3 := by
  rw [kernelModel_eq_quotient a b H hcard Q hQ0 hQx hQy, quotient_discriminant]

include hcard Q hQ0 hQx hQy in
/-- [DkMath.Lib] 同じ実3点核の標的判別式が満たす三次の積公式。 -/
theorem kernelModel_discriminant_product :
    (kernelModel (source a b) H).Δ * ((algebraMap K (AlgebraicClosure K) b) ^ 2) ^ 4 =
      ((source a b).map (algebraMap K (AlgebraicClosure K))).Δ ^ 3 := by
  rw [kernelModel_eq_quotient a b H hcard Q hQ0 hQx hQy]
  have he : (source a b).map (algebraMap K (AlgebraicClosure K)) =
      source (algebraMap K (AlgebraicClosure K) a) (algebraMap K (AlgebraicClosure K) b) := by
    ext <;> simp [source]
  rw [he]
  exact discriminant_product_identity _ _

include hcard Q hQ0 hQx hQy in
/-- [DkMath.Lib] 同じ実3点核の商で、b が付値1なら判別式の付値は源の3乗。
一般指数や、任意の乗法的還元曲線についての主張ではない。 -/
theorem kernelModel_value_of_b_unit {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation (AlgebraicClosure K) Γ₀) (hb : v (algebraMap K (AlgebraicClosure K) b) = 1) :
    v (kernelModel (source a b) H).Δ =
      v ((source a b).map (algebraMap K (AlgebraicClosure K))).Δ ^ 3 := by
  rw [kernelModel_eq_quotient a b H hcard Q hQ0 hQx hQy]
  have he : (source a b).map (algebraMap K (AlgebraicClosure K)) =
      source (algebraMap K (AlgebraicClosure K) a) (algebraMap K (AlgebraicClosure K) b) := by
    ext <;> simp [source]
  rw [he]
  exact quotient_value_of_b_unit v _ _ hb

include hcard Q hQ0 hQx hQy in
/-- [DkMath.Lib] 同じ実3点核の商で、a³−27b が付値1なら源判別式の付値は商の3乗。 -/
theorem kernelModel_value_of_complement_unit {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation (AlgebraicClosure K) Γ₀)
    (hc : v ((algebraMap K (AlgebraicClosure K) a) ^ 3 - 27 * algebraMap K (AlgebraicClosure K) b) = 1) :
    v ((source a b).map (algebraMap K (AlgebraicClosure K))).Δ =
      v (kernelModel (source a b) H).Δ ^ 3 := by
  rw [kernelModel_eq_quotient a b H hcard Q hQ0 hQx hQy]
  have he : (source a b).map (algebraMap K (AlgebraicClosure K)) =
      source (algebraMap K (AlgebraicClosure K) a) (algebraMap K (AlgebraicClosure K) b) := by
    ext <;> simp [source]
  rw [he]
  exact source_value_of_complement_unit v _ _ hc

include Q hQ0 hQx hQy in
omit [CharZero K] [(source a b).IsElliptic] [Fintype H] in
/-- [DkMath.Lib] Tate 型の原点の零成分所属は、係数 b の単元性と同値。
同じ整モデルと実際の非零核点を使い、原点での剰余方程式の偏微分を検査する。 -/
theorem origin_smooth_iff_b_unit (A : ValuationSubring (AlgebraicClosure K))
    (M : WeierstrassCurve A)
    (hM : M.map A.subtype = (source a b).map (algebraMap K (AlgebraicClosure K))) :
    HasSmoothReduction M Q.val ↔ A.valuation (algebraMap K (AlgebraicClosure K) b) = 1 := by
  have h2 : M.a₂ = 0 := A.subtype_injective (by
    have hh := congrArg WeierstrassCurve.a₂ hM
    simpa only [map_a₂, source, map_zero] using hh)
  have h4 : M.a₄ = 0 := A.subtype_injective (by
    have hh := congrArg WeierstrassCurve.a₄ hM
    simpa only [map_a₄, source, map_zero] using hh)
  have h6 : M.a₆ = 0 := A.subtype_injective (by
    have hh := congrArg WeierstrassCurve.a₆ hM
    simpa only [map_a₆, source, map_zero] using hh)
  have hb : (M.a₃ : AlgebraicClosure K) = algebraMap K (AlgebraicClosure K) b := by
    change A.subtype M.a₃ = _
    have hh := congrArg WeierstrassCurve.a₃ hM
    simpa only [map_a₃, source] using hh
  have hm : M = source M.a₁ M.a₃ := by
    ext <;> simp [source, h2, h4, h6]
  have hns := Point.nonsingular_xc_yc hQ0
  have he := Point.eq_some_xc_yc hQ0
  have hs : HasSmoothReduction M Q.val ↔
      (M.map (residue A)).toAffine.Nonsingular 0 0 := by
    rw [he, hasSmoothReduction_some_iff]
    change (∀ (hx : Q.val.xc ∈ A) (hy : Q.val.yc ∈ A),
      (M.map (residue A)).toAffine.Nonsingular (residue A ⟨Q.val.xc, hx⟩)
        (residue A ⟨Q.val.yc, hy⟩)) ↔ _
    rw [hQx, hQy]
    have hz : ∀ h : (0 : AlgebraicClosure K) ∈ A, (⟨0, h⟩ : A) = 0 := fun _ => rfl
    simp only [hz, map_zero]
    exact ⟨fun hh => hh (zero_mem A) (zero_mem A), fun hh _ _ => hh⟩
  rw [hs, ← hb, ← residue_ne_zero_iff A M.a₃, hm]
  simp [source, nonsingular_iff', equation_iff, WeierstrassCurve.toAffine]

include hcard Q hQ0 hQx hQy in
/-- [DkMath.Lib] Tate 型の同じ非零3点核が滑らかに還元すれば、同じ商の判別式の値は源の3乗。
核点の滑らかさから b の単元性を導き、任意の付値環で成立する。 -/
theorem kernelModel_value_of_smooth_origin (A : ValuationSubring (AlgebraicClosure K))
    (M : WeierstrassCurve A)
    (hM : M.map A.subtype = (source a b).map (algebraMap K (AlgebraicClosure K)))
    (hs : HasSmoothReduction M Q.val) :
    A.valuation (kernelModel (source a b) H).Δ =
      A.valuation ((source a b).map (algebraMap K (AlgebraicClosure K))).Δ ^ 3 :=
  kernelModel_value_of_b_unit a b H hcard Q hQ0 hQx hQy A.valuation
    ((origin_smooth_iff_b_unit a b H Q hQ0 hQx hQy A M hM).mp hs)

include hcard Q hQ0 hQx hQy in
/-- [DkMath.Lib] Tate 型の同じ非零3点核が特異に還元し c₄ が単元なら、
同じ源の判別式の値は商の3乗。乗法的還元の c₄ 条件を明示し、核位置から
補因子 a³−27b の単元性を内部で導く。 -/
theorem kernelModel_value_of_nonsmooth_origin (A : ValuationSubring (AlgebraicClosure K))
    (M : WeierstrassCurve A)
    (hM : M.map A.subtype = (source a b).map (algebraMap K (AlgebraicClosure K)))
    (hbad : ¬ HasSmoothReduction M Q.val)
    (hc4 : A.valuation ((source a b).map (algebraMap K (AlgebraicClosure K))).c₄ = 1) :
    A.valuation ((source a b).map (algebraMap K (AlgebraicClosure K))).Δ =
      A.valuation (kernelModel (source a b) H).Δ ^ 3 := by
  have ha : algebraMap K (AlgebraicClosure K) a ∈ A := by
    have he := congrArg WeierstrassCurve.a₁ hM
    simp only [map_a₁, source] at he
    exact he ▸ M.a₁.property
  have hbmem : algebraMap K (AlgebraicClosure K) b ∈ A := by
    have he := congrArg WeierstrassCurve.a₃ hM
    simp only [map_a₃, source] at he
    exact he ▸ M.a₃.property
  have hbne : A.valuation (algebraMap K (AlgebraicClosure K) b) ≠ 1 := fun he =>
    hbad ((origin_smooth_iff_b_unit a b H Q hQ0 hQx hQy A M hM).mpr he)
  have hblt := lt_of_le_of_ne ((A.valuation_le_one_iff _).mpr hbmem) hbne
  have he : (source a b).map (algebraMap K (AlgebraicClosure K)) =
      source (algebraMap K (AlgebraicClosure K) a) (algebraMap K (AlgebraicClosure K) b) := by
    ext <;> simp [source]
  rw [he] at hc4
  have hunit := complement_unit_of_c4_unit A _ _ ha hblt hc4
  exact kernelModel_value_of_complement_unit a b H hcard Q hQ0 hQx hQy A.valuation hunit

end DkMath.Lib.NumberTheory.EllipticThreeKernelDiscriminant
