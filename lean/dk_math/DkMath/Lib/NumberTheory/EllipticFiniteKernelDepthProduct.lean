/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/
import DkMath.Lib.NumberTheory.EllipticFiniteKernelSingularInverse

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelDepthProduct"

/-!
# 特異な奇素数核の節点水準と判別式の深さ

[DkMath.Lib] 半核の実点の節点距離を比較し、同水準なら二枝の和差が滑らかになる。
特異核ではその和差も同じ核なので、異なる半核点の水準は重ならない。
奇数捩れ点の深さ定理と組み合わせ、判別式積の付値側を構成する。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open WeierstrassCurve WeierstrassCurve.Affine
open EllipticTorsionRepresentation EllipticGoodReductionSeparation
open EllipticCriticalCentre EllipticCriticalCentreAlgebra EllipticTangentDirections
open EllipticTorsionDepth EllipticCriticalDepth
open scoped BigOperators
noncomputable local instance instDecidableEqEllipticFiniteKernelDepthProduct {α : Type*} : DecidableEq α := Classical.decEq _

variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
  (H : AddSubgroup (Points E)) [Fintype H] (p : ℕ) [Fact p.Prime]
  (hcard : Nat.card H = p) (hp2 : p ≠ 2) (hkill : ∀ Q : H, p • Q.val = 0)
  (A : ValuationSubring (AlgebraicClosure K)) (M : WeierstrassCurve A)
  (hM : M.map A.subtype = E.map (algebraMap K (AlgebraicClosure K)))
  (hp : A.valuation (p : AlgebraicClosure K) = 1)
  (C : CriticalCentre A (E.map (algebraMap K (AlgebraicClosure K)))) (D : TangentDirections C)
  (hbad : ∀ Q : H, Q.val ≠ 0 → ¬ HasSmoothReduction M Q.val)

include hp2 hkill hM hp D hbad in
omit [E.IsElliptic] in
/-- [DkMath.Lib] 特異な同じ奇素数核の半核では、異なる二点の節点距離の付値は異なる。
同水準なら二点の差か和が滑らかに還元するが、その差・和は同じ核にある。
特異核条件からその点はOなので、元の二点は等しいか反転対となり、半核の選択に反する。 -/
theorem singular_half_levels_injective {Q R : H} (hQ : Q ∈ halfKernel E H) (hR : R ∈ halfKernel E H)
    (heq : A.valuation (Q.val.xc - C.x) = A.valuation (R.val.xc - C.x)) : Q = R := by
  have hQ0 : Q.val ≠ 0 := fun hz => ((mem_halfKernel E H Q).mp hQ).1 (Subtype.ext hz)
  have hR0 : R.val ≠ 0 := fun hz => ((mem_halfKernel E H R).mp hR).1 (Subtype.ext hz)
  have hQx := (nonsmooth_coordinates_congr E A M hM C Q.val (hbad Q hQ0)).1
  have hRx := (nonsmooth_coordinates_congr E A M hM C R.val (hbad R hR0)).1
  have hsh := singular_kernel_shallow E H p hp2 hkill A M hM hp C D hbad Q hQ0
  rcases same_level_sub_or_add_smooth E A M hM C D Q.val R.val hQ0 hR0 hQx hRx heq hsh with hs | hs
  · have hz : (Q - R : H).val = 0 := by
      by_contra hn
      exact hbad (Q - R) hn hs
    exact sub_eq_zero.mp (Subtype.ext hz)
  · have hz : (Q + R : H).val = 0 := by
      by_contra hn
      exact hbad (Q + R) hn hs
    have he : Q = -R := eq_neg_of_add_eq_zero_left (Subtype.ext hz)
    exact ((neg_not_mem_halfKernel E H R hR) (he ▸ hQ)).elim

include hp2 hkill hM hp D hbad in
omit [E.IsElliptic] in
/-- [DkMath.Lib] 特異核の各半核点の節点距離は、同じ判別式の付値の p 分の j 乗に対応する。
j の範囲を 1 ≤ j ≤ p/2 に揃え、離散付値や根の選択に依存しない冪等式で表す。 -/
theorem singular_half_depth_exponent (Q : H) (hQ : Q ∈ halfKernel E H) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ p / 2 ∧
      A.valuation (Q.val.xc - C.x) ^ p = A.valuation (E.map (algebraMap K (AlgebraicClosure K))).Δ ^ j := by
  have hQ0 : Q.val ≠ 0 := fun hz => ((mem_halfKernel E H Q).mp hQ).1 (Subtype.ext hz)
  have hx := (nonsmooth_coordinates_congr E A M hM C Q.val (hbad Q hQ0)).1
  have hns := Point.nonsingular_xc_yc hQ0
  have he := Point.eq_some_xc_yc hQ0
  have ht : p • Point.some Q.val.xc Q.val.yc hns = 0 := by
    rw [← he]
    exact hkill Q
  obtain ⟨_, j, hj, hjp, hd⟩ := odd_torsion_depth_of_model M _ hM C D
    ((Fact.out : p.Prime).odd_of_ne_two hp2) (by have := (Fact.out : p.Prime).two_le; omega) hp hns ht hx
  refine ⟨j, hj, ?_, ?_⟩
  · omega
  · rwa [C.defect_valuation] at hd

include hp2 hkill hM hp D hbad in
/-- [DkMath.Lib] 同じ半核点の深さを、0 から p/2−1 までの有限番号に記録する。
内部で選ぶ j は深さ定理に由来し、後で番号が半核を重複なく列挙すると証明する。 -/
noncomputable def singularHalfDepthIndex (Q : halfKernel E H) : Fin (p / 2) := by
  let j := Classical.choose (singular_half_depth_exponent E H p hp2 hkill A M hM hp C D hbad Q.val Q.property)
  have hj := Classical.choose_spec (singular_half_depth_exponent E H p hp2 hkill A M hM hp C D hbad Q.val Q.property)
  exact ⟨j - 1, by omega⟩

include hp2 hkill hM hp D hbad in
omit [E.IsElliptic] in
/-- [DkMath.Lib] 半核の深さ番号に対応する冪関係。番号は j−1 なので指数は番号+1。 -/
theorem singularHalfDepthIndex_spec (Q : halfKernel E H) :
    A.valuation (Q.val.val.xc - C.x) ^ p =
      A.valuation (E.map (algebraMap K (AlgebraicClosure K))).Δ ^
        ((singularHalfDepthIndex E H p hp2 hkill A M hM hp C D hbad Q).val + 1) := by
  have hj := Classical.choose_spec (singular_half_depth_exponent E H p hp2 hkill A M hM hp C D hbad Q.val Q.property)
  change _ = _ ^ (Classical.choose (singular_half_depth_exponent E H p hp2 hkill A M hM hp C D hbad Q.val Q.property) - 1 + 1)
  rw [Nat.sub_add_cancel hj.1]
  exact hj.2.2

include hp2 hkill hM hp D hbad in
omit [E.IsElliptic] in
/-- [DkMath.Lib] 半核の深さ番号は単射。同じ番号なら節点距離の p 乗が等しく、
距離も等しいため、同じ特異核の枝比較で点が一致する。 -/
theorem singularHalfDepthIndex_injective :
    Function.Injective (singularHalfDepthIndex E H p hp2 hkill A M hM hp C D hbad) := by
  intro Q R he
  apply Subtype.ext
  apply singular_half_levels_injective E H p hp2 hkill A M hM hp C D hbad Q.property R.property
  have hq := singularHalfDepthIndex_spec E H p hp2 hkill A M hM hp C D hbad Q
  have hr := singularHalfDepthIndex_spec E H p hp2 hkill A M hM hp C D hbad R
  have hidx := congrArg Fin.val he
  rw [hidx] at hq
  have hpowers := hq.trans hr.symm
  exact (pow_left_inj₀ zero_le zero_le (Fact.out : p.Prime).ne_zero).mp hpowers

include hcard hp2 hkill hM hp D hbad in
omit [E.IsElliptic] in
/-- [DkMath.Lib] 特異核の半核の深さ番号は 0,…,p/2−1 をちょうど一度ずつ取る。
半核の点数と深さ番号の単射性から有限集合の全射性を得る。 -/
theorem singularHalfDepthIndex_bijective :
    Function.Bijective (singularHalfDepthIndex E H p hp2 hkill A M hM hp C D hbad) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨singularHalfDepthIndex_injective E H p hp2 hkill A M hM hp C D hbad, ?_⟩
  rw [Fintype.card_coe, Fintype.card_fin]
  have ho : Odd (Nat.card H) := hcard ▸ (Fact.out : p.Prime).odd_of_ne_two hp2
  have hc := card_halfKernel E H ho
  rw [hcard] at hc
  have hpodd := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hnum := Nat.two_mul_div_two_add_one_of_odd hpodd
  omega

include hp2 hkill hM hp D hbad in
omit [E.IsElliptic] in
/-- [DkMath.Lib] 同じ特異半核点の接線分母の平方の付値は節点距離の付値の平方に等しい。
源の節点中心と同じ実点の浅さを使用し、標数2の剰余も扱う。 -/
theorem singular_half_tangent_square_value (Q : H) (hQ : Q ∈ halfKernel E H) :
    A.valuation (2 * Q.val.yc + (E.map (algebraMap K (AlgebraicClosure K))).a₁ * Q.val.xc +
      (E.map (algebraMap K (AlgebraicClosure K))).a₃) ^ 2 =
      A.valuation (Q.val.xc - C.x) ^ 2 := by
  have hQ0 : Q.val ≠ 0 := fun hz => ((mem_halfKernel E H Q).mp hQ).1 (Subtype.ext hz)
  have hx := (nonsmooth_coordinates_congr E A M hM C Q.val (hbad Q hQ0)).1
  have hsh := singular_kernel_shallow E H p hp2 hkill A M hM hp C D hbad Q hQ0
  have hn := shallow_denominator_valuation C (Point.nonsingular_xc_yc hQ0).1 hx hsh
  exact congrArg (fun x => x ^ 2) hn

include hcard hp2 hkill hM hp D hbad in
omit [E.IsElliptic] in
/-- [DkMath.Lib] 奇素数位数の特異核の半核では、接線分母の平方の積について
その付値の p 乗が、源判別式の付値の `(p/2)*(p/2+1)` 乗に等しい。
各点の深さ指数を重複なく列挙して得る。一般の商判別式積公式は別途必要。 -/
theorem singular_half_tangent_product_value :
    (∏ Q : halfKernel E H, A.valuation (2 * Q.val.val.yc +
      (E.map (algebraMap K (AlgebraicClosure K))).a₁ * Q.val.val.xc +
      (E.map (algebraMap K (AlgebraicClosure K))).a₃) ^ 2) ^ p =
      A.valuation (E.map (algebraMap K (AlgebraicClosure K))).Δ ^ ((p / 2) * (p / 2 + 1)) := by
  let n := p / 2
  let ix := singularHalfDepthIndex E H p hp2 hkill A M hM hp C D hbad
  let e : (halfKernel E H) ≃ Fin n := Equiv.ofBijective ix
    (singularHalfDepthIndex_bijective E H p hcard hp2 hkill A M hM hp C D hbad)
  have hsum : (∑ Q : halfKernel E H, ((ix Q).val + 1) * 2) = n * (n + 1) := by
    have hr : (∑ i : Fin n, (i.val + 1) * 2) = n * (n + 1) := by
      rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (i + 1) * 2) n]
      have hs : (∑ i ∈ Finset.range n, (i + 1)) = ∑ i ∈ Finset.range (n + 1), i := by
        rw [Finset.sum_range_succ']
        simp
      rw [← Finset.sum_mul, hs, Finset.sum_range_id_mul_two]
      simp [Nat.mul_comm]
    calc
      _ = ∑ i : Fin n, (i.val + 1) * 2 := e.sum_comp (fun i => (i.val + 1) * 2)
      _ = n * (n + 1) := hr
  rw [← Finset.prod_pow]
  calc
    _ = ∏ Q : halfKernel E H,
        A.valuation (E.map (algebraMap K (AlgebraicClosure K))).Δ ^ (((ix Q).val + 1) * 2) := by
          apply Finset.prod_congr rfl
          intro Q _
          rw [singular_half_tangent_square_value E H p hp2 hkill A M hM hp C D hbad Q.val Q.property,
            ← pow_mul, Nat.mul_comm 2 p, pow_mul,
            singularHalfDepthIndex_spec E H p hp2 hkill A M hM hp C D hbad Q, ← pow_mul]
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum, hsum]

include hcard hp2 hkill hM hp D hbad in
/-- [DkMath.Lib] 一般の判別式積公式が同じ商標的と半核について成立すれば、
特異核側の源判別式の値は商判別式の値の p 乗に等しい。
積公式そのものはこの定理の仮定であり、内部では証明していない。 -/
theorem singular_discriminant_value_of_product_identity
    (hprod : (kernelModel E H).Δ *
      (∏ Q : halfKernel E H, (2 * Q.val.val.yc +
        (E.map (algebraMap K (AlgebraicClosure K))).a₁ * Q.val.val.xc +
        (E.map (algebraMap K (AlgebraicClosure K))).a₃) ^ 2) ^ 4 =
      (E.map (algebraMap K (AlgebraicClosure K))).Δ ^ p) :
    A.valuation (kernelModel E H).Δ ^ p =
      A.valuation (E.map (algebraMap K (AlgebraicClosure K))).Δ := by
  let δ := A.valuation (E.map (algebraMap K (AlgebraicClosure K))).Δ
  let υ := A.valuation (kernelModel E H).Δ
  let n := p / 2
  let u := ∏ Q : halfKernel E H, (2 * Q.val.val.yc +
    (E.map (algebraMap K (AlgebraicClosure K))).a₁ * Q.val.val.xc +
    (E.map (algebraMap K (AlgebraicClosure K))).a₃) ^ 2
  have hδ : δ ≠ 0 := by
    change A.valuation (E.map (algebraMap K (AlgebraicClosure K))).Δ ≠ 0
    rw [← C.defect_valuation]
    exact (Valuation.ne_zero_iff _).mpr C.defect_ne_zero
  have hu : A.valuation u ^ p = δ ^ (n * (n + 1)) := by
    dsimp [u, δ, n]
    rw [map_prod]
    simp only [map_pow]
    exact singular_half_tangent_product_value E H p hcard hp2 hkill A M hM hp C D hbad
  have hv : υ * A.valuation u ^ 4 = δ ^ p := by
    have he := congrArg A.valuation hprod
    simpa only [map_mul, map_pow] using he
  have hodd := Nat.two_mul_div_two_add_one_of_odd ((Fact.out : p.Prime).odd_of_ne_two hp2)
  have hnat : p ^ 2 = 4 * (n * (n + 1)) + 1 := by
    dsimp [n]
    nlinarith
  have hh := congrArg (fun x => x ^ p) hv
  rw [mul_pow, ← pow_mul (A.valuation u) 4 p, Nat.mul_comm 4 p,
    pow_mul, hu, ← pow_mul, ← pow_mul] at hh
  have he : p * p = (n * (n + 1)) * 4 + 1 := by nlinarith [hnat]
  rw [he, pow_add, pow_one] at hh
  apply mul_right_cancel₀ (pow_ne_zero _ hδ)
  simpa only [mul_comm] using hh

end DkMath.Lib.NumberTheory.EllipticFiniteKernel

namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open EllipticTorsionRepresentation EllipticGoodReductionSeparation EllipticSmoothReduction
open WeierstrassResidueModel
open scoped BigOperators
noncomputable local instance instDecidableEqEllipticFiniteKernelSmoothDepth {α : Type*} : DecidableEq α := Classical.decEq _

/-- [DkMath.Lib] 有限点で接線分母が零なら、その点は反転で固定される。
剰余標数2も含め、分母2で割らない。 -/
theorem point_neg_eq_of_tangent_zero {F : Type*} [Field F] (W : WeierstrassCurve F)
    (P : W.toAffine.Point) (hP : P ≠ 0)
    (h : 2 * P.yc + W.a₁ * P.xc + W.a₃ = 0) : -P = P := by
  cases P with
  | zero => exact (hP rfl).elim
  | some x y hy =>
    change 2 * y + W.a₁ * x + W.a₃ = 0 at h
    rw [Point.neg_some]
    rw [Point.some.injEq]
    constructor
    · rfl
    · dsimp only [negY]
      linear_combination -h

variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
  (H : AddSubgroup (Points E)) [Fintype H] (n : ℕ)
  (hkill : ∀ Q : H, n • Q.val = 0) (A : ValuationSubring (AlgebraicClosure K))
  (M : WeierstrassCurve A) (hM : M.map A.subtype = E.map (algebraMap K (AlgebraicClosure K)))
  (hn : A.valuation (n : AlgebraicClosure K) = 1)
  (ho : Odd (Nat.card H)) (hs : ∀ Q : H, HasSmoothReduction M Q.val)

include n hkill M hM hn ho hs in
omit [E.IsElliptic] [Fintype H] in
/-- [DkMath.Lib] 滑らかな奇数核の非零点では、実際の接線分母は付値環の単元である。
還元された接線分母が零なら点は反転固定となり、核の単射な還元と奇数位数に矛盾する。 -/
theorem smooth_kernel_tangent_value_one (Q : H) (hQ : Q ≠ 0) :
    A.valuation (2 * Q.val.yc + (E.map (algebraMap K (AlgebraicClosure K))).a₁ * Q.val.xc +
      (E.map (algebraMap K (AlgebraicClosure K))).a₃) = 1 := by
  let x : A := ⟨Q.val.xc, (kernel_coordinates_mem E H n hkill A M hM hn Q).1⟩
  let y : A := ⟨Q.val.yc, (kernel_coordinates_mem E H n hkill A M hM hn Q).2⟩
  let t : A := 2 * y + M.a₁ * x + M.a₃
  have hcoeff1 := congrArg WeierstrassCurve.a₁ hM
  have hcoeff3 := congrArg WeierstrassCurve.a₃ hM
  simp only [map_a₁, map_a₃] at hcoeff1 hcoeff3
  have ht : (t : AlgebraicClosure K) = 2 * Q.val.yc +
      (E.map (algebraMap K (AlgebraicClosure K))).a₁ * Q.val.xc +
      (E.map (algebraMap K (AlgebraicClosure K))).a₃ := by
    change A.subtype (2 * y + M.a₁ * x + M.a₃) = _
    simp only [map_add, map_mul, map_ofNat, hcoeff1, hcoeff3]
    rfl
  rw [← ht, ← residue_ne_zero_iff A t]
  intro hzero
  let f := smoothKernelReduction E H A M hM hs
  let R := f Q
  have hR : R ≠ 0 := by
    intro hz
    apply hQ
    apply (smoothKernelReduction_injective E H A M hM hs n hkill hn)
    simpa only [map_zero] using hz
  have hcoords := smoothKernelReduction_coordinates E H A M hM hs n hkill hn Q
  have htan : 2 * R.yc + (M.map (residue A)).a₁ * R.xc + (M.map (residue A)).a₃ = 0 := by
    change 2 * (f Q).yc + (M.map (residue A)).a₁ * (f Q).xc + (M.map (residue A)).a₃ = 0
    rw [hcoords.1, hcoords.2]
    change 2 * residue A y + residue A M.a₁ * residue A x + residue A M.a₃ = 0
    change residue A (2 * y + M.a₁ * x + M.a₃) = 0 at hzero
    simpa only [map_add, map_mul, map_ofNat] using hzero
  have hfix := point_neg_eq_of_tangent_zero (M.map (residue A)) R hR htan
  have he : -Q = Q := by
    apply (smoothKernelReduction_injective E H A M hM hs n hkill hn)
    simpa only [map_neg] using hfix
  exact neg_ne_self_of_odd_kernel E H ho Q hQ he

include n hkill M hM hn ho hs in
omit [E.IsElliptic] in
/-- [DkMath.Lib] 滑らかな奇数核の同じ半核では、接線分母の平方の積は付値1。
各点の単元性を積にまとめ、剰余標数が2の場合も含む。 -/
theorem smooth_half_tangent_product_value_one :
    A.valuation (∏ Q : halfKernel E H, (2 * Q.val.val.yc +
      (E.map (algebraMap K (AlgebraicClosure K))).a₁ * Q.val.val.xc +
      (E.map (algebraMap K (AlgebraicClosure K))).a₃) ^ 2) = 1 := by
  rw [map_prod]
  apply Finset.prod_eq_one
  intro Q _
  rw [map_pow, smooth_kernel_tangent_value_one E H n hkill A M hM hn ho hs Q.val
    ((mem_halfKernel E H Q.val).mp Q.property).1, one_pow]

include n hkill M hM hn ho hs in
/-- [DkMath.Lib] 同じ商と半核について判別式積公式を仮定すると、滑らかな核側では
商判別式の付値は源判別式の `(Nat.card H)` 乗に等しい。
一般の判別式積公式そのものは、この定理の入力として保持する。 -/
theorem smooth_discriminant_value_of_product_identity
    (hprod : (kernelModel E H).Δ *
      (∏ Q : halfKernel E H, (2 * Q.val.val.yc +
        (E.map (algebraMap K (AlgebraicClosure K))).a₁ * Q.val.val.xc +
        (E.map (algebraMap K (AlgebraicClosure K))).a₃) ^ 2) ^ 4 =
      (E.map (algebraMap K (AlgebraicClosure K))).Δ ^ Nat.card H) :
    A.valuation (kernelModel E H).Δ =
      A.valuation (E.map (algebraMap K (AlgebraicClosure K))).Δ ^ Nat.card H := by
  have hv := congrArg A.valuation hprod
  rw [map_mul, map_pow, map_pow,
    smooth_half_tangent_product_value_one E H n hkill A M hM hn ho hs, one_pow, mul_one] at hv
  exact hv

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
