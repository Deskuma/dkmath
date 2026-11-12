/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelGoodReduction
import DkMath.Lib.NumberTheory.EllipticFiniteKernelHom
import DkMath.Lib.NumberTheory.WeierstrassVeluFormal

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelFormal"

/-!
# 同じ実点商写像は無限遠近傍を保つ

[DkMath.Lib] 一般点の公式だけで止めず、実点Pの正規化和を同じ半核の有理式へ変換する。
整な核座標と非整なx(P)から全分母の非零性を供給し、同じ商写像のx付値保存を得る。
この像は同じ付値環標的で滑らかに還元し、還元像はOとなる。
この章だけで、整座標を持つ零成分の全点を扱ったとはしない。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open EllipticTorsionRepresentation WeierstrassVeluPair EllipticGoodReductionSeparation
open EllipticSmoothReduction WeierstrassVariableChange
open scoped BigOperators
noncomputable local instance instDecidableEqEllipticFiniteKernelFormal {α : Type*} : DecidableEq α :=
  Classical.decEq _
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]

omit [CharZero K] [E.IsElliptic] in
private theorem point_pair_x (P Q : Points E) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hx : P.xc ≠ Q.xc) :
    (P + Q).xc + (P + -Q).xc - 2 * Q.xc =
      xCorrection (E.map (algebraMap K (AlgebraicClosure K))) Q.xc Q.yc P.xc := by
  rcases P with _ | ⟨x,y,h⟩
  · exact (hP rfl).elim
  rcases Q with _ | ⟨a,b,ha⟩
  · exact (hQ rfl).elim
  change x ≠ a at hx
  erw [Point.neg_some, Point.add_of_X_ne hx, Point.add_of_X_ne hx]
  simp only [Point.xc_some, Point.yc_some, slope_of_X_ne hx]
  exact secant_pair_x _ hx h.1 ha.1

omit [CharZero K] in
/-- [DkMath.Lib] 同じ実点の特殊化x値の半核表示。分母非零の条件を実点で明記する。 -/
theorem kernelXAt_half (H : AddSubgroup (Points E)) [Fintype H] (ho : Odd (Nat.card H))
    (P : Points E) (hP : P ∉ H)
    (hx : ∀ Q ∈ halfKernel E H, P.xc ≠ Q.val.xc) :
    kernelXAt E H P hP = P.xc + ∑ Q ∈ halfKernel E H,
      xCorrection (E.map (algebraMap K (AlgebraicClosure K))) Q.val.xc Q.val.yc P.xc := by
  rw [kernelXAt_eq_sum]
  rw [← Finset.sum_sub_distrib, sum_kernel_half E H ho]
  have h0 : (P + (0 : H).val).xc - (0 : H).val.xc = P.xc := by
    change (P + 0).xc - 0 = P.xc
    rw [add_zero, sub_zero]
  rw [h0]
  congr 1
  apply Finset.sum_congr rfl
  intro Q hQ
  have hQ0 : Q.val ≠ 0 := fun he => (mem_halfKernel E H Q).mp hQ |>.1 <| Subtype.ext he
  have hn : (-Q.val).xc = Q.val.xc := by cases Q.val <;> rfl
  simp only [AddSubgroup.coe_neg, hn]
  have hp := point_pair_x E P Q.val (fun he => hP (he ▸ H.zero_mem)) hQ0 (hx Q hQ)
  linear_combination hp

variable (H : AddSubgroup (Points E)) [Fintype H] (n : ℕ) (hkill : ∀ Q : H, n • Q.val = 0)
  (A : ValuationSubring (AlgebraicClosure K)) (M : WeierstrassCurve A)
  (hM : M.map A.subtype = E.map (algebraMap K (AlgebraicClosure K)))
  (hn : A.valuation (n : AlgebraicClosure K) = 1)

include n hkill M hM hn

omit [Fintype H] [E.IsElliptic] in
/-- [DkMath.Lib] 非整なx座標の点は同じ単元位数核に属さない。Oもこの枝には入らない。 -/
theorem not_mem_kernel_of_x_not_mem (P : Points E) (hx : P.xc ∉ A) : P ∉ H := by
  intro hP
  exact hx (kernel_coordinates_mem E H n hkill A M hM hn ⟨P,hP⟩).1

/-- [DkMath.Lib] 無限遠近傍で同じ特殊化X_Hの付値はx(P)の付値と正確に一致する。 -/
theorem kernelXAt_value_of_x_not_mem (ho : Odd (Nat.card H))
    (P : Points E) (hx : P.xc ∉ A) :
    A.valuation (kernelXAt E H P (not_mem_kernel_of_x_not_mem E H n hkill A M hM hn P hx)) =
      A.valuation P.xc := by
  have hP := not_mem_kernel_of_x_not_mem E H n hkill A M hM hn P hx
  have hxy := kernel_coordinates_mem E H n hkill A M hM hn
  have hne (Q : H) : P.xc ≠ Q.val.xc := fun he => hx (he ▸ (hxy Q).1)
  rw [kernelXAt_half E H ho P hP (fun Q _ => hne Q), ← hM]
  exact WeierstrassVeluFormal.x_value_eq A M (halfKernel E H)
    (fun Q => ⟨Q.val.xc,(hxy Q).1⟩) (fun Q => ⟨Q.val.yc,(hxy Q).2⟩)
    (lt_of_not_ge (fun hh => hx ((A.valuation_le_one_iff _).mp hh)))

/-- [DkMath.Lib] 同じ全点写像は非整なx座標を保つ。従ってその像の還元は無限遠となる。 -/
theorem oddKernelPointMap_x_not_mem (ho : Odd (Nat.card H))
    (P : Points E) (hx : P.xc ∉ A) : (oddKernelPointMap E H ho P).xc ∉ A := by
  let := kernelModel_isElliptic_of_odd_card E H ho
  have hP := not_mem_kernel_of_x_not_mem E H n hkill A M hM hn P hx
  have he : oddKernelPointMap E H ho P = Point.some _ _ (kernelAt_nonsingular E H P hP) :=
    kernelPointMap_of_not_mem E H P hP
  rw [he, Point.xc_some]
  intro hi
  have hv := kernelXAt_value_of_x_not_mem E H n hkill A M hM hn ho P hx
  exact hx ((A.valuation_le_one_iff _).mp (hv ▸ (A.valuation_le_one_iff _).mpr hi))

/-- [DkMath.Lib] 無限遠近傍の像は、同じ付値環標的で滑らかに還元する。還元型の制限は不要。 -/
theorem oddKernelPointMap_smooth_of_x_not_mem (ho : Odd (Nat.card H))
    (P : Points E) (hx : P.xc ∉ A) :
    HasSmoothReduction (valuationKernelModel E H n hkill A M hM hn) (oddKernelPointMap E H ho P) := by
  let := kernelModel_isElliptic_of_odd_card E H ho
  have hP := not_mem_kernel_of_x_not_mem E H n hkill A M hM hn P hx
  rw [show oddKernelPointMap E H ho P = Point.some _ _ (kernelAt_nonsingular E H P hP) from
    kernelPointMap_of_not_mem E H P hP]
  apply hasSmoothReduction_of_notMem
  simpa only [show oddKernelPointMap E H ho P = Point.some _ _ (kernelAt_nonsingular E H P hP) from
    kernelPointMap_of_not_mem E H P hP, Point.xc_some] using
    oddKernelPointMap_x_not_mem E H n hkill A M hM hn ho P hx

/-- [DkMath.Lib] 同じ無限遠近傍の像は、実際の還元関数でもOへ写る。
滑らかさだけで止めず、同じ付値環標的へのモデル輸送を含める。 -/
theorem oddKernelPointMap_reduce_zero_of_x_not_mem (ho : Odd (Nat.card H))
    (P : Points E) (hx : P.xc ∉ A) :
    reducePointSmooth (valuationKernelModel E H n hkill A M hM hn)
      (pointEquivOfModelEq (valuationKernelModel_map E H n hkill A M hM hn ho).symm
        (oddKernelPointMap E H ho P)) = 0 := by
  let := kernelModel_isElliptic_of_odd_card E H ho
  have hP := not_mem_kernel_of_x_not_mem E H n hkill A M hM hn P hx
  have he : oddKernelPointMap E H ho P = Point.some _ _ (kernelAt_nonsingular E H P hP) :=
    kernelPointMap_of_not_mem E H P hP
  rw [he, pointEquivOfModelEq_some]
  apply reducePointSmooth_some_of_notMem
  simpa only [he, Point.xc_some] using oddKernelPointMap_x_not_mem E H n hkill A M hM hn ho P hx

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
