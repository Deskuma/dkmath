/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelVeluEquation
import DkMath.Lib.NumberTheory.WeierstrassResidueModel
import DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelReduction"

/-!
# 同じ有限核の付値環モデルと、特異点へ落ちる核の還元比較

[DkMath.Lib] 同じ整な核座標を付値環の元として包み、半核の多項式係数モデルを構成する。
一般ファイバーが既存kernelModelに一致することと、剰余が同じ座標の多項式構成となることを証明する。
全ての非零核点が滑らかに還元しない場合、各モーメントは剰余で零となるので、
源と商の剰余モデルが完全に一致する。これは付値の零/単元条件を運ぶが、Δの深さの一致ではない。
滑らかな核の商での還元型は別の未解決部分である。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open EllipticTorsionRepresentation WeierstrassVeluPolynomial WeierstrassResidueModel
open EllipticGoodReductionSeparation
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
noncomputable local instance instDecidableEqEllipticFiniteKernelReduction {α : Type*} : DecidableEq α := Classical.decEq _
variable (H : AddSubgroup (Points E)) [Fintype H] (n : ℕ) (hkill : ∀ Q : H, n • Q.val = 0)
  (A : ValuationSubring (AlgebraicClosure K)) (M : WeierstrassCurve A)
  (hM : M.map A.subtype = E.map (algebraMap K (AlgebraicClosure K)))
  (hn : A.valuation (n : AlgebraicClosure K) = 1)

/-- [DkMath.Lib] 同じ半核の実座標を同じ付値環に入れて構成したモデル。
整座標の供給は同じn捩れ条件から行い、新しい座標や核を選ばない。 -/
noncomputable def valuationKernelModel : WeierstrassCurve A :=
  polynomialModel M (halfKernel E H)
    (fun Q => ⟨Q.val.xc, (kernel_coordinates_mem E H n hkill A M hM hn Q).1⟩)
    (fun Q => ⟨Q.val.yc, (kernel_coordinates_mem E H n hkill A M hM hn Q).2⟩)

/-- [DkMath.Lib] この付値環モデルの一般ファイバーは既存の同じkernelModel。奇数性はここで使う。 -/
theorem valuationKernelModel_map (ho : Odd (Nat.card H)) :
    (valuationKernelModel E H n hkill A M hM hn).map A.subtype = kernelModel E H := by
  unfold valuationKernelModel
  rw [polynomialModel_map, hM]
  exact halfKernelPolynomialModel_eq_kernelModel E H ho

omit [E.IsElliptic] in
/-- [DkMath.Lib] 同じ整な核座標の剰余を添字ごとに保ち、係数構成と剰余を可換にする。
異なる核点が同じ特異点へ還元しても、添字を潰さない。 -/
theorem valuationKernelModel_residue :
    (valuationKernelModel E H n hkill A M hM hn).map (residue A) =
      polynomialModel (M.map (residue A)) (halfKernel E H)
        (fun Q => residue A ⟨Q.val.xc, (kernel_coordinates_mem E H n hkill A M hM hn Q).1⟩)
        (fun Q => residue A ⟨Q.val.yc, (kernel_coordinates_mem E H n hkill A M hM hn Q).2⟩) :=
  polynomialModel_residue _ _ _ _ _

omit [E.IsElliptic] [Fintype H] in
/-- [DkMath.Lib] 同じ非零核点の滑らかさは、内部供給した同じ整座標の剰余で判定できる。 -/
theorem kernelPoint_smooth_iff_residue (Q : H) (hQ : Q.val ≠ 0) :
    HasSmoothReduction M Q.val ↔ (M.map (residue A)).toAffine.Nonsingular
      (residue A ⟨Q.val.xc, (kernel_coordinates_mem E H n hkill A M hM hn Q).1⟩)
      (residue A ⟨Q.val.yc, (kernel_coordinates_mem E H n hkill A M hM hn Q).2⟩) := by
  have heq : HasSmoothReduction M Q.val = HasSmoothReduction M
      (Point.some Q.val.xc Q.val.yc (Point.nonsingular_xc_yc hQ)) :=
    congrArg (fun P : (E.toAffine⁄(AlgebraicClosure K)).Point => HasSmoothReduction M P)
      (Point.eq_some_xc_yc hQ)
  rw [heq, hasSmoothReduction_some_iff]
  exact ⟨fun h => h _ _, fun h _ _ => h⟩

omit [E.IsElliptic] in
/-- [DkMath.Lib] 非零核点が全て滑らかに還元しない場合、同じ源と商の剰余モデルは一致する。
Oは半核に含めず、便宜座標(0,0)を特異点として扱わない。 -/
theorem valuationKernelModel_residue_eq_of_not_smooth
    (hbad : ∀ Q : H, Q.val ≠ 0 → ¬ HasSmoothReduction M Q.val) :
    (valuationKernelModel E H n hkill A M hM hn).map (residue A) = M.map (residue A) := by
  apply polynomialModel_residue_eq_of_singular
  intro Q hQ
  have hQ0 : Q.val ≠ 0 := fun he => (mem_halfKernel E H Q).mp hQ |>.1 <| Subtype.ext he
  have he : (M.map A.subtype).toAffine.Equation Q.val.xc Q.val.yc :=
    hM ▸ (Point.nonsingular_xc_yc hQ0).1
  refine ⟨equation_residue M he, ?_⟩
  intro hs
  apply hbad Q hQ0
  rw [Point.eq_some_xc_yc hQ0]
  apply (hasSmoothReduction_some_iff M _).mpr
  intro _ _
  exact hs

include n hkill hM hn in
/-- [DkMath.Lib] 特異核側では、源と既存商のΔの非単元性・c₄の単元性が正確に対応する。
数値的な付値の等号や最小性へは、この定理だけでは進まない。 -/
theorem kernelModel_invariant_conditions_of_not_smooth (ho : Odd (Nat.card H))
    (hbad : ∀ Q : H, Q.val ≠ 0 → ¬ HasSmoothReduction M Q.val) :
    (A.valuation (kernelModel E H).Δ < 1 ↔
      A.valuation (E.map (algebraMap K (AlgebraicClosure K))).Δ < 1) ∧
    (A.valuation (kernelModel E H).c₄ = 1 ↔
      A.valuation (E.map (algebraMap K (AlgebraicClosure K))).c₄ = 1) := by
  have hi := invariant_conditions_iff A _ M
    (valuationKernelModel_residue_eq_of_not_smooth E H n hkill A M hM hn hbad)
  have hd := congrArg WeierstrassCurve.Δ (valuationKernelModel_map E H n hkill A M hM hn ho)
  have hc := congrArg WeierstrassCurve.c₄ (valuationKernelModel_map E H n hkill A M hM hn ho)
  have hsd := congrArg WeierstrassCurve.Δ hM
  have hsc := congrArg WeierstrassCurve.c₄ hM
  simp only [map_Δ] at hd hsd
  simp only [map_c₄] at hc hsc
  simp only [map_Δ, map_c₄]
  rw [← hd, ← hc, ← hsd, ← hsc]
  exact hi

include n hkill hM hn in
/-- [DkMath.Lib] 240が非単元の場所では、核の滑らかさに依らず既存商のc₄単元性を保つ。 -/
theorem kernelModel_c4_value_one_of_small_240 (ho : Odd (Nat.card H))
    (h240 : A.valuation (240 : AlgebraicClosure K) < 1)
    (hc : A.valuation (E.map (algebraMap K (AlgebraicClosure K))).c₄ = 1) :
    A.valuation (kernelModel E H).c₄ = 1 := by
  have hsrc : A.valuation (M.c₄ : AlgebraicClosure K) = 1 := by
    have he := congrArg WeierstrassCurve.c₄ hM
    rw [map_c₄] at he
    rwa [← he] at hc
  have ht := polynomialModel_c4_value_one A M (halfKernel E H)
    (fun Q => ⟨Q.val.xc, (kernel_coordinates_mem E H n hkill A M hM hn Q).1⟩)
    (fun Q => ⟨Q.val.yc, (kernel_coordinates_mem E H n hkill A M hM hn Q).2⟩) h240 hsrc
  have he := congrArg WeierstrassCurve.c₄ (valuationKernelModel_map E H n hkill A M hM hn ho)
  rw [map_c₄] at he
  rw [← he]
  exact ht

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
