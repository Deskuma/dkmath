/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelZeroComponent
import DkMath.Lib.NumberTheory.WeierstrassModelReduction

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelCollision"

/-!
# 還元像が核と衝突する点を、同じ商写像で無限遠へ送る

[DkMath.Lib] 零成分の二点P,Qが同じ点へ還元すれば、P−Qは還元核に入る。
Qが実際の有限核Hにあれば商準同型はPとP−Qで一致する。
既存の無限遠近傍保存から、元のPの像も滑らかで剰余ではOとなる。
これにより、有限座標の分母が単元でなくなる衝突点を別の曲線へ置き換えずに扱う。
全核の滑らかさや源の還元型は要求しない。非衝突の整点はこの章の範囲外である。
-/
namespace DkMath.Lib.NumberTheory
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open EllipticGoodReductionSeparation EllipticSmoothReduction WeierstrassVariableChange
noncomputable local instance instDecidableEqEllipticFiniteKernelCollision {α : Type*} : DecidableEq α :=
  Classical.decEq _

namespace WeierstrassModelReduction
variable {L : Type*} [Field L] [DecidableEq L] (A : ValuationSubring L)
  (M : WeierstrassCurve A) (V : WeierstrassCurve L) (hM : M.map A.subtype = V)

include hM in
/-- [DkMath.Lib] 指定モデルの一般ファイバーで、滑らかな還元を持つ点は加法で閉じる。 -/
theorem smooth_add_of_model {P Q : V.toAffine.Point}
    (hP : HasSmoothReduction M P) (hQ : HasSmoothReduction M Q) :
    HasSmoothReduction M (P + Q) := by
  subst V
  exact (smooth_add_and_reduce M hP hQ).1

/-- [DkMath.Lib] 滑らかな二点の和と、指定モデルでの実際の還元が可換。 -/
theorem modelReduce_add {P Q : V.toAffine.Point}
    (hP : HasSmoothReduction M P) (hQ : HasSmoothReduction M Q) :
    modelReduce A M V hM (P + Q) = modelReduce A M V hM P + modelReduce A M V hM Q := by
  subst V
  exact (smooth_add_and_reduce M hP hQ).2

/-- [DkMath.Lib] 滑らかな二点の差と、指定モデルでの実際の還元が可換。 -/
theorem modelReduce_sub {P Q : V.toAffine.Point}
    (hP : HasSmoothReduction M P) (hQ : HasSmoothReduction M Q) :
    modelReduce A M V hM (P - Q) = modelReduce A M V hM P - modelReduce A M V hM Q := by
  subst V
  change reducePointSmooth M (P - Q) = reducePointSmooth M P - reducePointSmooth M Q
  exact map_sub (zeroComponentReduction M) (⟨P, hP⟩ : zeroComponentSubgroup M) ⟨Q, hQ⟩

/-- [DkMath.Lib] 滑らかな還元を持つ点がOへ還元する条件は、Oまたはx非整である。
特異点を便宜的にOへ送る全域還元関数なので、滑らかさの仮定を保持する。 -/
theorem modelReduce_eq_zero_iff {P : V.toAffine.Point} (hP : HasSmoothReduction M P) :
    modelReduce A M V hM P = 0 ↔ P = 0 ∨ P.xc ∉ A := by
  subst V
  cases P with
  | zero => exact ⟨fun _ => Or.inl rfl, fun _ => modelReduce_zero _ _ _ _⟩
  | some x y h =>
    by_cases hx : x ∈ A
    · have hy := EllipticTorsionValuationIntegrality.y_mem_of_x_mem A M _ rfl h.1 hx
      have hs := (hasSmoothReduction_some_iff M h).mp hP hx hy
      rw [modelReduce_some A M _ rfl h hx hs]
      simp only [Point.some_ne_zero, Point.xc_some, hx, not_true_eq_false, or_self]
    · rw [modelReduce_some_not_mem A M _ rfl h hx]
      simp only [Point.xc_some, hx, not_false_eq_true, or_true]

end WeierstrassModelReduction

namespace EllipticFiniteKernel
open EllipticTorsionRepresentation WeierstrassModelReduction
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
  (H : AddSubgroup (Points E)) [Fintype H] (n : ℕ) (hkill : ∀ Q : H, n • Q.val = 0)
  (A : ValuationSubring (AlgebraicClosure K)) (M : WeierstrassCurve A)
  (hM : M.map A.subtype = E.map (algebraMap K (AlgebraicClosure K)))
  (hn : A.valuation (n : AlgebraicClosure K) = 1)

/-- [DkMath.Lib] 源でOへ還元する全滑らかな点の同じ商像は、滑らかでOへ還元する。
非整点の定理にOを加え、モデル輸送を実際の還元関数に保持する。 -/
theorem oddKernelPointMap_of_reduce_zero (ho : Odd (Nat.card H)) (P : Points E)
    (hP : HasSmoothReduction M P)
    (hr : modelReduce A M _ hM P = 0) :
    HasSmoothReduction (valuationKernelModel E H n hkill A M hM hn) (oddKernelPointMap E H ho P) ∧
      modelReduce A (valuationKernelModel E H n hkill A M hM hn) (kernelModel E H)
        (valuationKernelModel_map E H n hkill A M hM hn ho) (oddKernelPointMap E H ho P) = 0 := by
  let := kernelModel_isElliptic_of_odd_card E H ho
  rcases (modelReduce_eq_zero_iff A M _ hM hP).mp hr with hz | hx
  · subst P
    change HasSmoothReduction _ (oddKernelPointHom E H ho (0 : Points E)) ∧
      modelReduce A _ (kernelModel E H) _ (oddKernelPointHom E H ho (0 : Points E)) = 0
    rw [map_zero]
    exact ⟨hasSmoothReduction_zero _ _, modelReduce_zero _ _ _ _⟩
  · exact ⟨oddKernelPointMap_smooth_of_x_not_mem E H n hkill A M hM hn ho P hx,
      oddKernelPointMap_reduce_zero_of_x_not_mem E H n hkill A M hM hn ho P hx⟩

/-- [DkMath.Lib] 同じ実核点Qと同じ点へ還元する零成分点Pは、同じ商で滑らかにOへ還元する。
P自体が核にある場合も含む。衝突分母を展開せず、P−Qの還元核所属で解消する。 -/
theorem oddKernelPointMap_of_reduction_collision (ho : Odd (Nat.card H))
    (P : Points E) (Q : H) (hP : HasSmoothReduction M P) (hQ : HasSmoothReduction M Q.val)
    (hr : modelReduce A M _ hM P = modelReduce A M _ hM Q.val) :
    HasSmoothReduction (valuationKernelModel E H n hkill A M hM hn) (oddKernelPointMap E H ho P) ∧
      modelReduce A (valuationKernelModel E H n hkill A M hM hn) (kernelModel E H)
        (valuationKernelModel_map E H n hkill A M hM hn ho) (oddKernelPointMap E H ho P) = 0 := by
  let := kernelModel_isElliptic_of_odd_card E H ho
  have hs := smooth_sub_of_model A M _ hM hP hQ
  have hd : modelReduce A M _ hM (P - Q.val) = 0 := by
    exact (modelReduce_sub A M _ hM hP hQ).trans (sub_eq_zero.mpr hr)
  have hi := oddKernelPointMap_of_reduce_zero E H n hkill A M hM hn ho (P - Q.val) hs hd
  have he : oddKernelPointMap E H ho (P - Q.val) = oddKernelPointMap E H ho P := by
    change oddKernelPointHom E H ho (P - Q.val) = oddKernelPointHom E H ho P
    rw [map_sub, show oddKernelPointHom E H ho Q.val = 0 from
      kernelPointMap_of_mem E H Q.val Q.property, sub_zero]
  rwa [he] at hi

end EllipticFiniteKernel
end DkMath.Lib.NumberTheory
