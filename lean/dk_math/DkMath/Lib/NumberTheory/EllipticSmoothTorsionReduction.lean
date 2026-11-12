/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticSmoothReduction
import Mathlib.Data.Set.Card

#print "file: DkMath.Lib.NumberTheory.EllipticSmoothTorsionReduction"

/-!
# NOTE-032-003B: 零成分上の単元位数torsionを単射に還元する

[DkMath.Lib] 還元が無限遠となる滑らかなn捩れ点は、nが付値環の単元なら零点である。
有限点の両座標は既存の捩れ整性から付値環へ入るため、有限滑らかな剰余点が得られる。
これが無限遠へ還元することはない。

次に還元が一致する二点の差を取る。零成分上の還元は加法準同型なので差は還元核へ入り、
同じn倍で消える。従って差は零である。良還元や剰余判別式の非零性は要求しない。
位数の比較は、この単射性と剰余torsionの有限性を得た後で適用する。
-/
namespace DkMath.Lib.NumberTheory.EllipticSmoothTorsionReduction
open WeierstrassCurve IsLocalRing EllipticGoodReductionSeparation EllipticSmoothReduction
variable {L : Type*} [Field L] [CharZero L] [DecidableEq L]
    {A : ValuationSubring L} (W : WeierstrassCurve A)

/-- [DkMath.Lib] 単元位数の滑らかな捩れ点が無限遠へ還元すれば、元の点も零である。
有限点の捩れ整性と、その滑らかな還元の有限性を使い、E₁の非零捩れを排除する。 -/
theorem eq_zero_of_reduce_eq_zero {n : ℕ} (hn : A.valuation (n : L) = 1)
    {P : (W.map A.subtype).toAffine.Point} (hP : HasSmoothReduction W P)
    (hkill : n • P = 0) (hred : reducePointSmooth W P = 0) : P = 0 := by
  cases P with
  | zero => rfl
  | some x y h =>
    have hx := EllipticTorsionValuationIntegrality.torsion_x_mem A W _ rfl hn h hkill
    have hy := EllipticTorsionValuationIntegrality.y_mem_of_x_mem A W _ rfl h.1 hx
    have hns := (hasSmoothReduction_some_iff W h).mp hP hx hy
    rw [reducePointSmooth_some_of_mem W h hx hns] at hred
    exact (Affine.Point.some_ne_zero hns hred).elim

/-- [DkMath.Lib] 零成分のn捩れ上の還元は、nが単元なら単射である。
両点の差を同じ零成分部分群で計算し、還元の加法性を使って零点判定へ戻す。 -/
theorem reduce_injOn_torsion {n : ℕ} (hn : A.valuation (n : L) = 1) :
    Set.InjOn (reducePointSmooth W)
      {P : (W.map A.subtype).toAffine.Point | HasSmoothReduction W P ∧ n • P = 0} := by
  classical
  intro P hP Q hQ heq
  let P₀ : zeroComponentSubgroup W := ⟨P, hP.1⟩
  let Q₀ : zeroComponentSubgroup W := ⟨Q, hQ.1⟩
  have hdiff : HasSmoothReduction W (P - Q) := (P₀ - Q₀).property
  have hred : reducePointSmooth W (P - Q) = 0 := by
    have he := map_sub (zeroComponentReduction W) P₀ Q₀
    change reducePointSmooth W (P - Q) = reducePointSmooth W P - reducePointSmooth W Q at he
    rw [he, heq, sub_self]
  apply sub_eq_zero.mp
  exact eq_zero_of_reduce_eq_zero W hn hdiff (by rw [nsmul_sub, hP.2, hQ.2, sub_self]) hred

variable [DecidableEq (ResidueField A)]

/-- [DkMath.Lib] 剰余n捩れの有限上界を、滑らかな一般ファイバーのn捩れへ輸送する。
有限性を明示してからncardを比較し、無限集合のncard=0という既定値に頼らない。 -/
theorem finite_and_ncard_le_of_residue_bound {n b : ℕ} (hn : A.valuation (n : L) = 1)
    (hfinite : {P : (W.map (residue A)).toAffine.Point | n • P = 0}.Finite)
    (hbound : {P : (W.map (residue A)).toAffine.Point | n • P = 0}.ncard ≤ b) :
    {P : (W.map A.subtype).toAffine.Point | HasSmoothReduction W P ∧ n • P = 0}.Finite ∧
      {P : (W.map A.subtype).toAffine.Point | HasSmoothReduction W P ∧ n • P = 0}.ncard ≤ b := by
  let S : Set (W.map A.subtype).toAffine.Point := {P | HasSmoothReduction W P ∧ n • P = 0}
  let T : Set (W.map (residue A)).toAffine.Point := {P | n • P = 0}
  have himage : reducePointSmooth W '' S ⊆ T := by
    rintro _ ⟨P, hP, rfl⟩
    exact nsmul_reduce_eq_zero W hP.1 n hP.2
  have hinj : Set.InjOn (reducePointSmooth W) S := reduce_injOn_torsion W hn
  refine ⟨Set.Finite.of_finite_image (hfinite.subset himage) hinj, ?_⟩
  calc S.ncard = (reducePointSmooth W '' S).ncard := hinj.ncard_image.symm
    _ ≤ T.ncard := Set.ncard_le_ncard himage hfinite
    _ ≤ b := hbound

end DkMath.Lib.NumberTheory.EllipticSmoothTorsionReduction
