/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelSmoothReduction
import DkMath.Lib.NumberTheory.WeierstrassFiniteKernelModel

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelGoodReduction"

/-!
# 良い奇素数住所で、同じ有限核の商も良還元を持つ

[DkMath.Lib] 良還元では全核点が滑らかに還元する。単元位数捩れの還元は単射なので、
同じ核の同じ半集合による剰余モデルへ非特異性定理を適用できる。
既存の付値環標的・kernelModelとの同一性を保ち、判別式の単元性を供給する。
良還元の場所では全像点の滑らかさも得るが、悪い場所での零成分輸送とは区別する。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open EllipticTorsionRepresentation EllipticGoodReductionSeparation WeierstrassResidueModel
open WeierstrassVariableChange
noncomputable local instance instDecidableEqEllipticFiniteKernelGoodReduction {α : Type*} : DecidableEq α :=
  Classical.decEq _

/-- [DkMath.Lib] 同じ一般ファイバーと等しい任意のモデル上で、良還元なら全点が滑らか。
モデルの等式による輸送を明示し、別の点を選ばない。 -/
theorem hasSmoothReduction_of_good_of_model {L : Type*} [Field L]
    (A : ValuationSubring L) (M : WeierstrassCurve A) (V : WeierstrassCurve L)
    (hM : M.map A.subtype = V) (hgood : (M.map (residue A)).Δ ≠ 0) (P : V.toAffine.Point) :
    HasSmoothReduction M P :=
  (smooth_pointEquiv_of_model A M V hM P).mp
    (hasSmoothReduction_of_good M hgood (pointEquivOfModelEq hM.symm P))

variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
  (H : AddSubgroup (Points E)) [Fintype H] (n : ℕ) (hkill : ∀ Q : H, n • Q.val = 0)
  (A : ValuationSubring (AlgebraicClosure K)) (M : WeierstrassCurve A)
  (hM : M.map A.subtype = E.map (algebraMap K (AlgebraicClosure K)))
  (hn : A.valuation (n : AlgebraicClosure K) = 1)

omit [E.IsElliptic] in
/-- [DkMath.Lib] 良い剰余曲線と同じ奇数有限核から、同じ付値環標的の剰余のΔ≠0を得る。
2非零は剰余体で要求する。源の標数0だけで剰余標数2を除外したことにはしない。 -/
theorem valuationKernelModel_good_discriminant [NeZero (2 : ResidueField A)]
    (ho : Odd (Nat.card H)) (hgood : (M.map (residue A)).Δ ≠ 0) :
    ((valuationKernelModel E H n hkill A M hM hn).map (residue A)).Δ ≠ 0 := by
  let : (M.map (residue A)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hgood⟩
  have hs (Q : H) : HasSmoothReduction M Q.val :=
    hasSmoothReduction_of_good_of_model A M _ hM hgood Q.val
  rw [valuationKernelModel_residue_of_smooth E H A M hM hs n hkill hn]
  exact WeierstrassFiniteKernelModel.polynomialModel_discriminant_ne_zero _
    (smoothKernelReduction E H A M hM hs) (smoothKernelReduction_injective E H A M hM hs n hkill hn)
    ho (halfKernel E H) (halfKernel_partition E H ho)

omit [E.IsElliptic] in
/-- [DkMath.Lib] 同じ付値環標的の判別式は単元。数値的なΔの付値1を直接供給する。 -/
theorem valuationKernelModel_good_value_one [NeZero (2 : ResidueField A)]
    (ho : Odd (Nat.card H)) (hgood : (M.map (residue A)).Δ ≠ 0) :
    A.valuation ((valuationKernelModel E H n hkill A M hM hn).Δ : AlgebraicClosure K) = 1 := by
  apply (residue_ne_zero_iff A _).mp
  rw [← map_Δ]
  exact valuationKernelModel_good_discriminant E H n hkill A M hM hn ho hgood

include n hkill hM hn in
/-- [DkMath.Lib] 同じ既存kernelModelの判別式も同じ良い奇素数住所で付値1を持つ。 -/
theorem kernelModel_good_value_one [NeZero (2 : ResidueField A)]
    (ho : Odd (Nat.card H)) (hgood : (M.map (residue A)).Δ ≠ 0) :
    A.valuation (kernelModel E H).Δ = 1 := by
  have hd := congrArg WeierstrassCurve.Δ (valuationKernelModel_map E H n hkill A M hM hn ho)
  rw [map_Δ] at hd
  rw [← hd]
  exact valuationKernelModel_good_value_one E H n hkill A M hM hn ho hgood

/-- [DkMath.Lib] 良還元の場所では、同じ既存点写像の全像点が同じ付値環標的で滑らかに還元する。
悪い場所の零成分輸送や、還元準同型との可換性までは結論に含めない。 -/
theorem oddKernelPointMap_smooth_of_good [NeZero (2 : ResidueField A)]
    (ho : Odd (Nat.card H)) (hgood : (M.map (residue A)).Δ ≠ 0) (P : Points E) :
    HasSmoothReduction (valuationKernelModel E H n hkill A M hM hn) (oddKernelPointMap E H ho P) :=
  hasSmoothReduction_of_good_of_model A _ _ (valuationKernelModel_map E H n hkill A M hM hn ho)
    (valuationKernelModel_good_discriminant E H n hkill A M hM hn ho hgood) _

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
