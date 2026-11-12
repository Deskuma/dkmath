/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelNonsingular
import DkMath.Lib.NumberTheory.EllipticTorsionAllCard
import DkMathTest.Lib.NumberTheory.EllipticFiniteKernelPoles

#print "file: DkMathTest.Lib.NumberTheory.EllipticFiniteKernelNonsingular"

/-!
同じ実曲線y²=x³−xの全3捩れ核E[3]を使う。位数9の奇数核に対し、
標的Δ≠0・三つの2捩れ像の分離・K係数モデルの楕円性・全点零ファイバーを確認する。
素数位数や巡回生成元を追加入力しない。従来の二元核では奇数条件が失敗することも確認する。
-/
namespace EllipticFiniteKernelNonsingularTest
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open EllipticFiniteKernelTest EllipticFiniteKernelPolesTest
noncomputable section
local instance : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _
local instance : DecidableEq (Points curve) := Classical.decEq _
local instance : curve.IsElliptic := ⟨by rw [curve_discriminant]; norm_num⟩

/-- 同じ幾何学的実点群内の全3捩れ部分群。 -/
def fullThreeKernel : AddSubgroup (Points curve) := torsionGroup curve 3

local instance : Fintype fullThreeKernel := by
  let := finite_torsion_of_ne_zero curve 3 (by decide)
  exact Fintype.ofFinite (Torsion curve 3)

/-- この核は実際に9点を持ち、奇数条件を内部供給する。 -/
theorem fullThree_card : Nat.card fullThreeKernel = 9 ∧ Odd (Nat.card fullThreeKernel) := by
  have h : Nat.card fullThreeKernel = 9 := by
    change Nat.card (Torsion curve 3) = 9
    simpa using card_torsion_sq curve 3 (by decide)
  exact ⟨h, h ▸ (by decide : Odd 9)⟩

/-- 三根分離providerや標的IsEllipticなしで、同じ9点核の標的Δ≠0を得る。 -/
theorem actual_target_discriminant : (kernelModel curve fullThreeKernel).Δ ≠ 0 :=
  kernelModel_discriminant_ne_zero_of_odd_card curve fullThreeKernel fullThree_card.2

/-- 9点核の同じ有理式の分子分母最大次数も9となる。 -/
theorem actual_rational_degree :
    ∃ r : RatFunc (AlgebraicClosure ℚ), max r.num.natDegree r.denom.natDegree = 9 ∧
      veluX curve fullThreeKernel = Polynomial.aeval (EllipticFunctionField.genericX curve (AlgebraicClosure ℚ)) r.num /
        Polynomial.aeval (EllipticFunctionField.genericX curve (AlgebraicClosure ℚ)) r.denom := by
  simpa only [fullThree_card.1] using exists_veluX_rational curve fullThreeKernel

/-- 同じ9点核の有限ファイバーは、相異なるx座標を高々9個しか持たない。 -/
theorem actual_fiber_bound (c : AlgebraicClosure ℚ) (T : Finset (AlgebraicClosure ℚ))
    (hT : ∀ a ∈ T, ∃ (P : Points curve) (hP : P ∉ fullThreeKernel),
      P.xc = a ∧ kernelXAt curve fullThreeKernel P hP = c) : T.card ≤ 9 := by
  simpa only [fullThree_card.1] using card_veluX_fiber_le curve fullThreeKernel c T hT

/-- 同じ実曲線の三つの非零反転固定点と、互いに異なる三つの標的x値を実際に得る。 -/
theorem actual_three_separated_images :
    ∃ (P : Fin 3 → Points curve) (hout : ∀ i, P i ∉ fullThreeKernel),
      (∀ i, P i ≠ 0 ∧ -P i = P i) ∧
      Function.Injective (fun i => kernelXAt curve fullThreeKernel (P i) (hout i)) := by
  obtain ⟨P, hP, hn, hinj⟩ := exists_three_nonzero_fixed_points curve
  have hout (i : Fin 3) : P i ∉ fullThreeKernel := fun h =>
    hP i (eq_zero_of_mem_odd_kernel_fixed curve fullThreeKernel fullThree_card.2 _ h (hn i))
  refine ⟨P, hout, fun i => ⟨hP i, hn i⟩, ?_⟩
  intro i j he
  apply hinj
  exact kernelXAt_injective_on_twoTorsion curve fullThreeKernel fullThree_card.2 _ _
    (hn i) (hn j) (hout i) (hout j) he

/-- 同じ9点核は係数ガロア作用で安定する。個々の3捩れ点の有理性は仮定しない。 -/
theorem fullThree_stable : ∀ σ P, P ∈ fullThreeKernel → pointAction curve σ P ∈ fullThreeKernel := by
  intro σ P hP
  change 3 • pointAction curve σ P = 0
  have hkill : 3 • P = 0 := hP
  rw [← map_nsmul, hkill, map_zero]

/-- 同じ核から降下したℚ係数モデルは、実際に楕円曲線となる。 -/
theorem actual_rational_target_elliptic :
    (descendedKernelModel curve fullThreeKernel fullThree_stable).IsElliptic :=
  descendedKernelModel_isElliptic_of_odd_card curve fullThreeKernel fullThree_card.2 fullThree_stable

/-- 全点関数の正確な零ファイバー。標的楕円性の追加インスタンスは入力しない。 -/
theorem actual_zero_fiber (P : Points curve) :
    oddKernelPointMap curve fullThreeKernel fullThree_card.2 P = 0 ↔ P ∈ fullThreeKernel :=
  oddKernelPointMap_eq_zero_iff curve fullThreeKernel fullThree_card.2 P

/-- 奇数核全点関数のH軌道不変性も、同じ位数9の核で検査する。 -/
theorem actual_orbit (P : Points curve) (Q : fullThreeKernel) :
    oddKernelPointMap curve fullThreeKernel fullThree_card.2 (P + Q.val) =
      oddKernelPointMap curve fullThreeKernel fullThree_card.2 P :=
  oddKernelPointMap_translation curve fullThreeKernel fullThree_card.2 P Q

local instance : Fintype kernel := Fintype.ofFinset {0, Q} (fun P => by simp [kernel])

/-- 従来の二元核には今回の奇数条件を供給できない。標的が特異という結論ではない。 -/
theorem even_kernel_guard : ¬Odd (Nat.card kernel) := by rw [degree_two.1]; decide

end
end EllipticFiniteKernelNonsingularTest
