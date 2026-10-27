/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from blob ab1aee61bdcfbe439dcf9693d5f1417cacc05b6b,
P2M/Sol/S_WeierstrassCurve_inZeroComponentAt_veluCoord_iff_of_multiplicative.lean.
Modified: use DkMath critical centres, actual point map and arbitrary indexed half-kernels.
-/
import DkMath.Lib.NumberTheory.WeierstrassVeluNodalValuation
import DkMath.Lib.NumberTheory.EllipticFiniteKernelNodalInverse

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelNodalLevels"

/-!
# 特異核の節点距離と実際の商座標

[DkMath.Lib] 節点中心での Vélu の対補正を、源点と核点の中心からの距離へ展開する。
核の全ての水準を外れる点では補正和が小さく、一つの水準とだけ一致する点では
その項が支配する。水準の分離と中心誤差の深さは明示的な仮定として保持する。
-/
namespace DkMath.Lib.NumberTheory
open WeierstrassCurve WeierstrassCurve.Affine EllipticCriticalCentreAlgebra
open WeierstrassVeluPolynomial WeierstrassVeluPair WeierstrassVeluNodalValuation
open scoped BigOperators

/-- [DkMath.Lib] 節点中心の一次条件を使った反転対の補正分子。
曲線方程式と分母を払った恒等式であり、標数 2 と 3 でも成立する。 -/
theorem velu_pair_nodal_numerator {F : Type*} [Field F] (W : WeierstrassCurve F)
    {x₀ y₀ a b : F} (hFy : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0)
    (hFx : W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄) = 0)
    (hab : W.toAffine.Equation a b) (x : F) :
    momentT W a * (x - a) + (2 * b + W.a₁ * a + W.a₃) ^ 2 =
      (W.b₂ + 12 * x₀) * (a - x₀) * (x - x₀) + 6 * (a - x₀) ^ 2 * (x - x₀)
        - 2 * (a - x₀) ^ 3 - 4 * equationDefect W x₀ y₀ := by
  rw [equation_iff] at hab
  simp only [momentT, b₂, b₄, equationDefect]
  linear_combination 4 * hab + ((2 * y₀ + W.a₁ * x₀ + W.a₃) + 2 * W.a₁ * (a - x₀)) * hFy
    - 4 * (a - x₀) * hFx + (x - a) * (W.a₁ * hFy - 2 * hFx)

/-- [DkMath.Lib] 有限点と反転対の x 座標が異なる場合、Vélu 補正は節点距離による
正規化分数に等しい。中心誤差を省かずに記録する。 -/
theorem velu_pair_nodal_correction {F : Type*} [Field F] (W : WeierstrassCurve F)
    {x₀ y₀ a b x : F} (hFy : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0)
    (hFx : W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄) = 0)
    (hab : W.toAffine.Equation a b) (hne : x ≠ a) :
    xCorrection W a b x =
      ((W.b₂ + 12 * x₀) * (a - x₀) * (x - x₀) + 6 * (a - x₀) ^ 2 * (x - x₀)
        - 2 * (a - x₀) ^ 3 - 4 * equationDefect W x₀ y₀) / ((x - x₀) - (a - x₀)) ^ 2 := by
  have hn := velu_pair_nodal_numerator W hFy hFx hab x
  have hd : x - a ≠ 0 := sub_ne_zero.mpr hne
  simp only [xCorrection]
  rw [show (x - x₀) - (a - x₀) = x - a by ring, ← hn]
  field_simp

end DkMath.Lib.NumberTheory

namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open WeierstrassCurve WeierstrassCurve.Affine
open EllipticTorsionRepresentation EllipticCriticalCentre EllipticCriticalCentreAlgebra
open EllipticGoodReductionSeparation EllipticNodalReduction
open WeierstrassResidueModel ValuationResidue IsLocalRing
open WeierstrassVeluPair WeierstrassVeluNodalValuation
open scoped BigOperators
noncomputable local instance instDecidableEqEllipticFiniteKernelNodalLevels {α : Type*} : DecidableEq α :=
  Classical.decEq _
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
  (H : AddSubgroup (Points E)) [Fintype H] (A : ValuationSubring (AlgebraicClosure K))
  (C : CriticalCentre A (E.map (algebraMap K (AlgebraicClosure K))))
  (ho : Odd (Nat.card H)) (P : Points E) (hP : P ∉ H)

include hP in
omit [CharZero K] [E.IsElliptic] in
/-- [DkMath.Lib] 実点が核外にあれば、非零半核点の x 座標とは一致しない。
一致すれば曲線上でその点または反転点となり、同じ H に入ってしまう。 -/
theorem point_x_ne_halfKernel (Q : H) (hQ : Q ∈ halfKernel E H) : P.xc ≠ Q.val.xc := by
  intro he
  have hp0 : P ≠ 0 := fun hz => hP (hz ▸ H.zero_mem)
  have hq0 : Q.val ≠ 0 := fun hz => ((mem_halfKernel E H Q).mp hQ).1 (Subtype.ext hz)
  rcases point_eq_or_eq_neg_of_xc_eq E P Q.val hp0 hq0 he with hh | hh
  · exact hP (hh ▸ Q.property)
  · exact hP (hh ▸ H.neg_mem Q.property)

include ho in
omit [CharZero K] in
/-- [DkMath.Lib] 同じ半核による実商 x 座標を、節点距離で正規化した有限和に書き換える。
中心誤差と同じ一般ファイバーの実点・半核を保持する。 -/
theorem kernelXAt_eq_nodal_levels :
    kernelXAt E H P hP - C.x = (P.xc - C.x) + ∑ Q ∈ halfKernel E H,
      (((E.map (algebraMap K (AlgebraicClosure K))).b₂ + 12 * C.x) * (Q.val.xc - C.x) * (P.xc - C.x)
       + 6 * (Q.val.xc - C.x) ^ 2 * (P.xc - C.x) - 2 * (Q.val.xc - C.x) ^ 3
       - 4 * equationDefect (E.map (algebraMap K (AlgebraicClosure K))) C.x C.y) /
       ((P.xc - C.x) - (Q.val.xc - C.x)) ^ 2 := by
  rw [kernelXAt_half E H ho P hP (point_x_ne_halfKernel E H P hP)]
  have hh : (∑ Q ∈ halfKernel E H,
      xCorrection (E.map (algebraMap K (AlgebraicClosure K))) Q.val.xc Q.val.yc P.xc) =
    ∑ Q ∈ halfKernel E H,
      (((E.map (algebraMap K (AlgebraicClosure K))).b₂ + 12 * C.x) * (Q.val.xc - C.x) * (P.xc - C.x)
       + 6 * (Q.val.xc - C.x) ^ 2 * (P.xc - C.x) - 2 * (Q.val.xc - C.x) ^ 3
       - 4 * equationDefect (E.map (algebraMap K (AlgebraicClosure K))) C.x C.y) /
       ((P.xc - C.x) - (Q.val.xc - C.x)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro Q hQ
    have hq0 : Q.val ≠ 0 := fun hz => ((mem_halfKernel E H Q).mp hQ).1 (Subtype.ext hz)
    exact velu_pair_nodal_correction _ C.derivativeY C.derivativeX
      (Point.nonsingular_xc_yc hq0).1 (point_x_ne_halfKernel E H P hP Q hQ)
  rw [hh]
  ring

include ho in
omit [CharZero K] in
/-- [DkMath.Lib] 特異核の全水準を外れる節点近傍の点では、同じ実商 x も節点近傍にある。
各核水準と中心誤差の深さを仮定として保持し、まだその成立を主張しない。 -/
theorem kernelXAt_nodal_off_levels (hX : A.valuation (P.xc - C.x) < 1)
    (hk : ∀ Q ∈ halfKernel E H, A.valuation (Q.val.xc - C.x) < 1)
    (hne : ∀ Q ∈ halfKernel E H, A.valuation (P.xc - C.x) ≠ A.valuation (Q.val.xc - C.x))
    (hsh : ∀ Q ∈ halfKernel E H, A.valuation (4 * equationDefect
      (E.map (algebraMap K (AlgebraicClosure K))) C.x C.y) < A.valuation (Q.val.xc - C.x) ^ 2) :
    A.valuation (kernelXAt E H P hP - C.x) < 1 := by
  rw [kernelXAt_eq_nodal_levels E H A C ho P hP]
  refine A.valuation.map_add_lt hX ?_
  apply off_level_sum_lt_one A.valuation (halfKernel E H)
    ((E.map (algebraMap K (AlgebraicClosure K))).b₂ + 12 * C.x) (P.xc - C.x)
    (4 * equationDefect (E.map (algebraMap K (AlgebraicClosure K))) C.x C.y)
    (fun Q : H => Q.val.xc - C.x) C.node_unit
    ((A.valuation_le_one_iff _).mpr (ofNat_mem A 6))
    ((A.valuation_le_one_iff _).mpr (ofNat_mem A 2)) hX.le hk hne hsh

include ho in
omit [CharZero K] in
/-- [DkMath.Lib] 節点距離がちょうど一つの半核水準に一致すると、その水準の補正が
同じ実商 x の有限和を支配する。水準一意性・中心誤差の深さを明示する。 -/
theorem kernelXAt_nodal_unique_level (hX : A.valuation (P.xc - C.x) < 1)
    (hX0 : A.valuation (P.xc - C.x) ≠ 0)
    (hk : ∀ Q ∈ halfKernel E H, A.valuation (Q.val.xc - C.x) < 1)
    (j : H) (hj : j ∈ halfKernel E H)
    (heq : A.valuation (j.val.xc - C.x) = A.valuation (P.xc - C.x))
    (hne : ∀ Q ∈ halfKernel E H, Q ≠ j →
      A.valuation (P.xc - C.x) ≠ A.valuation (Q.val.xc - C.x))
    (hsh : ∀ Q ∈ halfKernel E H, A.valuation (4 * equationDefect
      (E.map (algebraMap K (AlgebraicClosure K))) C.x C.y) < A.valuation (Q.val.xc - C.x) ^ 2) :
    1 ≤ A.valuation (kernelXAt E H P hP - C.x) := by
  rw [kernelXAt_eq_nodal_levels E H A C ho P hP]
  apply unique_level_sum_ge_one A.valuation (halfKernel E H)
    ((E.map (algebraMap K (AlgebraicClosure K))).b₂ + 12 * C.x) (P.xc - C.x)
    (4 * equationDefect (E.map (algebraMap K (AlgebraicClosure K))) C.x C.y)
    (fun Q : H => Q.val.xc - C.x) j hj C.node_unit
    ((A.valuation_le_one_iff _).mpr (ofNat_mem A 6))
    ((A.valuation_le_one_iff _).mpr (ofNat_mem A 2)) hX hX0 hk heq hne hsh
  intro he
  exact point_x_ne_halfKernel E H P hP j hj (sub_eq_zero.mp (by linear_combination he))

variable (n : ℕ) (hkill : ∀ Q : H, n • Q.val = 0) (M : WeierstrassCurve A)
  (hM : M.map A.subtype = E.map (algebraMap K (AlgebraicClosure K)))
  (hn : A.valuation (n : AlgebraicClosure K) = 1) (T : CriticalCentre A (kernelModel E H))
  (hanchor : A.valuation (C.x - T.x) < 1)

include hkill hM hn ho T in
/-- [DkMath.Lib] 特異核側の源・標的の節点中心は合同する。
剰余モデルの一致と、節点以外の x 座標では曲線上の点が非特異であることを使う。
標的の臨界中心の存在自体はこの定理の入力である。 -/
theorem singular_nodal_centres_congr
    (hbad : ∀ Q : H, Q.val ≠ 0 → ¬ HasSmoothReduction M Q.val) :
    A.valuation (C.x - T.x) < 1 := by
  let U := valuationKernelModel E H n hkill A M hM hn
  let hU := valuationKernelModel_map E H n hkill A M hM hn ho
  have hc := CriticalCentre.residue_singular_of_model M hM C
  have ht := CriticalCentre.residue_singular_of_model U hU T
  rw [valuationKernelModel_residue_eq_of_not_smooth E H n hkill A M hM hn hbad] at ht
  have hnode : (M.map (residue A)).b₂ + 12 * residue A ⟨C.x, C.x_mem⟩ ≠ 0 := by
    let v : A := M.b₂ + 12 * (⟨C.x, C.x_mem⟩ : A)
    have hb : A.subtype M.b₂ = (E.map (algebraMap K (AlgebraicClosure K))).b₂ := by
      have he := congrArg WeierstrassCurve.b₂ hM
      simpa only [map_b₂] using he
    have hvco : (v : AlgebraicClosure K) = (E.map (algebraMap K (AlgebraicClosure K))).b₂ + 12 * C.x := by
      change A.subtype (M.b₂ + 12 * (⟨C.x, C.x_mem⟩ : A)) = _
      simp only [map_add, map_mul, map_ofNat]
      change A.subtype M.b₂ + 12 * C.x = _
      rw [hb]
    have hv : IsUnit v := (A.valuation_eq_one_iff _).mpr (hvco.symm ▸ C.node_unit)
    have hr := (residue_ne_zero_iff_isUnit v).mpr hv
    simpa only [v, map_add, map_mul, map_ofNat, map_b₂] using hr
  have he : residue A ⟨C.x, C.x_mem⟩ = residue A ⟨T.x, T.x_mem⟩ := by
    by_contra hne
    exact ht.2 (nonsingular_of_node_of_x_ne (M.map (residue A)) _ _ hc.1 hc.2 hnode ht.1 (Ne.symm hne))
  exact (ValuationSubring.mem_nonunits_iff _).mp
    ((residue_eq_residue_iff_sub_mem_nonunits A C.x_mem T.x_mem).mp he)

include ho hP T hanchor hkill hM hn in
/-- [DkMath.Lib] 核水準を全て外れる節点近傍点は、同じ商標的でも特異に還元する。
標的中心と源中心の合同、水準条件と誤差の深さを明示的に保持する。 -/
theorem oddKernelPointMap_nonsmooth_off_levels (hX : A.valuation (P.xc - C.x) < 1)
    (hk : ∀ Q ∈ halfKernel E H, A.valuation (Q.val.xc - C.x) < 1)
    (hne : ∀ Q ∈ halfKernel E H, A.valuation (P.xc - C.x) ≠ A.valuation (Q.val.xc - C.x))
    (hsh : ∀ Q ∈ halfKernel E H, A.valuation (4 * equationDefect
      (E.map (algebraMap K (AlgebraicClosure K))) C.x C.y) < A.valuation (Q.val.xc - C.x) ^ 2) :
    ¬ HasSmoothReduction (valuationKernelModel E H n hkill A M hM hn) (oddKernelPointMap E H ho P) := by
  let := kernelModel_isElliptic_of_odd_card E H ho
  have hc : A.valuation (kernelXAt E H P hP - T.x) < 1 :=
    (show A.valuation.Cong (kernelXAt E H P hP) C.x from
      kernelXAt_nodal_off_levels E H A C ho P hP hX hk hne hsh).trans hanchor
  rw [show oddKernelPointMap E H ho P = Point.some _ _ (kernelAt_nonsingular E H P hP) from
    kernelPointMap_of_not_mem E H P hP]
  exact (not_hasSmoothReduction_some_iff_of_model _ _
    (valuationKernelModel_map E H n hkill A M hM hn ho) T _).mpr hc

include ho hP T hanchor hkill hM hn in
/-- [DkMath.Lib] 一つの核水準にだけ一致する節点近傍点の商像は、標的で滑らかに還元する。
同じ半核と標的中心について、支配項の付値評価から結論する。 -/
theorem oddKernelPointMap_smooth_unique_level (hX : A.valuation (P.xc - C.x) < 1)
    (hX0 : A.valuation (P.xc - C.x) ≠ 0)
    (hk : ∀ Q ∈ halfKernel E H, A.valuation (Q.val.xc - C.x) < 1)
    (j : H) (hj : j ∈ halfKernel E H)
    (heq : A.valuation (j.val.xc - C.x) = A.valuation (P.xc - C.x))
    (hne : ∀ Q ∈ halfKernel E H, Q ≠ j →
      A.valuation (P.xc - C.x) ≠ A.valuation (Q.val.xc - C.x))
    (hsh : ∀ Q ∈ halfKernel E H, A.valuation (4 * equationDefect
      (E.map (algebraMap K (AlgebraicClosure K))) C.x C.y) < A.valuation (Q.val.xc - C.x) ^ 2) :
    HasSmoothReduction (valuationKernelModel E H n hkill A M hM hn) (oddKernelPointMap E H ho P) := by
  let := kernelModel_isElliptic_of_odd_card E H ho
  have hlarge := kernelXAt_nodal_unique_level E H A C ho P hP hX hX0 hk j hj heq hne hsh
  rw [show oddKernelPointMap E H ho P = Point.some _ _ (kernelAt_nonsingular E H P hP) from
    kernelPointMap_of_not_mem E H P hP]
  by_contra hnonsmooth
  have ht := (not_hasSmoothReduction_some_iff_of_model _ _
    (valuationKernelModel_map E H n hkill A M hM hn ho) T _).mp hnonsmooth
  have hc : A.valuation (kernelXAt E H P hP - C.x) < 1 :=
    (show A.valuation.Cong (kernelXAt E H P hP) T.x from ht).trans
      (show A.valuation.Cong C.x T.x from hanchor).symm
  exact (not_lt_of_ge hlarge) hc

include ho hP hkill hM hn T in
/-- [DkMath.Lib] 特異核側で、源点は特異だが商像は滑らかなら、源点の節点距離は
同じ半核の少なくとも一つの節点距離と同じ付値を持つ。
特異核点の中心合同と標的中心の合同は内部で供給する。中心誤差が各核距離の二乗より
小さいという深さ条件は明示し、この水準一致だけから零成分への移動は結論しない。 -/
theorem singular_smooth_implies_kernel_level
    (hbad : ∀ Q : H, Q.val ≠ 0 → ¬ HasSmoothReduction M Q.val)
    (hPbad : ¬ HasSmoothReduction M P)
    (hdeep : ∀ Q ∈ halfKernel E H, A.valuation (4 * equationDefect
      (E.map (algebraMap K (AlgebraicClosure K))) C.x C.y) < A.valuation (Q.val.xc - C.x) ^ 2)
    (himage : HasSmoothReduction (valuationKernelModel E H n hkill A M hM hn) (oddKernelPointMap E H ho P)) :
    ∃ Q ∈ halfKernel E H, A.valuation (P.xc - C.x) = A.valuation (Q.val.xc - C.x) := by
  have hX := (nonsmooth_coordinates_congr E A M hM C P hPbad).1
  have hk (Q : H) (hQ : Q ∈ halfKernel E H) : A.valuation (Q.val.xc - C.x) < 1 := by
    have hnz : Q.val ≠ 0 := fun he => ((mem_halfKernel E H Q).mp hQ).1 (Subtype.ext he)
    exact (nonsmooth_coordinates_congr E A M hM C Q.val (hbad Q hnz)).1
  have ha := singular_nodal_centres_congr E H A C ho n hkill M hM hn T hbad
  by_contra hnone
  have hne : ∀ Q ∈ halfKernel E H, A.valuation (P.xc - C.x) ≠ A.valuation (Q.val.xc - C.x) := by
    intro Q hQ he
    exact hnone ⟨Q, hQ, he⟩
  exact oddKernelPointMap_nonsmooth_off_levels E H A C ho P hP n hkill M hM hn T ha
    hX hk hne hdeep himage

include ho hP hkill hM hn T in
/-- [DkMath.Lib] 特異核の異なる半核点が互いに異なる節点距離を持ち、中心誤差が
それぞれの距離の二乗より小さいとき、源の特異な核外点の商像が滑らかであることは、
その点の距離が同じ半核の水準の一つに一致することと同値である。
水準の分離・深さは入力であり、対応する核点で平行移動した点の滑らかさはまだ結論しない。 -/
theorem singular_target_smooth_iff_kernel_level
    (hbad : ∀ Q : H, Q.val ≠ 0 → ¬ HasSmoothReduction M Q.val)
    (hPbad : ¬ HasSmoothReduction M P)
    (hdeep : ∀ Q ∈ halfKernel E H, A.valuation (4 * equationDefect
      (E.map (algebraMap K (AlgebraicClosure K))) C.x C.y) < A.valuation (Q.val.xc - C.x) ^ 2)
    (hsep : ∀ Q ∈ halfKernel E H, ∀ R ∈ halfKernel E H, Q ≠ R →
      A.valuation (Q.val.xc - C.x) ≠ A.valuation (R.val.xc - C.x)) :
    HasSmoothReduction (valuationKernelModel E H n hkill A M hM hn) (oddKernelPointMap E H ho P) ↔
      ∃ Q ∈ halfKernel E H, A.valuation (P.xc - C.x) = A.valuation (Q.val.xc - C.x) := by
  constructor
  · exact singular_smooth_implies_kernel_level E H A C ho P hP n hkill M hM hn T hbad hPbad hdeep
  · rintro ⟨j, hj, heq⟩
    have hX := (nonsmooth_coordinates_congr E A M hM C P hPbad).1
    have hX0 : A.valuation (P.xc - C.x) ≠ 0 := by
      intro hz
      have hh := hdeep j hj
      rw [← heq, hz, zero_pow two_ne_zero] at hh
      exact not_lt_zero hh
    have hk (Q : H) (hQ : Q ∈ halfKernel E H) : A.valuation (Q.val.xc - C.x) < 1 := by
      have hnz : Q.val ≠ 0 := fun he => ((mem_halfKernel E H Q).mp hQ).1 (Subtype.ext he)
      exact (nonsmooth_coordinates_congr E A M hM C Q.val (hbad Q hnz)).1
    have hne (Q : H) (hQ : Q ∈ halfKernel E H) (hQj : Q ≠ j) :
        A.valuation (P.xc - C.x) ≠ A.valuation (Q.val.xc - C.x) := by
      rw [heq]
      exact hsep j hj Q hQ (Ne.symm hQj)
    have ha := singular_nodal_centres_congr E H A C ho n hkill M hM hn T hbad
    exact oddKernelPointMap_smooth_unique_level E H A C ho P hP n hkill M hM hn T ha
      hX hX0 hk j hj heq.symm hne hdeep

include ho hP hkill hM hn T in
/-- [DkMath.Lib] 3点核では半核は一点なので、水準分離を外部に仮定する必要がない。
特異核の深さ条件の下、源の特異な核外点の商像が滑らかであることは、
同じ半核の水準との一致に等しい。 -/
theorem singular_three_target_smooth_iff_kernel_level (hcard : Nat.card H = 3)
    (hbad : ∀ Q : H, Q.val ≠ 0 → ¬ HasSmoothReduction M Q.val)
    (hPbad : ¬ HasSmoothReduction M P)
    (hdeep : ∀ Q ∈ halfKernel E H, A.valuation (4 * equationDefect
      (E.map (algebraMap K (AlgebraicClosure K))) C.x C.y) < A.valuation (Q.val.xc - C.x) ^ 2) :
    HasSmoothReduction (valuationKernelModel E H n hkill A M hM hn) (oddKernelPointMap E H ho P) ↔
      ∃ Q ∈ halfKernel E H, A.valuation (P.xc - C.x) = A.valuation (Q.val.xc - C.x) := by
  apply singular_target_smooth_iff_kernel_level E H A C ho P hP n hkill M hM hn T hbad hPbad hdeep
  intro Q hQ R hR hne
  have hc : (halfKernel E H).card ≤ 1 := by
    have hh := card_halfKernel E H ho
    rw [hcard] at hh
    omega
  exact (hne ((Finset.card_le_one_iff.mp hc) hQ hR)).elim

include C ho hkill hM hn in
/-- [DkMath.Lib] 特異核側で、同じ核点 Q を引いた源点が滑らかなら、元の点の商像も滑らか。
商準同型が Q を零に送ることと前向き零成分輸送を使う。P が H の点である場合も含む。 -/
theorem singular_target_smooth_of_kernel_translate
    (hbad : ∀ Q : H, Q.val ≠ 0 → ¬ HasSmoothReduction M Q.val)
    (Q : H) (hs : HasSmoothReduction M (P - Q.val)) :
    HasSmoothReduction (valuationKernelModel E H n hkill A M hM hn) (oddKernelPointMap E H ho P) := by
  let := kernelModel_isElliptic_of_odd_card E H ho
  have ht := oddKernelPointMap_smooth_of_not_smooth_kernel E H A M hM C n hkill hn ho hbad (P - Q.val) hs
  have he : oddKernelPointMap E H ho (P - Q.val) = oddKernelPointMap E H ho P := by
    change oddKernelPointHom E H ho (P - Q.val) = oddKernelPointHom E H ho P
    rw [map_sub, show oddKernelPointHom E H ho Q.val = 0 from kernelPointMap_of_mem E H Q.val Q.property,
      sub_zero]
  rwa [he] at ht

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
