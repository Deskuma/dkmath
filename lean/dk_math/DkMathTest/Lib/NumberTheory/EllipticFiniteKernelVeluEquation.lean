/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelVeluEquation
import DkMathTest.Lib.NumberTheory.EllipticFiniteKernelLocalIntegrality
import DkMathTest.Lib.NumberTheory.EllipticFiniteKernelSpecialization

#print "file: DkMathTest.Lib.NumberTheory.EllipticFiniteKernelVeluEquation"

/-!
位数9の非巡回核で同じ候補方程式と標的同一性を確認する。
さらにy²+y=x³の実際の3点核から、既存kernelModelがy²+y=x³−7になることを計算する。
偶数核へ奇数核の半核式を流用できない境界も検査する。
-/
namespace EllipticFiniteKernelVeluEquationTest
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open EllipticFunctionField WeierstrassVeluPolynomial
open EllipticFiniteKernelTest EllipticFiniteKernelNonsingularTest
noncomputable section
local instance {α : Type*} : DecidableEq α := Classical.decEq _
local instance : curve.IsElliptic := ⟨by rw [curve_discriminant]; norm_num⟩
local instance : Fintype fullThreeKernel := by
  let := finite_torsion_of_ne_zero curve 3 (by decide)
  exact Fintype.ofFinite (Torsion curve 3)

/-- 同じ非巡回9点核でも、方程式providerなしで既存標的と明示的候補が一致する。 -/
theorem actual_nine_point_model : halfKernelPolynomialModel curve fullThreeKernel =
    kernelModel curve fullThreeKernel :=
  halfKernelPolynomialModel_eq_kernelModel curve fullThreeKernel fullThree_card.2

/-- 同じ非巡回核の残差は実際に零。全点正則というだけの結論ではない。 -/
theorem actual_nine_point_defect : halfKernelPolynomialDefect curve fullThreeKernel = 0 := by
  have hr := halfKernelPolynomialDefect_regular curve fullThreeKernel
  exact eq_zero_of_kernel_regular_lt_one curve fullThreeKernel _ hr.1 hr.2
    (halfKernelPolynomialDefect_lt_one curve fullThreeKernel fullThree_card.2)

/-- 同じ3点核の源となる有理曲線。 -/
def toy : WeierstrassCurve ℚ := ⟨0, 0, 1, 0, 0⟩
local instance : toy.IsElliptic := ⟨by norm_num [toy, WeierstrassCurve.Δ, b₂, b₄, b₆, b₈]⟩

/-- 同じ源の実際の幾何学的点(0,0)。 -/
def q0 : (toy.toAffine⁄(AlgebraicClosure ℚ)).Point := .some 0 0 (by
  norm_num [toy, WeierstrassCurve.map, nonsingular_iff', equation_iff'])

/-- 同じ幾何学的点を固定済みPointsの群構造で扱う。 -/
def Q : Points toy := q0

/-- 接線公式によりQ+Q=−Q。3点核の閉性を実際の群法から得る。 -/
theorem toy_double : Q + Q = -Q := by
  have he : q0 + q0 = -q0 := by
    change Point.some 0 0 _ + Point.some 0 0 _ = -Point.some 0 0 _
    erw [Point.add_self_of_Y_ne (by norm_num [negY, toy, WeierstrassCurve.map] :
      (0 : AlgebraicClosure ℚ) ≠ (toy⁄(AlgebraicClosure ℚ)).negY 0 0), Point.neg_some]
    simp only [Point.some.injEq]
    norm_num [addX, addY, negAddY, negY, slope, toy, WeierstrassCurve.map]
  exact he

/-- 反転対は実際に異なる。 -/
theorem toy_neg_ne : Q ≠ -Q := by
  intro he
  have hv := congrArg Point.yc he
  have hn : (-q0).yc = -1 := by
    unfold q0
    erw [Point.neg_some]
    norm_num [Point.yc, negY, toy, WeierstrassCurve.map]
  have hn' : (-Q).yc = -1 := hn
  rw [hn'] at hv
  have h0 : Q.yc = 0 := rfl
  rw [h0] at hv
  norm_num at hv

/-- O,Q,−Qから成る同じ実点部分群。存在仮定ではなく閉性を証明して構成する。 -/
def toyKernel : AddSubgroup (Points toy) where
  carrier := {P | P = 0 ∨ P = Q ∨ P = -Q}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro P R hP hR
    rcases hP with rfl | rfl | rfl <;> rcases hR with rfl | rfl | rfl
    all_goals simp only [Set.mem_ofPred_eq, zero_add, add_zero, add_neg_cancel, neg_add_cancel,
      toy_double, ← neg_add, neg_neg]
    all_goals tauto
  neg_mem' := by
    intro P hP
    rcases hP with rfl | rfl | rfl <;> simp
local instance : Fintype toyKernel := Fintype.ofFinset {0, Q, -Q} (by
  intro P
  change P ∈ ({0, Q, -Q} : Finset (Points toy)) ↔ P = 0 ∨ P = Q ∨ P = -Q
  simp only [Finset.mem_insert, Finset.mem_singleton])

/-- 同じ核の点数は3。半核の計算へつなぐ。 -/
theorem toyKernel_card : Nat.card toyKernel = 3 := by
  let A : toyKernel := ⟨0, Or.inl rfl⟩
  let B : toyKernel := ⟨Q, Or.inr (Or.inl rfl)⟩
  let C : toyKernel := ⟨-Q, Or.inr (Or.inr rfl)⟩
  have hu : (Finset.univ : Finset toyKernel) = {A, B, C} := by
    ext P
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases P.property with h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Subtype.ext h))
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ, hu]
  have hQ : Q ≠ 0 := Point.some_ne_zero _
  have hAB : A ≠ B := by intro he; exact hQ (congrArg Subtype.val he).symm
  have hAC : A ≠ C := by
    intro he
    have hv : (0 : Points toy) = -Q := congrArg Subtype.val he
    exact (neg_ne_zero.mpr hQ) hv.symm
  have hBC : B ≠ C := by intro he; exact toy_neg_ne (congrArg Subtype.val he)
  simp [hAB, hAC, hBC]

/-- 番号付けがどちらの代表を選んでも、同じ既存標的はy²+y=x³−7。 -/
theorem toy_actual_model : kernelModel toy toyKernel =
    (⟨0, 0, 1, 0, -7⟩ : WeierstrassCurve (AlgebraicClosure ℚ)) := by
  have ho : Odd (Nat.card toyKernel) := toyKernel_card ▸ (by decide : Odd 3)
  rw [← halfKernelPolynomialModel_eq_kernelModel toy toyKernel ho]
  have hc := card_halfKernel toy toyKernel ho
  rw [toyKernel_card] at hc
  have hs : (halfKernel toy toyKernel).card = 1 := by omega
  obtain ⟨R, hR⟩ := Finset.card_eq_one.mp hs
  have hr : R ∈ halfKernel toy toyKernel := by rw [hR]; exact Finset.mem_singleton_self _
  have hn : R.val ≠ 0 := fun he => (mem_halfKernel toy toyKernel R).mp hr |>.1 <| Subtype.ext he
  have hd : R.val = Q ∨ R.val = -Q := by
    rcases R.property with hz | hq | hq
    · exact (hn hz).elim
    · exact Or.inl hq
    · exact Or.inr hq
  unfold halfKernelPolynomialModel
  rw [hR]
  have hpos : Q.xc = 0 ∧ Q.yc = 0 := ⟨rfl, rfl⟩
  have hneg0 : (-q0).xc = 0 ∧ (-q0).yc = -1 := by
    unfold q0
    erw [Point.neg_some]
    norm_num [Point.xc, Point.yc, negY, toy, WeierstrassCurve.map]
  have hneg : (-Q).xc = 0 ∧ (-Q).yc = -1 := hneg0
  have he : polynomialModel (toy.map (algebraMap ℚ (AlgebraicClosure ℚ))) ({R} : Finset toyKernel)
      (fun P => P.val.xc) (fun P => P.val.yc) =
      (⟨0, 0, 1, 0, -7⟩ : WeierstrassCurve (AlgebraicClosure ℚ)) := by
    simp only [polynomialModel, Finset.sum_singleton]
    rcases hd with hd | hd
    all_goals
      simp only [hd]
      ext <;> norm_num [momentT, momentW, hpos.1, hpos.2, hneg.1, hneg.2, toy, WeierstrassCurve.map, b₂, b₄]
  exact he

/-- 同じ既存標的の判別式も具体的に−19683。 -/
theorem toy_actual_discriminant : (kernelModel toy toyKernel).Δ = -19683 := by
  rw [toy_actual_model]
  norm_num [WeierstrassCurve.Δ, b₂, b₄, b₆, b₈]

local instance : Fintype kernel := Fintype.ofFinset {0, EllipticFiniteKernelTest.Q}
  (fun P => by simp [kernel])

/-- 偶数核では、反転固定点が半核から漏れる。奇数性を外すと候補は既存標的と異なる。 -/
theorem even_kernel_candidate_fails : halfKernelPolynomialModel curve kernel ≠ kernelModel curve kernel := by
  have hn (P : kernel) : -P = P := by
    apply Subtype.ext
    rcases P.property with hp | hp
    · change -(P.val : Points curve) = P.val
      rw [hp, neg_zero]
    · change -(P.val : Points curve) = P.val
      rw [hp]
      exact neg_eq_of_add_eq_zero_left point_data.2.1
  have hs : halfKernel curve kernel = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro P hP
    have hl := (mem_halfKernel curve kernel P).mp hP |>.2
    rw [hn P] at hl
    exact lt_irrefl _ hl
  have hm : halfKernelPolynomialModel curve kernel = curve.map (algebraMap ℚ (AlgebraicClosure ℚ)) := by
    unfold halfKernelPolynomialModel
    rw [hs]
    ext <;> simp [polynomialModel]
  intro he
  have hc := EllipticFiniteKernelSpecializationTest.actual_specialized_equation
  rw [← he, hm] at hc
  norm_num [curve, WeierstrassCurve.map, equation_iff] at hc

end
end EllipticFiniteKernelVeluEquationTest
