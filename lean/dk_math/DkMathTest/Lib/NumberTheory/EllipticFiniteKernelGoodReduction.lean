/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelGoodReduction

#print "file: DkMathTest.Lib.NumberTheory.EllipticFiniteKernelGoodReduction"

/-!
標数5の楕円曲線y²+y=x³と実際の3点核を使い、標数0を外した非特異性定理を検査する。
零核だけの例にせず、接線によるQ+Q=−Qと三点の分離から核を構成する。
-/
namespace EllipticFiniteKernelGoodReductionTest
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory WeierstrassVeluPolynomial
noncomputable section
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : NeZero (2 : ZMod 5) := ⟨by decide⟩
local instance {α : Type*} : DecidableEq α := Classical.decEq _
/-- 同じ3点核の源となる標数5の曲線。 -/
def toy : WeierstrassCurve (ZMod 5) := ⟨0, 0, 1, 0, 0⟩
local instance : toy.IsElliptic := ⟨by norm_num [toy, WeierstrassCurve.Δ, b₂, b₄, b₆, b₈]; decide⟩

/-- 同じ源の実点(0,0)。 -/
def q0 : toy.toAffine.Point := .some 0 0 (by
  norm_num [toy, WeierstrassCurve.map, nonsingular_iff', equation_iff'])

/-- 同じ実点を実際のPointの群構造で扱う。 -/
def Q : toy.toAffine.Point := q0

/-- 接線公式によりQ+Q=−Q。3点核の閉性を実際の群法から得る。 -/
theorem toy_double : Q + Q = -Q := by
  have he : q0 + q0 = -q0 := by
    change Point.some 0 0 _ + Point.some 0 0 _ = -Point.some 0 0 _
    erw [Point.add_self_of_Y_ne (by norm_num [negY, toy, WeierstrassCurve.map] :
      (0 : ZMod 5) ≠ toy.toAffine.negY 0 0), Point.neg_some]
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
def toyKernel : AddSubgroup (toy.toAffine.Point) where
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
  change P ∈ ({0, Q, -Q} : Finset (toy.toAffine.Point)) ↔ P = 0 ∨ P = Q ∨ P = -Q
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
    have hv : (0 : toy.toAffine.Point) = -Q := congrArg Subtype.val he
    exact (neg_ne_zero.mpr hQ) hv.symm
  have hBC : B ≠ C := by intro he; exact toy_neg_ne (congrArg Subtype.val he)
  simp [hAB, hAC, hBC]

/-- 反転対の代表をQ一つに固定した、実際の半集合。 -/
def half : Finset toyKernel := {⟨Q, Or.inr (Or.inl rfl)⟩}

/-- Oを除く二点をちょうど一度ずつ数える。 -/
theorem half_partition : DkMath.Lib.Algebra.FiniteInversionHalf.IsHalf half := by
  have hQ : Q ≠ 0 := Point.some_ne_zero _
  constructor
  · ext P
    simp only [half, Finset.image_singleton, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_erase, Finset.mem_univ, and_true]
    change (P = ⟨Q, _⟩ ∨ P = ⟨-Q, _⟩) ↔ P ≠ 0
    constructor
    · rintro (rfl | rfl) he
      · exact hQ (congrArg Subtype.val he)
      · exact (neg_ne_zero.mpr hQ) (congrArg Subtype.val he)
    · intro hn
      rcases P.property with hz | hq | hq
      · exact (hn (Subtype.ext hz)).elim
      · exact Or.inl (Subtype.ext hq)
      · exact Or.inr (Subtype.ext hq)
  · simp only [half, Finset.image_singleton, Finset.disjoint_singleton]
    intro he
    exact toy_neg_ne (congrArg Subtype.val he)

/-- 標数5の実際の3点核から、標的非特異性を入力せず同じ多項式標的のΔ≠0を得る。 -/
theorem actual_positive_characteristic_target :
    (polynomialModel toy half
      (fun q : toyKernel => q.val.xc) (fun q => q.val.yc)).Δ ≠ 0 := by
  have ho : Odd (Nat.card toyKernel) := by rw [toyKernel_card]; decide
  have hf : Function.Injective toyKernel.subtype := Subtype.val_injective
  exact WeierstrassFiniteKernelModel.polynomialModel_discriminant_ne_zero
    (k := ZMod 5) (G := toyKernel) toy toyKernel.subtype hf ho half half_partition

/-- 同じ標的を係数計算でも確認する。標数5でもy²+y=x³−7になる。 -/
theorem actual_model_coefficients :
    polynomialModel toy half (fun q : toyKernel => q.val.xc) (fun q => q.val.yc) =
      (⟨0, 0, 1, 0, -7⟩ : WeierstrassCurve (ZMod 5)) := by
  ext <;> norm_num [polynomialModel, half, toy, momentT, momentW, Q, q0,
    Point.xc, Point.yc, b₂, b₄, b₆]

end
end EllipticFiniteKernelGoodReductionTest
