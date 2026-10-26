/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelSmoothReduction
import DkMath.Lib.NumberTheory.FreyLocalReduction
import DkMath.Lib.NumberTheory.ValuationPrimeSupport

#print "file: DkMathTest.Lib.NumberTheory.EllipticFiniteKernelReduction"

/-!
同じ曲線y²+xy+7y=x³と実際の3点核O,(0,0),(0,−7)を使う。
7上では非零核点が節点に落ち、47上では全核が滑らかに還元する。
同じ既存標的を保ち、剰余一致・不一致と還元核の点数を検査する。
-/
namespace EllipticFiniteKernelReductionTest
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open EllipticGoodReductionSeparation WeierstrassVeluPolynomial ValuationPrimeSupport ValuationInertia
noncomputable section
local instance {α : Type*} : DecidableEq α := Classical.decEq _

/-- 同じ3点核の源となる有理曲線。 -/
def sample : WeierstrassCurve ℚ := ⟨1, 0, 7, 0, 0⟩
local instance : sample.IsElliptic := ⟨by norm_num [sample, WeierstrassCurve.Δ, b₂, b₄, b₆, b₈]⟩

/-- 同じ源の実際の幾何学的点(0,0)。 -/
def q0 : (sample.toAffine⁄(AlgebraicClosure ℚ)).Point := .some 0 0 (by
  norm_num [sample, WeierstrassCurve.map, nonsingular_iff', equation_iff'])

/-- 同じ幾何学的点を固定済みPointsの群構造で扱う。 -/
def Q : Points sample := q0

/-- 接線公式によりQ+Q=−Q。3点核の閉性を実際の群法から得る。 -/
theorem sample_double : Q + Q = -Q := by
  have he : q0 + q0 = -q0 := by
    change Point.some 0 0 _ + Point.some 0 0 _ = -Point.some 0 0 _
    erw [Point.add_self_of_Y_ne (by norm_num [negY, sample, WeierstrassCurve.map] :
      (0 : AlgebraicClosure ℚ) ≠ (sample⁄(AlgebraicClosure ℚ)).negY 0 0), Point.neg_some]
    simp only [Point.some.injEq]
    norm_num [addX, addY, negAddY, negY, slope, sample, WeierstrassCurve.map]
  exact he

/-- 反転対は実際に異なる。 -/
theorem sample_neg_ne : Q ≠ -Q := by
  intro he
  have hv := congrArg Point.yc he
  have hn : (-q0).yc = -7 := by
    unfold q0
    erw [Point.neg_some]
    norm_num [Point.yc, negY, sample, WeierstrassCurve.map]
  have hn' : (-Q).yc = -7 := hn
  rw [hn'] at hv
  have h0 : Q.yc = 0 := rfl
  rw [h0] at hv
  norm_num at hv

/-- O,Q,−Qから成る同じ実点部分群。存在仮定ではなく閉性を証明して構成する。 -/
def sampleKernel : AddSubgroup (Points sample) where
  carrier := {P | P = 0 ∨ P = Q ∨ P = -Q}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro P R hP hR
    rcases hP with rfl | rfl | rfl <;> rcases hR with rfl | rfl | rfl
    all_goals simp only [Set.mem_ofPred_eq, zero_add, add_zero, add_neg_cancel, neg_add_cancel,
      sample_double, ← neg_add, neg_neg]
    all_goals tauto
  neg_mem' := by
    intro P hP
    rcases hP with rfl | rfl | rfl <;> simp
local instance : Fintype sampleKernel := Fintype.ofFinset {0, Q, -Q} (by
  intro P
  change P ∈ ({0, Q, -Q} : Finset (Points sample)) ↔ P = 0 ∨ P = Q ∨ P = -Q
  simp only [Finset.mem_insert, Finset.mem_singleton])

/-- 同じ核の点数は3。半核の計算へつなぐ。 -/
theorem sampleKernel_card : Nat.card sampleKernel = 3 := by
  let A : sampleKernel := ⟨0, Or.inl rfl⟩
  let B : sampleKernel := ⟨Q, Or.inr (Or.inl rfl)⟩
  let C : sampleKernel := ⟨-Q, Or.inr (Or.inr rfl)⟩
  have hu : (Finset.univ : Finset sampleKernel) = {A, B, C} := by
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
    have hv : (0 : Points sample) = -Q := congrArg Subtype.val he
    exact (neg_ne_zero.mpr hQ) hv.symm
  have hBC : B ≠ C := by intro he; exact sample_neg_ne (congrArg Subtype.val he)
  simp [hAB, hAC, hBC]

/-- 番号付けがどちらの代表を選んでも、同じ既存標的はy²+xy+7y=x³−35x−350。 -/
theorem sample_actual_model : kernelModel sample sampleKernel =
    (⟨1, 0, 7, -35, -350⟩ : WeierstrassCurve (AlgebraicClosure ℚ)) := by
  have ho : Odd (Nat.card sampleKernel) := sampleKernel_card ▸ (by decide : Odd 3)
  rw [← halfKernelPolynomialModel_eq_kernelModel sample sampleKernel ho]
  have hc := card_halfKernel sample sampleKernel ho
  rw [sampleKernel_card] at hc
  have hs : (halfKernel sample sampleKernel).card = 1 := by omega
  obtain ⟨R, hR⟩ := Finset.card_eq_one.mp hs
  have hr : R ∈ halfKernel sample sampleKernel := by rw [hR]; exact Finset.mem_singleton_self _
  have hn : R.val ≠ 0 := fun he => (mem_halfKernel sample sampleKernel R).mp hr |>.1 <| Subtype.ext he
  have hd : R.val = Q ∨ R.val = -Q := by
    rcases R.property with hz | hq | hq
    · exact (hn hz).elim
    · exact Or.inl hq
    · exact Or.inr hq
  unfold halfKernelPolynomialModel
  rw [hR]
  have hpos : Q.xc = 0 ∧ Q.yc = 0 := ⟨rfl, rfl⟩
  have hneg0 : (-q0).xc = 0 ∧ (-q0).yc = -7 := by
    unfold q0
    erw [Point.neg_some]
    norm_num [Point.xc, Point.yc, negY, sample, WeierstrassCurve.map]
  have hneg : (-Q).xc = 0 ∧ (-Q).yc = -7 := hneg0
  have he : polynomialModel (sample.map (algebraMap ℚ (AlgebraicClosure ℚ))) ({R} : Finset sampleKernel)
      (fun P => P.val.xc) (fun P => P.val.yc) =
      (⟨1, 0, 7, -35, -350⟩ : WeierstrassCurve (AlgebraicClosure ℚ)) := by
    simp only [polynomialModel, Finset.sum_singleton]
    rcases hd with hd | hd
    all_goals
      simp only [hd]
      ext <;> norm_num [momentT, momentW, hpos.1, hpos.2, hneg.1, hneg.2, sample, WeierstrassCurve.map, b₂, b₄]
  exact he

/-- 同じ既存標的の判別式も具体的に−46512704。 -/
theorem sample_actual_discriminant : (kernelModel sample sampleKernel).Δ = -46512704 := by
  rw [sample_actual_model]
  norm_num [WeierstrassCurve.Δ, b₂, b₄, b₆, b₈]

/-- 同じ源と標的の整数不変量。剰余一致でも判別式の整数値は一致しない。
7と47の指数が3対1、1対3になる正確な因数分解を検査する。 -/
theorem sample_integer_invariants :
    (⟨1, 0, 7, 0, 0⟩ : WeierstrassCurve ℤ).Δ = -(2 ^ 2 * 7 ^ 3 * 47) ∧
      (⟨1, 0, 7, -35, -350⟩ : WeierstrassCurve ℤ).Δ = -(2 ^ 6 * 7 * 47 ^ 3) ∧
      (⟨1, 0, 7, 0, 0⟩ : WeierstrassCurve ℤ).c₄ = -167 ∧
      (⟨1, 0, 7, -35, -350⟩ : WeierstrassCurve ℤ).c₄ = 1513 := by
  norm_num [WeierstrassCurve.Δ, c₄, b₂, b₄, b₆, b₈]

/-- 同じ核は実際に3倍で消える。 -/
theorem sample_killed (R : sampleKernel) : 3 • R.val = 0 := by
  have hq : 3 • Q = 0 := by
    change (2 + 1) • Q = 0
    rw [add_nsmul, two_nsmul, one_nsmul, sample_double, neg_add_cancel]
  rcases R.property with hr | hr | hr
  · rw [hr, nsmul_zero]
  · rw [hr]; exact hq
  · rw [hr, smul_neg, hq, neg_zero]

/-- 同じ核の二有限点の座標を明示する。 -/
theorem sample_kernel_coordinates : Q.xc = 0 ∧ Q.yc = 0 ∧ (-Q).xc = 0 ∧ (-Q).yc = -7 := by
  have hn : (-q0).xc = 0 ∧ (-q0).yc = -7 := by
    unfold q0
    erw [Point.neg_some]
    norm_num [Point.xc, Point.yc, negY, sample, WeierstrassCurve.map]
  exact ⟨rfl, rfl, hn.1, hn.2⟩

/-- 同じ源の係数を各延長付値環に置いたモデル。 -/
def localSource (A : ValuationSubring (AlgebraicClosure ℚ)) : WeierstrassCurve A := ⟨1, 0, 7, 0, 0⟩

/-- 局所モデルの一般ファイバーは同じ源である。 -/
theorem localSource_map (A : ValuationSubring (AlgebraicClosure ℚ)) :
    (localSource A).map A.subtype = sample.map (algebraMap ℚ (AlgebraicClosure ℚ)) := by
  ext <;> norm_num [localSource, sample, WeierstrassCurve.map]
  exact map_ofNat A.subtype 7

private theorem residue_zero_coord (A : ValuationSubring (AlgebraicClosure ℚ)) (h : 0 ∈ A) :
    residue A ⟨0, h⟩ = 0 := (residue A).map_zero

private theorem residue_neg_seven_coord (A : ValuationSubring (AlgebraicClosure ℚ)) (h : -7 ∈ A) :
    residue A ⟨-7, h⟩ = -(7 : ResidueField A) := by
  change residue A (-(7 : A)) = _
  simp only [map_neg, map_ofNat]

private theorem three_unit {q : ℕ} (hq : q.Prime) (hq3 : q ≠ 3)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q) :
    A.valuation (3 : AlgebraicClosure ℚ) = 1 := by
  simpa only [Int.cast_ofNat] using valuation_intCast_eq_one_of_not_dvd A hq
    ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := 3) (by
      intro hd
      exact hq3 ((Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 3)).mp (by exact_mod_cast hd)))

/-- 7上では同じ二有限核点がともに特異な剰余点になる。 -/
theorem sample_kernel_singular_at_seven (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : LiesOverPrime A 7) (R : sampleKernel) (hR : R.val ≠ 0) :
    ¬ HasSmoothReduction (localSource A) R.val := by
  have h7 : (7 : ResidueField A) = 0 := by
    have hh := (WeierstrassResidueModel.residue_zero_iff A (7 : A)).mpr
      ((ValuationSubring.mem_nonunits_iff _).mp hA)
    simpa only [map_ofNat] using hh
  intro hs
  have hns := (kernelPoint_smooth_iff_residue sample sampleKernel 3 sample_killed A
    (localSource A) (localSource_map A) (three_unit (by decide) (by decide) A hA) R hR).mp hs
  rcases R.property with hr | hr | hr
  · exact hR hr
  all_goals
    simp only [hr, sample_kernel_coordinates.1, sample_kernel_coordinates.2.1,
      sample_kernel_coordinates.2.2.1, sample_kernel_coordinates.2.2.2] at hns
    norm_num [localSource, WeierstrassCurve.map, nonsingular_iff', residue_zero_coord,
      residue_neg_seven_coord, map_ofNat, h7] at hns
    simp_all only

/-- 7上で、同じ既存商の局所モデルと源の剰余が一致する。 -/
theorem sample_singular_branch_residue (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : LiesOverPrime A 7) :
    (valuationKernelModel sample sampleKernel 3 sample_killed A (localSource A) (localSource_map A)
      (three_unit (by decide) (by decide) A hA)).map (residue A) = (localSource A).map (residue A) :=
  valuationKernelModel_residue_eq_of_not_smooth sample sampleKernel 3 sample_killed A _ _ _
    (sample_kernel_singular_at_seven A hA)

/-- 47上では同じ3点核の全点が滑らかに還元する。 -/
theorem sample_kernel_smooth_at_fortySeven (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : LiesOverPrime A 47) (R : sampleKernel) : HasSmoothReduction (localSource A) R.val := by
  have hv : A.valuation (7 : AlgebraicClosure ℚ) = 1 := by
    simpa only [Int.cast_ofNat] using valuation_intCast_eq_one_of_not_dvd A (by decide : Nat.Prime 47)
      ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := 7) (by norm_num)
  have h7 : (7 : ResidueField A) ≠ 0 := by
    have hh := (WeierstrassResidueModel.residue_ne_zero_iff A (7 : A)).mpr hv
    simpa only [map_ofNat] using hh
  by_cases hR : R.val = 0
  · rw [hR]; exact hasSmoothReduction_zero _ _
  · apply (kernelPoint_smooth_iff_residue sample sampleKernel 3 sample_killed A
      (localSource A) (localSource_map A) (three_unit (by decide) (by decide) A hA) R hR).mpr
    rcases R.property with hr | hr | hr
    · exact (hR hr).elim
    all_goals
      simp only [hr, sample_kernel_coordinates.1, sample_kernel_coordinates.2.1,
        sample_kernel_coordinates.2.2.1, sample_kernel_coordinates.2.2.2]
      norm_num [localSource, WeierstrassCurve.map, nonsingular_iff', equation_iff, residue_zero_coord,
        residue_neg_seven_coord, map_ofNat, h7]

/-- 滑らかな側の同じ還元像は実際に3点。節点へ落ちる側と同一視しない。 -/
theorem sample_smooth_branch_card (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 47) :
    Nat.card (smoothKernelReduction sample sampleKernel A (localSource A) (localSource_map A)
      (sample_kernel_smooth_at_fortySeven A hA)).range = 3 :=
  (card_smoothKernelReduction_range sample sampleKernel A _ _ (sample_kernel_smooth_at_fortySeven A hA)
    3 sample_killed (three_unit (by decide) (by decide) A hA)).trans sampleKernel_card

/-- 滑らかな側では剰余モデルの完全一致は成立しない。特異核側の仮定の必要性を検査。 -/
theorem sample_models_differ_mod_fortySeven :
    (⟨1, 0, 7, -35, -350⟩ : WeierstrassCurve ℤ).map (Int.castRingHom (ZMod 47)) ≠
      (⟨1, 0, 7, 0, 0⟩ : WeierstrassCurve ℤ).map (Int.castRingHom (ZMod 47)) := by
  intro he
  have hh := congrArg WeierstrassCurve.a₄ he
  have hz : ((-35 : ℤ) : ZMod 47) = 0 := by
    simpa only [WeierstrassCurve.map, map_neg, map_ofNat, map_zero, Int.cast_neg, Int.cast_ofNat] using hh
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (-35) 47).mp hz
  norm_num at hd

end
end EllipticFiniteKernelReductionTest
