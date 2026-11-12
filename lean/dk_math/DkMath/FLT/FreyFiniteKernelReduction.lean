/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFiniteKernelDenominatorSupport
import DkMath.FLT.FreyCofixedBranchSwap
import DkMath.Lib.NumberTheory.EllipticFiniteKernelSmoothReduction
import DkMath.Lib.NumberTheory.FreyLocalReduction

#print "file: DkMath.FLT.FreyFiniteKernelReduction"

/-!
# 同じFrey源と既存整数標的の局所還元比較

同じLと実点核Hから付値環モデルを作り、既存の同じ商標的との一致を保持する。
LがE₀[p]と交わらない側では、全非零核点が特異点へ還元し、源と商の剰余モデルが一致する。
その側でΔの非単元性・c₄の単元性を運び、既存整数標的の正式な最小性・乗法的還元へ接続する。
また240が非単元の場所では、滑らかな核の側も含めc₄の単元性を保つ。
一般の滑らかな核の還元型、Δの深さ、全点の零成分輸送は未証明である。
-/
namespace DkMath.FLT.Frey.Source
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open DkMath.Lib.NumberTheory EllipticTorsionRepresentation EllipticFiniteKernel
open ValuationInertia ValuationPrimeSupport ValuationRationalPrimeSupport
open EllipticGoodReductionSeparation DkMath.Lib.RepresentationTheory
noncomputable local instance instDecidableEqFreyFiniteKernelReduction {α : Type*} : DecidableEq α := Classical.decEq _
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private theorem prime_unit {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q) :
    A.valuation (p : AlgebraicClosure ℚ) = 1 := by
  simpa only [pow_one] using prime_power_value_one A (Fact.out : p.Prime) hq
    ((ValuationSubring.mem_nonunits_iff _).mp hA) hqp 1

/-- 同じ実点核を使う付値環係数の標的。整座標とpの単元性を内部供給する。 -/
noncomputable def residualValuationKernelModel
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q) : WeierstrassCurve A := by
  let := S.finite_residualPointSubgroup L hl
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact valuationKernelModel S.rationalCurve _ p (S.residual_kernel_killed L) A
    (S.valuationModel A) (S.valuationModel_map A) (prime_unit hq hqp A hA)

/-- 新しい付値環モデルの一般ファイバーは、既存の同じ幾何学的標的。 -/
theorem residual_valuation_kernel_model_map (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q) :
    (S.residualValuationKernelModel L hl hq hqp A hA).map A.subtype = S.residualKernelModel L hl := by
  let := S.finite_residualPointSubgroup L hl
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact valuationKernelModel_map S.rationalCurve _ p (S.residual_kernel_killed L) A
    (S.valuationModel A) (S.valuationModel_map A) (prime_unit hq hqp A hA)
      (S.residual_pointSubgroup_odd hp2 L hl)

/-- 一次元Lは同じE₀[p]に含まれるか、それと交わらない。どちらの側も消さずに残す。 -/
theorem residual_line_smooth_or_disjoint
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    (A : ValuationSubring (AlgebraicClosure ℚ)) :
    L ≤ S.residualZeroComponent A ∨ Disjoint L (S.residualZeroComponent A) := by
  by_cases h : L ≤ S.residualZeroComponent A
  · exact Or.inl h
  · exact Or.inr ((Submodule.isAtom_iff_finrank_eq_one.mpr hl).not_le_iff_disjoint.mp h)

/-- 交わらない側では、同じ核の非零点が全て滑らかに還元しない。 -/
theorem residual_kernel_not_smooth_of_disjoint
    (L : Submodule (ZMod p) S.ResidualSpace) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hd : Disjoint L (S.residualZeroComponent A))
    (Q : pointSubgroup S.rationalCurve p L) (hQ : Q.val ≠ 0) :
    ¬ HasSmoothReduction (S.valuationModel A) Q.val := by
  intro hs
  obtain ⟨T, hTL, he⟩ := Q.property
  have he' : T.val = Q.val := he
  have hsm : HasSmoothReduction (S.valuationModel A) T.val :=
    Eq.mpr (congrArg (fun P : Points S.rationalCurve => HasSmoothReduction (S.valuationModel A) P) he') hs
  have hTm : T ∈ S.residualZeroComponent A := (S.mem_residualZeroComponent_iff A T).mpr hsm
  have ht : T = 0 := (Submodule.disjoint_def.mp hd) T hTL hTm
  have hv := congrArg Subtype.val ht
  exact hQ (he'.symm.trans hv)

/-- 特異核側では源と同じ付値環標的の剰余が完全に一致する。滑らかな側へは流用しない。 -/
theorem residual_valuation_kernel_residue_eq_of_disjoint
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hd : Disjoint L (S.residualZeroComponent A)) :
    (S.residualValuationKernelModel L hl hq hqp A hA).map (residue A) =
      (S.valuationModel A).map (residue A) := by
  let := S.finite_residualPointSubgroup L hl
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact valuationKernelModel_residue_eq_of_not_smooth S.rationalCurve _ p (S.residual_kernel_killed L)
    A (S.valuationModel A) (S.valuationModel_map A) (prime_unit hq hqp A hA)
    (S.residual_kernel_not_smooth_of_disjoint L A hd)

/-- 同じ整数標的と付値環標的は、Δ,c₄の付値がp以外で一致する。
整数化の単元倍率と既存標的の同一性を内部で結ぶ。 -/
theorem residual_integer_valuation_kernel_values (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    (hs : IsStable S.residualRepresentation L) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q) :
    A.valuation ((S.residualIntegerKernelModel L hl hs).Δ : AlgebraicClosure ℚ) =
        A.valuation ((S.residualValuationKernelModel L hl hq hqp A hA).Δ : AlgebraicClosure ℚ) ∧
      A.valuation ((S.residualIntegerKernelModel L hl hs).c₄ : AlgebraicClosure ℚ) =
        A.valuation ((S.residualValuationKernelModel L hl hq hqp A hA).c₄ : AlgebraicClosure ℚ) := by
  have hv := S.residual_integer_target_invariant_values hp2 L hl hs A hq hqp hA
  have hm := S.residual_valuation_kernel_model_map hp2 L hl hq hqp A hA
  have hd := S.residual_descended_kernel_model_map L hl hs
  have he := hm.trans hd.symm
  have hΔ := congrArg WeierstrassCurve.Δ he
  have hc := congrArg WeierstrassCurve.c₄ he
  simp only [map_Δ] at hΔ
  simp only [map_c₄] at hc
  exact ⟨hv.1.trans (congrArg A.valuation hΔ).symm, hv.2.trans (congrArg A.valuation hc).symm⟩

/-- 特異核側で、源と既存整数標的のΔの非単元性・c₄の単元性を運ぶ。 -/
theorem residual_integer_target_conditions_of_disjoint (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    (hs : IsStable S.residualRepresentation L) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hd : Disjoint L (S.residualZeroComponent A)) :
    (A.valuation ((S.residualIntegerKernelModel L hl hs).Δ : AlgebraicClosure ℚ) < 1 ↔
      A.valuation (S.curve.Δ : AlgebraicClosure ℚ) < 1) ∧
    (A.valuation ((S.residualIntegerKernelModel L hl hs).c₄ : AlgebraicClosure ℚ) = 1 ↔
      A.valuation (S.curve.c₄ : AlgebraicClosure ℚ) = 1) := by
  have hi := WeierstrassResidueModel.invariant_conditions_iff A _ _
    (S.residual_valuation_kernel_residue_eq_of_disjoint L hl hq hqp A hA hd)
  have hv := S.residual_integer_valuation_kernel_values hp2 L hl hs hq hqp A hA
  have hsrcΔ : ((S.valuationModel A).Δ : AlgebraicClosure ℚ) = (S.curve.Δ : AlgebraicClosure ℚ) := by
    simp [valuationModel, eq_intCast]
  have hsrcC : ((S.valuationModel A).c₄ : AlgebraicClosure ℚ) = (S.curve.c₄ : AlgebraicClosure ℚ) := by
    simp [valuationModel, eq_intCast]
  rw [hv.1, hv.2, ← hsrcΔ, ← hsrcC]
  exact hi

/-- 特異核側の悪い奇素数で、同じ整数標的は正式な乗法的還元を持つ。最小性も定義に含まれる。 -/
theorem residual_integer_target_multiplicative_of_disjoint (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    (hs : IsStable S.residualRepresentation L) {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) (hqp : q ≠ p)
    (hbad : (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hd : Disjoint L (S.residualZeroComponent A)) :
    HasMultiplicativeReduction (FreyLocalReduction.LocalRing q)
      ((S.residualIntegerKernelModel L hl hs).map (Int.castRingHom ℚ)) := by
  have hi := S.residual_integer_target_conditions_of_disjoint hp2 L hl hs Fact.out hqp A hA hd
  have hqv := (ValuationSubring.mem_nonunits_iff _).mp hA
  have hΔ := hi.1.mpr (valuation_intCast_lt_one_of_dvd A hqv
    (S.local_arithmetic (Nat.Prime.pos (Fact.out : p.Prime)) hq2 hbad).1)
  have hc := hi.2.mpr (S.valuation_c4_eq_one (Nat.Prime.pos (Fact.out : p.Prime)) hq2 hbad A hA)
  apply FreyLocalReduction.hasMultiplicativeReduction_at_prime q _
  · by_contra hn
    exact hΔ.ne (valuation_intCast_eq_one_of_not_dvd A Fact.out hqv hn)
  · intro hn
    have hh := valuation_intCast_lt_one_of_dvd A hqv hn
    rw [hc] at hh
    exact lt_irrefl _ hh

/-- 240を割る素数住所では、核の還元の側に依らず、源のc₄単元性が既存整数標的へ移る。 -/
theorem residual_integer_target_c4_of_dvd240 (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    (hs : IsStable S.residualRepresentation L) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (hq240 : q ∣ 240)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hc : A.valuation (S.curve.c₄ : AlgebraicClosure ℚ) = 1) :
    A.valuation ((S.residualIntegerKernelModel L hl hs).c₄ : AlgebraicClosure ℚ) = 1 := by
  let := S.finite_residualPointSubgroup L hl
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  have hsrc : A.valuation (S.rationalCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).c₄ = 1 := by
    rw [← S.curve_map, map_c₄, map_c₄]
    simpa [eq_intCast] using hc
  have ht := kernelModel_c4_value_one_of_small_240 S.rationalCurve _ p (S.residual_kernel_killed L)
    A (S.valuationModel A) (S.valuationModel_map A) (prime_unit hq hqp A hA)
    (S.residual_pointSubgroup_odd hp2 L hl)
    (valuation_intCast_lt_one_of_dvd A ((ValuationSubring.mem_nonunits_iff _).mp hA)
      (z := 240) (by exact_mod_cast hq240)) hsrc
  have he := congrArg WeierstrassCurve.c₄ (S.residual_valuation_kernel_model_map hp2 L hl hq hqp A hA)
  rw [map_c₄] at he
  have hv := (S.residual_integer_valuation_kernel_values hp2 L hl hs hq hqp A hA).2
  exact hv.trans ((congrArg A.valuation he).trans ht)

/-- 同じ既存整数標的のc₄は2で割れない。滑らかな核の側も含み、追加の局所条件はない。 -/
theorem residual_integer_target_c4_odd (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    (hs : IsStable S.residualRepresentation L) : ¬ (2 : ℤ) ∣ (S.residualIntegerKernelModel L hl hs).c₄ := by
  obtain ⟨A, hA⟩ := ValuationPrimeExistence.exists_liesOverPrime (L := AlgebraicClosure ℚ) Nat.prime_two
  have hqv := (ValuationSubring.mem_nonunits_iff _).mp hA
  have hc := S.residual_integer_target_c4_of_dvd240 hp2 L hl hs Nat.prime_two (Ne.symm hp2)
    (by decide) A hA (valuation_intCast_eq_one_of_not_dvd A Nat.prime_two hqv
      (FreyGapCubic.not_two_dvd_integral_c4 _ _ S.normalization))
  intro hd
  have hlt := valuation_intCast_lt_one_of_dvd A hqv hd
  rw [hc] at hlt
  exact lt_irrefl _ hlt

/-- 同じ既存整数標的は2で正式に最小。判別式が2で割れるかどうかは別の未解決部分。 -/
theorem residual_integer_target_minimal_at_two (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    (hs : IsStable S.residualRepresentation L) :
    IsMinimal (FreyLocalReduction.LocalRing 2)
      ((S.residualIntegerKernelModel L hl hs).map (Int.castRingHom ℚ)) :=
  FreyLocalReduction.isMinimal_at_prime_of_not_dvd_c4 2 _ (S.residual_integer_target_c4_odd hp2 L hl hs)

/-- 240を割る素数で源のc₄が単元なら、既存整数標的は正式に最小である。
還元型の判定や、判別式の深さは結論へ付け加えない。 -/
theorem residual_integer_target_minimal_of_dvd240 (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    (hs : IsStable S.residualRepresentation L) {q : ℕ} [Fact q.Prime] (hqp : q ≠ p) (hq240 : q ∣ 240)
    (hc : ¬ (q : ℤ) ∣ S.curve.c₄) :
    IsMinimal (FreyLocalReduction.LocalRing q)
      ((S.residualIntegerKernelModel L hl hs).map (Int.castRingHom ℚ)) := by
  obtain ⟨A, hA⟩ := ValuationPrimeExistence.exists_liesOverPrime (L := AlgebraicClosure ℚ) (Fact.out : q.Prime)
  have hqv := (ValuationSubring.mem_nonunits_iff _).mp hA
  have ht := S.residual_integer_target_c4_of_dvd240 hp2 L hl hs Fact.out hqp hq240 A hA
    (valuation_intCast_eq_one_of_not_dvd A Fact.out hqv hc)
  apply FreyLocalReduction.isMinimal_at_prime_of_not_dvd_c4 q _
  intro hd
  have hh := valuation_intCast_lt_one_of_dvd A hqv hd
  rw [ht] at hh
  exact lt_irrefl _ hh

/-- abcを割る3,5上では、源のc₄単元性を既存算術から供給して同じ標的の最小性を得る。 -/
theorem residual_integer_target_minimal_at_bad_small_prime (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    (hs : IsStable S.residualRepresentation L) {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) (hqp : q ≠ p)
    (hq240 : q ∣ 240) (hbad : (q : ℤ) ∣ S.a * S.b * S.c) :
    IsMinimal (FreyLocalReduction.LocalRing q)
      ((S.residualIntegerKernelModel L hl hs).map (Int.castRingHom ℚ)) :=
  S.residual_integer_target_minimal_of_dvd240 hp2 L hl hs hqp hq240
    (S.local_arithmetic (Nat.Prime.pos (Fact.out : p.Prime)) hq2 hbad).2.1

/-- 滑らかな側では、同じLの全核点が同じ源モデルの零成分に入る。 -/
theorem residual_kernel_smooth_of_le
    (L : Submodule (ZMod p) S.ResidualSpace) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hle : L ≤ S.residualZeroComponent A) (Q : pointSubgroup S.rationalCurve p L) :
    HasSmoothReduction (S.valuationModel A) Q.val := by
  obtain ⟨T, hTL, he⟩ := Q.property
  have ht := (S.mem_residualZeroComponent_iff A T).mp (hle hTL)
  have he' : T.val = Q.val := he
  exact Eq.mp (congrArg (fun P : Points S.rationalCurve => HasSmoothReduction (S.valuationModel A) P) he') ht

/-- 同じ一次元核の全点が滑らかに還元する側と、全非零点が特異に還元する側を内部で供給する。 -/
theorem residual_kernel_reduction_cases
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    (A : ValuationSubring (AlgebraicClosure ℚ)) :
    (∀ Q : pointSubgroup S.rationalCurve p L, HasSmoothReduction (S.valuationModel A) Q.val) ∨
      (∀ Q : pointSubgroup S.rationalCurve p L, Q.val ≠ 0 → ¬ HasSmoothReduction (S.valuationModel A) Q.val) := by
  rcases S.residual_line_smooth_or_disjoint L hl A with hle | hd
  · exact Or.inl (S.residual_kernel_smooth_of_le L A hle)
  · exact Or.inr (S.residual_kernel_not_smooth_of_disjoint L A hd)

/-- 同じLが零成分に入る側で、同じ核Hを剰余点群へ送る加法準同型。 -/
noncomputable def residualSmoothKernelReduction
    (L : Submodule (ZMod p) S.ResidualSpace) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hle : L ≤ S.residualZeroComponent A) :
    pointSubgroup S.rationalCurve p L →+ ((S.valuationModel A).map (residue A)).toAffine.Point :=
  smoothKernelReduction S.rationalCurve _ A (S.valuationModel A) (S.valuationModel_map A)
    (S.residual_kernel_smooth_of_le L A hle)

/-- 同じ滑らかな核の還元像も正確にp点を持つ。核の位数を外部の仮定に戻さない。 -/
theorem residual_smooth_kernel_range_card
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hle : L ≤ S.residualZeroComponent A) :
    Nat.card (S.residualSmoothKernelReduction L A hle).range = p := by
  let := S.finite_residualPointSubgroup L hl
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact (card_smoothKernelReduction_range S.rationalCurve _ A (S.valuationModel A) (S.valuationModel_map A)
    (S.residual_kernel_smooth_of_le L A hle) p (S.residual_kernel_killed L) (prime_unit hq hqp A hA)).trans
    (card_pointSubgroup S.rationalCurve p L hl)

/-- 滑らかな側でも、既存標的の付値環モデルの剰余は同じ還元核の半核座標で書ける。
この剰余多項式モデルの節点上の不変量公式が残る接続である。 -/
theorem residual_valuation_kernel_residue_of_smooth
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hle : L ≤ S.residualZeroComponent A) :
    letI := S.finite_residualPointSubgroup L hl
    letI := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
    (S.residualValuationKernelModel L hl hq hqp A hA).map (residue A) =
      WeierstrassVeluPolynomial.polynomialModel ((S.valuationModel A).map (residue A))
        (halfKernel S.rationalCurve (pointSubgroup S.rationalCurve p L))
        (fun Q => (S.residualSmoothKernelReduction L A hle Q).xc)
        (fun Q => (S.residualSmoothKernelReduction L A hle Q).yc) := by
  let := S.finite_residualPointSubgroup L hl
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact valuationKernelModel_residue_of_smooth S.rationalCurve _ A (S.valuationModel A) (S.valuationModel_map A)
    (S.residual_kernel_smooth_of_le L A hle) p (S.residual_kernel_killed L) (prime_unit hq hqp A hA)

end DkMath.FLT.Frey.Source
