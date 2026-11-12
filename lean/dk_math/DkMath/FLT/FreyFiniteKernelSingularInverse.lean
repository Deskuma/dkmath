/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/
import DkMath.FLT.FreyFiniteKernelNodalInverse
import DkMath.FLT.FreyFiniteKernelZeroComponentAway
import DkMath.Lib.NumberTheory.EllipticFiniteKernelSingularInverse

#print "file: DkMath.FLT.FreyFiniteKernelSingularInverse"

/-!
# Frey 商の零成分逆像：滑らかな核と特異核

同じ Source、一次元核 L と同じ実点商準同型を保持する。
滑らかな核側は既存の零成分同値、特異核側は節点水準と枝比較による逆像判定を使う。
2 を含む悪い住所の中心と接方向を内部供給する。
-/
namespace DkMath.FLT.Frey.Source
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open EllipticGoodReductionSeparation WeierstrassModelReduction WeierstrassRationalIntegralModel
open ValuationInertia ValuationPrimeSupport ValuationRationalPrimeSupport
open DkMath.Lib.RepresentationTheory
noncomputable local instance instDecidableEqFreyFiniteKernelSingularInverse {α : Type*} : DecidableEq α := Classical.decEq _
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 悪い住所の特異核側の零成分逆像。源の中心・接方向と標的中心を内部供給する。 -/
theorem residual_pointHom_smooth_iff_translate_of_disjoint (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    {q : ℕ} [Fact q.Prime] (hqp : q ≠ p) (hbad : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hd : Disjoint L (S.residualZeroComponent A)) (P : Points S.rationalCurve) :
    HasSmoothReduction (S.residualValuationKernelModel L hl Fact.out hqp A hA)
      (S.residualOddKernelPointHom (by omega) L hl P) ↔
      ∃ Q : pointSubgroup S.rationalCurve p L, HasSmoothReduction (S.valuationModel A) (P - Q.val) := by
  let := S.finite_residualPointSubgroup L hl
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  have hunit : A.valuation (p : AlgebraicClosure ℚ) = 1 := by
    simpa only [pow_one] using prime_power_value_one A (Fact.out : p.Prime) Fact.out
      ((ValuationSubring.mem_nonunits_iff _).mp hA) hqp 1
  by_cases hq2 : q = 2
  · subst q
    obtain ⟨C, D, -, -⟩ := S.exists_dyadic_geometry hp5 A hA
    exact singular_kernel_smooth_iff_translate S.rationalCurve (pointSubgroup S.rationalCurve p L) p
      (card_pointSubgroup S.rationalCurve p L hl) (by omega) (S.residual_kernel_killed L) A
      (S.valuationModel A) (S.valuationModel_map A) hunit C D
      (S.residual_kernel_not_smooth_of_disjoint L A hd) P
  · obtain ⟨C, D, -, -⟩ := S.exists_criticalCentre_directions_at_bad_prime
      (Fact.out : p.Prime).pos hq2 (hbad.resolve_left hq2) A hA
    exact singular_kernel_smooth_iff_translate S.rationalCurve (pointSubgroup S.rationalCurve p L) p
      (card_pointSubgroup S.rationalCurve p L hl) (by omega) (S.residual_kernel_killed L) A
      (S.valuationModel A) (S.valuationModel_map A) hunit C D
      (S.residual_kernel_not_smooth_of_disjoint L A hd) P

/-- 同じ Frey 商について、滑らかな核と特異核の両方を統合した零成分逆像。
核の分岐と源の節点構造を内部供給し、同じ L と実点を保つ。 -/
theorem residual_pointHom_smooth_iff_translate_at_bad_place (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    {q : ℕ} [Fact q.Prime] (hqp : q ≠ p) (hbad : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q) (P : Points S.rationalCurve) :
    HasSmoothReduction (S.residualValuationKernelModel L hl Fact.out hqp A hA)
      (S.residualOddKernelPointHom (by omega) L hl P) ↔
      ∃ Q : pointSubgroup S.rationalCurve p L, HasSmoothReduction (S.valuationModel A) (P - Q.val) := by
  rcases S.residual_line_smooth_or_disjoint L hl A with hle | hd
  · rw [S.residual_pointHom_smooth_iff_at_bad_place_of_le hp5 L hl hqp hbad A hA hle P]
    constructor
    · intro hs
      exact ⟨0, by simpa using hs⟩
    · rintro ⟨Q, hQ⟩
      have hqs := S.residual_kernel_smooth_of_le L A hle Q
      have hh := smooth_add_of_model A (S.valuationModel A) _ (S.valuationModel_map A) hQ hqs
      have he : P - Q.val + Q.val = P := sub_add_cancel _ _
      exact he ▸ hh
  · exact S.residual_pointHom_smooth_iff_translate_of_disjoint hp5 L hl hqp hbad A hA hd P

/-- 同じ Galois 安定核から構成した既存整数標的への逆像判定。
整数モデルと付値環標的の点同型は既存の単元倍率による輸送を使う。 -/
theorem residual_integer_pointHom_smooth_iff_translate_at_bad_place (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    (hst : IsStable S.residualRepresentation L) {q : ℕ} [Fact q.Prime]
    (hqp : q ≠ p) (hbad : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q) (P : Points S.rationalCurve) :
    HasSmoothReduction (integerValuationModel A (S.residualIntegerKernelModel L hl hst))
      (S.residualIntegerKernelPointHom (by omega) L hl hst P) ↔
      ∃ Q : pointSubgroup S.rationalCurve p L, HasSmoothReduction (S.valuationModel A) (P - Q.val) :=
  (S.residual_integer_pointHom_smooth_iff (by omega) L hl hst Fact.out hqp A hA P).trans
    (S.residual_pointHom_smooth_iff_translate_at_bad_place hp5 L hl hqp hbad A hA P)

/-- p 以外の任意の素点で、同じ商像の零成分逆像は源零成分と同じ核の和。
悪い住所では節点の二分岐、良い住所では源の全点の滑らかな還元を使用する。 -/
theorem residual_pointHom_smooth_iff_translate_away (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    {q : ℕ} [Fact q.Prime] (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q) (P : Points S.rationalCurve) :
    HasSmoothReduction (S.residualValuationKernelModel L hl Fact.out hqp A hA)
      (S.residualOddKernelPointHom (by omega) L hl P) ↔
      ∃ Q : pointSubgroup S.rationalCurve p L, HasSmoothReduction (S.valuationModel A) (P - Q.val) := by
  by_cases hbad : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c
  · exact S.residual_pointHom_smooth_iff_translate_at_bad_place hp5 L hl hqp hbad A hA P
  · push Not at hbad
    let := S.valuation_reduction_isElliptic (Fact.out : p.Prime).pos hbad.1 hbad.2 A hA
    have hs : HasSmoothReduction (S.valuationModel A) P := by
      apply (smooth_pointEquiv_of_model A (S.valuationModel A) _ (S.valuationModel_map A) P).mp
      exact hasSmoothReduction_of_good (S.valuationModel A)
        ((S.valuationModel A).map (IsLocalRing.residue A)).Δ'.ne_zero _
    constructor
    · intro _
      exact ⟨0, by simpa using hs⟩
    · intro _
      exact S.residual_pointHom_smooth_away hp5 L hl hqp A hA P hs

/-- p 以外の任意の素点における、同じ安定核と既存整数標的の零成分逆像判定。 -/
theorem residual_integer_pointHom_smooth_iff_translate_away (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    (hst : IsStable S.residualRepresentation L) {q : ℕ} [Fact q.Prime] (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q) (P : Points S.rationalCurve) :
    HasSmoothReduction (integerValuationModel A (S.residualIntegerKernelModel L hl hst))
      (S.residualIntegerKernelPointHom (by omega) L hl hst P) ↔
      ∃ Q : pointSubgroup S.rationalCurve p L, HasSmoothReduction (S.valuationModel A) (P - Q.val) :=
  (S.residual_integer_pointHom_smooth_iff (by omega) L hl hst Fact.out hqp A hA P).trans
    (S.residual_pointHom_smooth_iff_translate_away hp5 L hl hqp A hA P)

end DkMath.FLT.Frey.Source
