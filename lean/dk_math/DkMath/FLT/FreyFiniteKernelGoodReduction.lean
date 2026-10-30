/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFiniteKernelNodalReduction
import DkMath.Lib.NumberTheory.EllipticFiniteKernelGoodReduction

#print "file: DkMath.FLT.FreyFiniteKernelGoodReduction"

/-!
# 同じ整数商標的の、p以外での還元型

良い奇素数住所では、同じ有限核の還元の単射性と、奇標数へ拡張した商の非特異性を使う。
整数化の単元倍率を通して、既存の整数標的の判別式も単元と分かる。
前章の悪い住所での乗法的還元と合わせ、p以外の全素数で良還元または乗法的還元を得る。
pでの挙動、判別式の深さ、悪い場所での零成分輸送、hnoはこの章の結論に含めない。
-/
namespace DkMath.FLT.Frey.Source
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open DkMath.Lib.NumberTheory EllipticTorsionRepresentation EllipticFiniteKernel
open ValuationInertia ValuationRationalPrimeSupport ValuationPrimeSupport WeierstrassResidueModel
open DkMath.Lib.RepresentationTheory
noncomputable local instance instDecidableEqFreyFiniteKernelGoodReduction {α : Type*} : DecidableEq α :=
  Classical.decEq _
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 同じ良い奇素数住所で、同じ既存整数標的のΔの付値は1。
標的の良還元を仮定せず、同じ核の還元から導く。 -/
theorem residual_integer_target_good_value_one (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    (hs : IsStable S.residualRepresentation L) {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (hqp : q ≠ p) (hd : ¬ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q) :
    A.valuation ((S.residualIntegerKernelModel L hl hs).Δ : AlgebraicClosure ℚ) = 1 := by
  let := S.finite_residualPointSubgroup L hl
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  have hv2 := valuation_intCast_eq_one_of_not_dvd A (Fact.out : q.Prime)
    ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := 2)
    (by intro h; exact hq2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp (by exact_mod_cast h)))
  let : NeZero (2 : ResidueField A) := ⟨by
    have hr := (residue_ne_zero_iff A (2 : A)).mpr hv2
    simpa only [map_ofNat] using hr⟩
  have hp : A.valuation (p : AlgebraicClosure ℚ) = 1 := by
    simpa only [pow_one] using prime_power_value_one A (Fact.out : p.Prime) Fact.out
      ((ValuationSubring.mem_nonunits_iff _).mp hA) hqp 1
  let := S.valuation_reduction_isElliptic (Nat.Prime.pos (Fact.out : p.Prime)) hq2 hd A hA
  have hi := valuationKernelModel_good_value_one S.rationalCurve
    (pointSubgroup S.rationalCurve p L) p (S.residual_kernel_killed L)
    A (S.valuationModel A) (S.valuationModel_map A) hp
    (S.residual_pointSubgroup_odd hp2 L hl) ((S.valuationModel A).map (residue A)).Δ'.ne_zero
  rw [(S.residual_integer_valuation_kernel_values hp2 L hl hs Fact.out hqp A hA).1]
  exact hi

/-- 同じSourceの良い奇素数q≠pで、同じ整数標的は正式な良還元を持つ。
付値環の存在も内部で供給するので、局所標的の非特異性providerを要求しない。 -/
theorem residual_integer_target_good_at_prime (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    (hs : IsStable S.residualRepresentation L) {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (hqp : q ≠ p) (hd : ¬ (q : ℤ) ∣ S.a * S.b * S.c) :
    HasGoodReduction (FreyLocalReduction.LocalRing q)
      ((S.residualIntegerKernelModel L hl hs).map (Int.castRingHom ℚ)) := by
  obtain ⟨A,hA⟩ := ValuationPrimeExistence.exists_liesOverPrime (L := AlgebraicClosure ℚ) (Fact.out : q.Prime)
  have hi := S.residual_integer_target_good_value_one hp2 L hl hs hq2 hqp hd A hA
  apply FreyLocalReduction.hasGoodReduction_at_prime q _
  intro hn
  have hh := valuation_intCast_lt_one_of_dvd A ((ValuationSubring.mem_nonunits_iff _).mp hA) hn
  rw [hi] at hh
  exact lt_irrefl _ hh

/-!
The preceding provider is phrased as a local model predicate.  For the
integer torsion-order bridge we expose the exact arithmetic input instead:
the integer discriminant is not divisible by `q`.  The proof reuses the
valuation-one statement and does not duplicate the reduction construction.
-/

/-- A good odd prime away from the support of `a*b*c` does not divide the integer target discriminant. -/
theorem residual_integer_target_discriminant_not_dvd_at_good_prime (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    (hs : IsStable S.residualRepresentation L) {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (hqp : q ≠ p) (hd : ¬ (q : ℤ) ∣ S.a * S.b * S.c) :
    ¬ (q : ℤ) ∣ (S.residualIntegerKernelModel L hl hs).Δ := by
  obtain ⟨A, hA⟩ :=
    ValuationPrimeExistence.exists_liesOverPrime (L := AlgebraicClosure ℚ)
      (Fact.out : q.Prime)
  intro hdiv
  have hone := S.residual_integer_target_good_value_one hp2 L hl hs hq2 hqp hd A hA
  have hlt := valuation_intCast_lt_one_of_dvd A
    ((ValuationSubring.mem_nonunits_iff _).mp hA) hdiv
  rw [hone] at hlt
  exact lt_irrefl _ hlt

/-- p≥5なら同じ既存整数標的は、p以外の全素数で良還元または乗法的還元を持つ。
2は前章の乗法的還元、奇素数はabcの支持で分岐する。pでの結論を混入しない。 -/
theorem residual_integer_target_semistable_away (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    (hs : IsStable S.residualRepresentation L) {q : ℕ} [Fact q.Prime] (hqp : q ≠ p) :
    HasGoodReduction (FreyLocalReduction.LocalRing q)
        ((S.residualIntegerKernelModel L hl hs).map (Int.castRingHom ℚ)) ∨
      HasMultiplicativeReduction (FreyLocalReduction.LocalRing q)
        ((S.residualIntegerKernelModel L hl hs).map (Int.castRingHom ℚ)) := by
  by_cases hbad : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c
  · exact Or.inr (S.residual_integer_target_multiplicative_at_bad_place hp5 L hl hs hqp hbad)
  · push Not at hbad
    exact Or.inl (S.residual_integer_target_good_at_prime (by omega) L hl hs hbad.1 hqp hbad.2)

end DkMath.FLT.Frey.Source
