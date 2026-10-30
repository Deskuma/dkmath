/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelPairRelation

#print "file: DkMathTest.Lib.NumberTheory.EllipticFiniteKernelPairRelation"

namespace DkMathTest.EllipticFiniteKernelPairRelation

open WeierstrassCurve
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open DkMath.Lib.NumberTheory.EllipticFiniteKernel
open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K]

noncomputable local instance {α : Type*} : DecidableEq α := Classical.decEq _

example (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (Pj Pk Pl : Points E)
    (hPj : Pj ∉ H) (hPk : Pk ∉ H)
    (hnegj : -Pj = Pj)
    (htranslated :
      (∏ Q : halfKernel E H, (Pk.xc - (Pj + Q.val.val).xc)) *
          (∏ Q ∈ halfKernel E H, (Q.val.xc - Pj.xc)) =
        (Pk.xc - Pj.xc) ^ (halfKernel E H).card *
          ∏ Q ∈ halfKernel E H, (Q.val.xc - Pl.xc)) :
    (kernelXAt E H Pj hPj - kernelXAt E H Pk hPk) ^ 2 *
        (∏ Q ∈ halfKernel E H, (Q.val.xc - Pj.xc)) ^ 4 *
        (∏ Q ∈ halfKernel E H, (Q.val.xc - Pk.xc)) ^ 4 =
      (Pk.xc - Pj.xc) ^ (2 * (2 * (halfKernel E H).card + 1)) *
        (∏ Q ∈ halfKernel E H, (Q.val.xc - Pl.xc)) ^ 4 :=
  veluHalf_base_pair_relation_of_translated_root_product E H ho Pj Pk Pl
    hPj hPk hnegj htranslated

example (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (Pj Pk Pl : Points E)
    (hPj : Pj ∉ H) (hPk : Pk ∉ H)
    (hnegj : -Pj = Pj)
    (hT : (E.map (algebraMap K (AlgebraicClosure K))).toAffine.Nonsingular Pj.xc Pj.yc)
    (htor : 2 • (Affine.Point.some Pj.xc Pj.yc hT) = 0)
    (h₁ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval Pj.xc = 0)
    (h₂ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval Pk.xc = 0)
    (h₃ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval Pl.xc = 0)
    (h₁₂ : Pj.xc ≠ Pk.xc) (h₁₃ : Pj.xc ≠ Pl.xc)
    (h₂₃ : Pk.xc ≠ Pl.xc) :
    (kernelXAt E H Pj hPj - kernelXAt E H Pk hPk) ^ 2 *
        (∏ Q ∈ halfKernel E H, (Q.val.xc - Pj.xc)) ^ 4 *
        (∏ Q ∈ halfKernel E H, (Q.val.xc - Pk.xc)) ^ 4 =
      (Pk.xc - Pj.xc) ^ (2 * (2 * (halfKernel E H).card + 1)) *
        (∏ Q ∈ halfKernel E H, (Q.val.xc - Pl.xc)) ^ 4 :=
  veluHalf_base_pair_relation_of_two_torsion_points E H ho Pj Pk Pl hPj hPk hnegj
    hT htor h₁ h₂ h₃ h₁₂ h₁₃ h₂₃

example (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (P₁ P₂ P₃ : Points E)
    (hP₁ : P₁ ∉ H) (hP₂ : P₂ ∉ H) (hP₃ : P₃ ∉ H)
    (hneg₁ : -P₁ = P₁) (hneg₂ : -P₂ = P₂)
    (hT₁ : (E.map (algebraMap K (AlgebraicClosure K))).toAffine.Nonsingular P₁.xc P₁.yc)
    (htor₁ : 2 • (Affine.Point.some P₁.xc P₁.yc hT₁) = 0)
    (hT₂ : (E.map (algebraMap K (AlgebraicClosure K))).toAffine.Nonsingular P₂.xc P₂.yc)
    (htor₂ : 2 • (Affine.Point.some P₂.xc P₂.yc hT₂) = 0)
    (h₁ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval P₁.xc = 0)
    (h₂ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval P₂.xc = 0)
    (h₃ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval P₃.xc = 0)
    (h₁₂ : P₁.xc ≠ P₂.xc) (h₁₃ : P₁.xc ≠ P₃.xc)
    (h₂₃ : P₂.xc ≠ P₃.xc)
    (Δ Δ' U : AlgebraicClosure K)
    (hH :
      (∏ Q ∈ halfKernel E H, (Q.val.xc - P₁.xc)) *
        (∏ Q ∈ halfKernel E H, (Q.val.xc - P₂.xc)) *
        (∏ Q ∈ halfKernel E H, (Q.val.xc - P₃.xc)) ≠ 0)
    (hU : U = 4 ^ (halfKernel E H).card *
      ((∏ Q ∈ halfKernel E H, (Q.val.xc - P₁.xc)) *
        (∏ Q ∈ halfKernel E H, (Q.val.xc - P₂.xc)) *
        (∏ Q ∈ halfKernel E H, (Q.val.xc - P₃.xc))))
    (hΔ : Δ = 16 * ((P₂.xc - P₁.xc) * (P₃.xc - P₁.xc) *
      (P₃.xc - P₂.xc)) ^ 2)
    (hΔ' : Δ' = 16 *
      ((kernelXAt E H P₁ hP₁ - kernelXAt E H P₂ hP₂) *
        (kernelXAt E H P₁ hP₁ - kernelXAt E H P₃ hP₃) *
        (kernelXAt E H P₂ hP₂ - kernelXAt E H P₃ hP₃)) ^ 2) :
    Δ' * U ^ 4 = Δ ^ (2 * (halfKernel E H).card + 1) :=
  veluHalf_base_discriminant_product_of_three_two_torsion_points E H ho P₁ P₂ P₃
    hP₁ hP₂ hP₃ hneg₁ hneg₂ hT₁ htor₁ hT₂ htor₂ h₁ h₂ h₃ h₁₂ h₁₃ h₂₃
    Δ Δ' U hH hU hΔ hΔ'

#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluHalf_base_pair_relation_of_translated_root_product
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluHalf_base_pair_relation_of_two_torsion_points
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluHalf_base_discriminant_product_of_three_two_torsion_points

end DkMathTest.EllipticFiniteKernelPairRelation
