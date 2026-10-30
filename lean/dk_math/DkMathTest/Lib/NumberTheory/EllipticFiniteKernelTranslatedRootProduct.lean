/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelTranslatedRootProduct

#print "file: DkMathTest.Lib.NumberTheory.EllipticFiniteKernelTranslatedRootProduct"

namespace DkMathTest.EllipticFiniteKernelTranslatedRootProduct

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open DkMath.Lib.NumberTheory.EllipticFiniteKernel
open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K]
noncomputable local instance {α : Type*} : DecidableEq α := Classical.decEq _

example (E : WeierstrassCurve K) (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (r₁ r₂ r₃ t₁ : AlgebraicClosure K)
    (h₁ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval r₁ = 0)
    (h₂ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval r₂ = 0)
    (h₃ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval r₃ = 0)
    (h₁₂ : r₁ ≠ r₂) (h₁₃ : r₁ ≠ r₃) (h₂₃ : r₂ ≠ r₃)
    (hσ₁ : 4 * (r₁ + r₂ + r₃) = -((E.map (algebraMap K (AlgebraicClosure K))).a₁ ^ 2 +
      4 * (E.map (algebraMap K (AlgebraicClosure K))).a₂))
    (hTtwo : 2 * t₁ +
      (E.map (algebraMap K (AlgebraicClosure K))).a₁ * r₁ +
        (E.map (algebraMap K (AlgebraicClosure K))).a₃ = 0) :
    (∏ Q : halfKernel E H,
      (r₂ - (E.map (algebraMap K (AlgebraicClosure K))).toAffine.addX r₁
        Q.val.val.xc
        ((E.map (algebraMap K (AlgebraicClosure K))).toAffine.slope r₁
          Q.val.val.xc t₁ Q.val.val.yc))) *
        (∏ Q : halfKernel E H, (Q.val.val.xc - r₁)) =
      (r₂ - r₁) ^ (halfKernel E H).card *
        ∏ Q : halfKernel E H, (Q.val.val.xc - r₃) :=
  halfKernel_translated_root_product_relation E H ho r₁ r₂ r₃ t₁
    h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hσ₁ hTtwo

example (E : WeierstrassCurve K) (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (r₁ r₂ r₃ t₁ : AlgebraicClosure K)
    (h₁ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval r₁ = 0)
    (h₂ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval r₂ = 0)
    (h₃ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval r₃ = 0)
    (h₁₂ : r₁ ≠ r₂) (h₁₃ : r₁ ≠ r₃) (h₂₃ : r₂ ≠ r₃)
    (hTtwo : 2 * t₁ +
      (E.map (algebraMap K (AlgebraicClosure K))).a₁ * r₁ +
        (E.map (algebraMap K (AlgebraicClosure K))).a₃ = 0) :
    (∏ Q : halfKernel E H,
      (r₂ - (E.map (algebraMap K (AlgebraicClosure K))).toAffine.addX r₁
        Q.val.val.xc
        ((E.map (algebraMap K (AlgebraicClosure K))).toAffine.slope r₁
          Q.val.val.xc t₁ Q.val.val.yc))) *
        (∏ Q : halfKernel E H, (Q.val.val.xc - r₁)) =
      (r₂ - r₁) ^ (halfKernel E H).card *
        ∏ Q : halfKernel E H, (Q.val.val.xc - r₃) :=
  halfKernel_translated_root_product_relation_of_roots E H ho r₁ r₂ r₃ t₁
    h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hTtwo

example (E : WeierstrassCurve K) (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (r₁ r₂ r₃ t₁ : AlgebraicClosure K)
    (h₁ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval r₁ = 0)
    (h₂ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval r₂ = 0)
    (h₃ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval r₃ = 0)
    (h₁₂ : r₁ ≠ r₂) (h₁₃ : r₁ ≠ r₃) (h₂₃ : r₂ ≠ r₃)
    (hT : (E.map (algebraMap K (AlgebraicClosure K))).toAffine.Nonsingular r₁ t₁)
    (htor : 2 • (Affine.Point.some r₁ t₁ hT) = 0) :
    (∏ Q : halfKernel E H,
      (r₂ - (E.map (algebraMap K (AlgebraicClosure K))).toAffine.addX r₁
        Q.val.val.xc
        ((E.map (algebraMap K (AlgebraicClosure K))).toAffine.slope r₁
          Q.val.val.xc t₁ Q.val.val.yc))) *
        (∏ Q : halfKernel E H, (Q.val.val.xc - r₁)) =
      (r₂ - r₁) ^ (halfKernel E H).card *
        ∏ Q : halfKernel E H, (Q.val.val.xc - r₃) :=
  halfKernel_translated_root_product_relation_of_two_torsion E H ho r₁ r₂ r₃ t₁
    h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hT htor

#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.halfKernel_translated_root_product_relation
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.halfKernel_translated_root_product_relation_of_roots
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.halfKernel_translated_root_product_relation_of_two_torsion

end DkMathTest.EllipticFiniteKernelTranslatedRootProduct
