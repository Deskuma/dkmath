/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelDiscriminantNormalization
import DkMath.Lib.NumberTheory.EllipticFiniteKernelWronskianSpecialization

#print "file: DkMathTest.Lib.NumberTheory.EllipticFiniteKernelDiscriminantNormalization"

namespace DkMathTest.EllipticFiniteKernelDiscriminantNormalization

open Polynomial
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory.EllipticFunctionField
  DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
  DkMath.Lib.NumberTheory.EllipticPointEvaluation
open DkMath.Lib.Algebra
open DkMath.Lib.Algebra.FiniteProductWronskian
open DkMath.Lib.Algebra.RationalPolynomialFiber
open DkMath.Lib.NumberTheory.WeierstrassDiscriminantAssembly
open DkMath.Lib.NumberTheory.EllipticFiniteKernel

noncomputable local instance instDecidableEqEllipticFiniteKernelDiscriminantNormalizationTest
    {α : Type*} : DecidableEq α := Classical.decEq _

variable {F : Type*} [Field F] [CharZero F] [NeZero (2 : F)]

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (P Q : (AlgebraicClosure F)[X])
    (hQ : Polynomial.aeval (genericX E (AlgebraicClosure F)) Q ≠ 0)
    (hrel : veluX E H =
      Polynomial.aeval (genericX E (AlgebraicClosure F)) P /
        Polynomial.aeval (genericX E (AlgebraicClosure F)) Q)
    (hcop : IsCoprime P Q) :
    P ∣ veluHalfNumeratorBase E H :=
  veluX_standard_pair_numerator_dvd E H ho P Q hQ hrel hcop

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (P Q : (AlgebraicClosure F)[X])
    (hQ : Polynomial.aeval (genericX E (AlgebraicClosure F)) Q ≠ 0)
    (hrel : veluX E H =
      Polynomial.aeval (genericX E (AlgebraicClosure F)) P /
        Polynomial.aeval (genericX E (AlgebraicClosure F)) Q)
    (hcop : IsCoprime P Q) :
    Q ∣ veluHalfDenominatorBase E H :=
  veluX_standard_pair_denominator_dvd E H ho P Q hQ hrel hcop

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (P Q : (AlgebraicClosure F)[X])
    (hQ : Polynomial.aeval (genericX E (AlgebraicClosure F)) Q ≠ 0)
    (hrel : veluX E H =
      Polynomial.aeval (genericX E (AlgebraicClosure F)) P /
        Polynomial.aeval (genericX E (AlgebraicClosure F)) Q)
    (hcop : IsCoprime P Q)
    (hP : P.Monic)
    (hA : (veluHalfNumeratorBase E H).Monic)
    (hdeg : (veluHalfNumeratorBase E H).natDegree ≤ P.natDegree) :
    P = veluHalfNumeratorBase E H :=
  veluX_standard_pair_numerator_eq_of_monic E H ho P Q hQ hrel hcop hP hA hdeg

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (P Q : (AlgebraicClosure F)[X])
    (hQ : Polynomial.aeval (genericX E (AlgebraicClosure F)) Q ≠ 0)
    (hrel : veluX E H =
      Polynomial.aeval (genericX E (AlgebraicClosure F)) P /
        Polynomial.aeval (genericX E (AlgebraicClosure F)) Q)
    (hcop : IsCoprime P Q)
    (hQmonic : Q.Monic)
    (hD : (veluHalfDenominatorBase E H).Monic)
    (hdeg : (veluHalfDenominatorBase E H).natDegree ≤ Q.natDegree) :
    Q = veluHalfDenominatorBase E H :=
  veluX_standard_pair_denominator_eq_of_monic E H ho P Q hQ hrel hcop
    hQmonic hD hdeg

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (P Q : (AlgebraicClosure F)[X])
    (hQ : Polynomial.aeval (genericX E (AlgebraicClosure F)) Q ≠ 0)
    (hrel : veluX E H =
      Polynomial.aeval (genericX E (AlgebraicClosure F)) P /
        Polynomial.aeval (genericX E (AlgebraicClosure F)) Q)
    (hcop : IsCoprime P Q)
    (hP : P.Monic) (hQmonic : Q.Monic)
    (hA : (veluHalfNumeratorBase E H).Monic)
    (hD : (veluHalfDenominatorBase E H).Monic)
    (hPdeg : (veluHalfNumeratorBase E H).natDegree ≤ P.natDegree)
    (hQdeg : (veluHalfDenominatorBase E H).natDegree ≤ Q.natDegree) :
    P = veluHalfNumeratorBase E H ∧ Q = veluHalfDenominatorBase E H :=
  veluX_standard_pair_eq_of_monic E H ho P Q hQ hrel hcop hP hQmonic hA hD hPdeg hQdeg

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (P Q : (AlgebraicClosure F)[X])
    (hQ : Polynomial.aeval (genericX E (AlgebraicClosure F)) Q ≠ 0)
    (hrel : veluX E H =
      Polynomial.aeval (genericX E (AlgebraicClosure F)) P /
        Polynomial.aeval (genericX E (AlgebraicClosure F)) Q)
    (hcop : IsCoprime P Q)
    (hP : P.Monic) (hQmonic : Q.Monic)
    (hA : (veluHalfNumeratorBase E H).Monic)
    (hD : (veluHalfDenominatorBase E H).Monic)
    (hPdeg : (veluHalfNumeratorBase E H).natDegree ≤ P.natDegree)
    (hQdeg : (veluHalfDenominatorBase E H).natDegree ≤ Q.natDegree) :
    wronskian P Q =
      wronskian (veluHalfNumeratorBase E H) (veluHalfDenominatorBase E H) :=
  veluX_standard_pair_wronskian_eq_base_of_monic E H ho P Q hQ hrel hcop
    hP hQmonic hA hD hPdeg hQdeg

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (P Q : (AlgebraicClosure F)[X])
    (hQ : Polynomial.aeval (genericX E (AlgebraicClosure F)) Q ≠ 0)
    (hrel : veluX E H =
      Polynomial.aeval (genericX E (AlgebraicClosure F)) P /
        Polynomial.aeval (genericX E (AlgebraicClosure F)) Q)
    (hcop : IsCoprime P Q)
    (hP : P.Monic) (hQmonic : Q.Monic)
    (hA : (veluHalfNumeratorBase E H).Monic)
    (hD : (veluHalfDenominatorBase E H).Monic)
    (hPdeg : (veluHalfNumeratorBase E H).natDegree ≤ P.natDegree)
    (hQdeg : (veluHalfDenominatorBase E H).natDegree ≤ Q.natDegree)
    (T : Points E) (hT : T ∉ H) (R : H) :
    Q.eval (T + R.val).xc ≠ 0 :=
  veluX_standard_pair_denominator_eval_ne_zero_of_monic E H ho P Q hQ hrel hcop
    hP hQmonic hA hD hPdeg hQdeg T hT R

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (P Q : (AlgebraicClosure F)[X])
    (hQ : Polynomial.aeval (genericX E (AlgebraicClosure F)) Q ≠ 0)
    (hrel : veluX E H =
      Polynomial.aeval (genericX E (AlgebraicClosure F)) P /
        Polynomial.aeval (genericX E (AlgebraicClosure F)) Q)
    (hcop : IsCoprime P Q)
    (hP : P.Monic) (hQmonic : Q.Monic)
    (hA : (veluHalfNumeratorBase E H).Monic)
    (hD : (veluHalfDenominatorBase E H).Monic)
    (hPdeg : (veluHalfNumeratorBase E H).natDegree ≤ P.natDegree)
    (hQdeg : (veluHalfDenominatorBase E H).natDegree ≤ Q.natDegree)
    (T : Points E) (hT : T ∉ H) (hneg : -T = T)
    (R : H) (hR : R ≠ 0) :
    (wronskian P Q).IsRoot (T + R.val).xc :=
  veluX_standard_pair_wronskian_root_of_monic_normalization E H ho P Q hQ hrel hcop
    hP hQmonic hA hD hPdeg hQdeg T hT hneg R hR

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (T : Points E) (hT : T ∉ H) (hneg : -T = T)
    (P Q : (AlgebraicClosure F)[X]) (hcop : IsCoprime P Q) (hQ : Q ≠ 0)
    (hrel : veluX E H =
      Polynomial.aeval (genericX E (AlgebraicClosure F)) P /
        Polynomial.aeval (genericX E (AlgebraicClosure F)) Q)
    (c : AlgebraicClosure F)
    (hp : (fiberPolynomial P Q c).Monic)
    (hPc : kernelXAt E H T hT = c)
    (hP : P.Monic) (hQmonic : Q.Monic)
    (hA : (veluHalfNumeratorBase E H).Monic)
    (hD : (veluHalfDenominatorBase E H).Monic)
    (hPdeg : (veluHalfNumeratorBase E H).natDegree ≤ P.natDegree)
    (hQdeg : (veluHalfDenominatorBase E H).natDegree ≤ Q.natDegree)
    (hdeg : (fiberPolynomial P Q c).natDegree ≤ Nat.card H) :
    fiberPolynomial P Q c =
      fiberFactor (Finset.univ : Finset (halfKernel E H)) T.xc
        (fun R : halfKernel E H => (T + R.val.val).xc) :=
  eq_orbit_x_fiberFactor_of_monic_of_veluX_quotient_of_monic_normalization
    E H ho T hT hneg P Q hcop hQ hrel c hp hPc hP hQmonic hA hD hPdeg hQdeg hdeg

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) :
    IsCoprime (veluHalfNumeratorBase E H) (veluHalfDenominatorBase E H) :=
  veluHalf_base_isCoprime E H ho

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (T : Points E) (hT : T ∉ H) (hneg : -T = T)
    (c : AlgebraicClosure F)
    (hTc : kernelXAt E H T hT = c)
    (hp : (fiberPolynomial (veluHalfNumeratorBase E H)
      (veluHalfDenominatorBase E H) c).Monic)
    (hdeg : (fiberPolynomial (veluHalfNumeratorBase E H)
      (veluHalfDenominatorBase E H) c).natDegree ≤ Nat.card H) :
    fiberPolynomial (veluHalfNumeratorBase E H)
        (veluHalfDenominatorBase E H) c =
      fiberFactor (Finset.univ : Finset (halfKernel E H)) T.xc
        (fun R : halfKernel E H => (T + R.val.val).xc) :=
  veluHalf_base_special_fiber E H ho T hT hneg c hTc hp hdeg

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (T : Points E) (hT : T ∉ H) (hneg : -T = T)
    (c : AlgebraicClosure F)
    (hTc : kernelXAt E H T hT = c) :
    fiberPolynomial (veluHalfNumeratorBase E H)
        (veluHalfDenominatorBase E H) c =
      fiberFactor (Finset.univ : Finset (halfKernel E H)) T.xc
        (fun R : halfKernel E H => (T + R.val.val).xc) :=
  veluHalf_base_special_fiber_of_odd_twoTorsion E H ho T hT hneg c hTc

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) (hcard : 1 < Nat.card H)
    (T : Points E) (hT : T ∉ H) (hneg : -T = T)
    (c : AlgebraicClosure F)
    (hTc : kernelXAt E H T hT = c) :
    (fiberPolynomial (veluHalfNumeratorBase E H)
      (veluHalfDenominatorBase E H) c).discr = 0 :=
  veluHalf_base_special_fiber_discr_eq_zero_of_one_lt_card
    E H ho hcard T hT hneg c hTc

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) (hcard : 1 < Nat.card H)
    (P : Points E) (hP : P ∉ H) (hP2 : 2 • P ∈ H)
    (c : AlgebraicClosure F)
    (hPc : kernelXAt E H P hP = c) :
    (fiberPolynomial (veluHalfNumeratorBase E H)
      (veluHalfDenominatorBase E H) c).discr = 0 :=
  veluHalf_base_special_fiber_discr_eq_zero_of_two_smul_mem
    E H ho hcard P hP hP2 c hPc

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (P : Points E) (hP : P ∉ H) (htwo : 2 • P ∉ H)
    (c : AlgebraicClosure F)
    (hPc : kernelXAt E H P hP = c) :
    fiberPolynomial (veluHalfNumeratorBase E H)
        (veluHalfDenominatorBase E H) c =
      ∏ Q : H, (Polynomial.X - Polynomial.C ((P + Q.val).xc)) :=
  veluHalf_base_general_fiber_of_two_smul_not_mem E H ho P hP htwo c hPc

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (P : Points E) (hP : P ∉ H) (htwo : 2 • P ∉ H)
    (c : AlgebraicClosure F)
    (hPc : kernelXAt E H P hP = c) :
    (fiberPolynomial (veluHalfNumeratorBase E H)
      (veluHalfDenominatorBase E H) c).discr ≠ 0 :=
  veluHalf_base_general_fiber_discr_ne_zero_of_two_smul_not_mem
    E H ho P hP htwo c hPc

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) (hcard : 1 < Nat.card H)
    (P : Points E) (hP : P ∉ H)
    (c : AlgebraicClosure F)
    (hPc : kernelXAt E H P hP = c) :
    (fiberPolynomial (veluHalfNumeratorBase E H)
      (veluHalfDenominatorBase E H) c).discr = 0 ↔ 2 • P ∈ H :=
  veluHalf_base_fiber_discr_eq_zero_iff_two_smul_mem
    E H ho hcard P hP c hPc

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (P Q : (AlgebraicClosure F)[X])
    (hQ : Polynomial.aeval (genericX E (AlgebraicClosure F)) Q ≠ 0)
    (hrel : veluX E H =
      Polynomial.aeval (genericX E (AlgebraicClosure F)) P /
        Polynomial.aeval (genericX E (AlgebraicClosure F)) Q)
    (hPdeg : P.natDegree = Nat.card H) :
    ∃ u : AlgebraicClosure F, u ≠ 0 ∧
      P = Polynomial.C u * veluHalfNumeratorBase E H ∧
      Q = Polynomial.C u * veluHalfDenominatorBase E H :=
  veluX_standard_pair_proportional_to_veluHalf_base
    E H ho P Q hQ hrel hPdeg

example (A D P Q : (AlgebraicClosure F)[X]) (u c : AlgebraicClosure F)
    (hP : P = Polynomial.C u * A) (hQ : Q = Polynomial.C u * D) :
    fiberPolynomial P Q c = Polynomial.C u * fiberPolynomial A D c :=
  fiberPolynomial_eq_C_mul_of_proportional hP hQ

example (A D P Q : (AlgebraicClosure F)[X]) (u c : AlgebraicClosure F)
    (hu : u ≠ 0)
    (hP : P = Polynomial.C u * A) (hQ : Q = Polynomial.C u * D) :
    normalize (fiberPolynomial P Q c) = normalize (fiberPolynomial A D c) :=
  normalize_fiberPolynomial_eq_of_proportional hu hP hQ

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (P Q : (AlgebraicClosure F)[X])
    (hQ : Polynomial.aeval (genericX E (AlgebraicClosure F)) Q ≠ 0)
    (hrel : veluX E H =
      Polynomial.aeval (genericX E (AlgebraicClosure F)) P /
        Polynomial.aeval (genericX E (AlgebraicClosure F)) Q)
    (hPdeg : P.natDegree = Nat.card H)
    (T : Points E) (hT : T ∉ H) (hneg : -T = T)
    (c : AlgebraicClosure F)
    (hTc : kernelXAt E H T hT = c) :
    normalize (fiberPolynomial P Q c) =
      fiberFactor (Finset.univ : Finset (halfKernel E H)) T.xc
        (fun R : halfKernel E H => (T + R.val.val).xc) :=
  veluX_standard_pair_special_fiber_of_odd_twoTorsion
    E H ho P Q hQ hrel hPdeg T hT hneg c hTc

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (P : Points E) (hP : P ∉ H) (hneg : -P = P)
    (c e : AlgebraicClosure F)
    (hPc : kernelXAt E H P hP = c) :
    (fiberPolynomial (veluHalfNumeratorBase E H)
      (veluHalfDenominatorBase E H) c).eval e =
      (e - P.xc) *
        (∏ Q : halfKernel E H, (e - (P + Q.val.val).xc)) ^ 2 :=
  veluHalf_base_special_fiber_eval_eq_root_distance_product_sq
    E H ho P hP hneg c hPc e

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (R : Points E) (hR : R ∉ H) (c : AlgebraicClosure F) :
    (veluHalfNumeratorBase E H).eval R.xc -
        c * (veluHalfDenominatorBase E H).eval R.xc =
      (kernelXAt E H R hR - c) *
        (veluHalfDenominatorBase E H).eval R.xc :=
  veluHalf_base_eval_sub_eq_kernelXAt_sub_mul_denominator E H ho R hR c

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (P R : Points E) (hP : P ∉ H) (hR : R ∉ H)
    (hneg : -P = P) (c : AlgebraicClosure F)
    (hPc : kernelXAt E H P hP = c) :
    (kernelXAt E H R hR - c) *
        (∏ Q ∈ halfKernel E H, (Q.val.xc - R.xc)) ^ 2 =
      (R.xc - P.xc) *
        (∏ Q : halfKernel E H,
          (R.xc - (P + Q.val.val).xc)) ^ 2 :=
  veluHalf_base_special_fiber_intersection_eval E H ho P hP hneg c hPc R hR

#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluX_standard_pair_numerator_dvd
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluX_standard_pair_denominator_dvd
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluX_standard_pair_numerator_eq_of_monic
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluX_standard_pair_denominator_eq_of_monic
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluX_standard_pair_eq_of_monic
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluX_standard_pair_wronskian_eq_base_of_monic
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluX_standard_pair_denominator_eval_ne_zero_of_monic
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluX_standard_pair_wronskian_root_of_monic_normalization
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.eq_orbit_x_fiberFactor_of_monic_of_veluX_quotient_of_monic_normalization
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluHalf_base_isCoprime
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluHalf_base_special_fiber
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluHalf_base_special_fiber_of_odd_twoTorsion
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluHalf_base_special_fiber_discr_eq_zero_of_one_lt_card
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluHalf_base_special_fiber_discr_eq_zero_of_two_smul_mem
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluHalf_base_general_fiber_of_two_smul_not_mem
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluHalf_base_general_fiber_discr_ne_zero_of_two_smul_not_mem
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluHalf_base_fiber_discr_eq_zero_iff_two_smul_mem
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluX_standard_pair_proportional_to_veluHalf_base
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.fiberPolynomial_eq_C_mul_of_proportional
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.normalize_fiberPolynomial_eq_of_proportional
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluX_standard_pair_special_fiber_of_odd_twoTorsion
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluHalf_base_special_fiber_eval_eq_root_distance_product_sq
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluHalf_base_eval_sub_eq_kernelXAt_sub_mul_denominator
#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluHalf_base_special_fiber_intersection_eval

end DkMathTest.EllipticFiniteKernelDiscriminantNormalization
