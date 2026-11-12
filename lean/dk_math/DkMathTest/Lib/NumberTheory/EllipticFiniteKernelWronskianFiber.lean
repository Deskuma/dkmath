/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelWronskianFiber

#print "file: DkMathTest.Lib.NumberTheory.EllipticFiniteKernelWronskianFiber"

namespace DkMathTest.EllipticFiniteKernelWronskianFiber

open Polynomial
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory.EllipticFunctionField
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open DkMath.Lib.Algebra.RationalPolynomialFiber
open DkMath.Lib.NumberTheory.EllipticFiniteKernel
open DkMath.Lib.NumberTheory.WeierstrassDiscriminantAssembly

noncomputable local instance instDecidableEqEllipticFiniteKernelWronskianFiberTest
    {α : Type*} : DecidableEq α := Classical.decEq _

variable {F : Type*} [Field F] [CharZero F]

example (E : WeierstrassCurve F) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (T : Points E) (hT : T ∉ H) (hneg : -T = T)
    (c : AlgebraicClosure F)
    (hTc : kernelXAt E H T hT = c) :
    ∃ P QF : (AlgebraicClosure F)[X],
      IsCoprime P QF ∧ QF ≠ 0 ∧ P.natDegree = Nat.card H ∧
        QF.natDegree < P.natDegree ∧
        veluX E H = aeval (genericX E (AlgebraicClosure F)) P /
          aeval (genericX E (AlgebraicClosure F)) QF ∧
        fiberPolynomial P QF c ≠ 0 ∧
        (normalize (fiberPolynomial P QF c)).Monic ∧
        (normalize (fiberPolynomial P QF c)).natDegree = Nat.card H ∧
        (∀ (R : Points E) (hR : R ∉ H),
          kernelXAt E H R hR = c →
            (normalize (fiberPolynomial P QF c)).IsRoot R.xc) ∧
        normalize (fiberPolynomial P QF c) =
          fiberFactor (Finset.univ : Finset (halfKernel E H)) T.xc
            (fun Q : halfKernel E H => (T + Q.val.val).xc) :=
  exists_veluX_normalized_fiberFactor_of_odd_twoTorsion E H ho T hT hneg c hTc

#print axioms DkMath.Lib.NumberTheory.EllipticFiniteKernel.exists_veluX_normalized_fiberFactor_of_odd_twoTorsion

end DkMathTest.EllipticFiniteKernelWronskianFiber
