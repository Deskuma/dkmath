/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.Algebra.RationalPolynomialDiscriminant

#print "file: DkMathTest.Lib.Algebra.RationalPolynomialDiscriminant"

namespace DkMathTest.Algebra.RationalPolynomialDiscriminant

open Polynomial
open DkMath.Lib.Algebra.RationalPolynomialDiscriminant

variable {K : Type*} [Field K]

noncomputable section

example (φ : K →+* K) {p : K[X]} (hp : 0 < p.degree)
    (hdeg : (p.map φ).natDegree = p.natDegree)
    (hlc : φ p.leadingCoeff ≠ 0) :
    (p.map φ).discr = φ p.discr :=
  discr_map_of_natDegree_eq φ hp hdeg hlc

example (F G : K[X]) : K[X] :=
  fiberDiscriminantFamily F G

example {F G : K[X]} (hdeg : G.natDegree < F.natDegree) :
    (fiberPolynomialFamily F G).natDegree = F.natDegree :=
  fiberPolynomialFamily_natDegree_eq_of_natDegree_lt hdeg

example {F G : K[X]} (hdeg : G.natDegree < F.natDegree) :
    (fiberPolynomialFamily F G).leadingCoeff = Polynomial.C F.leadingCoeff :=
  fiberPolynomialFamily_leadingCoeff_eq_C_of_natDegree_lt hdeg

example (F G : K[X]) (c : K) :
    (fiberPolynomialFamily F G).map (Polynomial.evalRingHom c) =
      DkMath.Lib.Algebra.RationalPolynomialFiber.fiberPolynomial F G c :=
  fiberPolynomialFamily_map_evalRingHom F G c

example (F G : K[X]) (c : K)
    (hp : 0 < (fiberPolynomialFamily F G).degree)
    (hdeg : ((fiberPolynomialFamily F G).map (Polynomial.evalRingHom c)).natDegree =
      (fiberPolynomialFamily F G).natDegree)
    (hlc : Polynomial.evalRingHom c (fiberPolynomialFamily F G).leadingCoeff ≠ 0) :
    (fiberDiscriminantFamily F G).eval c =
      (DkMath.Lib.Algebra.RationalPolynomialFiber.fiberPolynomial F G c).discr :=
  fiberDiscriminantFamily_eval_of_natDegree_eq F G c hp hdeg hlc

example (F G : K[X]) (hdeg : G.natDegree < F.natDegree) (c : K) :
    (fiberDiscriminantFamily F G).eval c =
      (DkMath.Lib.Algebra.RationalPolynomialFiber.fiberPolynomial F G c).discr :=
  fiberDiscriminantFamily_eval_of_natDegree_lt F G hdeg c

#print axioms DkMath.Lib.Algebra.RationalPolynomialDiscriminant.discr_map_of_natDegree_eq
#print axioms DkMath.Lib.Algebra.RationalPolynomialDiscriminant.fiberDiscriminantFamily_eval_of_natDegree_eq
#print axioms DkMath.Lib.Algebra.RationalPolynomialDiscriminant.fiberDiscriminantFamily_eval_of_natDegree_lt

end
end DkMathTest.Algebra.RationalPolynomialDiscriminant
