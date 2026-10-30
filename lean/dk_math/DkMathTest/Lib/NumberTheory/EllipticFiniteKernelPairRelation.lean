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

#print axioms
  DkMath.Lib.NumberTheory.EllipticFiniteKernel.veluHalf_base_pair_relation_of_translated_root_product

end DkMathTest.EllipticFiniteKernelPairRelation
