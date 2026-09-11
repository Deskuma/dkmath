/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.IdealPowerFactor

#print "file: DkMathTest.FLT.Prime.IdealPowerFactorAuditProbe"

namespace DkMathTest.FLT.Prime

open scoped nonZeroDivisors

example {R : Type*} [CommRing R] [IsDedekindDomain R]
    {I J K : Ideal R} {p : ℕ}
    (hcop : IsCoprime I J) (hpow : I * J = K ^ p) :
    ∃ A : Ideal R, I = A ^ p := by
  exact DkMath.Lib.NumberTheory.exists_eq_pow_of_isCoprime_mul_eq_pow hcop hpow

example {R : Type*} [CommRing R] [IsDedekindDomain R]
    {I : Ideal R} (hI : I ∈ (Ideal R)⁰) {p : ℕ}
    (hfree : DkMath.Lib.NumberTheory.classGroupPTorsionFreeAt R p)
    (hPrincipal : (I ^ p).IsPrincipal) : I.IsPrincipal := by
  exact DkMath.Lib.NumberTheory.ideal_isPrincipal_of_pow_isPrincipal_of_classGroupPTorsionFreeAt
    hI hfree hPrincipal

example {R : Type*} [CommRing R] [IsDedekindDomain R]
    {I J K : Ideal R} {p : ℕ}
    (hcop : IsCoprime I J) (hpow : I * J = K ^ p) :
    (∃ A : Ideal R, I = A ^ p) ∧ (∃ B : Ideal R, J = B ^ p) := by
  exact DkMath.Lib.NumberTheory.exists_eq_pow_of_isCoprime_mul_eq_pow_pair hcop hpow

end DkMathTest.FLT.Prime
