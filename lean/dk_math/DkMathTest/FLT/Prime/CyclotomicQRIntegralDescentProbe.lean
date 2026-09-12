/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.CyclotomicQRIntegralDescent

#print "file: DkMathTest.FLT.Prime.CyclotomicQRIntegralDescentProbe"

namespace DkMathTest.FLT.Prime

open DkMath.NumberTheory.CyclotomicQRGaloisAction
open DkMath.NumberTheory.CyclotomicQRIntegralDescent

noncomputable section

private instance factPrime3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
private instance factPrime5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
private instance factPrime7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
private instance factPrime11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩
private instance factPrime13 : Fact (Nat.Prime 13) := ⟨by norm_num⟩

private abbrev cycloField (p : ℕ) := CyclotomicField p ℚ

private instance cycloField_isCyclotomicExtension (p : ℕ) [Fact p.Prime] :
    IsCyclotomicExtension {p} ℚ (cycloField p) := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  letI : NeZero (p : ℚ) := ⟨by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero⟩
  exact CyclotomicField.isCyclotomicExtension p ℚ

private def cycloZeta (p : ℕ) [Fact p.Prime] : cycloField p := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  exact IsCyclotomicExtension.zeta p ℚ (cycloField p)

private theorem cycloZeta_isPrimitiveRoot (p : ℕ) [Fact p.Prime] :
    IsPrimitiveRoot (cycloZeta p) p := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  exact IsCyclotomicExtension.zeta_spec p ℚ (cycloField p)

private theorem integral_descent_regression
    (p : ℕ) [Fact p.Prime] :
    (∃ RZ : MvPolynomial (Fin 2) ℤ,
      MvPolynomial.map (algebraMap ℤ (cycloField p)) RZ =
        Rpoly (p := p) (cycloZeta p)) ∧
    (∃ D2Z : MvPolynomial (Fin 2) ℤ,
      MvPolynomial.map (algebraMap ℤ (cycloField p)) D2Z =
        Dpoly (p := p) (cycloZeta p) ^ 2) := by
  exact ⟨
    exists_Rpoly_over_int (cycloZeta p) (cycloZeta_isPrimitiveRoot p),
    exists_Dpoly_sq_over_int (cycloZeta p) (cycloZeta_isPrimitiveRoot p)⟩

example := integral_descent_regression 3
example := integral_descent_regression 5
example := integral_descent_regression 7
example := integral_descent_regression 11
example := integral_descent_regression 13

example {p : ℕ} [Fact p.Prime] (a : ZMod p) :
    IsIntegral ℤ ((cycloZeta p) ^ a.val) := by
  exact (IsPrimitiveRoot.isIntegral (cycloZeta_isPrimitiveRoot p)
    (Fact.out : Nat.Prime p).pos).pow _

example {p : ℕ} [Fact p.Prime] (d : Fin 2 →₀ ℕ) :
    IsIntegral ℤ (MvPolynomial.coeff d (Rpoly (p := p) (cycloZeta p))) := by
  exact coeff_Rpoly_isIntegral_int (cycloZeta p)
    (cycloZeta_isPrimitiveRoot p) d

example {p : ℕ} [Fact p.Prime] (d : Fin 2 →₀ ℕ) :
    IsIntegral ℤ (MvPolynomial.coeff d (Dpoly (p := p) (cycloZeta p) ^ 2)) := by
  exact coeff_Dpoly_sq_isIntegral_int (cycloZeta p)
    (cycloZeta_isPrimitiveRoot p) d

#print axioms rootFactorPoly_integral
#print axioms qrFactorPoly_integral
#print axioms qnrFactorPoly_integral
#print axioms Rpoly_integral
#print axioms Dpoly_sq_integral
#print axioms isIntegral_rat_of_map_isIntegral
#print axioms rat_isIntegral_iff_exists_int
#print axioms exists_Rpoly_over_int
#print axioms exists_Dpoly_sq_over_int

end

end DkMathTest.FLT.Prime
