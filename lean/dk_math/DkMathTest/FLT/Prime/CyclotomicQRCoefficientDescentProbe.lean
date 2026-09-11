/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.CyclotomicQRCoefficientDescent

#print "file: DkMathTest.FLT.Prime.CyclotomicQRCoefficientDescentProbe"

namespace DkMathTest.FLT.Prime

open DkMath.NumberTheory.CyclotomicQRCoefficientDescent
open DkMath.NumberTheory.CyclotomicQRGaloisAction

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

private theorem descent_regression
    (p : ℕ) [Fact p.Prime] :
    (∃ R0 : MvPolynomial (Fin 2) ℚ,
      MvPolynomial.map (algebraMap ℚ (cycloField p)) R0 =
        Rpoly (p := p) (cycloZeta p)) ∧
    (∃ D20 : MvPolynomial (Fin 2) ℚ,
      MvPolynomial.map (algebraMap ℚ (cycloField p)) D20 =
        Dpoly (p := p) (cycloZeta p) ^ 2) := by
  exact ⟨
    exists_Rpoly_over_base (cycloZeta p) (cycloZeta_isPrimitiveRoot p),
    exists_Dpoly_sq_over_base (cycloZeta p) (cycloZeta_isPrimitiveRoot p)⟩

example := descent_regression 3
example := descent_regression 5
example := descent_regression 7
example := descent_regression 11
example := descent_regression 13

example {p : ℕ} [Fact p.Prime] (d : Fin 2 →₀ ℕ) :
    MvPolynomial.coeff d (Rpoly (p := p) (cycloZeta p)) ∈
      Set.range (algebraMap ℚ (cycloField p)) := by
  exact coeff_Rpoly_mem_range_algebraMap (cycloZeta p)
    (cycloZeta_isPrimitiveRoot p) d

example {p : ℕ} [Fact p.Prime] (d : Fin 2 →₀ ℕ) :
    MvPolynomial.coeff d (Dpoly (p := p) (cycloZeta p) ^ 2) ∈
      Set.range (algebraMap ℚ (cycloField p)) := by
  exact coeff_Dpoly_sq_mem_range_algebraMap (cycloZeta p)
    (cycloZeta_isPrimitiveRoot p) d

/-! The p=11/p=13 product-to-shell-to-TraceOne norm checks remain in the
    existing Phase-8 compatibility target; this probe deliberately keeps the
    descended witnesses abstract and does not identify them with A11/B11 or
    A13/B13 coordinates. -/

#print axioms coeff_fixed_of_map_eq
#print axioms coeff_Rpoly_mem_fixedField
#print axioms coeff_Dpoly_sq_mem_fixedField
#print axioms coeff_Rpoly_mem_range_algebraMap
#print axioms coeff_Dpoly_sq_mem_range_algebraMap
#print axioms exists_Rpoly_over_base
#print axioms exists_Dpoly_sq_over_base

end

end DkMathTest.FLT.Prime
