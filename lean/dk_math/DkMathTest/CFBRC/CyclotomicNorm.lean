/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.CFBRC.CyclotomicNorm

#print "file: DkMathTest.CFBRC.CyclotomicNorm"

namespace DkMathTest.CFBRC

open DkMath.CFBRC
open DkMath.CosmicFormula
open DkMath.CosmicFormulaBinom
open DkMath.NumberTheory.CyclotomicQRProduct
open NumberField

noncomputable section

private instance factPrime3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
private instance factPrime5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
private instance factPrime7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

private abbrev cycloField (p : ℕ) := CyclotomicField p ℚ

private instance cycloField_isCyclotomicExtension (p : ℕ) [Fact p.Prime] :
    IsCyclotomicExtension {p} ℚ (cycloField p) := by
  let : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  let : NeZero (p : ℚ) := ⟨by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero⟩
  exact CyclotomicField.isCyclotomicExtension p ℚ

private def cycloZeta (p : ℕ) [Fact p.Prime] : cycloField p := by
  let : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  exact IsCyclotomicExtension.zeta p ℚ (cycloField p)

private theorem cycloZeta_isPrimitiveRoot (p : ℕ) [Fact p.Prime] :
    IsPrimitiveRoot (cycloZeta p) p := by
  let : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  exact IsCyclotomicExtension.zeta_spec p ℚ (cycloField p)

private theorem norm_regression (p : ℕ) [Fact p.Prime] :
    Algebra.norm ℤ
        (cyclotomicLinearFactorInRingOfIntegers
          (cycloZeta_isPrimitiveRoot p) 1 1) =
      ((DkMath.CosmicFormulaBinom.GN p 1 1 : ℕ) : ℤ) := by
  exact cyclotomicLinearFactor_norm_eq_GN
    (p := p) (x := 1) (u := 1) (cycloZeta_isPrimitiveRoot p)

private theorem zero_base_norm_regression (p : ℕ) [Fact p.Prime] :
    Algebra.norm ℤ
        (cyclotomicLinearFactorInRingOfIntegers
          (cycloZeta_isPrimitiveRoot p) 1 0) =
      ((DkMath.CosmicFormulaBinom.GN p 1 0 : ℕ) : ℤ) := by
  exact cyclotomicLinearFactor_norm_eq_GN
    (p := p) (x := 1) (u := 0) (cycloZeta_isPrimitiveRoot p)

example := norm_regression 3
example := norm_regression 5
example := norm_regression 7

example := zero_base_norm_regression 3
example := zero_base_norm_regression 5
example := zero_base_norm_regression 7

example :
    Algebra.norm ℤ
        (cyclotomicLinearFactorInRingOfIntegers
          (cycloZeta_isPrimitiveRoot 3) 0 0) =
      ((DkMath.CosmicFormulaBinom.GN 3 0 0 : ℕ) : ℤ) := by
  exact cyclotomicLinearFactor_norm_eq_GN
    (p := 3) (x := 0) (u := 0) (cycloZeta_isPrimitiveRoot 3)

example (p : ℕ) [Fact p.Prime] (x u : ℕ) :
    cyclotomicRootProduct (p := p) (cycloZeta p) (x : cycloField p) (u : cycloField p) =
      GTailCyclotomicShell p (x : cycloField p) (u : cycloField p) :=
  cyclotomicRootProduct_eq_shell (p := p) (cycloZeta p)
    (cycloZeta_isPrimitiveRoot p) (x : cycloField p) (u : cycloField p)

example (p : ℕ) [Fact p.Prime] (x u : ℕ) :
    cyclotomicRootProduct (p := p) (cycloZeta p) (x : cycloField p) (u : cycloField p) =
      ((DkMath.CosmicFormulaBinom.GN p x u : ℕ) : cycloField p) := by
  rw [cyclotomicRootProduct_eq_GN (p := p) (cycloZeta p)
    (cycloZeta_isPrimitiveRoot p)]
  simp [DkMath.CosmicFormula.GN]

example (d u : ℕ) :
    GTail d 1 0 u = GTailCyclotomicShell d 0 u := by
  exact GTail_one_eq_GTailCyclotomicShell d 0 u

#print axioms DkMath.CFBRC.cyclotomicLinearFactor_norm_eq_GN_ratCast
#print axioms DkMath.CFBRC.cyclotomicLinearFactor_norm_eq_GN
#print axioms DkMath.CFBRC.cyclotomicRootProduct_eq_GN
#print axioms DkMath.CFBRC.cyclotomicRootProduct_eq_shell

end

end DkMathTest.CFBRC
