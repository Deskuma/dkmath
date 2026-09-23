/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.CFBRC.CyclotomicIdeal

#print "file: DkMathTest.CFBRC.CyclotomicIdeal"

namespace DkMathTest.CFBRC

open DkMath.CFBRC
open DkMath.CosmicFormulaBinom
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

private theorem absNorm_regression (p : ℕ) [Fact p.Prime] :
    Ideal.absNorm
        (cyclotomicLinearFactorIdeal
          (cycloZeta_isPrimitiveRoot p) 1 1) =
      (DkMath.CosmicFormulaBinom.GN p 1 1 : ℕ) := by
  exact cyclotomicLinearFactorIdeal_absNorm_eq_GN
    (p := p) (x := 1) (u := 1) (cycloZeta_isPrimitiveRoot p)

private theorem zero_base_absNorm_regression (p : ℕ) [Fact p.Prime] :
    Ideal.absNorm
        (cyclotomicLinearFactorIdeal
          (cycloZeta_isPrimitiveRoot p) 1 0) =
      (DkMath.CosmicFormulaBinom.GN p 1 0 : ℕ) := by
  exact cyclotomicLinearFactorIdeal_absNorm_eq_GN
    (p := p) (x := 1) (u := 0) (cycloZeta_isPrimitiveRoot p)

example := absNorm_regression 3
example := absNorm_regression 5
example := absNorm_regression 7

example := zero_base_absNorm_regression 3
example := zero_base_absNorm_regression 5
example := zero_base_absNorm_regression 7

example (p : ℕ) [Fact p.Prime] (x u : ℕ) :
    x * Ideal.absNorm
        (cyclotomicLinearFactorIdeal
          (cycloZeta_isPrimitiveRoot p) x u) =
      (x + u) ^ p - u ^ p := by
  exact gap_mul_cyclotomicLinearFactorIdeal_absNorm_eq_sub_pow
    (p := p) (x := x) (u := u) (cycloZeta_isPrimitiveRoot p)

example (p x u q : ℕ) [Fact p.Prime] :
    q ∣ Ideal.absNorm
        (cyclotomicLinearFactorIdeal
          (cycloZeta_isPrimitiveRoot p) x u) ↔
      q ∣ DkMath.CosmicFormulaBinom.GN p x u := by
  exact dvd_cyclotomicLinearFactorIdeal_absNorm_iff_dvd_GN
    (p := p) (x := x) (u := u) (q := q) (cycloZeta_isPrimitiveRoot p)

example (p x u q : ℕ) [Fact p.Prime] :
    q ∣ ((x + u) ^ p - u ^ p) ↔
      q ∣ x * Ideal.absNorm
        (cyclotomicLinearFactorIdeal
          (cycloZeta_isPrimitiveRoot p) x u) := by
  exact dvd_sub_pow_iff_dvd_gap_mul_cyclotomicLinearFactorIdeal_absNorm
    (p := p) (x := x) (u := u) (q := q) (cycloZeta_isPrimitiveRoot p)

example (p x u q : ℕ) [Fact p.Prime] :
    padicValNat q
        (Ideal.absNorm
          (cyclotomicLinearFactorIdeal
            (cycloZeta_isPrimitiveRoot p) x u)) =
      padicValNat q (DkMath.CosmicFormulaBinom.GN p x u) := by
  exact padicValNat_cyclotomicLinearFactorIdeal_absNorm_eq_GN
    (p := p) (x := x) (u := u) (q := q) (cycloZeta_isPrimitiveRoot p)

example :
    padicValNat 2
        (Ideal.absNorm
          (cyclotomicLinearFactorIdeal
            (cycloZeta_isPrimitiveRoot 3) 1 1)) =
      padicValNat 2 ((1 + 1) ^ 3 - 1 ^ 3) := by
  exact padicValNat_cyclotomicLinearFactorIdeal_absNorm_eq_sub_pow_of_not_dvd_boundary
    (p := 3) (x := 1) (u := 1) (q := 2)
    (cycloZeta_isPrimitiveRoot 3) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

#print axioms DkMath.CFBRC.cyclotomicLinearFactorIdeal_absNorm_eq_GN
#print axioms DkMath.CFBRC.gap_mul_cyclotomicLinearFactorIdeal_absNorm_eq_sub_pow
#print axioms DkMath.CFBRC.padicValNat_cyclotomicLinearFactorIdeal_absNorm_eq_GN
#print axioms DkMath.CFBRC.padicValNat_cyclotomicLinearFactorIdeal_absNorm_eq_sub_pow_of_not_dvd_boundary

end

end DkMathTest.CFBRC
