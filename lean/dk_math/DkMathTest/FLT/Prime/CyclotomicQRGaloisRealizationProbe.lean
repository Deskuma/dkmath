/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.CyclotomicQRGaloisRealization

#print "file: DkMathTest.FLT.Prime.CyclotomicQRGaloisRealizationProbe"

namespace DkMathTest.FLT.Prime

open DkMath.NumberTheory.CyclotomicQRGaloisRealization
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

private theorem cycloIrreducible (p : ℕ) [Fact p.Prime] :
    Irreducible (Polynomial.cyclotomic p ℚ) := by
  have hp : Nat.Prime p := Fact.out
  exact Polynomial.cyclotomic.irreducible_rat hp.pos

private theorem full_invariance_regression
    {p : ℕ} [Fact p.Prime]
    (σ : cycloField p ≃ₐ[ℚ] cycloField p) :
    MvPolynomial.map σ.toRingEquiv.toRingHom
        (Rpoly (p := p) (cycloZeta p)) = Rpoly (p := p) (cycloZeta p) ∧
      MvPolynomial.map σ.toRingEquiv.toRingHom
        (Dpoly (p := p) (cycloZeta p) ^ 2) =
        Dpoly (p := p) (cycloZeta p) ^ 2 := by
  exact ⟨
    map_Rpoly_of_cyclotomicAut (cycloZeta p) (cycloZeta_isPrimitiveRoot p) σ,
    map_Dpoly_sq_of_cyclotomicAut (cycloZeta p)
      (cycloZeta_isPrimitiveRoot p) σ⟩

/-! Every nonzero residue is realized at the five finite regression primes. -/

example (t : ZMod 3) (ht : t ≠ 0) :
    ∃ σ : cycloField 3 ≃ₐ[ℚ] cycloField 3,
      σ (cycloZeta 3) = (cycloZeta 3) ^ t.val := by
  exact exists_cyclotomicAut_pow (cycloZeta 3)
    (cycloZeta_isPrimitiveRoot 3) (cycloIrreducible 3) t ht

example (t : ZMod 5) (ht : t ≠ 0) :
    ∃ σ : cycloField 5 ≃ₐ[ℚ] cycloField 5,
      σ (cycloZeta 5) = (cycloZeta 5) ^ t.val := by
  exact exists_cyclotomicAut_pow (cycloZeta 5)
    (cycloZeta_isPrimitiveRoot 5) (cycloIrreducible 5) t ht

example (t : ZMod 7) (ht : t ≠ 0) :
    ∃ σ : cycloField 7 ≃ₐ[ℚ] cycloField 7,
      σ (cycloZeta 7) = (cycloZeta 7) ^ t.val := by
  exact exists_cyclotomicAut_pow (cycloZeta 7)
    (cycloZeta_isPrimitiveRoot 7) (cycloIrreducible 7) t ht

example (t : ZMod 11) (ht : t ≠ 0) :
    ∃ σ : cycloField 11 ≃ₐ[ℚ] cycloField 11,
      σ (cycloZeta 11) = (cycloZeta 11) ^ t.val := by
  exact exists_cyclotomicAut_pow (cycloZeta 11)
    (cycloZeta_isPrimitiveRoot 11) (cycloIrreducible 11) t ht

example (t : ZMod 13) (ht : t ≠ 0) :
    ∃ σ : cycloField 13 ≃ₐ[ℚ] cycloField 13,
      σ (cycloZeta 13) = (cycloZeta 13) ^ t.val := by
  exact exists_cyclotomicAut_pow (cycloZeta 13)
    (cycloZeta_isPrimitiveRoot 13) (cycloIrreducible 13) t ht

/-! Every automorphism fixes the two Phase-9 invariant targets. -/

example (σ : cycloField 3 ≃ₐ[ℚ] cycloField 3) :=
  full_invariance_regression σ

example (σ : cycloField 5 ≃ₐ[ℚ] cycloField 5) :=
  full_invariance_regression σ

example (σ : cycloField 7 ≃ₐ[ℚ] cycloField 7) :=
  full_invariance_regression σ

example (σ : cycloField 11 ≃ₐ[ℚ] cycloField 11) :=
  full_invariance_regression σ

example (σ : cycloField 13 ≃ₐ[ℚ] cycloField 13) :=
  full_invariance_regression σ

example {p : ℕ} [Fact p.Prime] (t : ZMod p) (ht : t ≠ 0) :
    (nonzeroExponentUnit t ht : ZMod p) = t := by
  exact coe_nonzeroExponentUnit t ht

#print axioms exists_cyclotomicAut_pow
#print axioms cyclotomicAut_power_spec
#print axioms map_Rpoly_of_cyclotomicAut
#print axioms map_Dpoly_of_cyclotomicAut
#print axioms map_Dpoly_sq_of_cyclotomicAut
#print axioms coe_nonzeroExponentUnit

end

end DkMathTest.FLT.Prime
