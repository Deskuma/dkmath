/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Prime.PrimeCyclotomicIdeal
import DkMath.FLT.Seven.SevenAdicPowerSplit

#print "file: DkMathTest.FLT.Prime.PrimeCyclotomicIdeal"

namespace DkMathTest.FLT.Prime

open DkMath.CFBRC
open DkMath.CosmicFormula
open DkMath.FLT.Prime
open DkMath.FLT.Seven
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

section AdicPacket

variable {p g u x : ℕ} [Fact p.Prime]
variable (P : PrimeAdicFactorPacket p g u x)

example :
    Ideal.absNorm
        (cyclotomicLinearFactorIdeal
          (cycloZeta_isPrimitiveRoot p) g u) =
      GTail p 1 g u :=
  P.cyclotomicIdeal_absNorm_eq_residual (cycloZeta_isPrimitiveRoot p)

example :
    g * Ideal.absNorm
        (cyclotomicLinearFactorIdeal
          (cycloZeta_isPrimitiveRoot p) g u) = x ^ p :=
  P.gap_mul_cyclotomicIdeal_absNorm_eq_pow (cycloZeta_isPrimitiveRoot p)

example :
    padicValNat p
        (Ideal.absNorm
          (cyclotomicLinearFactorIdeal
            (cycloZeta_isPrimitiveRoot p) g u)) = 1 :=
  P.padicValNat_cyclotomicIdeal_absNorm_eq_one (cycloZeta_isPrimitiveRoot p)

example :
    p ∣ Ideal.absNorm
        (cyclotomicLinearFactorIdeal
          (cycloZeta_isPrimitiveRoot p) g u) :=
  P.prime_dvd_cyclotomicIdeal_absNorm (cycloZeta_isPrimitiveRoot p)

example :
    ¬ p ^ 2 ∣ Ideal.absNorm
        (cyclotomicLinearFactorIdeal
          (cycloZeta_isPrimitiveRoot p) g u) :=
  P.prime_sq_not_dvd_cyclotomicIdeal_absNorm (cycloZeta_isPrimitiveRoot p)

end AdicPacket

section PowerSplit

variable {p g u x : ℕ} [Fact p.Prime]
variable (S : PrimeAdicPowerSplit p g u x)

example :
    Ideal.absNorm
        (cyclotomicLinearFactorIdeal
          (cycloZeta_isPrimitiveRoot p) g u) = p * S.b ^ p :=
  S.cyclotomicIdeal_absNorm_eq_prime_mul_pow (cycloZeta_isPrimitiveRoot p)

example : g = p ^ (p - 1) * S.a ^ p := S.gap_eq

end PowerSplit

section PrimeGe5

variable {p x y z : ℕ} [Fact p.Prime]
variable (h : DkMath.FLT.PrimeGe5CounterexamplePack p x y z)

example :
    h.gap * Ideal.absNorm
        (cyclotomicLinearFactorIdeal
          (cycloZeta_isPrimitiveRoot p) h.gap y) = x ^ p :=
  DkMath.FLT.Prime.PrimeGe5CounterexamplePack.gap_mul_cyclotomicIdeal_absNorm_eq_pow
    (p := p) (x := x) (y := y) (z := z) (cycloZeta_isPrimitiveRoot p) h

example (hp_dvd_gap : p ∣ h.gap) :
    PrimeAdicFactorPacket p h.gap y x :=
  DkMath.FLT.Prime.PrimeGe5CounterexamplePack.toPrimeAdicFactorPacket_of_prime_dvd_gap
    h hp_dvd_gap

end PrimeGe5

section SevenCompatibility

variable {x y z : ℕ}

example (P : SevenAdicCounterexamplePacket x y z) :
    PrimeAdicFactorPacket 7 (z - y) y x :=
  P.toPrimeAdicFactorPacket

end SevenCompatibility

#print axioms DkMath.FLT.Prime.PrimeAdicFactorPacket.cyclotomicIdeal_absNorm_eq_residual
#print axioms DkMath.FLT.Prime.PrimeAdicFactorPacket.gap_mul_cyclotomicIdeal_absNorm_eq_pow
#print axioms DkMath.FLT.Prime.PrimeAdicFactorPacket.padicValNat_cyclotomicIdeal_absNorm_eq_one
#print axioms DkMath.FLT.Prime.PrimeAdicFactorPacket.prime_dvd_cyclotomicIdeal_absNorm
#print axioms DkMath.FLT.Prime.PrimeAdicFactorPacket.prime_sq_not_dvd_cyclotomicIdeal_absNorm
#print axioms DkMath.FLT.Prime.PrimeAdicPowerSplit.cyclotomicIdeal_absNorm_eq_prime_mul_pow
#print axioms DkMath.FLT.Prime.PrimeGe5CounterexamplePack.toPrimeAdicFactorPacket_of_prime_dvd_gap
#print axioms DkMath.FLT.Prime.PrimeGe5CounterexamplePack.gap_mul_cyclotomicIdeal_absNorm_eq_pow

end

end DkMathTest.FLT.Prime
