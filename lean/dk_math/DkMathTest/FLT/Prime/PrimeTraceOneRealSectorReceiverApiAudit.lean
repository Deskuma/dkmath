/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Five.SignedGoldenSectorArithmetic
import DkMath.FLT.Five.SignedGoldenRamifierStripped
import DkMath.FLT.Prime.PrimeTraceOneRealSectorReceiver
import DkMath.Lib.NumberTheory.TraceOnePowerLanding
import DkMath.NumberTheory.TraceOnePrimeUnitSectors

#print "file: DkMathTest.FLT.Prime.PrimeTraceOneRealSectorReceiverApiAudit"

open DkMath.FLT.Five
open DkMath.FLT.Prime
open DkMath.Lib.NumberTheory
open DkMath.NumberTheory.CyclotomicQRTraceOneBridge
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.NumberTheory.TraceOneQuadraticField
open DkMath.NumberTheory.TraceOnePrimeUnitSectors

noncomputable section

#check traceOnePowCoords
#check traceOne_pow_core_landing_iff
#check traceOne_norm_ne_zero_of_isUnit
#check exists_realSector_powCoords_of_primeTraceOneStrippedIdealPacket
#check PrimeTraceOneStrippedIdealPacket.residual_natAbs_norm_not_dvd
#check primeTraceOne_base_norm_not_dvd_of_sector_factor
#check exists_realSector_mul_pow_with_baseNorm_not_dvd
#check traceOneFiveResidualToGolden
#check exists_goldenSector_mul_fifth_of_primeTraceOneStrippedIdealPacket_five
#check exists_goldenSector_powCoords_of_primeTraceOneStrippedIdealPacket_five
#check goldenTraceOneFifthUnitPowerSectorSystem_rep_apply
#check traceOnePrimeRealFinSectorSystem
#check signedGolden_nonzero_unitSector_false
#check PrimeTraceOneStrippedIdealPacket.adicSplit
#check PrimeTraceOneStrippedIdealPacket.parent
#check PrimeTraceOneStrippedIdealPacket.residual
#check PrimeTraceOneStrippedIdealPacket.axis_eq
#check PrimeTraceOneStrippedIdealPacket.residual_axis_terminal
#check PrimeTraceOneStrippedIdealPacket.residual_coordinate_coprime
#check PrimeTraceOneStrippedIdealPacket.residual_norm_pow

example : signedPrimeParameter 5 = 1 := by
  exact signedPrimeParameter_five

example : signedPrimeParameter 13 = 3 := by
  norm_num [signedPrimeParameter, signedPrimeDiscriminant]

example : 5 % 4 = 1 := by norm_num

example : 13 % 4 = 1 := by norm_num

section PacketRegression

variable {L : Type*} [Field L] [Algebra ℚ L]
variable {g u x : ℕ}
variable [Fact (Nat.Prime 5)]
variable [IsCyclotomicExtension {5} ℚ L]
variable {ζ : L} {hζ : IsPrimitiveRoot ζ 5}
variable (P0 : PrimeAdicFactorPacket 5 g u x)
variable (P : PrimeTraceOneCoordinatePacket L 5 ζ hζ)
variable (Q : PrimeTraceOneStrippedIdealPacket L P0 P)

example :
    ∃ i : Fin 5, ∃ m n : ℤ,
      (traceOneFiveResidualToGolden P0 P Q * conj
        (goldenTraceOneFifthUnitPowerSectorSystem.rep i : TraceOneInt 1)).fst =
          norm (goldenTraceOneFifthUnitPowerSectorSystem.rep i : TraceOneInt 1) *
            (traceOnePowCoords 1 m n 5).1 ∧
      (traceOneFiveResidualToGolden P0 P Q * conj
        (goldenTraceOneFifthUnitPowerSectorSystem.rep i : TraceOneInt 1)).snd =
          norm (goldenTraceOneFifthUnitPowerSectorSystem.rep i : TraceOneInt 1) *
            (traceOnePowCoords 1 m n 5).2 := by
  exact exists_goldenSector_powCoords_of_primeTraceOneStrippedIdealPacket_five
    P0 P Q

example (i : Fin 5) :
    (goldenTraceOneFifthUnitPowerSectorSystem.rep i : TraceOneInt 1) =
      goldenToTraceOne (goldenPhi ^ i.val) := by
  exact goldenTraceOneFifthUnitPowerSectorSystem_rep_apply i

example :
    let : Fact (∀ r : ℚ,
        r ^ 2 ≠ (signedPrimeParameter 5 : ℚ) + 1 * r) :=
      ⟨traceOneRat_no_rational_root P0.prime (by norm_num)⟩
    let : Field (TraceOneRat (signedPrimeParameter 5)) :=
      traceOneRatField P0.prime (by norm_num)
    let : NumberField (TraceOneRat (signedPrimeParameter 5)) := {
      to_charZero := charZero_of_injective_algebraMap (by
        intro q₁ q₂ hq
        have hre := congrArg QuadraticAlgebra.re hq
        change q₁ = q₂ at hre
        exact hre)
      to_finiteDimensional := inferInstance }
    let : IsDomain (TraceOneInt (signedPrimeParameter 5)) :=
      (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
    let : IsDedekindDomain (TraceOneInt (signedPrimeParameter 5)) :=
      traceOneRat_isDedekindDomain P0.prime (by norm_num)
    ∃ i : Fin 5, ∃ delta : TraceOneInt (signedPrimeParameter 5),
      Q.residual =
        (traceOnePrimeRealFinSectorSystem P0.prime (by norm_num)).rep i *
          delta ^ 5 ∧
      ¬ 5 ∣ Int.natAbs (norm delta) := by
  have h := exists_realSector_mul_pow_with_baseNorm_not_dvd P0 P Q (by norm_num)
  dsimp at h
  apply h
  exact classGroupPTorsionFreeAt_traceOneOne_five

end PacketRegression

section ThirteenRegression

variable {L : Type*} [Field L] [Algebra ℚ L]
variable {g u x : ℕ}
variable [Fact (Nat.Prime 13)]
variable [IsCyclotomicExtension {13} ℚ L]

local instance traceOneThirteenFact : Fact (∀ r : ℚ,
    r ^ 2 ≠ (signedPrimeParameter 13 : ℚ) + 1 * r) :=
  ⟨traceOneRat_no_rational_root (by norm_num) (by norm_num)⟩

local instance traceOneThirteenField : Field (TraceOneRat (signedPrimeParameter 13)) :=
  traceOneRatField (by norm_num) (by norm_num)

local instance traceOneThirteenDomain : IsDomain
    (TraceOneInt (signedPrimeParameter 13)) :=
  (traceOneRatHom_injective _).isDomain (traceOneRatHom _)

variable {ζ : L} {hζ : IsPrimitiveRoot ζ 13}
variable (P0 : PrimeAdicFactorPacket 13 g u x)
variable (P : PrimeTraceOneCoordinatePacket L 13 ζ hζ)
variable (Q : PrimeTraceOneStrippedIdealPacket L P0 P)

example
    (hfree : classGroupPTorsionFreeAt
      (TraceOneInt (signedPrimeParameter 13)) 13) :
    ∃ i : Fin 13, ∃ m n : ℤ,
      (Q.residual * conj
        ((traceOnePrimeRealFinSectorSystem P0.prime (by norm_num)).rep i :
          TraceOneInt (signedPrimeParameter 13))).fst =
          norm ((traceOnePrimeRealFinSectorSystem P0.prime (by norm_num)).rep i :
            TraceOneInt (signedPrimeParameter 13)) *
            (traceOnePowCoords (signedPrimeParameter 13) m n 13).1 ∧
      (Q.residual * conj
        ((traceOnePrimeRealFinSectorSystem P0.prime (by norm_num)).rep i :
          TraceOneInt (signedPrimeParameter 13))).snd =
          norm ((traceOnePrimeRealFinSectorSystem P0.prime (by norm_num)).rep i :
            TraceOneInt (signedPrimeParameter 13)) *
            (traceOnePowCoords (signedPrimeParameter 13) m n 13).2 := by
  have h := exists_realSector_powCoords_of_primeTraceOneStrippedIdealPacket
    P0 P Q (by norm_num)
  dsimp at h
  apply h
  exact hfree

example
    (hfree : classGroupPTorsionFreeAt
      (TraceOneInt (signedPrimeParameter 13)) 13) :
    ∃ i : Fin 13, ∃ delta : TraceOneInt (signedPrimeParameter 13),
      Q.residual =
        (traceOnePrimeRealFinSectorSystem P0.prime (by norm_num)).rep i *
          delta ^ 13 ∧
      ¬ 13 ∣ Int.natAbs (norm delta) := by
  have h := exists_realSector_mul_pow_with_baseNorm_not_dvd P0 P Q (by norm_num)
  dsimp at h
  apply h
  exact hfree

end ThirteenRegression

end
