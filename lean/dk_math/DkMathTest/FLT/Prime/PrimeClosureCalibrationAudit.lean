/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Prime
import DkMath.FLT.Seven.SevenAdicPowerSplit

#print "file: DkMathTest.FLT.Prime.PrimeClosureCalibrationAudit"

open DkMath.FLT.Prime
open DkMath.FLT.Three
open DkMath.FLT.Five
open DkMath.FLT.Seven
open DkMath.Lib.NumberTheory
open DkMath.NumberTheory.CyclotomicQRTraceOneBridge
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.NumberTheory.TraceOneQuadraticField
open DkMath.NumberTheory.TraceOnePrimeUnitSectors

noncomputable section

/-! p = 3: the carrier, class-group discharge, and existing unit sectors. -/
example : signedPrimeParameter 3 = -1 := by
  exact signedPrimeParameter_three

example : EisensteinInt = TraceOneInt (-1) := rfl

example : classGroupPTorsionFreeAt (TraceOneInt (-1)) 3 := by
  exact classGroupPTorsionFreeAt_traceOneNegOne_three

example : UnitPowerSectorSystem (TraceOneInt (-1)) 3 :=
  eisensteinCubeUnitPowerSectorSystem

example {u : (TraceOneInt (-1))ˣ} :
    ∃ sector : EisensteinUnitSector, ∃ e : (TraceOneInt (-1))ˣ,
      u = eisensteinCubeUnitPowerSectorSystem.rep sector * e ^ 3 := by
  exact eisensteinCubeUnitPowerSectorSystem_complete u

section FivePacketCalibration

/-! p = 5: Golden transport and the generic endpoint on an existing packet. -/
variable {L : Type*} [Field L] [Algebra ℚ L]
variable {g u x : ℕ} [Fact (Nat.Prime 5)]
variable [IsCyclotomicExtension {5} ℚ L]
variable {ζ : L} {hζ : IsPrimitiveRoot ζ 5}
variable (P0 : PrimeAdicFactorPacket 5 g u x)
variable (P : PrimeTraceOneCoordinatePacket L 5 ζ hζ)
variable (Q : PrimeTraceOneStrippedIdealPacket L P0 P)

local instance traceOneOneEuclideanDomain : EuclideanDomain (TraceOneInt 1) :=
  goldenTraceOneRingEquiv.symm.euclideanDomain

local instance traceOneOneIsDomain : IsDomain (TraceOneInt 1) :=
  goldenTraceOneRingEquiv.symm.toMulEquiv.isDomain GoldenInt

example : signedPrimeParameter 5 = 1 := by
  exact signedPrimeParameter_five

example : GoldenInt ≃+* TraceOneInt 1 := goldenTraceOneRingEquiv

example : UnitPowerSectorSystem (TraceOneInt 1) 5 :=
  goldenTraceOneFifthUnitPowerSectorSystem

example : classGroupPTorsionFreeAt (TraceOneInt 1) 5 := by
  exact classGroupPTorsionFreeAt_traceOneOne_five

example :
    ∃ i : Fin 5, ∃ delta : TraceOneInt 1,
      Q.residual =
        (goldenTraceOneFifthUnitPowerSectorSystem.rep i : TraceOneInt 1) *
          delta ^ 5 := by
  exact exists_goldenSector_mul_fifth_of_primeTraceOneStrippedIdealPacket_five
    P0 P Q

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

end FivePacketCalibration

section SevenPacketCalibration

/-! p = 7: class-group discharge and the generic imaginary coordinate receiver. -/
variable {L : Type*} [Field L] [Algebra ℚ L]
variable {g u x : ℕ} [Fact (Nat.Prime 7)]
variable [IsCyclotomicExtension {7} ℚ L]
variable {ζ : L} {hζ : IsPrimitiveRoot ζ 7}
variable (P0 : PrimeAdicFactorPacket 7 g u x)
variable (P : PrimeTraceOneCoordinatePacket L 7 ζ hζ)
variable (Q : PrimeTraceOneStrippedIdealPacket L P0 P)

example : signedPrimeParameter 7 = -2 := by
  norm_num [signedPrimeParameter, signedPrimeDiscriminant]

example : classGroupPTorsionFreeAt (TraceOneInt (-2)) 7 := by
  exact classGroupPTorsionFreeAt_traceOneNegTwo_seven

example :
    ∃ m n : ℤ,
      Q.residual.fst =
        (traceOnePowCoords (signedPrimeParameter 7) m n 7).1 ∧
      Q.residual.snd =
        (traceOnePowCoords (signedPrimeParameter 7) m n 7).2 := by
  exact exists_powCoords_of_primeTraceOneImaginaryStrippedIdealPacket_seven
    P0 P Q

end SevenPacketCalibration

/-! The specialized p=7 packet is exposed only as the same generic adic packet. -/
example {x y z : ℕ} (P : SevenAdicCounterexamplePacket x y z) :
    PrimeAdicFactorPacket 7 (z - y) y x :=
  P.toPrimeAdicFactorPacket

/-! Cheap parameter boundaries used by the generic real receiver. -/
example : signedPrimeParameter 11 = -3 := by
  norm_num [signedPrimeParameter, signedPrimeDiscriminant]

example : signedPrimeParameter 13 = 3 := by
  norm_num [signedPrimeParameter, signedPrimeDiscriminant]

end
