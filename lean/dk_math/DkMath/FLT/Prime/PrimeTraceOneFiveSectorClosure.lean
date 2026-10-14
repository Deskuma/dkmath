/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Five.GoldenUnitClassification
import DkMath.FLT.Five.TraceOneBridge
import DkMath.FLT.Prime.PrimeTraceOneConditionalDescent
import DkMath.Lib.NumberTheory.ClassGroupTorsionBridge
import DkMath.Lib.NumberTheory.UnitPowerSector
import DkMath.NumberTheory.PrimeQuadraticDiscriminant
import Mathlib.Tactic

#print "file: DkMath.FLT.Prime.PrimeTraceOneFiveSectorClosure"

namespace DkMath.FLT.Prime

open DkMath.FLT.Five
open DkMath.Lib.NumberTheory
open DkMath.NumberTheory.CyclotomicQRTraceOneBridge
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.NumberTheory.TraceOneQuadraticField

noncomputable section

/-! ## Explicit golden fifth-power sectors -/

private noncomputable def goldenPhiPowUnit (i : Fin 5) : GoldenIntˣ :=
  (goldenUnit_iff_isUnit.mp <| by
    simpa only [golden_pow_eq] using goldenUnit_pow goldenUnit_phi i.val).unit

/-- The golden unit classes transported to the neutral `s = 1` carrier. -/
noncomputable def goldenTraceOneFifthUnitPowerSectorSystem :
    UnitPowerSectorSystem (TraceOneInt 1) 5 where
  Sector := Fin 5
  rep := fun i => Units.map goldenTraceOneRingEquiv.toMonoidHom (goldenPhiPowUnit i)
  complete := by
    intro u
    let uGolden : GoldenIntˣ :=
      Units.map goldenTraceOneRingEquiv.symm.toMonoidHom u
    have huGolden : GoldenUnit (uGolden : GoldenInt) :=
      goldenUnit_iff_isUnit.mpr uGolden.isUnit
    obtain ⟨i, delta, hdelta⟩ :=
      goldenUnitClassesModFifth (uGolden : GoldenInt) huGolden
    have hdelta' :
        (uGolden : GoldenInt) = (goldenPhi ^ i.val) * delta ^ 5 := by
      simpa only [golden_mul_eq, golden_pow_eq] using hdelta
    have hprod : IsUnit ((goldenPhi ^ i.val) * delta ^ 5) := by
      rw [← hdelta']
      exact uGolden.isUnit
    have hdeltaPow : IsUnit (delta ^ 5) :=
      (IsUnit.mul_iff.mp hprod).2
    have hdeltaUnit : IsUnit delta :=
      (isUnit_pow_iff (by decide : 5 ≠ 0)).mp hdeltaPow
    let deltaUnit : GoldenIntˣ := hdeltaUnit.unit
    refine ⟨i, Units.map goldenTraceOneRingEquiv.toMonoidHom deltaUnit, ?_⟩
    apply Units.ext
    change (u : TraceOneInt 1) =
      (goldenTraceOneRingEquiv (goldenPhi ^ i.val)) *
        (goldenTraceOneRingEquiv (deltaUnit : GoldenInt)) ^ 5
    have hmap := congrArg goldenTraceOneRingEquiv hdelta'
    simpa [uGolden, goldenPhiPowUnit, deltaUnit] using hmap

theorem goldenTraceOneFifthUnitPowerSectorSystem_complete
    (u : (TraceOneInt 1)ˣ) :
    ∃ i : Fin 5, ∃ e : (TraceOneInt 1)ˣ,
      u = goldenTraceOneFifthUnitPowerSectorSystem.rep i * e ^ 5 := by
  exact goldenTraceOneFifthUnitPowerSectorSystem.complete u

/-- The transported representative is the coordinate image of the golden power. -/
theorem goldenTraceOneFifthUnitPowerSectorSystem_rep_apply (i : Fin 5) :
    (goldenTraceOneFifthUnitPowerSectorSystem.rep i : TraceOneInt 1) =
      goldenToTraceOne (goldenPhi ^ i.val) := by
  simp only [goldenTraceOneFifthUnitPowerSectorSystem, Units.coe_map,
    goldenPhiPowUnit, IsUnit.unit_spec]
  rfl

/-! ## Structural class-group discharge -/

section TraceOneOnePID

local instance traceOneOneEuclideanDomain : EuclideanDomain (TraceOneInt 1) :=
  goldenTraceOneRingEquiv.symm.euclideanDomain

local instance traceOneOneIsDomain : IsDomain (TraceOneInt 1) :=
  goldenTraceOneRingEquiv.symm.toMulEquiv.isDomain GoldenInt

/-- Principal-ideal structure transported from the golden Euclidean domain. -/
theorem classGroupPTorsionFreeAt_traceOneOne_five :
    classGroupPTorsionFreeAt (TraceOneInt 1) 5 := by
  exact classGroupPTorsionFreeAt_of_isPrincipalIdealRing 5

end TraceOneOnePID

/-! ## Generic p=5 sector endpoint -/

/-- The generic stripped-ideal endpoint specialized to the golden p=5 sectors.

This is a structural sector closure statement; it does not remove any of the five
sectors and does not invoke the specialized FLT5 contradiction theorem.
-/
theorem exists_goldenSector_mul_fifth_of_primeTraceOneStrippedIdealPacket_five
    {L : Type*} [Field L] [Algebra ℚ L]
    {g u x : ℕ} [Fact (Nat.Prime 5)]
    [IsCyclotomicExtension {5} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ 5}
    (P0 : PrimeAdicFactorPacket 5 g u x)
    (P : PrimeTraceOneCoordinatePacket L 5 ζ hζ)
    (Q : PrimeTraceOneStrippedIdealPacket L P0 P) :
    ∃ i : Fin 5, ∃ delta : TraceOneInt 1,
      Q.residual =
        (goldenTraceOneFifthUnitPowerSectorSystem.rep i : TraceOneInt 1) *
        delta ^ 5 := by
  let hcarrier : TraceOneInt 1 =
      TraceOneInt (signedPrimeParameter 5) :=
    congrArg TraceOneInt signedPrimeParameter_five.symm
  let : EuclideanDomain (TraceOneInt (signedPrimeParameter 5)) :=
    hcarrier ▸ goldenTraceOneRingEquiv.symm.euclideanDomain
  let : IsDomain (TraceOneInt (signedPrimeParameter 5)) :=
    EuclideanDomain.instIsDomain _
  let : Fact (∀ r : ℚ,
      r ^ 2 ≠ (signedPrimeParameter 5 : ℚ) + 1 * r) :=
    ⟨traceOneRat_no_rational_root P0.prime (by norm_num)⟩
  let : Field (TraceOneRat (signedPrimeParameter 5)) :=
    traceOneRatField P0.prime (by norm_num)
  have hgeneric :=
    exists_sector_mul_pow_of_primeTraceOneStrippedIdealPacket
      P0 P Q goldenTraceOneFifthUnitPowerSectorSystem (by norm_num)
  dsimp at hgeneric
  have hfree :
      classGroupPTorsionFreeAt (TraceOneInt (signedPrimeParameter 5)) 5 := by
    exact classGroupPTorsionFreeAt_traceOneOne_five
  obtain ⟨i, delta, hdelta⟩ := hgeneric hfree
  refine ⟨i, delta, ?_⟩
  convert hdelta using 1
  rfl

end

end DkMath.FLT.Prime
