/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Prime.PrimeTraceOneConditionalDescent
import DkMath.FLT.Three.EisensteinLibBridge
import DkMath.Lib.NumberTheory.ClassGroupTorsionBridge
import DkMath.NumberTheory.PrimeQuadraticDiscriminant
import Mathlib.Tactic

#print "file: DkMath.FLT.Prime.PrimeTraceOneThreeSectorClosure"

namespace DkMath.FLT.Prime

open DkMath.FLT.Three
open DkMath.Lib.NumberTheory
open DkMath.NumberTheory.CyclotomicQRTraceOneBridge
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.NumberTheory.TraceOneQuadraticField

noncomputable section

/-! ## Structural p=3 class-group closure -/

/-- The Eisenstein carrier has trivial class-group 3-torsion structurally. -/
theorem classGroupPTorsionFreeAt_traceOneNegOne_three :
    classGroupPTorsionFreeAt (TraceOneInt (-1)) 3 :=
  classGroupPTorsionFreeAt_of_isPrincipalIdealRing 3

/-! ## Generic sector endpoint at p=3 -/

/-- The generic p=3 packet endpoint in the existing Eisenstein unit sectors. -/
theorem exists_eisensteinSector_mul_cube_of_primeTraceOneStrippedIdealPacket_three
    {L : Type*} [Field L] [Algebra ℚ L]
    {g u x : ℕ} [Fact (Nat.Prime 3)]
    [IsCyclotomicExtension {3} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ 3}
    (P0 : PrimeAdicFactorPacket 3 g u x)
    (P : PrimeTraceOneCoordinatePacket L 3 ζ hζ)
    (Q : PrimeTraceOneStrippedIdealPacket L P0 P) :
    ∃ sector : EisensteinUnitSector, ∃ delta : EisensteinInt,
      Q.residual =
        (eisensteinCubeUnitPowerSectorSystem.rep sector : EisensteinInt) *
          delta ^ 3 := by
  let : Fact (∀ r : ℚ,
      r ^ 2 ≠ (signedPrimeParameter 3 : ℚ) + 1 * r) :=
    ⟨traceOneRat_no_rational_root P0.prime (by norm_num)⟩
  let : Field (TraceOneRat (signedPrimeParameter 3)) :=
    traceOneRatField P0.prime (by norm_num)
  let : IsDomain (TraceOneInt (signedPrimeParameter 3)) :=
    (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
  let : IsDedekindDomain (TraceOneInt (signedPrimeParameter 3)) :=
    traceOneRat_isDedekindDomain P0.prime (by norm_num)
  have hgeneric :=
    exists_sector_mul_pow_of_primeTraceOneStrippedIdealPacket
      P0 P Q eisensteinCubeUnitPowerSectorSystem (by norm_num)
  dsimp at hgeneric
  have hfree :
      classGroupPTorsionFreeAt (TraceOneInt (signedPrimeParameter 3)) 3 := by
    simpa [signedPrimeParameter, signedPrimeDiscriminant] using
      classGroupPTorsionFreeAt_traceOneNegOne_three
  obtain ⟨sector, delta, hdelta⟩ := hgeneric hfree
  refine ⟨sector, delta, ?_⟩
  convert hdelta using 1
  simp [signedPrimeParameter, signedPrimeDiscriminant]
  rfl

end

end DkMath.FLT.Prime
