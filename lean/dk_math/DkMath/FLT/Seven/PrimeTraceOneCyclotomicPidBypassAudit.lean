/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimeTraceOnePrimitiveRamifiedProvenance
import DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicDegreeSixPID
import DkMath.FLT.Seven.SevenRamifiedFusionElementLevelOrientedPower
import DkMath.FLT.Kummer.CyclotomicPrincipalization
import DkMath.FLT.Kummer.RegularPrimeRoute
import DkMath.Lib.NumberTheory.ClassGroupTorsionBridge

#print "file: DkMath.FLT.Seven.PrimeTraceOneCyclotomicPidBypassAudit"

namespace DkMath.FLT.Seven

noncomputable section

open DkMath.Lib.NumberTheory
open NumberField
open scoped NumberField

/-!
This file is deliberately an audit surface.  It records the clean p = 7
principal-ideal adapters and the exact unit-bearing boundary, without
promoting a speculative cyclotomic bypass into the public facade.
-/

namespace CyclotomicSeven

variable (K : Type*) [Field K] [NumberField K]
  [hK : IsCyclotomicExtension {7} ℚ K]

local instance : IsPrincipalIdealRing (𝓞 K) :=
  CyclotomicSeven.ringOfIntegers_isPrincipalIdealRing K

/-- Class number one discharges the p = 7 torsion premise on the abstract
ring of integers, with no regular-prime or FLT theorem involved. -/
theorem classGroupPTorsionFreeAt_ringOfIntegers_seven :
    classGroupPTorsionFreeAt (𝓞 K) 7 :=
  classGroupPTorsionFreeAt_of_isPrincipalIdealRing 7

end CyclotomicSeven

namespace SevenCyclotomicDegreeSixInt

/-- The concrete degree-six PID supplies only its own p = 7 class-group
specialization.  This is intentionally weaker than the generic Kummer target,
which quantifies over every domain and every exponent. -/
theorem classGroupPTorsionFreeAt_seven :
    classGroupPTorsionFreeAt Ring 7 :=
  classGroupPTorsionFreeAt_of_isPrincipalIdealRing 7

/-- Exact unit-sector condition needed to remove the unit in a PID extraction. -/
def UnitSeventhPowerSurjective : Prop :=
  ∀ u : Ringˣ, ∃ v : Ringˣ, u = v ^ 7

/-- The existing concrete PID extraction retains the associated unit. -/
theorem unitMulPowOfSpanEqPow_audit
    {I : Ideal Ring} {a : Ring} {n : ℕ}
    (h : Ideal.span {a} = I ^ n) :
    ∃ u : Ring, IsUnit u ∧
      a = u * Submodule.IsPrincipal.generator I ^ n :=
  unitMulPowOfSpanEqPow h

end SevenCyclotomicDegreeSixInt

namespace RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

/-- The clean direct PID theorem reaches the existing oriented routed packet.
It is retained here as an audit witness only; the packet is downstream of the
older routing layer and is not used to construct the TraceOne receiver. -/
theorem directPid_orientedElementLevelPower_audit
    (p : RamifiedSignedRootRoutingPacket) :
    Nonempty (OrientedElementLevelPowerWitness p) :=
  exists_orientedElementLevelPowerWitness p

end RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

end

end DkMath.FLT.Seven
