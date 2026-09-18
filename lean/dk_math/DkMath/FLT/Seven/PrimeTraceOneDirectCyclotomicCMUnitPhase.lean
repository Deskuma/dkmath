/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicRelativeNormPhase

#print "file: DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicCMUnitPhase"

namespace DkMath.FLT.Seven

noncomputable section

open scoped NumberField

namespace SevenCyclotomicDegreeSixInt

/-- The concrete degree-six carrier is equivalent to the seventh cyclotomic
ring of integers.  The proof uses the explicit integral power basis and the
fraction-field minimal-polynomial calculation exposed by the PID layer. -/
noncomputable def ringOfIntegersToRingEquiv :
    (𝓞 (CyclotomicField 7 ℚ)) ≃ₐ[ℤ] Ring :=
  AlgEquiv.ofBijective ringOfIntegersToRing
    ⟨ringOfIntegersToRing_injective, ringOfIntegersToRing_surjective⟩

@[simp] theorem ringOfIntegersToRingEquiv_apply (x : 𝓞 (CyclotomicField 7 ℚ)) :
    ringOfIntegersToRingEquiv x = ringOfIntegersToRing x := rfl

theorem ringOfIntegersToRingEquiv_surjective :
    Function.Surjective ringOfIntegersToRingEquiv :=
  ringOfIntegersToRingEquiv.surjective

theorem ringOfIntegersToRingEquiv_injective :
    Function.Injective ringOfIntegersToRingEquiv :=
  ringOfIntegersToRingEquiv.injective

end SevenCyclotomicDegreeSixInt

end

end DkMath.FLT.Seven
