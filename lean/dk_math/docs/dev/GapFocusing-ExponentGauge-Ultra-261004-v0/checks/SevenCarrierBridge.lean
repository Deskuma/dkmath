/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.GapFocusing
import DkMath.FLT.Seven.CurrentCarrierNormalizedPower

/-! The focused coordinates and fixed-extraction unit class on the actual
current degree-six carrier. All source and packet inputs remain explicit. -/

namespace GapFocusingSevenCarrierAudit

open DkMath.FLT.Seven DkMath.FLT.Seven.SevenRealCubic
open SevenRealCubicInt SevenCyclotomicDegreeSixInt
open CurrentCarrierRamification CurrentCarrierPower
open DkMath.NumberTheory.GapFocusing

variable {x y z : ℕ} {source : CounterexamplePack x y z}
variable {r : PrimitiveCounterexampleRamifiedProvenance source}
variable {p : DirectRealCubicRootPacket source r}
variable {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}

/-- The current carrier has focused coordinates within its actual ring. -/
theorem currentLinearCarrier_eq_focusedGap (c : CurrentCommonPrimeCyclotomicPacket h q) :
    currentLinearCarrier c =
      (ofReal (rotateEquiv p.rho) - ofReal p.rho) +
        (1 - currentPhaseZeta c) * ofReal p.rho := by
  unfold currentLinearCarrier
  ring

/-- The carrier's existing arithmetic receiver supplies the extraction;
the same source also has the focused coordinate identity. -/
theorem currentLinearCarrier_focus_and_extraction
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    currentLinearCarrier c =
        (ofReal (rotateEquiv p.rho) - ofReal p.rho) +
          (1 - currentPhaseZeta c) * ofReal p.rho ∧
      ∃ u beta : Ring, IsUnit u ∧
        currentLinearCarrier c = ramifiedUniformizer * u * beta ^ 7 ∧
        Fermat7Equation x y z := by
  exact ⟨currentLinearCarrier_eq_focusedGap c, currentCarrier_ramified_element_receiver c⟩

/-- For this fixed source and uniformizer the residual seventh-power unit
class is independent of the chosen extraction root. -/
theorem currentLinearCarrier_unitClass_independent
    (c : CurrentCommonPrimeCyclotomicPacket h q) (u v : Ringˣ) (beta gamma : Ring)
    (hleft : currentLinearCarrier c = ramifiedUniformizer * ((u : Ring) * beta ^ 7))
    (hright : currentLinearCarrier c = ramifiedUniformizer * ((v : Ring) * gamma ^ 7)) :
    SameUnitPowerClass 7 u v := by
  have hA : currentLinearCarrier c ≠ 0 := by
    intro hzero
    apply currentLinearCarrier_not_mem_ramifiedPrime_sq c
    rw [hzero]
    exact (ramifiedPrime ^ 2).zero_mem
  exact sameUnitPowerClass_of_fixed_extraction u v (by decide) hA
    ramifiedUniformizer_ne_zero hleft hright

#print axioms currentLinearCarrier_eq_focusedGap
#print axioms currentLinearCarrier_focus_and_extraction
#print axioms currentLinearCarrier_unitClass_independent

end GapFocusingSevenCarrierAudit
