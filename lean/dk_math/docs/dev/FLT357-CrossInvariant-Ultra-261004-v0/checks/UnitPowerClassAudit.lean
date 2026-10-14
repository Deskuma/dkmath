/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.GoldenEuclidean
import DkMath.FLT.Three.EisensteinEuclidean
import DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicDegreeSixPID
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

namespace FLT357CrossInvariantAudit

/-- In an integrally closed domain, the unit class of a nonzero element
expressed as a unit times an n-th power is independent of the chosen root. -/
theorem unitPowerClass_independent
    {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {alpha beta gamma u v : R} {n : ℕ}
    (hn : n ≠ 0) (halpha : alpha ≠ 0)
    (hu : IsUnit u) (hv : IsUnit v)
    (hleft : alpha = u * beta ^ n)
    (hright : alpha = v * gamma ^ n) :
    ∃ t : R, IsUnit t ∧ u = v * t ^ n := by
  have hpowers : Associated (beta ^ n) (gamma ^ n) :=
    (associated_unit_mul_right (beta ^ n) u hu).trans
      ((Associated.of_eq (hleft.symm.trans hright)).trans
        (associated_unit_mul_left (gamma ^ n) v hv))
  obtain ⟨t, hroot⟩ := (Associated.pow_iff hn).mp hpowers
  have hbeta : beta ^ n ≠ 0 := by
    intro hzero
    apply halpha
    rw [hleft, hzero, mul_zero]
  refine ⟨(t : R), t.isUnit, ?_⟩
  have heq : u * beta ^ n = v * gamma ^ n := hleft.symm.trans hright
  rw [← hroot, mul_pow] at heq
  apply mul_right_cancel₀ hbeta
  simpa only [mul_assoc, mul_comm, mul_left_comm] using heq

end FLT357CrossInvariantAudit

namespace FLT357CrossInvariantAudit

/-- The same unit ambiguity result after a fixed nonzero ramifier is cancelled.
The raw element and the chosen ramifier remain explicit; this does not compare
representations using different ramifiers or construct additive landing. -/
theorem fixedRamifier_unitPowerClass_independent
    {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {A lambda beta gamma u v : R} {n : ℕ}
    (hn : n ≠ 0) (hA : A ≠ 0) (hlambda : lambda ≠ 0)
    (hu : IsUnit u) (hv : IsUnit v)
    (hleft : A = lambda * (u * beta ^ n))
    (hright : A = lambda * (v * gamma ^ n)) :
    ∃ t : R, IsUnit t ∧ u = v * t ^ n := by
  have hnormalized : u * beta ^ n = v * gamma ^ n :=
    mul_left_cancel₀ hlambda (hleft.symm.trans hright)
  have hnonzero : u * beta ^ n ≠ 0 := by
    intro hzero
    apply hA
    rw [hleft, hzero, mul_zero]
  exact unitPowerClass_independent hn hnonzero hu hv rfl hnormalized

-- The actual concrete carrier arithmetic discharges the normal-domain requirement.
example : IsIntegrallyClosed DkMath.FLT.Three.EisensteinInt := inferInstance
example : IsIntegrallyClosed DkMath.FLT.Five.GoldenInt := inferInstance
example : IsIntegrallyClosed DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.Ring :=
  inferInstance

example {A lambda beta gamma u v : DkMath.FLT.Three.EisensteinInt}
    (hA : A ≠ 0) (hlambda : lambda ≠ 0)
    (hu : IsUnit u) (hv : IsUnit v)
    (hleft : A = lambda * (u * beta ^ 3))
    (hright : A = lambda * (v * gamma ^ 3)) :
    ∃ t : DkMath.FLT.Three.EisensteinInt, IsUnit t ∧ u = v * t ^ 3 :=
  fixedRamifier_unitPowerClass_independent (by decide) hA hlambda hu hv hleft hright

example {A lambda beta gamma u v : DkMath.FLT.Five.GoldenInt}
    (hA : A ≠ 0) (hlambda : lambda ≠ 0)
    (hu : IsUnit u) (hv : IsUnit v)
    (hleft : A = lambda * (u * beta ^ 5))
    (hright : A = lambda * (v * gamma ^ 5)) :
    ∃ t : DkMath.FLT.Five.GoldenInt, IsUnit t ∧ u = v * t ^ 5 :=
  fixedRamifier_unitPowerClass_independent (by decide) hA hlambda hu hv hleft hright

example {A lambda beta gamma u v : DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.Ring}
    (hA : A ≠ 0) (hlambda : lambda ≠ 0)
    (hu : IsUnit u) (hv : IsUnit v)
    (hleft : A = lambda * (u * beta ^ 7))
    (hright : A = lambda * (v * gamma ^ 7)) :
    ∃ t : DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.Ring,
      IsUnit t ∧ u = v * t ^ 7 :=
  fixedRamifier_unitPowerClass_independent (by decide) hA hlambda hu hv hleft hright

#print axioms unitPowerClass_independent
#print axioms fixedRamifier_unitPowerClass_independent

end FLT357CrossInvariantAudit
