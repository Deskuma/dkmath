/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.Weave.Analytic.EtaPairedHolomorphic
import Mathlib.Tactic

#print "file: DkMath.RH.Weave.Analytic.EtaPoleAudit"

noncomputable section

namespace DkMath.RH.Weave.Analytic

/-- The point `s = 1` belongs to the open right half-plane. -/
@[simp] theorem one_mem_etaRightHalfPlane :
    (1 : ℂ) ∈ etaRightHalfPlane := by
  norm_num [etaRightHalfPlane]

/--
The raw product definition `analyticEta = (1 - 2^(1-s)) * riemannZeta s`
evaluates to zero at `s = 1`, because Mathlib assigns a value to zeta at its
pole and the dyadic factor itself is zero there.

This is a value audit, not the removable continuation value of Dirichlet eta.
-/
@[simp] theorem analyticEta_one :
    analyticEta (1 : ℂ) = 0 := by
  simp [analyticEta]

/--
At the pole point, identifying the genuine paired eta value with the raw zeta
product is exactly the additional claim that the paired value itself is zero.
Thus a continuation theorem must either exclude `s = 1` or introduce a
regularized eta value there.
-/
theorem etaPairedValue_eq_analyticEta_one_iff :
    etaPairedValue (1 : ℂ) = analyticEta (1 : ℂ) ↔
      etaPairedValue (1 : ℂ) = 0 := by
  rw [analyticEta_one]

/-- The pole-free right half-plane used by the raw zeta-product identity. -/
def etaPuncturedRightHalfPlane : Set ℂ :=
  etaRightHalfPlane ∩ ({1} : Set ℂ)ᶜ

/-- Membership in the pole-free right half-plane has the expected form. -/
theorem mem_etaPuncturedRightHalfPlane_iff (s : ℂ) :
    s ∈ etaPuncturedRightHalfPlane ↔
      0 < s.re ∧ s ≠ 1 := by
  simp [etaPuncturedRightHalfPlane, etaRightHalfPlane]

/-- The pole-free right half-plane is open. -/
theorem isOpen_etaPuncturedRightHalfPlane :
    IsOpen etaPuncturedRightHalfPlane := by
  exact isOpen_etaRightHalfPlane.inter isOpen_compl_singleton

end DkMath.RH.Weave.Analytic
