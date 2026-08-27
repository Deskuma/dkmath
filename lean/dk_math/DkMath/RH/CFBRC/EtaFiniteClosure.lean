/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.FiniteCenteredBridge
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaFiniteClosure"

namespace DkMath.RH.CFBRCProjection

/--
Unsigned Dirichlet vector at natural index `m + 1`:
`(m + 1)⁻ˢ`, written with Mathlib's complex power.
-/
noncomputable def etaUnsignedVector (s : ℂ) (m : ℕ) : ℂ :=
  ((m + 1 : ℕ) : ℂ) ^ (-s)

/--
The genuine alternating eta vector.  Even zero-based indices correspond to
positive odd natural indices `1, 3, 5, ...`.
-/
noncomputable def etaSignedVector (s : ℂ) (m : ℕ) : ℂ :=
  if Even m then etaUnsignedVector s m else -etaUnsignedVector s m

/-- Finite Dirichlet-eta endpoint using the first `N` natural indices. -/
noncomputable def etaPartialEndpoint (N : ℕ) (s : ℂ) : ℂ :=
  finiteEndpoint (Finset.range N) (etaSignedVector s)

/-- Positive odd-natural-index block of the finite eta sum. -/
noncomputable def etaPositivePartial (N : ℕ) (s : ℂ) : ℂ :=
  (Finset.range N).sum fun m =>
    if Even m then etaUnsignedVector s m else 0

/-- Unsigned even-natural-index block subtracted in the finite eta sum. -/
noncomputable def etaNegativePartial (N : ℕ) (s : ℂ) : ℂ :=
  (Finset.range N).sum fun m =>
    if Even m then 0 else etaUnsignedVector s m

/-- Each signed eta vector is positive contribution minus negative contribution. -/
theorem etaSignedVector_eq_positive_sub_negative
    (s : ℂ) (m : ℕ) :
    etaSignedVector s m =
      (if Even m then etaUnsignedVector s m else 0) -
        (if Even m then 0 else etaUnsignedVector s m) := by
  by_cases hm : Even m <;> simp [etaSignedVector, hm]

/-- The finite eta endpoint is exactly its positive block minus negative block. -/
theorem etaPartialEndpoint_eq_positive_sub_negative
    (N : ℕ) (s : ℂ) :
    etaPartialEndpoint N s =
      etaPositivePartial N s - etaNegativePartial N s := by
  unfold etaPartialEndpoint finiteEndpoint etaPositivePartial etaNegativePartial
  calc
    (Finset.range N).sum (etaSignedVector s) =
        (Finset.range N).sum (fun m =>
          (if Even m then etaUnsignedVector s m else 0) -
            (if Even m then 0 else etaUnsignedVector s m)) := by
      apply Finset.sum_congr rfl
      intro m hm
      exact etaSignedVector_eq_positive_sub_negative s m
    _ =
        (Finset.range N).sum (fun m =>
          if Even m then etaUnsignedVector s m else 0) -
        (Finset.range N).sum (fun m =>
          if Even m then 0 else etaUnsignedVector s m) := by
      rw [Finset.sum_sub_distrib]

/-- Finite eta closure is exactly equality of its two genuine parity blocks. -/
theorem etaPartialEndpoint_eq_zero_iff_parity_balance
    (N : ℕ) (s : ℂ) :
    etaPartialEndpoint N s = 0 ↔
      etaPositivePartial N s = etaNegativePartial N s := by
  rw [etaPartialEndpoint_eq_positive_sub_negative, sub_eq_zero]

/--
The generic finite CFBRC mass-gap decomposition specializes directly to the
finite eta vectors under every nonzero observation rotation.
-/
theorem etaPartialEndpoint_eq_zero_iff_mass_balance_and_transverseGap
    (N : ℕ) (s : ℂ) {ω : ℂ} (hω : ω ≠ 0) :
    etaPartialEndpoint N s = 0 ↔
      positiveProjectedMass (Finset.range N) (etaSignedVector s) ω =
        negativeProjectedMass (Finset.range N) (etaSignedVector s) ω ∧
      transverseGap (Finset.range N) (etaSignedVector s) ω = 0 := by
  exact finiteEndpoint_eq_zero_iff_mass_balance_and_transverseGap
    (Finset.range N) (etaSignedVector s) hω

/--
A closed finite eta endpoint with nontrivial projected mass has normalized
projected masses `1/2, 1/2`.
-/
theorem etaNormalizedProjectedMass_eq_half_of_endpoint_eq_zero
    (N : ℕ) (s : ℂ) {ω : ℂ}
    (hω : ω ≠ 0)
    (hClose : etaPartialEndpoint N s = 0)
    (hTotal :
      projectedMassTotal (Finset.range N) (etaSignedVector s) ω ≠ 0) :
    normalizedPositiveProjectedMass
        (Finset.range N) (etaSignedVector s) ω = (1 : ℝ) / 2 ∧
      normalizedNegativeProjectedMass
        (Finset.range N) (etaSignedVector s) ω = (1 : ℝ) / 2 := by
  exact normalizedProjectedMass_eq_half_of_finiteEndpoint_eq_zero
    (Finset.range N) (etaSignedVector s) hω hClose hTotal

end DkMath.RH.CFBRCProjection
