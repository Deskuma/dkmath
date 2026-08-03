/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.Weave.Analytic.EtaAbsoluteConvergence
import Mathlib.Tactic

#print "file: DkMath.RH.Weave.Analytic.EtaFiniteFactorization"

namespace DkMath.RH.Weave.Analytic

open DkMath.RH.CFBRCProjection

/-- Unsigned finite Dirichlet partial sum `1⁻ˢ + ... + K⁻ˢ`. -/
noncomputable def etaUnsignedPartial (K : ℕ) (s : ℂ) : ℂ :=
  (Finset.range K).sum (etaUnsignedVector s)

/-- Adding one index appends one unsigned Dirichlet vector. -/
theorem etaUnsignedPartial_succ (K : ℕ) (s : ℂ) :
    etaUnsignedPartial (K + 1) s =
      etaUnsignedPartial K s + etaUnsignedVector s K := by
  simp [etaUnsignedPartial, Finset.sum_range_succ]

/-- The odd zero-based eta vector factors through the dyadic complex power. -/
theorem etaUnsignedVector_two_mul_add_one_factor
    (s : ℂ) (k : ℕ) :
    etaUnsignedVector s (2 * k + 1) =
      (2 : ℂ) ^ (-s) * etaUnsignedVector s k := by
  unfold etaUnsignedVector
  rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega]
  simpa using
    (Complex.natCast_mul_natCast_cpow 2 (k + 1) (-s))

/-- Two additional unsigned terms extend the even partial sum. -/
theorem etaUnsignedPartial_two_mul_succ
    (K : ℕ) (s : ℂ) :
    etaUnsignedPartial (2 * (K + 1)) s =
      etaUnsignedPartial (2 * K) s +
        etaUnsignedVector s (2 * K) +
        etaUnsignedVector s (2 * K + 1) := by
  rw [show 2 * (K + 1) = (2 * K + 1) + 1 by omega]
  rw [etaUnsignedPartial_succ]
  rw [etaUnsignedPartial_succ]

/-- Two additional signed terms extend the even eta endpoint. -/
theorem etaPartialEndpoint_two_mul_succ
    (K : ℕ) (s : ℂ) :
    etaPartialEndpoint (2 * (K + 1)) s =
      etaPartialEndpoint (2 * K) s +
        etaUnsignedVector s (2 * K) -
        etaUnsignedVector s (2 * K + 1) := by
  rw [show 2 * (K + 1) = (2 * K + 1) + 1 by omega]
  rw [etaPartialEndpoint_succ]
  rw [etaPartialEndpoint_succ]
  simp
  abel

/-- Dyadic coefficient appearing in the finite eta factorization. -/
noncomputable def etaDyadicCoefficient (s : ℂ) : ℂ :=
  2 * ((2 : ℂ) ^ (-s))

/--
Finite eta factorization at every even truncation.

This is the finite precursor of
`eta(s) = (1 - 2^(1-s)) * zeta(s)`; no limit or analytic continuation is used.
-/
theorem etaPartialEndpoint_two_mul_factorization
    (K : ℕ) (s : ℂ) :
    etaPartialEndpoint (2 * K) s =
      etaUnsignedPartial (2 * K) s -
        etaDyadicCoefficient s * etaUnsignedPartial K s := by
  induction K with
  | zero =>
      simp [etaPartialEndpoint, finiteEndpoint, etaUnsignedPartial,
        etaDyadicCoefficient]
  | succ K ih =>
      rw [etaPartialEndpoint_two_mul_succ]
      rw [etaUnsignedPartial_two_mul_succ]
      rw [etaUnsignedPartial_succ]
      rw [ih]
      rw [etaUnsignedVector_two_mul_add_one_factor]
      unfold etaDyadicCoefficient
      ring

end DkMath.RH.Weave.Analytic
