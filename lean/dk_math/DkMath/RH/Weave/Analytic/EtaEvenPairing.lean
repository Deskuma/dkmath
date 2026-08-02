/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.Weave.Analytic.EtaLimitBridge
import Mathlib.Tactic

#print "file: DkMath.RH.Weave.Analytic.EtaEvenPairing"

namespace DkMath.RH.Weave.Analytic

open DkMath.RH.CFBRCProjection
open DkMath.RH.Weave.Finite

/--
One paired eta term:
`(2k + 1)⁻ˢ - (2k + 2)⁻ˢ` in one-based Dirichlet indexing.
-/
noncomputable def etaPairTerm (s : ℂ) (k : ℕ) : ℂ :=
  etaUnsignedVector s (2 * k) - etaUnsignedVector s (2 * k + 1)

/-- Finite sum of the first `K` paired eta differences. -/
noncomputable def etaPairedPartial (K : ℕ) (s : ℂ) : ℂ :=
  (Finset.range K).sum (etaPairTerm s)

/-- Adding one natural index appends exactly one signed eta vector. -/
theorem etaPartialEndpoint_succ (N : ℕ) (s : ℂ) :
    etaPartialEndpoint (N + 1) s =
      etaPartialEndpoint N s + etaSignedVector s N := by
  simp [etaPartialEndpoint, finiteEndpoint, Finset.sum_range_succ]

/-- Even zero-based eta indices carry the positive sign. -/
@[simp] theorem etaSignedVector_two_mul (s : ℂ) (k : ℕ) :
    etaSignedVector s (2 * k) = etaUnsignedVector s (2 * k) := by
  simp [etaSignedVector]

/-- Odd zero-based eta indices carry the negative sign. -/
@[simp] theorem etaSignedVector_two_mul_add_one (s : ℂ) (k : ℕ) :
    etaSignedVector s (2 * k + 1) =
      -etaUnsignedVector s (2 * k + 1) := by
  simp [etaSignedVector]

/-- Adding one pair appends exactly one paired eta difference. -/
theorem etaPairedPartial_succ (K : ℕ) (s : ℂ) :
    etaPairedPartial (K + 1) s =
      etaPairedPartial K s + etaPairTerm s K := by
  simp [etaPairedPartial, Finset.sum_range_succ]

/--
The first `2K` signed eta vectors are exactly the first `K` paired
differences.  This is a finite identity; no convergence theorem is used.
-/
theorem etaPartialEndpoint_two_mul_eq_etaPairedPartial
    (K : ℕ) (s : ℂ) :
    etaPartialEndpoint (2 * K) s = etaPairedPartial K s := by
  induction K with
  | zero =>
      simp [etaPartialEndpoint, finiteEndpoint, etaPairedPartial]
  | succ K ih =>
      rw [show 2 * (K + 1) = (2 * K + 1) + 1 by omega]
      rw [etaPartialEndpoint_succ]
      rw [etaPartialEndpoint_succ]
      rw [etaPairedPartial_succ, ← ih]
      simp [etaPairTerm]
      abel

/-- Even finite eta closure is exactly paired-difference closure. -/
theorem etaPartialEndpoint_two_mul_eq_zero_iff_etaPairedPartial_eq_zero
    (K : ℕ) (s : ℂ) :
    etaPartialEndpoint (2 * K) s = 0 ↔ etaPairedPartial K s = 0 := by
  rw [etaPartialEndpoint_two_mul_eq_etaPairedPartial]

/-- The even finite eta antisymmetric offset is controlled by the paired sum. -/
theorem two_mul_etaPairOffset_two_mul_eq_etaPairedPartial
    (K : ℕ) (s : ℂ) :
    2 * etaPairOffset (2 * K) s = etaPairedPartial K s := by
  rw [← etaPartialEndpoint_eq_two_mul_pairOffset]
  exact etaPartialEndpoint_two_mul_eq_etaPairedPartial K s

end DkMath.RH.Weave.Analytic
