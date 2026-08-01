/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaFiniteClosure
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.StandardZetaBridge"

namespace DkMath.RH.CFBRCProjection

/--
The standard Mathlib Riemann-zeta zero predicate with the trivial negative-even
zeros and the pole point excluded, matching `RiemannHypothesis` exactly.
-/
def NontrivialRiemannZetaZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧
    (¬∃ n : ℕ, s = -2 * (n + 1)) ∧
    s ≠ 1

/-- The local predicate is definitionally aligned with Mathlib's RH statement. -/
theorem riemannHypothesis_iff_nontrivialZero_re_eq_half :
    RiemannHypothesis ↔
      ∀ s : ℂ, NontrivialRiemannZetaZero s → s.re = (1 : ℝ) / 2 := by
  constructor
  · intro hRH s hs
    exact hRH s hs.1 hs.2.1 hs.2.2
  · intro h s hz htrivial hone
    exact h s ⟨hz, htrivial, hone⟩

/-- Standard-zeta specialization of the general positive-degree CFBRC bridge. -/
abbrev StandardZetaToCFBRCBridge :=
  ZeroToCFBRCBridge NontrivialRiemannZetaZero

/-- Standard-zeta specialization of the finite centered closure bridge. -/
abbrev StandardZetaFiniteCenteredBridge (ι : Type*) :=
  FiniteCenteredZeroBridge ι NontrivialRiemannZetaZero

/--
A zero-preserving standard-zeta-to-CFBRC bridge proves Mathlib's formal RH
statement.  All analytic difficulty remains in the bridge's `map_zero` field.
-/
theorem riemannHypothesis_of_standardZetaToCFBRCBridge
    (bridge : StandardZetaToCFBRCBridge) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_nontrivialZero_re_eq_half]
  intro s hs
  exact re_eq_half_of_zeroToCFBRCBridge bridge hs

/--
A finite centered realization of every standard nontrivial zeta zero also proves
Mathlib's formal RH statement.  The load-bearing analytic field is
`center_identification` together with a genuine endpoint realization.
-/
theorem riemannHypothesis_of_standardZetaFiniteCenteredBridge
    {ι : Type*} (bridge : StandardZetaFiniteCenteredBridge ι) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_nontrivialZero_re_eq_half]
  intro s hs
  exact re_eq_half_of_finiteCenteredZeroBridge bridge hs

/--
Direct formulation of the remaining positive-degree standard CFBRC obligation.
Supplying this function is sufficient for RH.
-/
theorem riemannHypothesis_of_standardZeta_map_zero
    {d : ℕ} (hd : 0 < d) (phase : ℂ → ℝ)
    (map_zero : ∀ {s : ℂ}, NontrivialRiemannZetaZero s →
      offCriticalCFBRC d s.re (phase s) = 0) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_standardZetaToCFBRCBridge
    { d := d
      hd := hd
      phase := phase
      map_zero := map_zero }

end DkMath.RH.CFBRCProjection
