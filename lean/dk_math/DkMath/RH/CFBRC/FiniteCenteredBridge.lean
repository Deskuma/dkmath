/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.FiniteMassNormalization
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.FiniteCenteredBridge"

namespace DkMath.RH.CFBRCProjection

/--
The finite closure model reaches centered coordinate zero once its normalized
projected center offset is identified with `σ - 1/2`.

This theorem isolates the future analytic obligation in `hCenter`.  Neither
closure nor the CFBRC exclusion theorem assumes the critical-line conclusion.
-/
theorem centeredSigma_eq_zero_of_finiteEndpoint_eq_zero
    {ι : Type*} (S : Finset ι) (v : ι → ℂ) {ω : ℂ} {σ : ℝ}
    (hω : ω ≠ 0)
    (hClose : finiteEndpoint S v = 0)
    (hTotal : projectedMassTotal S v ω ≠ 0)
    (hCenter :
      centeredSigma σ = normalizedProjectedCenterOffset S v ω) :
    centeredSigma σ = 0 := by
  calc
    centeredSigma σ = normalizedProjectedCenterOffset S v ω := hCenter
    _ = 0 :=
      normalizedProjectedCenterOffset_eq_zero_of_finiteEndpoint_eq_zero
        S v hω hClose hTotal

/--
A finite closure whose normalized center offset represents `σ - 1/2` forces
`σ = 1/2`.
-/
theorem re_eq_half_of_finiteEndpoint_eq_zero
    {ι : Type*} (S : Finset ι) (v : ι → ℂ) {ω : ℂ} {σ : ℝ}
    (hω : ω ≠ 0)
    (hClose : finiteEndpoint S v = 0)
    (hTotal : projectedMassTotal S v ω ≠ 0)
    (hCenter :
      centeredSigma σ = normalizedProjectedCenterOffset S v ω) :
    σ = (1 : ℝ) / 2 := by
  apply (centeredSigma_eq_zero_iff σ).mp
  exact centeredSigma_eq_zero_of_finiteEndpoint_eq_zero
    S v hω hClose hTotal hCenter

/--
The same finite center identification maps closure into the standard positive-
degree CFBRC zero locus.
-/
theorem offCriticalCFBRC_eq_zero_of_finiteEndpoint_eq_zero
    {ι : Type*} {d : ℕ} (hd : 0 < d)
    (S : Finset ι) (v : ι → ℂ) {ω : ℂ} {σ Θ : ℝ}
    (hω : ω ≠ 0)
    (hClose : finiteEndpoint S v = 0)
    (hTotal : projectedMassTotal S v ω ≠ 0)
    (hCenter :
      centeredSigma σ = normalizedProjectedCenterOffset S v ω) :
    offCriticalCFBRC d σ Θ = 0 := by
  apply (offCriticalCFBRC_eq_zero_iff_re_eq_half hd σ Θ).2
  exact re_eq_half_of_finiteEndpoint_eq_zero
    S v hω hClose hTotal hCenter

/--
Abstract finite realization of a selected complex-zero predicate.

The realization must provide a finite vector model, a nonzero observation
rotation, nontrivial projected mass, endpoint closure, and the identification
of the normalized center offset with `s.re - 1/2`.
-/
structure FiniteCenteredZeroBridge
    (ι : Type*) (Zero : ℂ → Prop) where
  support : ℂ → Finset ι
  vectors : ℂ → ι → ℂ
  rotation : ℂ → ℂ
  rotation_ne_zero : ∀ s, rotation s ≠ 0
  projectedMassTotal_ne_zero : ∀ {s}, Zero s →
    projectedMassTotal (support s) (vectors s) (rotation s) ≠ 0
  endpoint_eq_zero : ∀ {s}, Zero s →
    finiteEndpoint (support s) (vectors s) = 0
  center_identification : ∀ {s}, Zero s →
    centeredSigma s.re =
      normalizedProjectedCenterOffset (support s) (vectors s) (rotation s)

/--
Every zero predicate admitting a finite centered realization is confined to
real part `1/2`.
-/
theorem re_eq_half_of_finiteCenteredZeroBridge
    {ι : Type*} {Zero : ℂ → Prop}
    (bridge : FiniteCenteredZeroBridge ι Zero)
    {s : ℂ} (hs : Zero s) :
    s.re = (1 : ℝ) / 2 := by
  exact re_eq_half_of_finiteEndpoint_eq_zero
    (bridge.support s) (bridge.vectors s)
    (bridge.rotation_ne_zero s)
    (bridge.endpoint_eq_zero hs)
    (bridge.projectedMassTotal_ne_zero hs)
    (bridge.center_identification hs)

end DkMath.RH.CFBRCProjection
