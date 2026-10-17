/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenGNSource

#print "file: DkMathTest.FLT.Kummer.SevenGNSource"

namespace DkMathTest.FLT.Kummer.SevenGNSource

open scoped NumberField
open DkMath.FLT.Seven DkMath.Lib.Cosmic DkMath.FLT.Kummer.SevenPrimaryNorm

-- Base change sends both coefficients and the root.
example (ζ x u : ℤ) :
    (Int.castRingHom SevenCyclotomicDegreeSixInt.Ring) (phaseSource ζ x u) =
      phaseSource (ζ : SevenCyclotomicDegreeSixInt.Ring) (x : _) (u : _) :=
  map_phaseSource _ ζ x u

-- Index multiplication has to be reduced mod the root's order.
example (x u : SevenCyclotomicDegreeSixInt.Ring) :
    phaseSource (SevenCyclotomicDegreeSixInt.zeta ^ (2 * 4)) x u =
      phaseSource SevenCyclotomicDegreeSixInt.zeta x u := by
  simpa only [pow_one] using phaseSource_eq_of_pow_modEq
    SevenCyclotomicDegreeSixInt.zeta_pow_seven (by decide : 8 ≡ 1 [MOD 7]) x u

-- Changing only the phase fails when the parameter is nonzero.
example : phaseSource SevenCyclotomicDegreeSixInt.zeta (0 : SevenCyclotomicDegreeSixInt.Ring) 1 ≠
    phaseSource (SevenCyclotomicDegreeSixInt.zeta ^ 2) 0 1 := by
  intro h
  have he := (phaseSource_eq_iff_phase_eq _ _ _ _ (one_ne_zero : (1 : SevenCyclotomicDegreeSixInt.Ring) ≠ 0)).mp h
  have he' : SevenCyclotomicDegreeSixInt.zeta ^ 1 = SevenCyclotomicDegreeSixInt.zeta ^ 2 := by
    simpa only [pow_one] using he
  have hh := SevenCyclotomicDegreeSixInt.zeta_isPrimitiveRoot.pow_inj (by decide : 1 < 7) (by decide : 2 < 7) he'
  omega

-- Actual Galois transport rotates real coefficients, not only the phase.
example : SevenCyclotomicDegreeSixInt.rotateEquiv (realGNSource SevenRealCubicInt.alpha 1 1) =
    realGNSource (SevenRealCubicInt.alpha ^ 2 - 2 * SevenRealCubicInt.alpha) 1 2 := by
  simpa only [SevenRealCubicInt.rotateEquiv_alpha, map_one, Nat.mul_one] using
    rotate_realGNSource SevenRealCubicInt.alpha 1 1

example : SevenCyclotomicDegreeSixInt.rotateEquiv (realGNSource SevenRealCubicInt.alpha 1 1) ≠
    realGNSource SevenRealCubicInt.alpha 1 2 := by
  intro h
  rw [rotate_realGNSource] at h
  simp only [map_one, Nat.mul_one] at h
  rw [realGNSource_eq_endpoints, realGNSource_eq_endpoints] at h
  have he := ((real_phase_endpoints_unique _ _ _ _ (by decide : 2 ∈ (Finset.range 7).erase 0)).mp h).1
  have hr : SevenRealCubicInt.rotateEquiv SevenRealCubicInt.alpha = SevenRealCubicInt.alpha := add_right_cancel he
  rw [SevenRealCubicInt.rotateEquiv_alpha] at hr
  have hn : SevenRealCubicInt.alpha ^ 2 - 2 * SevenRealCubicInt.alpha ≠ SevenRealCubicInt.alpha := by decide +kernel
  exact hn hr

-- Integers really do give a GN source with the correct gap coordinates.
example (m n : ℤ) (i : ℕ) :
    SevenCyclotomicDegreeSixInt.ofReal (m : SevenRealCubicInt) -
      SevenCyclotomicDegreeSixInt.zeta ^ i * SevenCyclotomicDegreeSixInt.ofReal (n : SevenRealCubicInt) =
      GNPhaseFactor (m - n) n i := by
  rw [GNPhaseFactor_eq_realGNSource]
  simpa only [Int.cast_sub] using (realGNSource_sub_coordinates (m : SevenRealCubicInt) (n : SevenRealCubicInt) i).symm

-- alpha is an actual noninteger coefficient, without assuming an FLT counterexample.
example : ¬ ∃ x u : ℤ,
    SevenCyclotomicDegreeSixInt.ofReal SevenRealCubicInt.alpha -
      SevenCyclotomicDegreeSixInt.zeta * SevenCyclotomicDegreeSixInt.ofReal SevenRealCubicInt.alpha =
      GNPhaseFactor x u 1 := by
  intro h
  have he : ∃ x u : ℤ,
      SevenCyclotomicDegreeSixInt.ofReal SevenRealCubicInt.alpha -
        SevenCyclotomicDegreeSixInt.zeta ^ 1 * SevenCyclotomicDegreeSixInt.ofReal SevenRealCubicInt.alpha =
        GNPhaseFactor x u 1 := by simpa only [pow_one] using h
  obtain ⟨_, ⟨n, hn⟩⟩ := (exists_integer_GN_source_iff SevenRealCubicInt.alpha SevenRealCubicInt.alpha
    (by decide : 1 ∈ (Finset.range 7).erase 0)).mp he
  have hs := congrArg SevenRealCubicInt.snd hn
  norm_num [SevenRealCubicInt.alpha] at hs

-- At index 0 there is no endpoint uniqueness; the nontrivial-phase guard matters.
example : SevenCyclotomicDegreeSixInt.ofReal (0 : SevenRealCubicInt) -
      SevenCyclotomicDegreeSixInt.zeta ^ 0 * SevenCyclotomicDegreeSixInt.ofReal (0 : SevenRealCubicInt) =
    SevenCyclotomicDegreeSixInt.ofReal (1 : SevenRealCubicInt) -
      SevenCyclotomicDegreeSixInt.zeta ^ 0 * SevenCyclotomicDegreeSixInt.ofReal (1 : SevenRealCubicInt) := by simp

#print axioms currentLinearCarrier_eq_realGNSource
#print axioms current_real_GN_eq_orbitQuotient
#print axioms current_rho_not_integer
#print axioms currentLinearCarrier_ne_integer_GN_same_phase

run_cmd do
  for n in #[
      ``DkMath.Lib.Cosmic.phaseSource,
      ``DkMath.Lib.Cosmic.phaseSource_sub_coordinates,
      ``DkMath.Lib.Cosmic.map_phaseSource,
      ``DkMath.Lib.Cosmic.map_phaseSource_pow,
      ``DkMath.Lib.Cosmic.map_phaseSource_pow_of_fixed,
      ``DkMath.Lib.Cosmic.phaseSource_eq_of_pow_modEq,
      ``DkMath.Lib.Cosmic.phaseSource_eq_iff_phase_eq,
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.realGNSource,
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.realGNSource_sub_coordinates,
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.GNPhaseFactor_eq_realGNSource,
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.rotate_realGNSource,
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.star_realGNSource,
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.zeta_pow_im_ne_zero,
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.real_phase_endpoints_unique,
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.realGNSource_eq_endpoints,
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.real_phase_eq_integer_GN_iff,
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.exists_integer_GN_source_iff,
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.realGNSource_dvd_GN,
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.current_phase_index_mem,
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.currentLinearCarrier_eq_realGNSource,
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.currentLinearCarrier_dvd_real_GN,
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.current_real_GN_eq_orbitQuotient,
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.current_rho_not_integer,
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.currentLinearCarrier_ne_integer_GN_same_phase] do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {n}"

end DkMathTest.FLT.Kummer.SevenGNSource
