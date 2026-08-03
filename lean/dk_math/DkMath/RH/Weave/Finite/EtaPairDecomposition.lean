/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaFiniteClosure
import DkMath.RH.Weave.Finite.PairEnergy
import Mathlib.Tactic

#print "file: DkMath.RH.Weave.Finite.EtaPairDecomposition"

namespace DkMath.RH.Weave.Finite

open DkMath.RH.CFBRCProjection

/-- Symmetric center of the positive and negative finite eta blocks. -/
noncomputable def etaPairCenter (N : ℕ) (s : ℂ) : ℂ :=
  pairCenter (etaPositivePartial N s) (etaNegativePartial N s)

/-- Antisymmetric offset of the positive and negative finite eta blocks. -/
noncomputable def etaPairOffset (N : ℕ) (s : ℂ) : ℂ :=
  pairOffset (etaPositivePartial N s) (etaNegativePartial N s)

/-- The finite eta endpoint is twice its antisymmetric block offset. -/
theorem etaPartialEndpoint_eq_two_mul_pairOffset
    (N : ℕ) (s : ℂ) :
    etaPartialEndpoint N s = 2 * etaPairOffset N s := by
  rw [etaPartialEndpoint_eq_positive_sub_negative]
  unfold etaPairOffset
  exact (two_mul_pairOffset
    (etaPositivePartial N s) (etaNegativePartial N s)).symm

/-- Finite eta closure is exactly vanishing antisymmetric block offset. -/
theorem etaPartialEndpoint_eq_zero_iff_pairOffset_eq_zero
    (N : ℕ) (s : ℂ) :
    etaPartialEndpoint N s = 0 ↔ etaPairOffset N s = 0 := by
  rw [etaPartialEndpoint_eq_zero_iff_parity_balance]
  unfold etaPairOffset
  exact (pairOffset_eq_zero_iff
    (etaPositivePartial N s) (etaNegativePartial N s)).symm

/--
Pair-energy decomposition specialized to the two genuine finite eta blocks.
-/
theorem etaBlock_normSq_decomposition
    (N : ℕ) (s : ℂ) :
    Complex.normSq (etaPositivePartial N s) +
        Complex.normSq (etaNegativePartial N s) =
      2 * Complex.normSq (etaPairCenter N s) +
        2 * Complex.normSq (etaPairOffset N s) := by
  unfold etaPairCenter etaPairOffset
  exact normSq_pair_decomposition
    (etaPositivePartial N s) (etaNegativePartial N s)

/-- Antisymmetric energy carried by the finite eta parity imbalance. -/
noncomputable def etaAntisymmetricEnergy (N : ℕ) (s : ℂ) : ℝ :=
  2 * Complex.normSq (etaPairOffset N s)

/-- A closed finite eta endpoint has zero antisymmetric energy. -/
theorem etaAntisymmetricEnergy_eq_zero_of_endpoint_eq_zero
    {N : ℕ} {s : ℂ} (h : etaPartialEndpoint N s = 0) :
    etaAntisymmetricEnergy N s = 0 := by
  have hoff : etaPairOffset N s = 0 :=
    (etaPartialEndpoint_eq_zero_iff_pairOffset_eq_zero N s).mp h
  simp [etaAntisymmetricEnergy, hoff]

/-- Zero antisymmetric eta energy forces finite eta closure. -/
theorem etaPartialEndpoint_eq_zero_of_antisymmetricEnergy_eq_zero
    {N : ℕ} {s : ℂ} (h : etaAntisymmetricEnergy N s = 0) :
    etaPartialEndpoint N s = 0 := by
  have hnorm : Complex.normSq (etaPairOffset N s) = 0 := by
    unfold etaAntisymmetricEnergy at h
    nlinarith
  have hoff : etaPairOffset N s = 0 := Complex.normSq_eq_zero.mp hnorm
  exact (etaPartialEndpoint_eq_zero_iff_pairOffset_eq_zero N s).mpr hoff

/-- Finite eta closure is equivalent to zero antisymmetric block energy. -/
theorem etaPartialEndpoint_eq_zero_iff_antisymmetricEnergy_eq_zero
    (N : ℕ) (s : ℂ) :
    etaPartialEndpoint N s = 0 ↔ etaAntisymmetricEnergy N s = 0 := by
  constructor
  · exact etaAntisymmetricEnergy_eq_zero_of_endpoint_eq_zero
  · exact etaPartialEndpoint_eq_zero_of_antisymmetricEnergy_eq_zero

end DkMath.RH.Weave.Finite
