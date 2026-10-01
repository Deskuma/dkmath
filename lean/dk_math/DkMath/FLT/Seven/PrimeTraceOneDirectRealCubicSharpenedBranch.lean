/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicCalibrationExclusion
import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicCommonPrimeResidueOne
import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJet

#print "file: DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSharpenedBranch"

namespace DkMath.FLT.Seven

noncomputable section

open SevenRealCubicInt
open scoped NumberField Pointwise

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 2000000

namespace SevenRealCubic

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- The C = 1 branch after the R45 depth-9 correction and R47 calibration audit. -/
structure DirectOrbitTrivialCommonFactorSharpenedPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) where
  c_eq_one : h.c = 1
  eta : SevenRealCubicIntˣ
  xi : SevenRealCubicIntˣ
  v : SevenRealCubicIntˣ
  t : SevenRealCubicIntˣ
  gap_scalar_eq :
    h.squareRefinement.gapSquareRoot =
      (eta : SevenRealCubicInt) * (h.u : SevenRealCubicInt)
  quotient_scalar_eq :
    h.squareRefinement.quotientSquareRoot =
      (xi : SevenRealCubicInt) * (h.v : SevenRealCubicInt)
  global_correction_eq :
    directOrbitDeepJetWUnit h.squareRefinement eta =
      directOrbitDeepJetRho * v ^ 7
  linear_mod_seven : thetaLinearModSeven (v : SevenRealCubicInt) = 0
  v_eq_7pow8 : v = t ^ (7 ^ 8)
  correction_eq :
    directOrbitDeepJetWUnit h.squareRefinement eta =
      directOrbitDeepJetRho * t ^ (7 ^ 9)
  correction_ne_one : t ^ (7 ^ 9) ≠ 1
  correction_norm_eq_one : norm (t : SevenRealCubicInt) = 1
  correction_not_torsion :
    modelUnitsEquivRingOfIntegers t ∉ NumberField.Units.torsion Field

/-- The C > 1 branch after the R48 residue-one support strengthening. -/
structure DirectOrbitNontrivialCommonFactorSharpenedPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) where
  c_gt_one : 1 < h.c
  c_ge_29 : 29 ≤ h.c
  prime_support : ∀ q, q.Prime → q ∣ h.c → q % 7 = 1
  height_bound : 29 * h.u ^ 5 < h.v

theorem directOrbitTrivialCommonFactor_exists_nontrivial_7pow9_correction
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p)
    (hc : h.c = 1) :
    ∃ eta xi v t : SevenRealCubicIntˣ,
      h.squareRefinement.gapSquareRoot =
        (eta : SevenRealCubicInt) * (h.u : SevenRealCubicInt) ∧
      h.squareRefinement.quotientSquareRoot =
        (xi : SevenRealCubicInt) * (h.v : SevenRealCubicInt) ∧
      directOrbitDeepJetWUnit h.squareRefinement eta =
        directOrbitDeepJetRho * v ^ 7 ∧
      thetaLinearModSeven (v : SevenRealCubicInt) = 0 ∧
      v = t ^ (7 ^ 8) ∧
      directOrbitDeepJetWUnit h.squareRefinement eta =
        directOrbitDeepJetRho * t ^ (7 ^ 9) ∧
      t ^ (7 ^ 9) ≠ 1 := by
  obtain ⟨eta, heta⟩ :=
    directOrbitTrivialCommonFactor_gap_scalar_unit_of_c_eq_one h hc
  obtain ⟨xi, hxi⟩ :=
    directOrbitTrivialCommonFactor_quotient_scalar_unit_of_c_eq_one h hc
  obtain ⟨v, hv, hlin⟩ :=
    directOrbitDeepJet_global_thetaLinear_mod_seven h hc eta heta
  obtain ⟨t, _, ht, hw, _⟩ :=
    directOrbitPairedDeepJet_current_depth9_wrapper
      h hc eta xi v heta hxi hv hlin
  have htne : t ^ (7 ^ 9) ≠ 1 := by
    intro htone
    have hW : directOrbitDeepJetWUnit h.squareRefinement eta =
        directOrbitDeepJetRho := by
      rw [hw, htone, mul_one]
    exact (directOrbitDeepJetWUnit_ne_calibration h hc eta heta) hW
  exact ⟨eta, xi, v, t, heta, hxi, hv, hlin, ht, hw, htne⟩

theorem directOrbitTrivialCommonFactor_correction_norm_one
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p)
    (_hc : h.c = 1)
    (eta t : SevenRealCubicIntˣ)
    (hw : directOrbitDeepJetWUnit h.squareRefinement eta =
      directOrbitDeepJetRho * t ^ (7 ^ 9)) :
    norm (t : SevenRealCubicInt) = 1 := by
  have hpow : norm (t : SevenRealCubicInt) ^ (7 ^ 9) = 1 := by
    have hnormeq := congrArg
      (fun u : SevenRealCubicIntˣ => norm (u : SevenRealCubicInt)) hw
    rw [directOrbitDeepJetWUnit_norm h.squareRefinement eta] at hnormeq
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val,
      SevenRealCubicInt.norm_mul, SevenRealCubicInt.norm_pow,
      directOrbitDeepJetRho_norm, one_mul] using hnormeq.symm
  rcases Int.natAbs_eq_iff.mp (gapHeight_natAbs_norm_unit t) with ht | ht
  · exact ht
  · exfalso
    rw [ht] at hpow
    norm_num at hpow

theorem directOrbitTrivialCommonFactor_correction_not_torsion
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p)
    (_hc : h.c = 1)
    (eta t : SevenRealCubicIntˣ)
    (_hw : directOrbitDeepJetWUnit h.squareRefinement eta =
      directOrbitDeepJetRho * t ^ (7 ^ 9))
    (htne : t ^ (7 ^ 9) ≠ 1)
    (htnorm : norm (t : SevenRealCubicInt) = 1) :
    modelUnitsEquivRingOfIntegers t ∉ NumberField.Units.torsion Field := by
  intro htorsion
  have hodd : Odd (Module.finrank ℚ Field) := by
    rw [finrank_eq_three]
    norm_num
  have hpm := NumberField.Units.torsion_eq_one_or_neg_one_of_odd_finrank
    hodd ⟨modelUnitsEquivRingOfIntegers t, htorsion⟩
  rcases hpm with htone | htneg
  · have htone' : t = 1 := by
      apply modelUnitsEquivRingOfIntegers.injective
      simpa using htone
    apply htne
    rw [htone']
    simp
  · have htneg' : t = -1 := by
      apply modelUnitsEquivRingOfIntegers.injective
      rw [show modelUnitsEquivRingOfIntegers (-1 : SevenRealCubicIntˣ) =
          (-1 : (𝓞 Field)ˣ) by
        apply Units.ext
        change modelEquivRingOfIntegers (-1) = (-1 : 𝓞 Field)
        simp]
      exact htneg
    rw [htneg'] at htnorm
    norm_num [SevenRealCubicInt.norm] at htnorm

theorem directOrbitCommonFactor_large_residue_one_support
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p)
    (hc : 1 < h.c) :
    29 ≤ h.c ∧ ∀ q, q.Prime → q ∣ h.c → q % 7 = 1 := by
  refine ⟨directOrbitCommonFactor_c_ge_29 h hc, ?_⟩
  intro q hq hqc
  exact directOrbitCommonPrime_q_mod_seven_one h q hq hqc

theorem directOrbitCommonFactor_large_residue_one_height
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p)
    (hc : 1 < h.c) :
    29 * h.u ^ 5 < h.v := by
  exact lt_of_le_of_lt
    (Nat.mul_le_mul_right (h.u ^ 5)
      (directOrbitCommonFactor_c_ge_29 h hc)) h.height

theorem directOrbit_sharpened_common_factor_dichotomy
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) :
    Nonempty (DirectOrbitTrivialCommonFactorSharpenedPacket h) ∨
      Nonempty (DirectOrbitNontrivialCommonFactorSharpenedPacket h) := by
  by_cases hc : h.c = 1
  · left
    obtain ⟨eta, xi, v, t, heta, hxi, hv, hlin, ht, hw, htne⟩ :=
      directOrbitTrivialCommonFactor_exists_nontrivial_7pow9_correction h hc
    have htnorm := directOrbitTrivialCommonFactor_correction_norm_one
      h hc eta t hw
    have htnontorsion := directOrbitTrivialCommonFactor_correction_not_torsion
      h hc eta t hw htne htnorm
    exact ⟨{
      c_eq_one := hc
      eta := eta
      xi := xi
      v := v
      t := t
      gap_scalar_eq := heta
      quotient_scalar_eq := hxi
      global_correction_eq := hv
      linear_mod_seven := hlin
      v_eq_7pow8 := ht
      correction_eq := hw
      correction_ne_one := htne
      correction_norm_eq_one := htnorm
      correction_not_torsion := htnontorsion }⟩
  · right
    have hcpos := h.c_pos
    have hcgt : 1 < h.c := by omega
    have hsupport := directOrbitCommonFactor_large_residue_one_support h hcgt
    exact ⟨{
      c_gt_one := hcgt
      c_ge_29 := hsupport.1
      prime_support := hsupport.2
      height_bound := directOrbitCommonFactor_large_residue_one_height h hcgt }⟩

#print axioms directOrbitTrivialCommonFactor_exists_nontrivial_7pow9_correction
#print axioms directOrbitCommonFactor_large_residue_one_support
#print axioms directOrbit_sharpened_common_factor_dichotomy
#print axioms directOrbitTrivialCommonFactor_correction_not_torsion

end SevenRealCubic
end
end DkMath.FLT.Seven
