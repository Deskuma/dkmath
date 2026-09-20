/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicTrivialCommonFactor
import DkMath.FLT.Seven.SevenRealCubicThetaSeventhPowerMod49

#print "file: DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicTrivialCommonFactorDeepJet"

namespace DkMath.FLT.Seven

noncomputable section

open SevenRealCubicInt
open scoped NumberField Pointwise

set_option linter.style.longLine false
set_option linter.style.setOption false

namespace SevenRealCubic

def directOrbitCyclicTrace (x : SevenRealCubicInt) : SevenRealCubicInt :=
  x + rotateEquiv x + rotateEquiv (rotateEquiv x)

def directOrbitDeepJetRootUnit
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (eta : SevenRealCubicIntˣ) : SevenRealCubicIntˣ :=
  t.gapSquareUnit * eta ^ 2

def directOrbitDeepJetXUnit
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (eta : SevenRealCubicIntˣ) : SevenRealCubicIntˣ :=
  t.powerSplit.gapUnit * directOrbitDeepJetRootUnit t eta ^ 7

def directOrbitDeepJetThetaUnit : SevenRealCubicIntˣ :=
  thetaSevenUnit_isUnit.unit

def directOrbitDeepJetExponent
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) : ℕ :=
  10 + 14 * t.powerSplit.gapSplit.k

def directOrbitDeepJetWUnit
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (eta : SevenRealCubicIntˣ) : SevenRealCubicIntˣ :=
  directOrbitDeepJetThetaUnit⁻¹ ^ directOrbitDeepJetExponent t *
    directOrbitDeepJetXUnit t eta

theorem directOrbitDeepJetXUnit_eq_squareTwistCoeff0_mul_eta_pow14
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (eta : SevenRealCubicIntˣ) :
    directOrbitDeepJetXUnit t eta =
      directOrbitSquareTwistCoeff0 t * eta ^ 14 := by
  apply Units.ext
  dsimp [directOrbitDeepJetXUnit, directOrbitDeepJetRootUnit,
    directOrbitSquareTwistCoeff0, directOrbitTwistedCoeff0]
  ring

theorem directOrbitDeepJet_exponent_eq_three_mul_add_two
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    32 + 42 * t.powerSplit.gapSplit.k =
      3 * directOrbitDeepJetExponent t + 2 := by
  simp [directOrbitDeepJetExponent]
  ring

set_option maxHeartbeats 1600000 in
-- The cyclic coefficient expansion normalizes three nested unit rotations.
theorem directOrbitDeepJet_weighted_trace_eq_zero
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) (hc : h.c = 1)
    (eta : SevenRealCubicIntˣ)
    (heta : h.squareRefinement.gapSquareRoot =
      (eta : SevenRealCubicInt) * (h.u : SevenRealCubicInt)) :
    (directOrbitDeepJetXUnit h.squareRefinement eta : SevenRealCubicInt) +
        (directOrbitPairAxisUnitOne : SevenRealCubicInt) ^
            (32 + 42 * h.squareRefinement.powerSplit.gapSplit.k) *
          rotateEquiv (directOrbitDeepJetXUnit h.squareRefinement eta) +
        (directOrbitPairAxisUnitOne : SevenRealCubicInt) ^
            (32 + 42 * h.squareRefinement.powerSplit.gapSplit.k) *
          rotateEquiv ((directOrbitPairAxisUnitOne : SevenRealCubicInt) ^
            (32 + 42 * h.squareRefinement.powerSplit.gapSplit.k)) *
          rotateEquiv (rotateEquiv
            (directOrbitDeepJetXUnit h.squareRefinement eta)) = 0 := by
  have hunit := directOrbitTrivialCommonFactor_unit_twisted_eq h hc eta heta
  have hX := directOrbitDeepJetXUnit_eq_squareTwistCoeff0_mul_eta_pow14
    h.squareRefinement eta
  have hc1 := directOrbit_squareTwist_coeff1_transport h.squareRefinement
  have hc2 := directOrbit_squareTwist_coeff2_transport h.squareRefinement
  have hc1' :
      (directOrbitSquareTwistCoeff1 h.squareRefinement : SevenRealCubicInt) =
        (directOrbitPairAxisUnitOne : SevenRealCubicInt) ^
            (32 + 42 * h.squareRefinement.powerSplit.gapSplit.k) *
          rotateEquiv
            (directOrbitSquareTwistCoeff0 h.squareRefinement : SevenRealCubicInt) := by
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val,
      directOrbitRotateUnit_val] using
      congrArg (fun u : SevenRealCubicIntˣ => (u : SevenRealCubicInt)) hc1
  have hc2' :
      (directOrbitSquareTwistCoeff2 h.squareRefinement : SevenRealCubicInt) =
        (directOrbitPairAxisUnitOne : SevenRealCubicInt) ^
            (32 + 42 * h.squareRefinement.powerSplit.gapSplit.k) *
          rotateEquiv
            (directOrbitSquareTwistCoeff1 h.squareRefinement : SevenRealCubicInt) := by
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val,
      directOrbitRotateUnit_val] using
      congrArg (fun u : SevenRealCubicIntˣ => (u : SevenRealCubicInt)) hc2
  rw [hX]
  calc
    (directOrbitSquareTwistCoeff0 h.squareRefinement : SevenRealCubicInt) *
          (eta : SevenRealCubicInt) ^ 14 +
        (directOrbitPairAxisUnitOne : SevenRealCubicInt) ^
            (32 + 42 * h.squareRefinement.powerSplit.gapSplit.k) *
          rotateEquiv
            ((directOrbitSquareTwistCoeff0 h.squareRefinement : SevenRealCubicInt) *
              (eta : SevenRealCubicInt) ^ 14) +
        (directOrbitPairAxisUnitOne : SevenRealCubicInt) ^
            (32 + 42 * h.squareRefinement.powerSplit.gapSplit.k) *
          rotateEquiv ((directOrbitPairAxisUnitOne : SevenRealCubicInt) ^
            (32 + 42 * h.squareRefinement.powerSplit.gapSplit.k)) *
          rotateEquiv (rotateEquiv
            ((directOrbitSquareTwistCoeff0 h.squareRefinement : SevenRealCubicInt) *
              (eta : SevenRealCubicInt) ^ 14)) =
      (directOrbitSquareTwistCoeff0 h.squareRefinement : SevenRealCubicInt) *
          (eta : SevenRealCubicInt) ^ 14 +
        (directOrbitSquareTwistCoeff1 h.squareRefinement : SevenRealCubicInt) *
          (rotateEquiv (eta : SevenRealCubicInt)) ^ 14 +
        (directOrbitSquareTwistCoeff2 h.squareRefinement : SevenRealCubicInt) *
          (rotateEquiv (rotateEquiv (eta : SevenRealCubicInt))) ^ 14 := by
            simp only [hc1', hc2', map_mul, map_pow]
            ring
    _ = 0 := by
      simpa only [show (14 : ℕ) = 7 * 2 by norm_num, pow_mul,
        directOrbitRotateUnit_val] using hunit

theorem directOrbitCyclicTrace_weighted_eq_zero
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) (hc : h.c = 1)
    (eta : SevenRealCubicIntˣ)
    (heta : h.squareRefinement.gapSquareRoot =
      (eta : SevenRealCubicInt) * (h.u : SevenRealCubicInt)) :
    directOrbitCyclicTrace
        (eisensteinAxis ^
          (32 + 42 * h.squareRefinement.powerSplit.gapSplit.k) *
          (directOrbitDeepJetXUnit h.squareRefinement eta : SevenRealCubicInt)) =
      0 := by
  let t := h.squareRefinement
  let e := 32 + 42 * t.powerSplit.gapSplit.k
  have hweighted := directOrbitDeepJet_weighted_trace_eq_zero h hc eta heta
  have htrace :
      directOrbitCyclicTrace (eisensteinAxis ^ e *
          (directOrbitDeepJetXUnit t eta : SevenRealCubicInt)) =
        eisensteinAxis ^ e *
          ((directOrbitDeepJetXUnit t eta : SevenRealCubicInt) +
            (directOrbitPairAxisUnitOne : SevenRealCubicInt) ^ e *
              rotateEquiv (directOrbitDeepJetXUnit t eta) +
            (directOrbitPairAxisUnitOne : SevenRealCubicInt) ^ e *
              rotateEquiv ((directOrbitPairAxisUnitOne : SevenRealCubicInt) ^ e) *
              rotateEquiv (rotateEquiv
                (directOrbitDeepJetXUnit t eta : SevenRealCubicInt))) := by
    simp only [directOrbitCyclicTrace, map_mul]
    rw [directOrbit_rotate_twice_axis_pow e, directOrbit_rotate_axis_pow e]
    simp only [map_pow, directOrbitRotateUnit_val]
    ring
  have hweighted' :
      (directOrbitDeepJetXUnit t eta : SevenRealCubicInt) +
          (directOrbitPairAxisUnitOne : SevenRealCubicInt) ^ e *
            rotateEquiv (directOrbitDeepJetXUnit t eta) +
          (directOrbitPairAxisUnitOne : SevenRealCubicInt) ^ e *
            rotateEquiv ((directOrbitPairAxisUnitOne : SevenRealCubicInt) ^ e) *
            rotateEquiv (rotateEquiv
              (directOrbitDeepJetXUnit t eta : SevenRealCubicInt)) = 0 := by
    simpa [t, e] using hweighted
  rw [htrace, hweighted', mul_zero]

theorem directOrbitDeepJet_normalization
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) (_hc : h.c = 1)
    (eta : SevenRealCubicIntˣ)
    (_heta : h.squareRefinement.gapSquareRoot =
      (eta : SevenRealCubicInt) * (h.u : SevenRealCubicInt)) :
    eisensteinAxis ^
          (32 + 42 * h.squareRefinement.powerSplit.gapSplit.k) *
          (directOrbitDeepJetXUnit h.squareRefinement eta : SevenRealCubicInt) =
      (7 : SevenRealCubicInt) ^ directOrbitDeepJetExponent h.squareRefinement *
        eisensteinAxis ^ 2 *
          (directOrbitDeepJetWUnit h.squareRefinement eta : SevenRealCubicInt) := by
  let t := h.squareRefinement
  let n := directOrbitDeepJetExponent t
  let e := 32 + 42 * t.powerSplit.gapSplit.k
  have he : e = 3 * n + 2 := by
    exact directOrbitDeepJet_exponent_eq_three_mul_add_two t
  have hseven : (7 : SevenRealCubicInt) =
      eisensteinAxis ^ 3 * (directOrbitDeepJetThetaUnit : SevenRealCubicInt) := by
    simpa [directOrbitDeepJetThetaUnit] using
      seven_eq_eisensteinAxis_cube_mul_unit
  have hunit : (directOrbitDeepJetWUnit t eta : SevenRealCubicInt) =
      ((directOrbitDeepJetThetaUnit⁻¹ : SevenRealCubicIntˣ) :
        SevenRealCubicInt) ^ n *
        (directOrbitDeepJetXUnit t eta : SevenRealCubicInt) := by
    rfl
  change eisensteinAxis ^ e *
      (directOrbitDeepJetXUnit t eta : SevenRealCubicInt) = _
  rw [hunit, he, hseven, mul_pow]
  rw [← pow_mul]
  change eisensteinAxis ^ (3 * n + 2) *
      (directOrbitDeepJetXUnit t eta : SevenRealCubicInt) =
    eisensteinAxis ^ (3 * n) *
        (directOrbitDeepJetThetaUnit : SevenRealCubicInt) ^ n *
      eisensteinAxis ^ 2 *
        (((directOrbitDeepJetThetaUnit⁻¹ : SevenRealCubicIntˣ) :
          SevenRealCubicInt) ^ n *
            (directOrbitDeepJetXUnit t eta : SevenRealCubicInt))
  have hinv :
      (directOrbitDeepJetThetaUnit : SevenRealCubicInt) ^ n *
          ((directOrbitDeepJetThetaUnit⁻¹ : SevenRealCubicIntˣ) :
            SevenRealCubicInt) ^ n = 1 := by
    rw [← mul_pow]
    simp
  calc
    eisensteinAxis ^ (3 * n + 2) *
          (directOrbitDeepJetXUnit t eta : SevenRealCubicInt) =
        eisensteinAxis ^ (3 * n) * eisensteinAxis ^ 2 *
          (directOrbitDeepJetXUnit t eta : SevenRealCubicInt) := by
            rw [pow_add]
    _ = eisensteinAxis ^ (3 * n) *
          ((directOrbitDeepJetThetaUnit : SevenRealCubicInt) ^ n *
            ((directOrbitDeepJetThetaUnit⁻¹ : SevenRealCubicIntˣ) :
              SevenRealCubicInt) ^ n) *
          eisensteinAxis ^ 2 *
          (directOrbitDeepJetXUnit t eta : SevenRealCubicInt) := by
            rw [hinv]
            ring
    _ = eisensteinAxis ^ (3 * n) *
          (directOrbitDeepJetThetaUnit : SevenRealCubicInt) ^ n *
          eisensteinAxis ^ 2 *
          (((directOrbitDeepJetThetaUnit⁻¹ : SevenRealCubicIntˣ) :
            SevenRealCubicInt) ^ n *
            (directOrbitDeepJetXUnit t eta : SevenRealCubicInt)) := by
            ac_rfl

theorem directOrbitDeepJet_normalized_trace_zero
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) (hc : h.c = 1)
    (eta : SevenRealCubicIntˣ)
    (heta : h.squareRefinement.gapSquareRoot =
      (eta : SevenRealCubicInt) * (h.u : SevenRealCubicInt)) :
    directOrbitCyclicTrace
        (eisensteinAxis ^ 2 *
          (directOrbitDeepJetWUnit h.squareRefinement eta : SevenRealCubicInt)) =
      0 := by
  let t := h.squareRefinement
  let n := directOrbitDeepJetExponent t
  have htrace := directOrbitCyclicTrace_weighted_eq_zero h hc eta heta
  have hnorm := directOrbitDeepJet_normalization h hc eta heta
  have htrace' :
      directOrbitCyclicTrace
          (eisensteinAxis ^ (32 + 42 * t.powerSplit.gapSplit.k) *
            (directOrbitDeepJetXUnit t eta : SevenRealCubicInt)) = 0 := by
    simpa [t] using htrace
  rw [hnorm] at htrace'
  have hscalar (u : SevenRealCubicInt) :
      directOrbitCyclicTrace ((7 : SevenRealCubicInt) ^ n * u) =
        (7 : SevenRealCubicInt) ^ n * directOrbitCyclicTrace u := by
    have hrot7 : rotateEquiv (7 : SevenRealCubicInt) = 7 := by
      exact map_natCast (rotateEquiv : SevenRealCubicInt →+* SevenRealCubicInt) 7
    simp only [directOrbitCyclicTrace, map_mul, map_pow, hrot7]
    ring
  have htrace'' :
      directOrbitCyclicTrace
          ((7 : SevenRealCubicInt) ^ n *
            (eisensteinAxis ^ 2 *
              (directOrbitDeepJetWUnit t eta : SevenRealCubicInt))) = 0 := by
    simpa [mul_assoc] using htrace'
  have hprod : (7 : SevenRealCubicInt) ^ n *
      directOrbitCyclicTrace
        (eisensteinAxis ^ 2 *
          (directOrbitDeepJetWUnit t eta : SevenRealCubicInt)) = 0 := by
    rw [hscalar] at htrace''
    exact htrace''
  have h7 : (7 : SevenRealCubicInt) ≠ 0 := by
    intro hzero
    have hfst := congrArg SevenRealCubicInt.fst hzero
    change (7 : ℤ) = 0 at hfst
    norm_num at hfst
  exact (mul_eq_zero.mp hprod).resolve_left (pow_ne_zero _ h7)

-- The concrete cubic coordinate normalization is larger than the default.
theorem directOrbitCyclicTrace_theta_coordinate_formula
    (A B C : ℤ) :
    directOrbitCyclicTrace
        (eisensteinAxis ^ 2 * ofThetaCoordinates A B C) =
      ofInt (7 * (3 * A - 10 * B + 35 * C)) := by
  rw [eisensteinAxis_sq_coordinates]
  apply SevenRealCubicInt.ext <;>
    norm_num [directOrbitCyclicTrace, ofThetaCoordinates,
      ofInt, eisensteinAxis, rotateEquiv, rotateHom,
      SevenRealCubicInt.mul, pow_two, pow_succ] <;>
    ring

theorem directOrbitDeepJet_trace_plane
    (W : SevenRealCubicInt)
    (htrace : directOrbitCyclicTrace (eisensteinAxis ^ 2 * W) = 0) :
    3 * thetaConstInt W - 10 * thetaLinearInt W +
        35 * thetaSquareInt W = 0 := by
  rw [theta_coordinate_decomposition W] at htrace
  rw [directOrbitCyclicTrace_theta_coordinate_formula] at htrace
  have hz := congrArg SevenRealCubicInt.fst htrace
  norm_num at hz
  exact hz

def directOrbitDeepJetRho : SevenRealCubicIntˣ :=
  (-1) * alphaUnit ^ 3

theorem directOrbitDeepJetRho_val :
    (directOrbitDeepJetRho : SevenRealCubicInt) =
      ofThetaCoordinates (-20) (-13) (-2) := by
  change (-1 : SevenRealCubicInt) * alpha ^ 3 = _
  rw [alpha_cube]
  change (-1 : SevenRealCubicInt) *
      (SevenRealCubicInt.ofInt 2 * alpha ^ 2 + alpha -
        SevenRealCubicInt.ofInt 1) =
      SevenRealCubicInt.ofInt (-20) +
        SevenRealCubicInt.ofInt (-13) * eisensteinAxis +
        SevenRealCubicInt.ofInt (-2) * eisensteinAxis ^ 2
  apply SevenRealCubicInt.ext <;>
    norm_num [ofThetaCoordinates, ofInt, eisensteinAxis_sq_coordinates,
      eisensteinAxis, alpha, SevenRealCubicInt.mul, pow_two, pow_succ,
      SevenRealCubicInt.fst_natCast, SevenRealCubicInt.snd_natCast,
      SevenRealCubicInt.thd_natCast, SevenRealCubicInt.fst_intCast,
      SevenRealCubicInt.snd_intCast, SevenRealCubicInt.thd_intCast]

theorem directOrbitDeepJetRho_norm :
    norm (directOrbitDeepJetRho : SevenRealCubicInt) = 1 := by
  rw [directOrbitDeepJetRho_val]
  norm_num [SevenRealCubicInt.norm, ofThetaCoordinates,
    eisensteinAxis_sq_coordinates]

theorem directOrbitDeepJetRho_projectiveLog :
    projectiveLog (Additive.ofMul directOrbitDeepJetRho) = (1, 1) := by
  rw [directOrbitDeepJetRho, ofMul_mul, map_add, projectiveLog_neg_one,
    ofMul_pow, map_nsmul, projectiveLog_alpha]
  decide

theorem directOrbitDeepJetRho_trace_zero :
    directOrbitCyclicTrace
        (eisensteinAxis ^ 2 * (directOrbitDeepJetRho : SevenRealCubicInt)) =
      0 := by
  rw [directOrbitDeepJetRho_val]
  rw [directOrbitCyclicTrace_theta_coordinate_formula]
  apply SevenRealCubicInt.ext <;> norm_num [ofInt]

end SevenRealCubic
end
end DkMath.FLT.Seven
