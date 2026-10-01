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

/-! ## R41 global unit invariants -/

theorem directOrbitDeepJetThetaUnit_val :
    (directOrbitDeepJetThetaUnit : SevenRealCubicInt) = thetaSevenUnit := by
  exact thetaSevenUnit_isUnit.unit_spec

theorem directOrbitDeepJetThetaUnit_norm :
    norm (directOrbitDeepJetThetaUnit : SevenRealCubicInt) = -1 := by
  rw [directOrbitDeepJetThetaUnit_val]
  norm_num [thetaSevenUnit, SevenRealCubicInt.norm,
    eisensteinAxisUnitInv, mul, pow_succ]

theorem directOrbitDeepJetThetaUnit_projectiveLog :
    projectiveLog (Additive.ofMul directOrbitDeepJetThetaUnit) = (5, 1) := by
  have hinv2 : (2 : ZMod 7)⁻¹ = 4 := by
    exact ZMod.inv_eq_of_mul_eq_one 7 2 4 (by decide)
  have hinv29 : (29 : ZMod 7)⁻¹ = 1 := by
    exact ZMod.inv_eq_of_mul_eq_one 7 29 1 (by decide)
  have hinvNeg29 : (-29 : ZMod 7)⁻¹ = -1 := by
    exact ZMod.inv_eq_of_mul_eq_one 7 (-29) (-1) (by decide)
  rw [directOrbitDeepJetThetaUnit, projectiveLog_apply]
  simp only [unitNilpotentX, unitNilpotentY]
  rw [thetaSevenUnit_isUnit.unit_spec]
  norm_num [thetaSevenUnit, eisensteinAxisUnitInv,
    eisensteinAxisUnit, eisensteinAxis, alpha, mul, pow_two,
    thetaConstModSeven, thetaLinearModSeven, thetaSquareModSeven,
    hinv2, hinv29, hinvNeg29, div_eq_mul_inv]
  decide

private theorem directOrbit_unit_norm_sq (u : SevenRealCubicIntˣ) :
    norm (u : SevenRealCubicInt) ^ 2 = 1 := by
  rcases (Int.natAbs_eq_iff.mp (gapHeight_natAbs_norm_unit u)) with hu | hu
  · rw [hu]
    norm_num
  · rw [hu]
    norm_num

theorem directOrbitDeepJetXUnit_norm
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (eta : SevenRealCubicIntˣ) :
    norm (directOrbitDeepJetXUnit t eta : SevenRealCubicInt) = 1 := by
  rw [directOrbitDeepJetXUnit_eq_squareTwistCoeff0_mul_eta_pow14]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val,
    SevenRealCubicInt.norm_mul, SevenRealCubicInt.norm_pow,
    directOrbit_squareTwist_coeff0_norm_eq_one]
  rw [show (14 : ℕ) = 2 * 7 by norm_num, pow_mul,
    directOrbit_unit_norm_sq, one_pow]
  norm_num

theorem directOrbitDeepJetXUnit_projectiveLog
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (eta : SevenRealCubicIntˣ) :
    projectiveLog (Additive.ofMul (directOrbitDeepJetXUnit t eta)) = (2, 4) := by
  have hcoeff := directOrbit_squareTwist_coeff_projectiveLog t
  have heta : eta ^ 14 = (eta ^ 2) ^ 7 := by
    rw [show (14 : ℕ) = 2 * 7 by norm_num, pow_mul]
  rw [directOrbitDeepJetXUnit_eq_squareTwistCoeff0_mul_eta_pow14,
    heta, ofMul_mul, map_add, hcoeff.1, projectiveLog_pow_seven]
  simp

theorem directOrbitDeepJetExponent_even
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    Even (directOrbitDeepJetExponent t) := by
  refine ⟨5 + 7 * t.powerSplit.gapSplit.k, ?_⟩
  simp [directOrbitDeepJetExponent]
  ring

theorem directOrbitDeepJetExponent_mod_seven
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    (directOrbitDeepJetExponent t : ZMod 7) = 3 := by
  simp only [directOrbitDeepJetExponent, Nat.cast_add, Nat.cast_mul]
  rw [show (↑(14 : ℕ) : ZMod 7) = 0 by decide]
  simpa using (show (↑(10 : ℕ) : ZMod 7) = 3 by decide)

theorem directOrbitDeepJetWUnit_norm
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (eta : SevenRealCubicIntˣ) :
    norm (directOrbitDeepJetWUnit t eta : SevenRealCubicInt) = 1 := by
  have htheta : norm (directOrbitDeepJetThetaUnit : SevenRealCubicInt) = -1 :=
    directOrbitDeepJetThetaUnit_norm
  have hthetaInv :
      norm ((directOrbitDeepJetThetaUnit⁻¹ : SevenRealCubicIntˣ) :
        SevenRealCubicInt) = -1 := by
    have hmul :
        norm (directOrbitDeepJetThetaUnit : SevenRealCubicInt) *
            norm ((directOrbitDeepJetThetaUnit⁻¹ : SevenRealCubicIntˣ) :
              SevenRealCubicInt) = 1 := by
      calc
        norm (directOrbitDeepJetThetaUnit : SevenRealCubicInt) *
              norm ((directOrbitDeepJetThetaUnit⁻¹ : SevenRealCubicIntˣ) :
                SevenRealCubicInt) =
            norm ((directOrbitDeepJetThetaUnit : SevenRealCubicInt) *
              ((directOrbitDeepJetThetaUnit⁻¹ : SevenRealCubicIntˣ) :
                SevenRealCubicInt)) :=
          (SevenRealCubicInt.norm_mul _ _).symm
        _ = norm (1 : SevenRealCubicInt) := by simp
        _ = 1 := by norm_num [SevenRealCubicInt.norm]
    rw [htheta] at hmul
    linarith
  rw [directOrbitDeepJetWUnit, Units.val_mul,
    SevenRealCubicInt.norm_mul, Units.val_pow_eq_pow_val,
    SevenRealCubicInt.norm_pow, hthetaInv,
    directOrbitDeepJetXUnit_norm]
  obtain ⟨m, hm⟩ := directOrbitDeepJetExponent_even t
  rw [hm, pow_add]
  rw [← mul_pow]
  norm_num

theorem directOrbitDeepJetWUnit_projectiveLog
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (eta : SevenRealCubicIntˣ) :
    projectiveLog (Additive.ofMul (directOrbitDeepJetWUnit t eta)) = (1, 1) := by
  rw [directOrbitDeepJetWUnit, ofMul_mul, map_add, ofMul_pow,
    map_nsmul, ofMul_inv, map_neg,
    directOrbitDeepJetThetaUnit_projectiveLog,
    directOrbitDeepJetXUnit_projectiveLog]
  simp only [nsmul_eq_mul]
  have hn : (directOrbitDeepJetExponent t : ZMod 7 × ZMod 7) = (3, 3) := by
    apply Prod.ext <;>
      exact directOrbitDeepJetExponent_mod_seven t
  rw [hn]
  decide

theorem directOrbitDeepJet_global_seventh_correction
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (eta : SevenRealCubicIntˣ) :
    ∃ v : SevenRealCubicIntˣ,
      directOrbitDeepJetWUnit t eta = directOrbitDeepJetRho * v ^ 7 := by
  let delta := directOrbitDeepJetWUnit t eta * directOrbitDeepJetRho⁻¹
  have hdelta_log : projectiveLog (Additive.ofMul delta) = 0 := by
    rw [show delta = directOrbitDeepJetWUnit t eta *
        directOrbitDeepJetRho⁻¹ by rfl,
      ofMul_mul, map_add, ofMul_inv, map_neg,
      directOrbitDeepJetWUnit_projectiveLog,
      directOrbitDeepJetRho_projectiveLog]
    decide
  obtain ⟨v, hv⟩ :=
    (unit_isSeventhPower_iff_projectiveLog_eq_zero delta).mpr hdelta_log
  refine ⟨v, ?_⟩
  dsimp [delta] at hv
  calc
    directOrbitDeepJetWUnit t eta =
        (directOrbitDeepJetWUnit t eta * directOrbitDeepJetRho⁻¹) *
          directOrbitDeepJetRho := by group
    _ = v ^ 7 * directOrbitDeepJetRho := by rw [hv]
    _ = directOrbitDeepJetRho * v ^ 7 := by ac_rfl

/-! ## R41 trace-plane jet -/

def directOrbitTracePlaneForm (x : SevenRealCubicInt) : ℤ :=
  3 * thetaConstInt x - 10 * thetaLinearInt x + 35 * thetaSquareInt x

theorem directOrbitDeepJet_trace_plane_form
    (W : SevenRealCubicInt)
    (htrace : directOrbitCyclicTrace (eisensteinAxis ^ 2 * W) = 0) :
    directOrbitTracePlaneForm W = 0 := by
  exact directOrbitDeepJet_trace_plane W htrace

theorem directOrbitTracePlaneForm_rho_mul (Y : SevenRealCubicInt) :
    directOrbitTracePlaneForm
        ((directOrbitDeepJetRho : SevenRealCubicInt) * Y) =
      -3 * thetaLinearInt Y + 14 * thetaSquareInt Y := by
  rw [directOrbitDeepJetRho_val]
  rcases Y with ⟨D, E, F⟩
  norm_num [directOrbitTracePlaneForm, thetaConstInt, thetaLinearInt,
    thetaSquareInt, ofThetaCoordinates, ofInt,
    eisensteinAxis_sq_coordinates, eisensteinAxis, SevenRealCubicInt.mul,
    pow_two, pow_succ]
  ring

theorem directOrbitDeepJet_mod49_trace_plane
    (v : SevenRealCubicIntˣ) :
    (49 : ℤ) ∣
      directOrbitTracePlaneForm
          ((directOrbitDeepJetRho : SevenRealCubicInt) *
            (v : SevenRealCubicInt) ^ 7) +
        21 * thetaLinearInt (v : SevenRealCubicInt) *
          thetaConstInt (v : SevenRealCubicInt) ^ 6 := by
  let A : ℤ := thetaConstInt (v : SevenRealCubicInt)
  let B : ℤ := thetaLinearInt (v : SevenRealCubicInt)
  let C : ℤ := thetaSquareInt (v : SevenRealCubicInt)
  have hv : (v : SevenRealCubicInt) = ofThetaCoordinates A B C := by
    exact theta_coordinate_decomposition (v : SevenRealCubicInt)
  have hlin := thetaLinear_pow_seven_mod49_neutral A B C
  have hsq := thetaSquare_pow_seven_mod49_neutral A B C
  rw [← hv] at hlin hsq
  rcases hlin with ⟨q₁, hq₁⟩
  rcases hsq with ⟨q₂, hq₂⟩
  rw [directOrbitTracePlaneForm_rho_mul]
  refine ⟨-3 * q₁ + 14 * q₂ + 2 * C * A ^ 6 +
      6 * B ^ 2 * A ^ 5, ?_⟩
  dsimp [A, B, C] at hq₁ hq₂ ⊢
  linear_combination -3 * hq₁ + 14 * hq₂

local instance directOrbitFactPrimeSeven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

theorem directOrbitDeepJet_thetaConst_nonzero_mod_seven
    (v : SevenRealCubicIntˣ) :
    (thetaConstInt (v : SevenRealCubicInt) : ZMod 7) ≠ 0 := by
  change thetaConstModSeven (v : SevenRealCubicInt) ≠ 0
  exact thetaConstModSeven_unit_ne_zero v

theorem directOrbitDeepJet_thetaLinear_mod_seven
    (v : SevenRealCubicIntˣ)
    (htrace :
      directOrbitTracePlaneForm
          ((directOrbitDeepJetRho : SevenRealCubicInt) *
            (v : SevenRealCubicInt) ^ 7) = 0) :
    thetaLinearModSeven (v : SevenRealCubicInt) = 0 := by
  let A : ℤ := thetaConstInt (v : SevenRealCubicInt)
  let B : ℤ := thetaLinearInt (v : SevenRealCubicInt)
  have hA : (A : ZMod 7) ≠ 0 := by
    dsimp [A]
    exact directOrbitDeepJet_thetaConst_nonzero_mod_seven v
  have hjet := directOrbitDeepJet_mod49_trace_plane v
  have h49 : (49 : ℤ) ∣ 21 * B * A ^ 6 := by
    rcases hjet with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    dsimp [A, B] at hq ⊢
    rw [htrace] at hq
    simpa using hq
  rcases h49 with ⟨q, hq⟩
  have h7prod : (7 : ℤ) ∣ 3 * B * A ^ 6 := by
    refine ⟨q, ?_⟩
    nlinarith [hq]
  have hmod3 : ((3 * B * A ^ 6 : ℤ) : ZMod 7) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (3 * B * A ^ 6) 7).mpr h7prod
  have hmod3' :
      (3 : ZMod 7) * (B : ZMod 7) * (A : ZMod 7) ^ 6 = 0 := by
    simpa [Int.cast_mul, Int.cast_pow] using hmod3
  have hB : (B : ZMod 7) = 0 := by
    have hthree0 : (3 : ZMod 7) ≠ 0 := by
      change (↑(3 : ℕ) : ZMod 7) ≠ 0
      rw [ne_eq, ZMod.natCast_eq_zero_iff]
      norm_num
    rcases mul_eq_zero.mp hmod3' with hleft | hA6
    · rcases mul_eq_zero.mp hleft with hthreeEq | hB
      · exact False.elim (hthree0 hthreeEq)
      · exact hB
    · exact False.elim ((pow_ne_zero 6 hA) hA6)
  change ((thetaLinearInt (v : SevenRealCubicInt) : ℤ) : ZMod 7) = 0
  simpa [B] using hB

theorem directOrbitDeepJet_global_thetaLinear_mod_seven
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) (hc : h.c = 1)
    (eta : SevenRealCubicIntˣ)
    (heta : h.squareRefinement.gapSquareRoot =
      (eta : SevenRealCubicInt) * (h.u : SevenRealCubicInt)) :
    ∃ v : SevenRealCubicIntˣ,
      directOrbitDeepJetWUnit h.squareRefinement eta =
        directOrbitDeepJetRho * v ^ 7 ∧
      thetaLinearModSeven (v : SevenRealCubicInt) = 0 := by
  obtain ⟨v, hv⟩ := directOrbitDeepJet_global_seventh_correction
    h.squareRefinement eta
  have hplane :
      directOrbitTracePlaneForm
          (directOrbitDeepJetWUnit h.squareRefinement eta :
            SevenRealCubicInt) = 0 := by
    exact directOrbitDeepJet_trace_plane_form _
      (directOrbitDeepJet_normalized_trace_zero h hc eta heta)
  have hvtrace :
      directOrbitTracePlaneForm
          ((directOrbitDeepJetRho : SevenRealCubicInt) *
            (v : SevenRealCubicInt) ^ 7) = 0 := by
    convert hplane using 1
    rw [hv, Units.val_mul, Units.val_pow_eq_pow_val]
  exact ⟨v, hv, directOrbitDeepJet_thetaLinear_mod_seven v hvtrace⟩

end SevenRealCubic
end
end DkMath.FLT.Seven
