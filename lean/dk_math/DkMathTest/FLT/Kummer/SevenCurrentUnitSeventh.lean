/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenCurrentUnitSeventh

open DkMath.FLT.Seven DkMath.FLT.Kummer.SevenRealGN
open DkMath.FLT.Kummer.SevenPrimaryNorm
open DkMath.Lib.Algebra
open SevenRealCubicInt SevenRealCubic SevenCyclotomicDegreeSixInt

namespace DkMathTest.FLT.Kummer.SevenCurrentUnitSeventh

-- Every genuine integer congruence gives rotation fixedness, for arbitrary ring elements.
example (n : ℤ) (w : R) : (7 : R) ∣ SevenRealCubicInt.rotateEquiv ((n : R) + 7 * w) - ((n : R) + 7 * w) := by
  apply (rotation_fixed_mod_seven_iff_integer _).mpr
  exact ⟨n, w, by ring⟩

-- A noninteger element may be rotation fixed modulo 7; exact fixedness is stronger.
example : (7 : R) ∣ SevenRealCubicInt.rotateEquiv (7 * alpha) - 7 * alpha ∧
    (7 * alpha : R) ≠ 0 := by
  constructor
  · apply (rotation_fixed_mod_seven_iff_integer _).mpr
    exact ⟨0, alpha, by simp⟩
  · decide +kernel

-- Alpha itself does not satisfy the fixedness hypothesis.
example : ¬ (7 : R) ∣ SevenRealCubicInt.rotateEquiv alpha - alpha := by
  intro h
  have hd := rotation_fixed_mod_seven_fst alpha h
  have hs := (seven_dvd_iff_coordinates _).mp hd
  norm_num [alpha] at hs

-- The two theta-coordinate formulas have the expected off-diagonal contribution.
example : thetaLinearModSeven (SevenRealCubicInt.rotateEquiv (ofThetaCoordinates 2 1 1) -
      ofThetaCoordinates 2 1 1) = 3 ∧
    thetaSquareModSeven (SevenRealCubicInt.rotateEquiv (ofThetaCoordinates 2 1 1) -
      ofThetaCoordinates 2 1 1) = 2 := by
  rw [rotation_gap_thetaLinear_mod_seven, rotation_gap_thetaSquare_mod_seven]
  decide +kernel

-- Without rotation fixedness the earlier real-primary alpha counterexample still applies.
example : RealPrimary alphaEmbeddedUnit alpha ∧ ¬ ∃ k : Cˣ, alphaEmbeddedUnit = k ^ 7 :=
  ⟨alphaEmbeddedUnit_primary, alphaEmbeddedUnit_not_seventh⟩

-- The bridge consumes precisely rotation fixedness and the same delta's primary proof.
example (x : R) (hrot : (7 : R) ∣ SevenRealCubicInt.rotateEquiv x - x)
    (delta : Cˣ) (hd : RealPrimary delta (-x)) :
    (∃ n : ℤ, (7 : C) ∣ (delta : C) - (n : C)) ∧
      normCoordinates delta = 0 ∧ phaseCharacter delta = 1 := by
  exact ⟨realPrimary_integer_congruence_of_rotation_fixed x hrot delta hd,
    (unit_seventh_iff_obstruction delta).mp (realPrimary_seventh_of_rotation_fixed x hrot delta hd)⟩

-- An actual nonzero local packet with delta=-1 has a seventh root and unit-free factorization.
private noncomputable def P : PrimaryPacket := packetOfRealUnit (-1 : Rˣ)

example : P.source ≠ 0 ∧ P.source = (zeta ^ P.phase - 1) * (((-1 : Cˣ) : C) * P.gamma) ^ 7 ∧
    Ideal.span ({((-1 : Cˣ) : C) * P.gamma} : Set C) = Ideal.span ({P.gamma} : Set C) := by
  have hk : P.delta = (-1 : Cˣ) ^ 7 := by
    apply Units.ext
    change ofReal (-1 : R) = (-1 : C) ^ 7
    simpa only [map_neg, map_one, one_pow] using ((by decide : Odd 7).neg_pow (1 : C)).symm
  exact ⟨P.source_ne_zero, (P.unit_absorption (-1) hk).1, (P.unit_absorption (-1) hk).2.1⟩

-- Absorbing a seventh-power unit is not automatically a new primary packet with delta=1.
example : ¬ RealPrimary (1 : Cˣ) (-1 : R) := by
  intro h
  have hh := realPrimary_residue (1 : Cˣ) (-1) h
  apply (by decide : (1 : ZMod 7) ≠ -1)
  simpa using hh

variable {a b d : ℕ} {source : CounterexamplePack a b d}
variable {r : PrimitiveCounterexampleRamifiedProvenance source}
variable {p : DirectRealCubicRootPacket source r}
variable {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}

-- Every original extraction has the corrected seventh-power class, even before residue normalization.
example (c : CurrentCommonPrimeCyclotomicPacket h q) (epsilon : Cˣ) (beta : C)
    (hf : currentLinearCarrier c = ramifiedUniformizer * ((epsilon : C) * beta ^ 7)) :
    (epsilon : Cˣ ⧸ unitPowerSubgroup C 7) =
      (GNRamifierTwist (current_phase_index_mem c.phase) : Cˣ ⧸ unitPowerSubgroup C 7) := by
  obtain ⟨kappa, hkappa⟩ := current_corrected_unit_seventh c epsilon beta hf
  apply sameUnitPowerClass_iff_quotient_eq.mp
  refine ⟨kappa, ?_⟩
  rw [← hkappa, mul_left_comm, mul_inv_cancel, mul_one]

-- The actual current unit-free factor remains outside the real cubic coefficient ring.
example (c : CurrentCommonPrimeCyclotomicPacket h q) :
    ∃ theta : C,
      currentLinearCarrier c = (zeta ^ phaseInverseExponent c.phase - 1) * theta ^ 7 ∧
      (¬ ∃ v : R, theta = ofReal v) ∧ ¬ ramifiedUniformizer ∣ theta ∧ Fermat7Equation a b d := by
  obtain ⟨Q, kappa, theta, _, _, _, _, _, _, hf, _, ha, hFermat⟩ :=
    currentCarrier_unit_free_factor_receiver c
  exact ⟨theta, hf, current_unit_free_root_not_real c theta hf, ha, hFermat⟩

-- The same current delta has vanishing norm and phase; its absorption does not drop the root ideal.
example (p : DirectRealCubicRootPacket source r) (Q : PrimaryPacket) (hp : Q.parameter = p.rho)
    (m : Ideal C → ℕ) :
    normCoordinates Q.delta = 0 ∧ phaseCharacter Q.delta = 1 ∧
      ∃ kappa : Cˣ, Q.delta = kappa ^ 7 ∧
        ¬ m (Ideal.span ({(kappa : C) * Q.gamma} : Set C)) < m (Ideal.span ({Q.gamma} : Set C)) := by
  obtain ⟨kappa, hkappa⟩ := current_primary_packet_unit_seventh p Q hp
  exact ⟨(current_primary_packet_obstruction_zero p Q hp).1,
    (current_primary_packet_obstruction_zero p Q hp).2, kappa, hkappa,
    Q.unit_absorption_no_measure_drop kappa m⟩

end DkMathTest.FLT.Kummer.SevenCurrentUnitSeventh
