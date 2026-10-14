/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicTrivialCommonFactorDeepJet

#print "file: DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicCalibrationExclusion"

namespace DkMath.FLT.Seven

noncomputable section

open SevenRealCubicInt
open scoped NumberField Pointwise

set_option linter.style.longLine false
set_option linter.style.setOption false

namespace SevenRealCubic

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

private theorem source_tail_direction :
    eisensteinAxis ^ 35 * thetaSevenUnit ^ 12 =
      -(7 : SevenRealCubicInt) ^ 11 * (⟨2, 1, 1⟩ : SevenRealCubicInt) := by
  have hsmall : eisensteinAxis ^ 2 * thetaSevenUnit =
      -(⟨2, 1, 1⟩ : SevenRealCubicInt) := by
    ext <;> norm_num [eisensteinAxis, thetaSevenUnit,
      eisensteinAxisUnitInv, mul, pow_succ]
  calc
    _ = (eisensteinAxis ^ 3 * thetaSevenUnit) ^ 11 *
        (eisensteinAxis ^ 2 * thetaSevenUnit) := by ring
    _ = _ := by rw [← seven_eq_eisensteinAxis_cube_mul_unit, hsmall]; ring

private theorem source_root_seventh_plane
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) :
    (p.rho ^ 7).snd = (p.rho ^ 7).thd := by
  rw [← p.source_eq_pow, directChosenQuotientRealSource, source_tail_direction]
  norm_num [pow_succ]
  left
  rfl

private def calibrationQuintic (a K : ℤ) : ℤ :=
  3*a^5 + 40*a^4*K + 295*a^3*K^2 + 1293*a^2*K^3 +
    3145*a*K^4 + 3278*K^5

set_option maxHeartbeats 800000 in
-- The existing seventh-power coordinate identities require this normalization budget.
private theorem calibration_seventh_defect (a K : ℤ) :
    ((⟨a, K, K⟩ : SevenRealCubicInt) ^ 7).snd -
        ((⟨a, K, K⟩ : SevenRealCubicInt) ^ 7).thd =
      -49 * K ^ 2 * calibrationQuintic a K := by
  have hcoord : (⟨a, K, K⟩ : SevenRealCubicInt) =
      ofThetaCoordinates (a + 12*K) (7*K) K := by
    ext <;> norm_num [ofThetaCoordinates, ofInt,
      eisensteinAxis_sq_coordinates, eisensteinAxis, pow_two] <;> ring
  have hdefect (v : SevenRealCubicInt) :
      v.snd - v.thd = thetaLinearInt v - 7 * thetaSquareInt v := by
    simp only [thetaLinearInt, thetaSquareInt]
    ring
  rw [hdefect, hcoord, thetaLinear_pow_seven, thetaSquare_pow_seven]
  simp only [seventhThetaLinearQuotient, seventhThetaSquareQuotient,
    seventhThetaLinearBFactor, seventhThetaLinearCFactor,
    seventhThetaSquareBFactor, seventhThetaSquareCFactor, calibrationQuintic]
  ring

private theorem calibration_line_impossible (a K : ℤ)
    (hK : K ≠ 0) (hK7 : (7 : ℤ) ∣ K)
    (hres : thetaResidue (⟨a, K, K⟩ : SevenRealCubicInt) ≠ 0)
    (hplane : ((⟨a, K, K⟩ : SevenRealCubicInt) ^ 7).snd =
      ((⟨a, K, K⟩ : SevenRealCubicInt) ^ 7).thd) : False := by
  have hprod : -49 * K ^ 2 * calibrationQuintic a K = 0 := by
    rw [← calibration_seventh_defect, hplane, sub_self]
  have hpoly : calibrationQuintic a K = 0 :=
    (mul_eq_zero.mp hprod).resolve_left
      (mul_ne_zero (by norm_num) (pow_ne_zero _ hK))
  have hKmod : (K : ZMod 7) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd K 7).mpr hK7
  have hmod := congrArg (fun n : ℤ => (n : ZMod 7)) hpoly
  have ha : (a : ZMod 7) = 0 := by
    simp only [calibrationQuintic, Int.cast_add, Int.cast_mul, Int.cast_pow,
      Int.cast_ofNat, hKmod] at hmod
    norm_num at hmod
    exact hmod.resolve_left (by decide)
  apply hres
  simp [thetaResidue, thetaConstModSeven, ha, hKmod]

private theorem calibration_gap_coordinates (v : SevenRealCubicInt) (K : ℤ)
    (hgap : rotateEquiv v - v =
      (K : SevenRealCubicInt) * eisensteinAxis ^ 2 *
        (directOrbitDeepJetRho : SevenRealCubicInt)) :
    v = ⟨v.fst, K, K⟩ := by
  have hf := congrArg SevenRealCubicInt.fst hgap
  have ht := congrArg SevenRealCubicInt.thd hgap
  rw [directOrbitDeepJetRho_val] at hf ht
  norm_num [rotateEquiv, rotateHom, ofThetaCoordinates, ofInt,
    eisensteinAxis_sq_coordinates, eisensteinAxis, mul, pow_two] at hf ht
  ext
  · rfl
  · linarith
  · linarith

theorem directOrbitDeepJetWUnit_ne_calibration
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) (hc : h.c = 1)
    (eta : SevenRealCubicIntˣ)
    (heta : h.squareRefinement.gapSquareRoot =
      (eta : SevenRealCubicInt) * (h.u : SevenRealCubicInt)) :
    directOrbitDeepJetWUnit h.squareRefinement eta ≠ directOrbitDeepJetRho := by
  intro hW
  let n := directOrbitDeepJetExponent h.squareRefinement
  let K : ℤ := 7 ^ n * (h.u : ℤ) ^ 14
  have hn : 0 < n := by
    dsimp [n, directOrbitDeepJetExponent]
    omega
  have hu : (0 : ℤ) < h.u := by exact_mod_cast h.u_pos
  have hK : K ≠ 0 := by dsimp [K]; positivity
  have hK7 : (7 : ℤ) ∣ K :=
    dvd_mul_of_dvd_left (dvd_pow (dvd_refl _) hn.ne') _
  have hcast : (K : SevenRealCubicInt) =
      (7 : SevenRealCubicInt) ^ n * (h.u : SevenRealCubicInt) ^ 14 := by
    simp [K]
  have hcore : h.squareRefinement.powerSplit.gapCore =
      (directOrbitDeepJetXUnit h.squareRefinement eta : SevenRealCubicInt) *
        (h.u : SevenRealCubicInt) ^ 14 := by
    rw [h.squareRefinement.powerSplit.gapCore_eq,
      h.squareRefinement.gapRoot_eq, heta]
    simp only [directOrbitDeepJetXUnit, directOrbitDeepJetRootUnit,
      Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  have hgap := h.squareRefinement.powerSplit.gap_eq
  rw [hcore, ← mul_assoc,
    directOrbitDeepJet_normalization h hc eta heta, hW] at hgap
  have hgap' : rotateEquiv p.rho - p.rho =
      (K : SevenRealCubicInt) * eisensteinAxis ^ 2 *
        (directOrbitDeepJetRho : SevenRealCubicInt) := by
    change directOrbitGap p = _
    rw [hgap, hcast]
    dsimp [n]
    ring
  have hcoords := calibration_gap_coordinates p.rho K hgap'
  have hres := p.thetaResidue_ne_zero
  have hplane := source_root_seventh_plane p
  rw [hcoords] at hres hplane
  exact calibration_line_impossible p.rho.fst K hK hK7 hres hplane

#print axioms directOrbitDeepJetWUnit_ne_calibration

end SevenRealCubic
end
end DkMath.FLT.Seven
