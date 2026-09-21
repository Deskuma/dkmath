/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicRootPhaseNormalization
import DkMath.FLT.Seven.SevenRamifiedFusionRealPairCoprimalityNormGate
import DkMath.FLT.Seven.SevenRealCubicAxisDrop

#print "file: DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicOrbit"

namespace DkMath.FLT.Seven

noncomputable section

set_option linter.style.longLine false

open scoped QuadraticAlgebra
open SevenRealCubicInt
open SevenCyclotomicDegreeSixInt

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-! ## The finite mod-49 gate -/

set_option maxRecDepth 100000 in
theorem isUnit_seventhPower_iff_pow_six_eq_one_mod49
    (u : ZMod 49) (hu : IsUnit u) :
    (∃ c : ZMod 49, u = c ^ 7) ↔ u ^ 6 = 1 := by
  constructor
  · rintro ⟨c, rfl⟩
    have hc : IsUnit c := by
      apply (isUnit_pow_iff (n := 7) (by norm_num)).mp
      simpa using hu
    have hcard :
        hc.unit ^ Fintype.card (ZMod 49)ˣ = 1 := pow_card_eq_one
    have hcard' := congrArg Units.val hcard
    have hc42 : c ^ 42 = 1 := by
      have hcard'' : (hc.unit : ZMod 49) ^ 42 = 1 := by
        have hcardnum : Fintype.card (ZMod 49)ˣ = 42 := by
          decide
        rw [← hcardnum]
        exact hcard'
      rw [hc.unit_spec] at hcard''
      exact hcard''
    rw [show (c ^ 7) ^ 6 = c ^ 42 by ring, hc42]
  · intro h
    refine ⟨u, ?_⟩
    calc
      u = u ^ 6 * u := by rw [h, one_mul]
      _ = u ^ 7 := by ring

theorem normalizedRoot_endpointRight_seventhPower_iff_sixth_eq_one_mod49
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (_q : DirectCyclotomicNormalizedRootPacket source r) :
    (∃ c : ZMod 49, (r.summit.endpointRight : ZMod 49) = c ^ 7) ↔
      (r.summit.endpointRight : ZMod 49) ^ 6 = 1 := by
  exact isUnit_seventhPower_iff_pow_six_eq_one_mod49 _
    (intCast_isUnit_zmod_sevenPower
      (k := 2) r.summit.endpointRight_not_seven_dvd)

theorem normalizedRoot_endpointRight_mod49_gate_redundant
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (q : DirectCyclotomicNormalizedRootPacket source r) :
    (r.summit.endpointRight : ZMod 49) ^ 6 = 1 := by
  apply
    (normalizedRoot_endpointRight_seventhPower_iff_sixth_eq_one_mod49 q).mp
  refine ⟨scalarLift q.exactRoot.gamma, ?_⟩
  simpa using endpointRight_eq_scalarLift_pow_mod_fortyNine q

/-! ## Relative-norm transport to the real cubic order -/

structure DirectRealCubicRootPacket
    {x y z : ℕ} (source : CounterexamplePack x y z)
    (r : PrimitiveCounterexampleRamifiedProvenance source) where
  cyclotomicRoot : DirectCyclotomicNormalizedRootPacket source r
  rho : SevenRealCubicInt
  rho_eq_quadraticNorm :
    rho = QuadraticAlgebra.norm cyclotomicRoot.gammaNorm
  source_eq_pow :
    directChosenQuotientRealSource r = rho ^ 7
  norm_eq_residualRoot :
    SevenRealCubicInt.norm rho = (r.summit.residualRoot : ℤ)
  not_eisensteinAxis_dvd : ¬eisensteinAxis ∣ rho
  thetaResidue_ne_zero : thetaResidue rho ≠ 0

theorem directRealCubicRootPacket_of_normalizedRootPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (q : DirectCyclotomicNormalizedRootPacket source r) :
    ∃ _p : DirectRealCubicRootPacket source r, True := by
  let rho : SevenRealCubicInt := QuadraticAlgebra.norm q.gammaNorm
  have hsource : directChosenQuotientRealSource r = rho ^ 7 := by
    have h := congrArg QuadraticAlgebra.norm q.gammaNorm_pow_eq_quotient
    rw [QuadraticAlgebra.norm.map_pow,
      directCyclotomicChosenQuotient_quadraticNorm] at h
    exact h.symm
  have hnorm : SevenRealCubicInt.norm rho =
      (r.summit.residualRoot : ℤ) := by
    change cyclotomicNormHom q.gammaNorm =
      (r.summit.residualRoot : ℤ)
    exact q.gammaNorm_norm_eq_residualRoot
  have hnorm_not : ¬(7 : ℤ) ∣ SevenRealCubicInt.norm rho := by
    rw [hnorm]
    exact fun h => r.summit.residualRoot_not_seven_dvd (Int.ofNat_dvd.mp h)
  have hnot : ¬eisensteinAxis ∣ rho := by
    intro hdiv
    rcases hdiv with ⟨a, ha⟩
    have hnorm_mul : SevenRealCubicInt.norm rho =
        SevenRealCubicInt.norm eisensteinAxis *
          SevenRealCubicInt.norm a := by
      rw [ha, SevenRealCubicInt.norm_mul]
    have hseven : (7 : ℤ) ∣ SevenRealCubicInt.norm rho := by
      rw [hnorm_mul]
      norm_num [norm_eisensteinAxis]
    exact hnorm_not hseven
  have htheta : thetaResidue rho ≠ 0 := by
    change thetaConstModSeven rho ≠ 0
    intro hzero
    exact hnot ((eisensteinAxis_dvd_iff_thetaConstModSeven_eq_zero rho).mpr
      hzero)
  refine ⟨{
    cyclotomicRoot := q
    rho := rho
    rho_eq_quadraticNorm := rfl
    source_eq_pow := hsource
    norm_eq_residualRoot := hnorm
    not_eisensteinAxis_dvd := hnot
    thetaResidue_ne_zero := htheta }, trivial⟩

/-! ## The order-three real-cubic exact-power orbit -/

def directRealCubicOrbitSource
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source)
    (i : Fin 3) : SevenRealCubicInt :=
  if i = 0 then directChosenQuotientRealSource r
  else if i = 1 then
    SevenRealCubicInt.rotateEquiv (directChosenQuotientRealSource r)
  else
    SevenRealCubicInt.rotateEquiv
      (SevenRealCubicInt.rotateEquiv (directChosenQuotientRealSource r))

def directRealCubicOrbitRoot
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r)
    (i : Fin 3) : SevenRealCubicInt :=
  if i = 0 then p.rho
  else if i = 1 then SevenRealCubicInt.rotateEquiv p.rho
  else SevenRealCubicInt.rotateEquiv (SevenRealCubicInt.rotateEquiv p.rho)

theorem directRealCubicOrbit_exact_powers
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) :
    directRealCubicOrbitSource r 0 =
        directRealCubicOrbitRoot p 0 ^ 7 ∧
    directRealCubicOrbitSource r 1 =
        directRealCubicOrbitRoot p 1 ^ 7 ∧
    directRealCubicOrbitSource r 2 =
        directRealCubicOrbitRoot p 2 ^ 7 := by
  simp only [directRealCubicOrbitSource, directRealCubicOrbitRoot]
  norm_num
  constructor
  · exact p.source_eq_pow
  constructor
  · simpa only [SevenRealCubicInt.rotateEquiv_apply, map_pow] using
      congrArg SevenRealCubicInt.rotateEquiv p.source_eq_pow
  · simpa only [SevenRealCubicInt.rotateEquiv_apply, map_pow] using
      congrArg
        (fun t => SevenRealCubicInt.rotateEquiv
          (SevenRealCubicInt.rotateEquiv t)) p.source_eq_pow

theorem directRealCubicOrbit_source_three_eq_zero
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source} :
    SevenRealCubicInt.rotateEquiv (directRealCubicOrbitSource r 2) =
      directRealCubicOrbitSource r 0 := by
  simp only [directRealCubicOrbitSource]
  norm_num
  exact SevenRealCubicInt.rotateEquiv_three _

theorem directRealCubicOrbit_root_three_eq_zero
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) :
    SevenRealCubicInt.rotateEquiv (directRealCubicOrbitRoot p 2) =
      directRealCubicOrbitRoot p 0 := by
  simp only [directRealCubicOrbitRoot]
  norm_num
  exact SevenRealCubicInt.rotateEquiv_three _

/-! ## The first Galois source difference -/

theorem rotateEquiv_eisensteinAxis_mul_pairAxisUnit_one :
    SevenRealCubicInt.rotateEquiv eisensteinAxis =
      eisensteinAxis * pairAxisUnit 1 := by
  rw [SevenRealCubicInt.rotateEquiv_eisensteinAxis, pairAxisUnit_one,
    eisensteinAxis_eq]
  ring

theorem pairAxisUnit_one_cube_mul_rotate_thetaSevenUnit_eq :
    pairAxisUnit 1 ^ 3 * SevenRealCubicInt.rotateEquiv thetaSevenUnit =
      thetaSevenUnit := by
  have hmain :
      eisensteinAxis ^ 3 * thetaSevenUnit =
        eisensteinAxis ^ 3 *
          (pairAxisUnit 1 ^ 3 * rotateEquiv thetaSevenUnit) := by
    calc
      eisensteinAxis ^ 3 * thetaSevenUnit = 7 :=
        seven_eq_eisensteinAxis_cube_mul_unit.symm
      _ = SevenRealCubicInt.rotateEquiv (7 : SevenRealCubicInt) := by
        exact (map_intCast SevenRealCubicInt.rotateEquiv 7).symm
      _ = SevenRealCubicInt.rotateEquiv
          (eisensteinAxis ^ 3 * thetaSevenUnit) := by
        rw [seven_eq_eisensteinAxis_cube_mul_unit]
      _ = (eisensteinAxis * pairAxisUnit 1) ^ 3 *
          SevenRealCubicInt.rotateEquiv thetaSevenUnit := by
        rw [map_mul, map_pow,
          rotateEquiv_eisensteinAxis_mul_pairAxisUnit_one]
      _ = eisensteinAxis ^ 3 *
          (pairAxisUnit 1 ^ 3 * rotateEquiv thetaSevenUnit) := by ring
  exact (mul_left_cancel₀
    (pow_ne_zero 3 eisensteinAxis_prime.ne_zero) hmain).symm

private theorem rotateEquiv_intCast_real (n : ℤ) :
    SevenRealCubicInt.rotateEquiv (n : SevenRealCubicInt) = n := by
  exact map_intCast SevenRealCubicInt.rotateEquiv n

private theorem rotateEquiv_natCast_real (n : ℕ) :
    SevenRealCubicInt.rotateEquiv (n : SevenRealCubicInt) = n := by
  exact map_natCast SevenRealCubicInt.rotateEquiv n

def orbitUnit01 : SevenRealCubicInt :=
  (pairAxisUnit 1 - 1) * alphaAddOneInv * thetaSevenUnit ^ 5

theorem orbitUnit01_isUnit : IsUnit orbitUnit01 := by
  rw [orbitUnit01, pairAxisUnit_one]
  have hinv : IsUnit alphaAddOneInv := by
    apply IsUnit.of_mul_eq_one (1 + alpha)
    rw [mul_comm]
    exact alphaAddOne_mul_inv
  exact (alpha_isUnit.mul hinv).mul (thetaSevenUnit_isUnit.pow 5)

noncomputable def orbitUnit01Unit : SevenRealCubicIntˣ :=
  orbitUnit01_isUnit.unit

@[simp] theorem orbitUnit01Unit_val :
    (orbitUnit01Unit : SevenRealCubicInt) = orbitUnit01 :=
  orbitUnit01_isUnit.unit_spec

theorem directRealCubicOrbit_source_difference_factorization
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source} :
    directRealCubicOrbitSource r 1 - directRealCubicOrbitSource r 0 =
      orbitUnit01 *
        (eisensteinAxis ^ 5 * thetaSevenUnit *
          (r.summit.gapRoot : SevenRealCubicInt) ^ 2) ^ 7 := by
  let R : SevenRealCubicInt :=
    (r.summit.endpointLeft : SevenRealCubicInt) *
      (r.summit.endpointRight : SevenRealCubicInt)
  let T : SevenRealCubicInt :=
    eisensteinAxis ^ 35 * thetaSevenUnit ^ 12 *
      (r.summit.gapRoot : SevenRealCubicInt) ^ 14
  have hrotU : pairAxisUnit 1 ^ 3 *
      SevenRealCubicInt.rotateEquiv thetaSevenUnit =
      thetaSevenUnit := pairAxisUnit_one_cube_mul_rotate_thetaSevenUnit_eq
  have hp : pairAxisUnit 1 * alphaAddOneInv = 1 := by
    rw [pairAxisUnit_one]
    exact alphaAddOne_mul_inv
  have hrotU12 :
      pairAxisUnit 1 ^ 36 *
          (SevenRealCubicInt.rotateEquiv thetaSevenUnit) ^ 12 =
        thetaSevenUnit ^ 12 := by
    have h := congrArg (fun w : SevenRealCubicInt => w ^ 12) hrotU
    rw [mul_pow] at h
    convert h using 1; ring
  have hrotT : SevenRealCubicInt.rotateEquiv T =
      eisensteinAxis ^ 35 * alphaAddOneInv * thetaSevenUnit ^ 12 *
        (r.summit.gapRoot : SevenRealCubicInt) ^ 14 := by
    dsimp [T]
    rw [map_mul, map_mul, map_pow, map_pow, map_pow,
      ← SevenRealCubicInt.rotateEquiv_apply,
      ← SevenRealCubicInt.rotateEquiv_apply,
      ← SevenRealCubicInt.rotateEquiv_apply,
      rotateEquiv_eisensteinAxis_mul_pairAxisUnit_one,
      rotateEquiv_natCast_real]
    have haux :
        pairAxisUnit 1 ^ 35 *
            (SevenRealCubicInt.rotateEquiv thetaSevenUnit) ^ 12 =
          alphaAddOneInv * thetaSevenUnit ^ 12 := by
      calc
        pairAxisUnit 1 ^ 35 * (rotateEquiv thetaSevenUnit) ^ 12 =
            alphaAddOneInv *
              (pairAxisUnit 1 ^ 36 *
            (rotateEquiv thetaSevenUnit) ^ 12) := by
                  calc
                    _ = (pairAxisUnit 1 ^ 35 *
                      (pairAxisUnit 1 * alphaAddOneInv)) *
                        (rotateEquiv thetaSevenUnit) ^ 12 := by
                          rw [hp, mul_one]
                    _ = _ := by ring
        _ = alphaAddOneInv * thetaSevenUnit ^ 12 := by rw [hrotU12]
    calc
      _ = eisensteinAxis ^ 35 *
          (pairAxisUnit 1 ^ 35 *
            (SevenRealCubicInt.rotateEquiv thetaSevenUnit) ^ 12) *
          (r.summit.gapRoot : SevenRealCubicInt) ^ 14 := by ring
      _ = _ := by rw [haux]; ring
  have hrotR : SevenRealCubicInt.rotateEquiv R = R := by
    change SevenRealCubicInt.rotateEquiv
        ((r.summit.endpointLeft : SevenRealCubicInt) *
          (r.summit.endpointRight : SevenRealCubicInt)) = _
    rw [map_mul, rotateEquiv_intCast_real, rotateEquiv_intCast_real]
  change (SevenRealCubicInt.rotateEquiv (R - T) - (R - T)) = _
  rw [map_sub, hrotR, hrotT]
  dsimp [orbitUnit01, T, R]
  rw [pairAxisUnit_one]
  have hcoef : 1 - alphaAddOneInv = alphaAddOneInv * alpha := by
    calc
      1 - alphaAddOneInv =
          (1 + alpha) * alphaAddOneInv - alphaAddOneInv := by
            rw [alphaAddOne_mul_inv]
      _ = alphaAddOneInv * alpha := by ring
  linear_combination
    (eisensteinAxis ^ 35 * thetaSevenUnit ^ 12 *
      (r.summit.gapRoot : SevenRealCubicInt) ^ 14) * hcoef

/-! ## The fixed unit class -/

theorem orbitUnit01_projectiveLog :
    projectiveLog (Additive.ofMul orbitUnit01Unit) = (0, 5) := by
  let thetaUnit : SevenRealCubicIntˣ := thetaSevenUnit_isUnit.unit
  have hthetaUnit : (thetaUnit : SevenRealCubicInt) = thetaSevenUnit := by
    exact thetaSevenUnit_isUnit.unit_spec
  have hthetaLog :
      projectiveLog (Additive.ofMul thetaUnit) = (5, 1) := by
    have hinv2 : (2 : ZMod 7)⁻¹ = 4 := by
      exact ZMod.inv_eq_of_mul_eq_one 7 2 4 (by
        change ((8 : ℕ) : ZMod 7) = ((1 : ℕ) : ZMod 7)
        rw [ZMod.natCast_eq_natCast_iff]
        decide)
    rw [projectiveLog_apply]
    simp only [unitNilpotentX, unitNilpotentY]
    rw [hthetaUnit]
    have hinv29 : (29 : ZMod 7)⁻¹ = 1 := by
      exact ZMod.inv_eq_of_mul_eq_one 7 29 1 (by
        change ((29 : ℕ) : ZMod 7) = ((1 : ℕ) : ZMod 7)
        rw [ZMod.natCast_eq_natCast_iff]
        decide)
    norm_num [thetaSevenUnit, eisensteinAxisUnitInv,
      eisensteinAxisUnit, eisensteinAxis, alpha, mul, pow_two,
      thetaConstModSeven, thetaLinearModSeven, thetaSquareModSeven,
      hinv2, hinv29, div_eq_mul_inv]
    decide
  have hinvval :
      ((alphaAddOneUnit⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) =
        alphaAddOneInv := by
    have hmul :
        (alphaAddOneUnit : SevenRealCubicInt) *
            ((alphaAddOneUnit⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) = 1 := by
      simp only [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [alphaAddOneUnit_val] at hmul
    apply mul_left_cancel₀ alphaAddOne_isUnit.ne_zero
    calc
      (1 + alpha) *
          ((alphaAddOneUnit⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) = 1 := hmul
      _ = (1 + alpha) * alphaAddOneInv :=
        alphaAddOne_mul_inv.symm
  have hunit_eq :
      orbitUnit01Unit =
        alphaUnit * alphaAddOneUnit⁻¹ * thetaUnit ^ 5 := by
    apply Units.ext
    rw [orbitUnit01Unit_val, Units.val_mul, Units.val_mul,
      alphaUnit_val, hinvval]
    change orbitUnit01 = alpha * alphaAddOneInv *
      (thetaUnit : SevenRealCubicInt) ^ 5
    rw [hthetaUnit]
    rw [orbitUnit01, pairAxisUnit_one]
    ring
  rw [hunit_eq, ofMul_mul, map_add, ofMul_mul, map_add,
    projectiveLog_alpha, ofMul_inv, map_neg, ofMul_pow, map_nsmul,
    projectiveLog_alphaAddOne, hthetaLog]
  decide

theorem orbitUnit01_not_seventhPower :
    ¬ ∃ v : SevenRealCubicIntˣ, orbitUnit01Unit = v ^ 7 := by
  intro h
  have hlog :=
    (SevenRealCubic.unit_isSeventhPower_iff_projectiveLog_eq_zero
      orbitUnit01Unit).mp h
  rw [orbitUnit01_projectiveLog] at hlog
  have hne : (5 : ZMod 7) ≠ 0 := by decide
  exact hne (by simpa using congrArg Prod.snd hlog)

theorem orbitUnit01_class_is_nonzero :
    projectiveLog (Additive.ofMul orbitUnit01Unit) ≠ 0 := by
  rw [orbitUnit01_projectiveLog]
  decide

end

end DkMath.FLT.Seven
