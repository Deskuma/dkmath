/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionRelativeRealIndex

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionRealPairCarrier"

namespace DkMath.FLT.Seven

noncomputable section

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩
set_option maxRecDepth 4000
set_option linter.style.longLine false

namespace RamifiedSignedRootDepthPacket

private def normPacket (p : RamifiedSignedRootDepthPacket) :
    RamifiedRealCubicNormPacket :=
  p.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket

/-- Both signed roots reduce to the cube of the nonramified inner
coordinate. -/
theorem signedLeftRoot_modSeven_eq_innerFst_cube
    (p : RamifiedSignedRootDepthPacket) :
    (p.signedLeftRoot : ZMod 7) =
      (p.normPacket.quadratic.innerRoot.fst : ZMod 7) ^ 3 := by
  let q := p.normPacket
  have hsnd :
      (q.quadratic.innerRoot.snd : ZMod 7) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr q.innerSnd_seven_dvd
  have h := congrArg (fun z : ℤ => (z : ZMod 7)) q.leftCubic_eq
  push_cast at h
  rw [ZMod.pow_card] at h
  simp [seventhPowerSndLeftCubic, hsnd] at h
  rw [p.signedLeftRoot_eq]
  exact h.symm

theorem signedRightRoot_modSeven_eq_innerFst_cube
    (p : RamifiedSignedRootDepthPacket) :
    (p.signedRightRoot : ZMod 7) =
      (p.normPacket.quadratic.innerRoot.fst : ZMod 7) ^ 3 := by
  let q := p.normPacket
  have hsnd :
      (q.quadratic.innerRoot.snd : ZMod 7) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr q.innerSnd_seven_dvd
  have h := congrArg (fun z : ℤ => (z : ZMod 7)) q.rightCubic_eq
  push_cast at h
  rw [ZMod.pow_card] at h
  simp [seventhPowerSndRightCubic, hsnd] at h
  rw [p.signedRightRoot_eq]
  exact h.symm

/-- The product of the signed roots has neutral residue. -/
theorem signedRoots_product_modSeven_eq_one
    (p : RamifiedSignedRootDepthPacket) :
    ((p.signedRightRoot * p.signedLeftRoot : ℤ) : ZMod 7) = 1 := by
  push_cast
  rw [p.signedRightRoot_modSeven_eq_innerFst_cube,
    p.signedLeftRoot_modSeven_eq_innerFst_cube]
  rw [← pow_add]
  norm_num
  let a : (ZMod 7)ˣ :=
    Units.mk0 (p.normPacket.quadratic.innerRoot.fst : ZMod 7) (by
      intro hzero
      exact p.normPacket.innerFst_not_seven_dvd
        ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp hzero))
  exact congrArg Units.val (sevenUnit_pow_six a)

end RamifiedSignedRootDepthPacket

namespace SevenRealCubicInt

/-- The three real conjugates of `alpha`, indexed in Galois order. -/
def cyclicAlpha (i : Fin 3) : SevenRealCubicInt :=
  if i = 0 then alpha
  else if i = 1 then alpha ^ 2 - 2 * alpha
  else -alpha ^ 2 + alpha + 2

/-- Unit quotient of the conjugate ramified axis by `theta`. -/
def pairAxisUnit (i : Fin 3) : SevenRealCubicInt :=
  if i = 0 then 1
  else if i = 1 then 1 + alpha
  else alpha ^ 2

@[simp] theorem pairAxisUnit_zero : pairAxisUnit 0 = 1 := by
  simp only [pairAxisUnit, if_pos]

@[simp] theorem pairAxisUnit_one : pairAxisUnit 1 = 1 + alpha := by
  rw [pairAxisUnit, if_neg (by decide), if_pos]
  rfl

@[simp] theorem pairAxisUnit_two : pairAxisUnit 2 = alpha ^ 2 := by
  rw [pairAxisUnit, if_neg (by decide), if_neg (by decide)]

theorem cyclicAlpha_sub_three_eq_axis_mul_pairAxisUnit
    (i : Fin 3) :
    cyclicAlpha i - 3 = eisensteinAxis * pairAxisUnit i := by
  have hthree : (3 : SevenRealCubicInt) = ofInt 3 := by
    apply ext
    · exact fst_natCast 3
    · exact snd_natCast 3
    · exact thd_natCast 3
  have htwo : (2 : SevenRealCubicInt) = ofInt 2 := by
    apply ext
    · exact fst_natCast 2
    · exact snd_natCast 2
    · exact thd_natCast 2
  rw [hthree]
  fin_cases i <;>
    simp [cyclicAlpha, pairAxisUnit, htwo] <;>
    ext <;>
    norm_num [eisensteinAxis, alpha, mul, pow_two]

theorem pairAxisUnit_thetaResidue
    (i : Fin 3) :
    thetaResidue (pairAxisUnit i) =
      if i = 0 then 1 else if i = 1 then 4 else 2 := by
  fin_cases i <;>
    simp [pairAxisUnit] <;>
    norm_num [thetaResidue, thetaConstModSeven, alpha, mul, pow_two]
  decide

private def phaseUnit (i : Fin 3) : (ZMod 7)ˣ :=
  Units.mk0
    (if i = 0 then (1 : ZMod 7) else if i = 1 then 4 else 2)
    (by fin_cases i <;> decide)

/-- The three pair phases `1,4,2`, as the full ternary subgroup. -/
def pairPhase (i : Fin 3) : SevenTernarySector :=
  ⟨phaseUnit i, by
    apply Units.ext
    fin_cases i <;> decide⟩

@[simp] theorem pairPhase_zero :
    pairPhase 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  decide

theorem pairPhase_one_val :
    ((pairPhase 1 : (ZMod 7)ˣ) : ZMod 7) = 4 := by
  decide

theorem pairPhase_two_val :
    ((pairPhase 2 : (ZMod 7)ˣ) : ZMod 7) = 2 := by
  decide

theorem pairAxisUnit_thetaResidue_eq_pairPhase
    (i : Fin 3) :
    thetaResidue (pairAxisUnit i) =
      ((pairPhase i : (ZMod 7)ˣ) : ZMod 7) := by
  rw [pairAxisUnit_thetaResidue]
  fin_cases i <;> simp [pairPhase, phaseUnit]

private theorem zmodSeven_cube_eq_one_cases
    (x : ZMod 7) (hx : x ^ 3 = 1) :
    x = 1 ∨ x = 4 ∨ x = 2 := by
  have hfactor : (x - 1) * (x - 4) * (x - 2) = 0 := by
    have hseven : (7 : ZMod 7) = 0 := by decide
    linear_combination hx -
      (x ^ 2 - 2 * x + 1) * hseven
  rcases mul_eq_zero.mp hfactor with hfactor | htwo
  · rcases mul_eq_zero.mp hfactor with hone | hfour
    · exact Or.inl (sub_eq_zero.mp hone)
    · exact Or.inr (Or.inl (sub_eq_zero.mp hfour))
  · exact Or.inr (Or.inr (sub_eq_zero.mp htwo))

private def pairPhaseIndex (s : SevenTernarySector) : Fin 3 :=
  if (((s : (ZMod 7)ˣ) : ZMod 7)) = 1 then 0
  else if (((s : (ZMod 7)ˣ) : ZMod 7)) = 4 then 1
  else 2

/-- Explicit enumeration `0 ↦ 1`, `1 ↦ 4`, `2 ↦ 2` of the complete
ternary sector. -/
def pairPhaseEquiv : Fin 3 ≃ SevenTernarySector where
  toFun := pairPhase
  invFun := pairPhaseIndex
  left_inv i := by
    fin_cases i <;> decide
  right_inv s := by
    have hs :
        ((((s : SevenTernarySector) : (ZMod 7)ˣ) : ZMod 7) ^ 3) = 1 := by
      exact congrArg Units.val s.property
    rcases zmodSeven_cube_eq_one_cases _ hs with hs | hs | hs
    · have hi : pairPhaseIndex s = 0 := by
        simp [pairPhaseIndex, hs]
      rw [hi, pairPhase_zero]
      apply Subtype.ext
      apply Units.ext
      exact hs.symm
    · have hi : pairPhaseIndex s = 1 := by
        have h41 : (4 : ZMod 7) ≠ 1 := by decide
        simp [pairPhaseIndex, hs, h41]
      rw [hi]
      apply Subtype.ext
      apply Units.ext
      exact pairPhase_one_val.trans hs.symm
    · have hi : pairPhaseIndex s = 2 := by
        have h21 : (2 : ZMod 7) ≠ 1 := by decide
        have h24 : (2 : ZMod 7) ≠ 4 := by decide
        simp [pairPhaseIndex, hs, h21, h24]
      rw [hi]
      apply Subtype.ext
      apply Units.ext
      exact pairPhase_two_val.trans hs.symm

/-- The three forward pair-axis differences have norms `-1,-1,1`. -/
theorem pairAxisUnit_forward_difference_norms :
    norm (pairAxisUnit 1 - pairAxisUnit 0) = -1 ∧
      norm (pairAxisUnit 2 - pairAxisUnit 1) = -1 ∧
      norm (pairAxisUnit 2 - pairAxisUnit 0) = 1 := by
  have h10 : pairAxisUnit 1 - pairAxisUnit 0 = alpha := by
    rw [pairAxisUnit_one, pairAxisUnit_zero]
    ring
  have h21 :
      pairAxisUnit 2 - pairAxisUnit 1 =
        (⟨-1, -1, 1⟩ : SevenRealCubicInt) := by
    rw [pairAxisUnit_two, pairAxisUnit_one]
    ext <;> norm_num [alpha, mul, pow_two]
  have h20 :
      pairAxisUnit 2 - pairAxisUnit 0 =
        (⟨-1, 0, 1⟩ : SevenRealCubicInt) := by
    rw [pairAxisUnit_two, pairAxisUnit_zero]
    ext <;> norm_num [alpha, mul, pow_two]
  rw [h10, h21, h20]
  constructor
  · norm_num [norm, alpha]
  · norm_num [norm]

theorem pairAxisUnit_one_sub_zero_isUnit :
    IsUnit (pairAxisUnit 1 - pairAxisUnit 0) := by
  change IsUnit alpha
  exact alpha_isUnit

theorem pairAxisUnit_two_sub_one_isUnit :
    IsUnit (pairAxisUnit 2 - pairAxisUnit 1) := by
  change IsUnit (alpha ^ 2 - alpha - 1)
  let inv := alpha ^ 2 - 2 * alpha
  have htwo : (2 : SevenRealCubicInt) = ofInt 2 := by
    apply ext
    · exact fst_natCast 2
    · exact snd_natCast 2
    · exact thd_natCast 2
  have hmul :
      (alpha ^ 2 - alpha - 1) * inv = 1 := by
    dsimp [inv]
    rw [htwo]
    ext <;>
      norm_num [alpha, mul, pow_two]
  exact IsUnit.of_mul_eq_one inv hmul

theorem pairAxisUnit_two_sub_zero_isUnit :
    IsUnit (pairAxisUnit 2 - pairAxisUnit 0) := by
  change IsUnit (alpha ^ 2 - 1)
  let inv := alpha - 2
  have htwo : (2 : SevenRealCubicInt) = ofInt 2 := by
    apply ext
    · exact fst_natCast 2
    · exact snd_natCast 2
    · exact thd_natCast 2
  have hmul :
      (alpha ^ 2 - 1) * inv = 1 := by
    dsimp [inv]
    rw [htwo]
    ext <;>
      norm_num [alpha, mul, pow_two]
  exact IsUnit.of_mul_eq_one inv hmul

private theorem ofInt_mul (a b : ℤ) :
    ofInt a * ofInt b = ofInt (a * b) := by
  ext <;> simp

private theorem ofInt_pow (z : ℤ) (n : ℕ) :
    ofInt z ^ n = ofInt (z ^ n) := by
  induction n with
  | zero => ext <;> norm_num
  | succ n ih =>
      rw [pow_succ, ih, ofInt_mul, pow_succ]

@[simp] theorem fst_ofInt_pow (z : ℤ) (n : ℕ) :
    (ofInt z ^ n).fst = z ^ n := by
  exact congrArg fst (ofInt_pow z n)

@[simp] theorem snd_ofInt_pow (z : ℤ) (n : ℕ) :
    (ofInt z ^ n).snd = 0 := by
  exact congrArg snd (ofInt_pow z n)

@[simp] theorem thd_ofInt_pow (z : ℤ) (n : ℕ) :
    (ofInt z ^ n).thd = 0 := by
  exact congrArg thd (ofInt_pow z n)

end SevenRealCubicInt

namespace RamifiedSignedRootDepthPacket

open SevenRealCubicInt

/-- The real quadratic carrier attached to the `i`-th conjugate pair. -/
def realPairCarrier
    (p : RamifiedSignedRootDepthPacket) (i : Fin 3) :
    SevenRealCubicInt :=
  (p.signedRightRoot : SevenRealCubicInt) ^ 2 +
      (p.signedRightRoot : SevenRealCubicInt) *
        (p.signedLeftRoot : SevenRealCubicInt) +
      (p.signedLeftRoot : SevenRealCubicInt) ^ 2 -
    cyclicAlpha i *
      ((p.signedRightRoot : SevenRealCubicInt) *
        (p.signedLeftRoot : SevenRealCubicInt))

/-- The three real conjugate-pair carriers multiply to the signed
seventh quotient. -/
theorem realPairCarrier_product_eq_signedSeventhQuotient
    (p : RamifiedSignedRootDepthPacket) :
    p.realPairCarrier 0 * p.realPairCarrier 1 * p.realPairCarrier 2 =
      (signedSeventhQuotient p.signedRightRoot p.signedLeftRoot :
        SevenRealCubicInt) := by
  rw [show
    (signedSeventhQuotient p.signedRightRoot p.signedLeftRoot :
        SevenRealCubicInt) =
      (p.signedRightRoot : SevenRealCubicInt) ^ 6 +
        (p.signedRightRoot : SevenRealCubicInt) ^ 5 *
          (p.signedLeftRoot : SevenRealCubicInt) +
        (p.signedRightRoot : SevenRealCubicInt) ^ 4 *
          (p.signedLeftRoot : SevenRealCubicInt) ^ 2 +
        (p.signedRightRoot : SevenRealCubicInt) ^ 3 *
          (p.signedLeftRoot : SevenRealCubicInt) ^ 3 +
        (p.signedRightRoot : SevenRealCubicInt) ^ 2 *
          (p.signedLeftRoot : SevenRealCubicInt) ^ 4 +
        (p.signedRightRoot : SevenRealCubicInt) *
          (p.signedLeftRoot : SevenRealCubicInt) ^ 5 +
        (p.signedLeftRoot : SevenRealCubicInt) ^ 6 by
      simp [signedSeventhQuotient]]
  have halpha :
      alpha ^ 3 - 2 * alpha ^ 2 - alpha + 1 = 0 := by
    rw [SevenRealCubicInt.alpha_cube]
    ring
  simp only [realPairCarrier, SevenRealCubicInt.cyclicAlpha,
    Fin.isValue, Fin.reduceEq, ↓reduceIte]
  linear_combination
    ((p.signedLeftRoot : SevenRealCubicInt) ^ 2 *
      (p.signedRightRoot : SevenRealCubicInt) ^ 2 *
      (alpha ^ 2 *
          (p.signedLeftRoot : SevenRealCubicInt) *
          (p.signedRightRoot : SevenRealCubicInt) -
        alpha * (p.signedLeftRoot : SevenRealCubicInt) ^ 2 -
        2 * alpha *
          (p.signedLeftRoot : SevenRealCubicInt) *
          (p.signedRightRoot : SevenRealCubicInt) -
        alpha * (p.signedRightRoot : SevenRealCubicInt) ^ 2 +
        (p.signedLeftRoot : SevenRealCubicInt) ^ 2 +
        (p.signedRightRoot : SevenRealCubicInt) ^ 2)) * halpha

/-- The theta-unit core remaining after the one forced ramified factor
is removed from a real pair carrier. -/
def realPairCore
    (p : RamifiedSignedRootDepthPacket) (i : Fin 3) :
    SevenRealCubicInt :=
  eisensteinAxis ^ 23 * thetaSevenUnit ^ 8 *
      (p.gapRoot : SevenRealCubicInt) ^ 2 -
    pairAxisUnit i *
      ((p.signedRightRoot : SevenRealCubicInt) *
        (p.signedLeftRoot : SevenRealCubicInt))

/-- Every real pair carrier contains exactly the displayed first
ramified axis factor, without using division. -/
theorem realPairCarrier_eq_eisensteinAxis_mul_core
    (p : RamifiedSignedRootDepthPacket) (i : Fin 3) :
    p.realPairCarrier i = eisensteinAxis * p.realPairCore i := by
  have hgap := congrArg
    (fun z : ℤ => (z : SevenRealCubicInt)) p.signedGap_eq
  push_cast at hgap
  have hseven_four :
      (2401 : SevenRealCubicInt) =
        (7 : SevenRealCubicInt) ^ 4 := by
    norm_num
  rw [hseven_four] at hgap
  have hgap_sq :
      ((p.signedRightRoot : SevenRealCubicInt) -
          (p.signedLeftRoot : SevenRealCubicInt)) ^ 2 =
        eisensteinAxis ^ 24 * thetaSevenUnit ^ 8 *
          (p.gapRoot : SevenRealCubicInt) ^ 2 := by
    rw [hgap, seven_eq_eisensteinAxis_cube_mul_unit]
    ring
  calc
    p.realPairCarrier i =
        ((p.signedRightRoot : SevenRealCubicInt) -
            (p.signedLeftRoot : SevenRealCubicInt)) ^ 2 -
          (cyclicAlpha i - 3) *
            ((p.signedRightRoot : SevenRealCubicInt) *
              (p.signedLeftRoot : SevenRealCubicInt)) := by
      simp only [realPairCarrier]
      ring
    _ = eisensteinAxis * p.realPairCore i := by
      rw [hgap_sq,
        SevenRealCubicInt.cyclicAlpha_sub_three_eq_axis_mul_pairAxisUnit]
      simp only [realPairCore]
      ring

/-- The normalized core remembers precisely the negative ternary phase
of its real conjugate pair. -/
theorem realPairCore_thetaResidue
    (p : RamifiedSignedRootDepthPacket) (i : Fin 3) :
    thetaResidue (p.realPairCore i) =
      -(((pairPhase i : SevenTernarySector) : (ZMod 7)ˣ) : ZMod 7) := by
  have htheta : thetaResidue eisensteinAxis = 0 := by
    norm_num [thetaResidue, thetaConstModSeven, eisensteinAxis]
  have hscalar (z : ℤ) :
      thetaResidue (z : SevenRealCubicInt) = (z : ZMod 7) := by
    simp [thetaResidue, thetaConstModSeven]
  have hprod :
      thetaResidue
          ((p.signedRightRoot : SevenRealCubicInt) *
            (p.signedLeftRoot : SevenRealCubicInt)) = 1 := by
    rw [map_mul, hscalar, hscalar]
    simpa only [Int.cast_mul] using
      p.signedRoots_product_modSeven_eq_one
  simp only [realPairCore, map_sub, map_mul, map_pow, htheta,
    zero_pow (by norm_num : 23 ≠ 0), zero_mul, hprod, mul_one,
    SevenRealCubicInt.pairAxisUnit_thetaResidue_eq_pairPhase,
    zero_sub]

/-- Each real pair carrier has exact theta-depth one. -/
theorem realPairCarrier_exactThetaDepth_one
    (p : RamifiedSignedRootDepthPacket) (i : Fin 3) :
    HasExactThetaDepth (p.realPairCarrier i) 1 := by
  rw [p.realPairCarrier_eq_eisensteinAxis_mul_core]
  constructor
  · exact ⟨p.realPairCore i, by simp⟩
  · rintro ⟨z, hz⟩
    have htheta_ne : eisensteinAxis ≠ 0 := by
      intro h
      have := congrArg SevenRealCubicInt.snd h
      norm_num [eisensteinAxis] at this
    have hcore_eq :
        p.realPairCore i = z * eisensteinAxis := by
      apply mul_left_cancel₀ htheta_ne
      rw [hz]
      ring
    have hcore_dvd : eisensteinAxis ∣ p.realPairCore i := by
      exact ⟨z, by rw [hcore_eq]; ring⟩
    rw [SevenRealCubicInt.eisensteinAxis_dvd_iff_thetaConstModSeven_eq_zero]
      at hcore_dvd
    change thetaResidue (p.realPairCore i) = 0 at hcore_dvd
    have hres := p.realPairCore_thetaResidue i
    rw [hcore_dvd] at hres
    have hphase_ne :
        (((pairPhase i : SevenTernarySector) : (ZMod 7)ˣ) : ZMod 7) ≠ 0 :=
      Units.ne_zero _
    exact hphase_ne (neg_eq_zero.mp hres.symm)

/-- Exact reconstruction of the signed quotient root from the three
theta-unit pair cores. -/
theorem pairCore_product_eq_quotientRoot
    (p : RamifiedSignedRootDepthPacket) :
    -(eisensteinAxis + 1) ^ 2 *
        p.realPairCore 0 * p.realPairCore 1 * p.realPairCore 2 =
      (p.quotientRoot : SevenRealCubicInt) := by
  have hprod := p.realPairCarrier_product_eq_signedSeventhQuotient
  rw [p.realPairCarrier_eq_eisensteinAxis_mul_core 0,
    p.realPairCarrier_eq_eisensteinAxis_mul_core 1,
    p.realPairCarrier_eq_eisensteinAxis_mul_core 2] at hprod
  have hquot := congrArg
    (fun z : ℤ => (z : SevenRealCubicInt)) p.signedQuotient_eq
  push_cast at hquot
  rw [hquot] at hprod
  have hseven_ne : (7 : SevenRealCubicInt) ≠ 0 := by
    intro h
    have := congrArg SevenRealCubicInt.fst h
    change (7 : ℤ) = 0 at this
    norm_num at this
  apply mul_left_cancel₀ hseven_ne
  rw [← hprod]
  rw [show
    (eisensteinAxis * p.realPairCore 0) *
        (eisensteinAxis * p.realPairCore 1) *
        (eisensteinAxis * p.realPairCore 2) =
      eisensteinAxis ^ 3 *
        (p.realPairCore 0 * p.realPairCore 1 * p.realPairCore 2) by
    ring]
  rw [SevenRealCubicInt.eisensteinAxis_cube]
  ring

/-- A second proof of the positive quotient sector, obtained from the
three real-pair cores rather than the integer first variation. -/
theorem quotientRoot_modSeven_eq_one_from_pairCores
    (p : RamifiedSignedRootDepthPacket) :
    (p.quotientRoot : ZMod 7) = 1 := by
  have h := congrArg thetaResidue p.pairCore_product_eq_quotientRoot
  rw [map_mul, map_mul, map_mul, map_neg, map_pow, map_add,
    p.realPairCore_thetaResidue 0,
    p.realPairCore_thetaResidue 1,
    p.realPairCore_thetaResidue 2] at h
  norm_num [thetaResidue, thetaConstModSeven, eisensteinAxis,
    SevenRealCubicInt.pairPhase, SevenRealCubicInt.phaseUnit] at h
  simpa [thetaResidue, thetaConstModSeven] using h.symm

end RamifiedSignedRootDepthPacket

namespace RamifiedPairedThetaRootJetPacket

open SevenRealCubicInt

/-- The real conjugate pair selected by the absolute ternary coordinate
of the FUSION slope. -/
def selectedPairIndex
    (p : RamifiedPairedThetaRootJetPacket) : Fin 3 :=
  pairPhaseEquiv.symm p.rightUnitSectorAddress.2

theorem pairPhase_selectedPairIndex
    (p : RamifiedPairedThetaRootJetPacket) :
    pairPhase p.selectedPairIndex = p.rightUnitSectorAddress.2 :=
  pairPhaseEquiv.apply_symm_apply _

/-- The selected real pair has residue `-tau²`; no binary orientation
between `tau` and `-tau` is chosen. -/
theorem selectedPairCore_thetaResidue
    (p : RamifiedPairedThetaRootJetPacket) :
    thetaResidue
        (p.signedDepth.realPairCore p.selectedPairIndex) =
      -p.fusionSlope ^ 2 := by
  rw [p.signedDepth.realPairCore_thetaResidue,
    p.pairPhase_selectedPairIndex]
  rfl

/-- The relative real index is one exactly on the two orientations of
the absolute pair with phase `tau²`. -/
theorem relativeRealIndex_eq_one_iff_square_eq_fusionSlope
    (p : RamifiedPairedThetaRootJetPacket) (k : (ZMod 7)ˣ) :
    p.relativeRealIndex k = 1 ↔
      k ^ 2 = p.fusionSlopeUnit ^ 2 := by
  rw [p.relativeRealIndex_eq_one_iff]
  constructor
  · rintro (rfl | rfl)
    · rfl
    · simp
  · intro h
    exact Units.eq_or_eq_neg_of_sq_eq_sq _ _ h

/-- Direct fusion of the right normalized quadratic jet with the
selected real-pair core. -/
theorem right_normalizedQuadraticJet_eq_three_mul_selectedPairResidue
    (p : RamifiedPairedThetaRootJetPacket) :
    (p.right.thetaSquareCore : ZMod 7) /
        (p.right.thetaConst : ZMod 7) =
      3 * thetaResidue
        (p.signedDepth.realPairCore p.selectedPairIndex) := by
  rw [p.right_normalizedQuadraticJet_eq,
    p.selectedPairCore_thetaResidue]
  ring

/-- The same real-pair fusion certificate for the left quadratic jet. -/
theorem left_normalizedQuadraticJet_eq_three_mul_selectedPairResidue
    (p : RamifiedPairedThetaRootJetPacket) :
    (p.left.thetaSquareCore : ZMod 7) /
        (p.left.thetaConst : ZMod 7) =
      3 * thetaResidue
        (p.signedDepth.realPairCore p.selectedPairIndex) := by
  rw [p.left_normalizedQuadraticJet_eq,
    p.selectedPairCore_thetaResidue]
  ring

end RamifiedPairedThetaRootJetPacket

end

end DkMath.FLT.Seven
