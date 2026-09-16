/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRealCubicAxisDrop

#print "file: DkMath.FLT.Seven.SevenRamifiedSignedRootDepth"

namespace DkMath.FLT.Seven

noncomputable section

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- The homogeneous seventh quotient over the signed integers. -/
def signedSeventhQuotient (r l : ℤ) : ℤ :=
  r ^ 6 + r ^ 5 * l + r ^ 4 * l ^ 2 + r ^ 3 * l ^ 3 +
    r ^ 2 * l ^ 4 + r * l ^ 5 + l ^ 6

theorem signed_pow_seven_sub_factorization (r l : ℤ) :
    r ^ 7 - l ^ 7 =
      (r - l) * signedSeventhQuotient r l := by
  simp [signedSeventhQuotient]
  ring

/-- The first variation of the signed quotient at `r=l`. -/
def signedSeventhQuotientFirstVariation (r l : ℤ) : ℤ :=
  r ^ 5 + 2 * r ^ 4 * l + 3 * r ^ 3 * l ^ 2 +
    4 * r ^ 2 * l ^ 3 + 5 * r * l ^ 4 + 6 * l ^ 5

theorem signedSeventhQuotient_sub_seven_mul_pow_six (r l : ℤ) :
    signedSeventhQuotient r l - 7 * l ^ 6 =
      (r - l) * signedSeventhQuotientFirstVariation r l := by
  simp [signedSeventhQuotient, signedSeventhQuotientFirstVariation]
  ring

theorem firstVariation_sub_twentyOne_mul_pow_five (r l : ℤ) :
    signedSeventhQuotientFirstVariation r l - 21 * l ^ 5 =
      (r - l) *
        (r ^ 4 + 3 * r ^ 3 * l + 6 * r ^ 2 * l ^ 2 +
          10 * r * l ^ 3 + 15 * l ^ 4) := by
  simp [signedSeventhQuotientFirstVariation]
  ring

/-- Integer side of FUSION-001, attached to the completed balanced
real-cubic axis split.  The exact depths are recorded division-free. -/
structure RamifiedSignedRootDepthPacket : Type where
  balanced : RamifiedRealCubicBalancedAxisSplitPacket
  signedLeftRoot : ℤ
  signedRightRoot : ℤ
  signedLeftRoot_eq :
    signedLeftRoot =
      balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.leftRoot
  signedRightRoot_eq :
    signedRightRoot =
      balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.rightRoot
  signedRoots_isCoprime :
    IsCoprime signedLeftRoot signedRightRoot
  gapRoot : ℤ
  quotientRoot : ℤ
  signedGap_eq :
    signedRightRoot - signedLeftRoot = 7 ^ 4 * gapRoot
  signedQuotient_eq :
    signedSeventhQuotient signedRightRoot signedLeftRoot =
      7 * quotientRoot
  gapRoot_not_seven_dvd :
    ¬(7 : ℤ) ∣ gapRoot
  quotientRoot_not_seven_dvd :
    ¬(7 : ℤ) ∣ quotientRoot
  normalizedEquation :
    gapRoot * quotientRoot =
      balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.quadratic.innerRoot.fst *
        (balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.quadratic.innerRoot.fst +
          balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.quadratic.innerRoot.snd) *
        balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.innerSndRoot ^ 7

namespace RamifiedRealCubicNormPacket

theorem signedRoots_isCoprime
    (p : RamifiedRealCubicNormPacket) :
    IsCoprime p.leftRoot p.rightRoot := by
  apply
    (IsCoprime.pow_iff (m := 7) (n := 7)
      (by norm_num) (by norm_num)).mp
  rw [← p.leftCubic_eq, ← p.rightCubic_eq]
  apply Int.isCoprime_iff_nat_coprime.mpr
  exact sndCore_cubic_factors_coprime
    p.quadratic.innerRoot
    p.quadratic.innerRoot_coordinates_isCoprime
    p.quadratic.innerRoot_norm_not_seven_dvd

theorem signedLeftRoot_not_seven_dvd
    (p : RamifiedRealCubicNormPacket) :
    ¬(7 : ℤ) ∣ p.leftRoot := by
  intro hleft
  have hcubic :
      (7 : ℤ) ∣ seventhPowerSndLeftCubic
        p.quadratic.innerRoot.fst p.quadratic.innerRoot.snd := by
    rw [p.leftCubic_eq]
    exact dvd_pow hleft (by norm_num)
  have hsnd : (7 : ℤ) ∣ p.quadratic.innerRoot.snd :=
    p.innerSnd_seven_dvd
  have hfst : ¬(7 : ℤ) ∣ p.quadratic.innerRoot.fst := by
    intro ha
    have hunit :=
      p.quadratic.innerRoot_coordinates_isCoprime.isUnit_of_dvd'
        ha hsnd
    rcases Int.isUnit_iff.mp hunit with h | h
    · norm_num at h
    · norm_num at h
  apply hfst
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp
  have hcubic0 :
      (seventhPowerSndLeftCubic
          p.quadratic.innerRoot.fst
          p.quadratic.innerRoot.snd : ZMod 7) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr hcubic
  have hsnd0 :
      (p.quadratic.innerRoot.snd : ZMod 7) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr hsnd
  simp only [seventhPowerSndLeftCubic, Int.reduceNeg, Int.cast_add, Int.cast_sub, Int.cast_pow,
    Int.cast_mul, Int.cast_ofNat, hsnd0, mul_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, add_zero, pow_eq_zero_iff] at hcubic0
  exact hcubic0

theorem seven_dvd_signedRootGap
    (p : RamifiedRealCubicNormPacket) :
    (7 : ℤ) ∣ p.rightRoot - p.leftRoot := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp
  have h := congrArg (fun z : ℤ => (z : ZMod 7))
    p.signedRootGap_seventhPower_eq
  push_cast at h
  have hseven : (7 : ZMod 7) = 0 := by decide
  rw [hseven] at h
  simpa [ZMod.pow_card] using h

theorem exists_signedQuotientRoot_exact
    (p : RamifiedRealCubicNormPacket) :
    ∃ e : ℤ,
      signedSeventhQuotient p.rightRoot p.leftRoot = 7 * e ∧
      ¬(7 : ℤ) ∣ e := by
  rcases p.seven_dvd_signedRootGap with ⟨k, hk⟩
  have hfirst7 :
      (7 : ℤ) ∣
        signedSeventhQuotientFirstVariation
          p.rightRoot p.leftRoot := by
    refine ⟨3 * p.leftRoot ^ 5 +
        k * (p.rightRoot ^ 4 +
          3 * p.rightRoot ^ 3 * p.leftRoot +
          6 * p.rightRoot ^ 2 * p.leftRoot ^ 2 +
          10 * p.rightRoot * p.leftRoot ^ 3 +
          15 * p.leftRoot ^ 4), ?_⟩
    calc
      signedSeventhQuotientFirstVariation
          p.rightRoot p.leftRoot =
          21 * p.leftRoot ^ 5 +
            (p.rightRoot - p.leftRoot) *
              (p.rightRoot ^ 4 +
                3 * p.rightRoot ^ 3 * p.leftRoot +
                6 * p.rightRoot ^ 2 * p.leftRoot ^ 2 +
                10 * p.rightRoot * p.leftRoot ^ 3 +
                15 * p.leftRoot ^ 4) := by
        rw [← firstVariation_sub_twentyOne_mul_pow_five]
        ring
      _ = _ := by rw [hk]; ring
  rcases hfirst7 with ⟨f, hf⟩
  let e := p.leftRoot ^ 6 + 7 * k * f
  have he :
      signedSeventhQuotient p.rightRoot p.leftRoot = 7 * e := by
    rw [show signedSeventhQuotient p.rightRoot p.leftRoot =
        7 * p.leftRoot ^ 6 +
          (p.rightRoot - p.leftRoot) *
            signedSeventhQuotientFirstVariation
              p.rightRoot p.leftRoot by
      rw [← signedSeventhQuotient_sub_seven_mul_pow_six]
      ring]
    rw [hk, hf]
    simp [e]
    ring
  refine ⟨e, he, ?_⟩
  intro he7
  apply p.signedLeftRoot_not_seven_dvd
  have hlpow : (7 : ℤ) ∣ p.leftRoot ^ 6 := by
    dsimp [e] at he7
    have hterm : (7 : ℤ) ∣ 7 * k * f :=
      ⟨k * f, by ring⟩
    simpa using dvd_sub he7 hterm
  exact (by norm_num : Prime (7 : ℤ)).dvd_of_dvd_pow hlpow

theorem innerFst_not_seven_dvd
    (p : RamifiedRealCubicNormPacket) :
    ¬(7 : ℤ) ∣ p.quadratic.innerRoot.fst := by
  intro ha
  have hunit :=
    p.quadratic.innerRoot_coordinates_isCoprime.isUnit_of_dvd'
      ha p.innerSnd_seven_dvd
  rcases Int.isUnit_iff.mp hunit with h | h
  · norm_num at h
  · norm_num at h

theorem innerFst_add_innerSnd_not_seven_dvd
    (p : RamifiedRealCubicNormPacket) :
    ¬(7 : ℤ) ∣
      p.quadratic.innerRoot.fst +
        p.quadratic.innerRoot.snd := by
  intro hsum
  apply p.innerFst_not_seven_dvd
  simpa using dvd_sub hsum p.innerSnd_seven_dvd

end RamifiedRealCubicNormPacket

namespace RamifiedRealCubicBalancedAxisSplitPacket

theorem nonempty_signedRootDepth
    (balanced : RamifiedRealCubicBalancedAxisSplitPacket) :
    Nonempty RamifiedSignedRootDepthPacket := by
  let p :=
    balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket
  rcases p.exists_signedQuotientRoot_exact with ⟨e, he, he7⟩
  rcases p.seven_dvd_signedRootGap with ⟨k, hk⟩
  have hpower :
      (7 ^ 5 : ℤ) *
          (p.quadratic.innerRoot.fst *
            (p.quadratic.innerRoot.fst +
              p.quadratic.innerRoot.snd) *
            p.innerSndRoot ^ 7) =
        (7 ^ 2 : ℤ) * k * e := by
    calc
      _ = 7 * p.quadratic.innerRoot.fst *
          p.quadratic.innerRoot.snd *
          (p.quadratic.innerRoot.fst +
            p.quadratic.innerRoot.snd) := by
        rw [p.innerSnd_eq]
        ring
      _ = p.rightRoot ^ 7 - p.leftRoot ^ 7 :=
        p.signedRootGap_seventhPower_eq.symm
      _ = (p.rightRoot - p.leftRoot) *
          signedSeventhQuotient p.rightRoot p.leftRoot :=
        signed_pow_seven_sub_factorization _ _
      _ = 7 ^ 2 * k * e := by rw [hk, he]; ring
  have hke :
      (7 ^ 3 : ℤ) ∣ k * e := by
    refine ⟨p.quadratic.innerRoot.fst *
        (p.quadratic.innerRoot.fst +
          p.quadratic.innerRoot.snd) *
        p.innerSndRoot ^ 7, ?_⟩
    apply mul_left_cancel₀ (by norm_num : (49 : ℤ) ≠ 0)
    calc
      49 * (k * e) =
          7 ^ 2 * k * e := by ring
      _ = 7 ^ 5 *
          (p.quadratic.innerRoot.fst *
            (p.quadratic.innerRoot.fst +
              p.quadratic.innerRoot.snd) *
            p.innerSndRoot ^ 7) := hpower.symm
      _ = 49 * (7 ^ 3 *
          (p.quadratic.innerRoot.fst *
            (p.quadratic.innerRoot.fst +
              p.quadratic.innerRoot.snd) *
            p.innerSndRoot ^ 7)) := by ring
  have hcop : IsCoprime (7 ^ 3 : ℤ) e :=
    (show IsCoprime (7 : ℤ) e from
      (show Prime (7 : ℤ) by norm_num).coprime_iff_not_dvd.mpr he7).pow_left
  have hk4 : (7 ^ 3 : ℤ) ∣ k :=
    hcop.dvd_of_dvd_mul_right hke
  rcases hk4 with ⟨d, hd⟩
  have hnormalized :
      d * e =
        p.quadratic.innerRoot.fst *
          (p.quadratic.innerRoot.fst +
            p.quadratic.innerRoot.snd) *
          p.innerSndRoot ^ 7 := by
    rw [hd] at hpower
    apply mul_left_cancel₀ (by norm_num : (16807 : ℤ) ≠ 0)
    calc
      16807 * (d * e) =
          7 ^ 2 * (7 ^ 3 * d) * e := by ring
      _ = 7 ^ 5 *
          (p.quadratic.innerRoot.fst *
            (p.quadratic.innerRoot.fst +
              p.quadratic.innerRoot.snd) *
            p.innerSndRoot ^ 7) := hpower.symm
      _ = 16807 *
          (p.quadratic.innerRoot.fst *
            (p.quadratic.innerRoot.fst +
              p.quadratic.innerRoot.snd) *
            p.innerSndRoot ^ 7) := by ring
  have hd7 : ¬(7 : ℤ) ∣ d := by
    intro hdvd
    have hrhs : (7 : ℤ) ∣
        p.quadratic.innerRoot.fst *
          (p.quadratic.innerRoot.fst +
            p.quadratic.innerRoot.snd) *
          p.innerSndRoot ^ 7 := by
      rw [← hnormalized]
      exact dvd_mul_of_dvd_left hdvd e
    rcases (show Prime (7 : ℤ) by norm_num).dvd_mul.mp hrhs with h | hm
    · rcases (show Prime (7 : ℤ) by norm_num).dvd_mul.mp h with ha | han
      · exact p.innerFst_not_seven_dvd ha
      · exact p.innerFst_add_innerSnd_not_seven_dvd han
    · exact p.innerSndRoot_not_seven_dvd
        ((show Prime (7 : ℤ) by norm_num).dvd_of_dvd_pow hm)
  exact ⟨{
    balanced := balanced
    signedLeftRoot := p.leftRoot
    signedRightRoot := p.rightRoot
    signedLeftRoot_eq := rfl
    signedRightRoot_eq := rfl
    signedRoots_isCoprime := p.signedRoots_isCoprime
    gapRoot := d
    quotientRoot := e
    signedGap_eq := by rw [hk, hd]; ring
    signedQuotient_eq := he
    gapRoot_not_seven_dvd := hd7
    quotientRoot_not_seven_dvd := he7
    normalizedEquation := hnormalized }⟩

end RamifiedRealCubicBalancedAxisSplitPacket

namespace RamifiedSignedRootDepthPacket

/-- The two axis-free signed integer factors are coprime.  A common prime
would divide `7*l^6`; the seven branch contradicts exact gap depth, and the
`l` branch contradicts coprimality of the signed roots. -/
theorem gapRoot_isCoprime_quotientRoot
    (p : RamifiedSignedRootDepthPacket) :
    IsCoprime p.gapRoot p.quotientRoot := by
  apply isCoprime_of_prime_dvd
  · rintro ⟨hgap, _⟩
    apply p.gapRoot_not_seven_dvd
    simp [hgap]
  · intro q hq hqgap hqquotient
    have hqSignedGap :
        q ∣ p.signedRightRoot - p.signedLeftRoot := by
      rw [p.signedGap_eq]
      exact dvd_mul_of_dvd_right hqgap _
    have hqSignedQuotient :
        q ∣ signedSeventhQuotient
          p.signedRightRoot p.signedLeftRoot := by
      rw [p.signedQuotient_eq]
      exact dvd_mul_of_dvd_right hqquotient _
    have hqRemainder :
        q ∣ signedSeventhQuotient
            p.signedRightRoot p.signedLeftRoot -
          7 * p.signedLeftRoot ^ 6 := by
      rw [signedSeventhQuotient_sub_seven_mul_pow_six]
      exact dvd_mul_of_dvd_left hqSignedGap _
    have hqSevenMul :
        q ∣ 7 * p.signedLeftRoot ^ 6 := by
      simpa using dvd_sub hqSignedQuotient hqRemainder
    rcases hq.dvd_mul.mp hqSevenMul with hqSeven | hqLeftPow
    · have hassoc :
          Associated q (7 : ℤ) :=
        hq.associated_of_dvd (by norm_num) hqSeven
      exact p.gapRoot_not_seven_dvd
        (hassoc.dvd_iff_dvd_left.mp hqgap)
    · have hqLeft : q ∣ p.signedLeftRoot :=
        hq.dvd_of_dvd_pow hqLeftPow
      have hqRight : q ∣ p.signedRightRoot := by
        have := dvd_add hqSignedGap hqLeft
        simpa using this
      exact hq.not_isUnit
        (p.signedRoots_isCoprime.isUnit_of_dvd'
          hqLeft hqRight)

end RamifiedSignedRootDepthPacket


end

end DkMath.FLT.Seven
