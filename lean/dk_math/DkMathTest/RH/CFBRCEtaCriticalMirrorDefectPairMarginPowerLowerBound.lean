/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorDefectPairMarginPowerLowerBound

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorDefectPairMarginPowerLowerBound"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorDefectPairMarginPowerLowerBound

open DkMath.RH.CFBRCProjection

example (s : ℂ) {x : ℝ} (hx : 0 < x) :
    etaPairRadialDecay s x *
        etaCriticalMirrorContinuousWeightR s x =
      x ^ (s.re - 2) :=
  etaPairRadialDecay_mul_continuousWeightR_eq_rpow s hx

example {s : ℂ} (hs : NontrivialRiemannZetaZero s) (k : ℕ) :
    etaCriticalMirrorRightPairMarginPowerLowerBound s k ≤
      etaCriticalMirrorRightPairMargin s k :=
  etaCriticalMirrorRightPairMarginPowerLowerBound_le_of_nontrivialRiemannZetaZero
    hs k

example {s : ℂ} (hs : NontrivialRiemannZetaZero s) (k : ℕ) :
    etaCriticalMirrorLeftPairMarginPowerLowerBound s k ≤
      etaCriticalMirrorLeftPairMargin s k :=
  etaCriticalMirrorLeftPairMarginPowerLowerBound_le_of_nontrivialRiemannZetaZero
    hs k

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (K N : ℕ) :
    etaCriticalMirrorRightBlockMarginPowerLowerBound s K N ≤
      etaCriticalMirrorRightBlockMarginSum s K N :=
  etaCriticalMirrorRightBlockMarginPowerLowerBound_le hs K N

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (K N : ℕ) :
    etaCriticalMirrorLeftBlockMarginPowerLowerBound s K N ≤
      etaCriticalMirrorLeftBlockMarginSum s K N :=
  etaCriticalMirrorLeftBlockMarginPowerLowerBound_le hs K N

end DkMathTest.RH.CFBRCEtaCriticalMirrorDefectPairMarginPowerLowerBound
