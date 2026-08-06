/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedEvenDefectEndpointAsymptotic
import Mathlib.Tactic

namespace DkMathTest.RH

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

example {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    (a : ℝ) (k : ℕ) :
    etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint a s k =
      -etaCriticalMirrorIndexNormalizedRotatedDefectTail a s k := by
  exact
    etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint_eq_neg_rotatedDefectTail
      hs him a k

example (a : ℝ) (s : ℂ) (k : ℕ) :
    ‖etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint a s k‖ =
      ‖etaCriticalMirrorIndexNormalizedEvenDefectEndpoint a s k‖ := by
  exact
    norm_etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint a s k

example {a : ℝ} {s C : ℂ}
    (cert :
      EtaCriticalMirrorNormalizedEvenDefectEndpointAsymptoticCertificate
        a s C) :
    ¬ EtaCriticalMirrorIndexNormalizedEvenDefectEndpointRateCollapse a s := by
  exact
    not_etaCriticalMirrorIndexNormalizedEvenDefectEndpointRateCollapse_of_asymptoticCertificate
      cert

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    EtaCriticalMirrorNormalizedEvenDefectEndpointAsymptoticCertificate
      (criticalMirror s).re s
      (etaPairIndexNormalizedTailConstant (criticalMirror s)) := by
  exact
    etaCriticalMirrorRightNormalizedEvenDefectEndpointAsymptoticCertificate_of_zero
      hs him hre

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    EtaCriticalMirrorNormalizedEvenDefectEndpointAsymptoticCertificate
      s.re s (-etaPairIndexNormalizedTailConstant s) := by
  exact
    etaCriticalMirrorLeftNormalizedEvenDefectEndpointAsymptoticCertificate_of_zero
      hs him hre

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ¬ EtaCriticalMirrorIndexNormalizedEvenDefectEndpointRateCollapse
        (criticalMirror s).re s := by
  exact
    not_etaCriticalMirrorRightIndexNormalizedEvenDefectEndpointRateCollapse
      hs him hre

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ¬ EtaCriticalMirrorIndexNormalizedEvenDefectEndpointRateCollapse s.re s := by
  exact
    not_etaCriticalMirrorLeftIndexNormalizedEvenDefectEndpointRateCollapse
      hs him hre

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re ≠ (1 : ℝ) / 2) :
    EtaCriticalMirrorOffCriticalDominantEndpointAsymptoticCertificate s := by
  exact
    etaCriticalMirrorOffCriticalDominantEndpointAsymptoticCertificate_of_zero
      hs him hre

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re ≠ (1 : ℝ) / 2) :
    ¬ EtaCriticalMirrorZeroLocusDominantEndpointRateCollapse s := by
  exact
    not_etaCriticalMirrorZeroLocusDominantEndpointRateCollapse_of_offCriticalZero
      hs him hre

end DkMathTest.RH
