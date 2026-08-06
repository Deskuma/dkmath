/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameMirrorInvolutionAsymptoticAudit
import Mathlib.Tactic

namespace DkMathTest.RH

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

example (s : ℂ) (k : ℕ) :
    etaPairBaseRotation (criticalMirror s) k =
      etaPairBaseRotation s k := by
  exact etaPairBaseRotation_criticalMirror s k

example (s : ℂ) (k : ℕ) :
    etaCriticalMirrorDefectPairTerm (criticalMirror s) k =
      -etaCriticalMirrorDefectPairTerm s k := by
  exact etaCriticalMirrorDefectPairTerm_criticalMirror_eq_neg s k

example (K : ℕ) (s : ℂ) :
    etaCriticalMirrorDefectPairTail K (criticalMirror s) =
      -etaCriticalMirrorDefectPairTail K s := by
  exact etaCriticalMirrorDefectPairTail_criticalMirror_eq_neg K s

example (a : ℝ) (s : ℂ) (k : ℕ) :
    etaCriticalMirrorIndexNormalizedEvenDefectEndpoint a (criticalMirror s) k =
      -etaCriticalMirrorIndexNormalizedEvenDefectEndpoint a s k := by
  exact
    etaCriticalMirrorIndexNormalizedEvenDefectEndpoint_criticalMirror_eq_neg
      a s k

example (a : ℝ) (s : ℂ) (k : ℕ) :
    etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint
        a (criticalMirror s) k =
      -etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint a s k := by
  exact
    etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint_criticalMirror_eq_neg
      a s k

example {a : ℝ} {s C : ℂ}
    (hendpoint :
      Tendsto
        (etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint a s)
        atTop (nhds C)) :
    Tendsto
      (etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint
        a (criticalMirror s))
      atTop (nhds (-C)) := by
  exact
    etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint_criticalMirror_tendsto_neg
      hendpoint

example {a : ℝ} {s C : ℂ}
    (hendpoint :
      Tendsto
        (etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint a s)
        atTop (nhds C)) :
    EtaCriticalMirrorEndpointMirrorAsymptoticCompatibilityCertificate
      a s C := by
  exact
    etaCriticalMirrorEndpointMirrorAsymptoticCompatibilityCertificate_of_limit
      hendpoint

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    EtaCriticalMirrorEndpointMirrorAsymptoticCompatibilityCertificate
      (criticalMirror s).re s
      (-etaPairIndexNormalizedTailConstant (criticalMirror s)) := by
  exact
    etaCriticalMirrorRightEndpointMirrorAsymptoticCompatibilityCertificate_of_zero
      hs him hre

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    EtaCriticalMirrorEndpointMirrorAsymptoticCompatibilityCertificate
      s.re s (etaPairIndexNormalizedTailConstant s) := by
  exact
    etaCriticalMirrorLeftEndpointMirrorAsymptoticCompatibilityCertificate_of_zero
      hs him hre

end DkMathTest.RH
