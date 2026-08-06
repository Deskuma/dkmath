import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameConjugationAsymptoticAudit
import Mathlib.Tactic

namespace DkMathTest.RH

open Filter
open ComplexConjugate
open scoped Topology
open DkMath.RH.CFBRCProjection

example {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    NontrivialRiemannZetaZero (conj s) := by
  exact nontrivialRiemannZetaZero_conj hs

example (s : ℂ) :
    criticalMirror (conj s) = conj (criticalMirror s) := by
  exact criticalMirror_conj s

example (s : ℂ) (k : ℕ) :
    etaPairBaseRotation (conj s) k =
      conj (etaPairBaseRotation s k) := by
  exact etaPairBaseRotation_conj s k

example (a : ℝ) (s : ℂ) (k : ℕ) :
    etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint
        a (conj s) k =
      conj
        (etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint a s k) := by
  exact
    etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint_conj
      a s k

example {a : ℝ} {s C : ℂ}
    (hendpoint :
      Tendsto
        (etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint a s)
        atTop (nhds C)) :
    EtaCriticalMirrorEndpointConjugationAsymptoticCompatibilityCertificate
      a s C := by
  exact
    etaCriticalMirrorEndpointConjugationAsymptoticCompatibilityCertificate_of_limit
      hendpoint

example {s : ℂ}
    (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0)
    (hre : (1 : ℝ) / 2 < s.re) :
    EtaCriticalMirrorEndpointConjugationAsymptoticCompatibilityCertificate
      (criticalMirror s).re s
      (-etaPairIndexNormalizedTailConstant (criticalMirror s)) := by
  exact
    etaCriticalMirrorRightEndpointConjugationAsymptoticCompatibilityCertificate_of_zero
      hs him hre

example {s : ℂ}
    (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0)
    (hre : s.re < (1 : ℝ) / 2) :
    EtaCriticalMirrorEndpointConjugationAsymptoticCompatibilityCertificate
      s.re s (etaPairIndexNormalizedTailConstant s) := by
  exact
    etaCriticalMirrorLeftEndpointConjugationAsymptoticCompatibilityCertificate_of_zero
      hs him hre

end DkMathTest.RH
