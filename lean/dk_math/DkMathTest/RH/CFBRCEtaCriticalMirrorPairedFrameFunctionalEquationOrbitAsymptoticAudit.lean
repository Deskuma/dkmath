import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameFunctionalEquationOrbitAsymptoticAudit
import Mathlib.Tactic

namespace DkMathTest.RH

open Filter
open ComplexConjugate
open scoped Topology
open DkMath.RH.CFBRCProjection

example (s : ℂ) :
    1 - s = conj (criticalMirror s) := by
  exact one_sub_eq_conj_criticalMirror s

example {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    NontrivialRiemannZetaZero (1 - s) := by
  exact nontrivialRiemannZetaZero_one_sub hs

example (a : ℝ) (s : ℂ) (k : ℕ) :
    etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint
        a (1 - s) k =
      -conj
        (etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint a s k) := by
  exact
    etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint_one_sub_eq_neg_conj
      a s k

example {a : ℝ} {s C : ℂ}
    (hendpoint :
      Tendsto
        (etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint a s)
        atTop (nhds C)) :
    Tendsto
      (etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint
        a (1 - s))
      atTop (nhds (-conj C)) := by
  exact
    etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint_one_sub_tendsto_neg_conj
      hendpoint

example {s : ℂ}
    (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0)
    (hre : (1 : ℝ) / 2 < s.re) :
    EtaCriticalMirrorEndpointFunctionalEquationOrbitAsymptoticCertificate
      (criticalMirror s).re s
      (-etaPairIndexNormalizedTailConstant (criticalMirror s)) := by
  exact
    etaCriticalMirrorRightEndpointFunctionalEquationOrbitAsymptoticCertificate_of_zero
      hs him hre

example {s : ℂ}
    (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0)
    (hre : s.re < (1 : ℝ) / 2) :
    EtaCriticalMirrorEndpointFunctionalEquationOrbitAsymptoticCertificate
      s.re s (etaPairIndexNormalizedTailConstant s) := by
  exact
    etaCriticalMirrorLeftEndpointFunctionalEquationOrbitAsymptoticCertificate_of_zero
      hs him hre

end DkMathTest.RH
