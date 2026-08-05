import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaFirstOrderOrbitAudit
import Mathlib.Tactic

namespace DkMathTest.RH

open DkMath.RH.CFBRCProjection

example {s : ℂ}
    (hs : NontrivialRiemannZetaZero s) :
    deriv completedRiemannZeta (1 - s) =
      -deriv completedRiemannZeta s := by
  exact
    completedRiemannZeta_deriv_one_sub_eq_neg_of_nontrivialRiemannZetaZero hs

example {s : ℂ}
    (hs : NontrivialRiemannZetaZero s) :
    completedZetaFunctionalReflectionTransportedDerivative s =
      deriv completedRiemannZeta s := by
  exact completedZetaFunctionalReflectionTransportedDerivative_eq hs

example {s : ℂ}
    (hs : NontrivialRiemannZetaZero s) :
    ‖deriv completedRiemannZeta (1 - s)‖ =
      ‖deriv completedRiemannZeta s‖ := by
  exact norm_completedRiemannZeta_deriv_one_sub_eq hs

example {s : ℂ}
    (hs : NontrivialRiemannZetaZero s) :
    CompletedRiemannZetaSimpleZeroAt (1 - s) ↔
      CompletedRiemannZetaSimpleZeroAt s := by
  exact completedRiemannZetaSimpleZeroAt_one_sub_iff hs

example {s : ℂ}
    (hs : NontrivialRiemannZetaZero s) :
    EtaCriticalMirrorCompletedZetaFirstOrderOrbitCompatibilityCertificate s := by
  exact
    etaCriticalMirrorCompletedZetaFirstOrderOrbitCompatibilityCertificate_of_zero hs

end DkMathTest.RH
