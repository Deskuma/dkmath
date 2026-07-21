/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Hackathon.JacobianCounterexample3.Normalized
import DkMath.Verification.Collision

namespace DkMath.Hackathon.JacobianCounterexample3

noncomputable section

/-- The first two normalized collision points as a generic collision certificate. -/
def normalizedCollisionCertificateC :
    DkMath.Verification.CollisionCertificate
      evalNormalizedCounterexampleC where
  left := p0C
  right := p1C
  left_ne_right := p0C_ne_p1C
  map_eq := by
    calc
      evalNormalizedCounterexampleC p0C = normalizedTargetC := normalized_eval_p0C
      _ = evalNormalizedCounterexampleC p1C := normalized_eval_p1C.symm

/-- Generic collision reasoning recovers normalized noninjectivity. -/
theorem normalizedCollisionCertificateC_notInjective :
    ¬ Function.Injective evalNormalizedCounterexampleC :=
  normalizedCollisionCertificateC.notInjective

/-- Generic collision reasoning rules out a left inverse for the normalized map. -/
theorem normalizedCollisionCertificateC_noLeftInverse :
    ¬ ∃ G : Point3C → Point3C,
      Function.LeftInverse G evalNormalizedCounterexampleC :=
  normalizedCollisionCertificateC.noLeftInverse

end

end DkMath.Hackathon.JacobianCounterexample3

#print "file: DkMath.Hackathon.JacobianCounterexample3.VerificationBridge"
