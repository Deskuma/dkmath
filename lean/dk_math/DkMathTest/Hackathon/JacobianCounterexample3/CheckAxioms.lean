/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Hackathon.JacobianCounterexample3

#print "file: DkMathTest.Hackathon.JacobianCounterexample3.CheckAxioms"

#print axioms DkMath.Hackathon.JacobianCounterexample3.jacobianCounterexampleCertificateQ
#print axioms DkMath.Hackathon.JacobianCounterexample3.jacobianCounterexampleCertificateC
#print axioms DkMath.Hackathon.JacobianCounterexample3.normalizedJacobianCounterexampleCertificateC
#print axioms DkMath.Hackathon.JacobianCounterexample3.jacobianDemoCertificateC
#print axioms DkMath.Hackathon.JacobianCounterexample3.normalizedCollisionCertificateC_notInjective
#print axioms DkMath.Hackathon.JacobianCounterexample3.normalizedCollisionCertificateC_noLeftInverse

example :
    ¬ Function.Injective
      DkMath.Hackathon.JacobianCounterexample3.evalNormalizedCounterexampleC :=
  DkMath.Hackathon.JacobianCounterexample3.normalizedCollisionCertificateC_notInjective

example :
    ¬ ∃ G : DkMath.Hackathon.JacobianCounterexample3.Point3C →
        DkMath.Hackathon.JacobianCounterexample3.Point3C,
      Function.LeftInverse G
        DkMath.Hackathon.JacobianCounterexample3.evalNormalizedCounterexampleC :=
  DkMath.Hackathon.JacobianCounterexample3.normalizedCollisionCertificateC_noLeftInverse
