/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Three.EisensteinCubeExtraction
import DkMath.FLT.Five.GoldenEuclidean
import DkMath.FLT.Seven.QuadraticCoprimeFactor

#print "file: DkMathTest.FLT.Prime.IdealPowerFiniteInstantiationAudit"

/-!
This file records only instances that synthesize in the pinned checkout.
The missing TraceOneInt `1`, `-3`, and `3` arithmetic is intentionally not
represented by placeholder instances.
-/

open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.FLT.Five

#synth IsDomain (TraceOneInt (-1))
#synth EuclideanDomain (TraceOneInt (-1))
#synth GCDMonoid (TraceOneInt (-1))
#synth IsPrincipalIdealRing (TraceOneInt (-1))
#synth IsDedekindDomain (TraceOneInt (-1))

#synth IsDomain DkMath.FLT.Five.GoldenInt
#synth EuclideanDomain DkMath.FLT.Five.GoldenInt
#synth IsPrincipalIdealRing DkMath.FLT.Five.GoldenInt
#synth IsDedekindDomain DkMath.FLT.Five.GoldenInt

#synth IsDomain (TraceOneInt (-2))
#synth EuclideanDomain (TraceOneInt (-2))
#synth GCDMonoid (TraceOneInt (-2))
#synth IsPrincipalIdealRing (TraceOneInt (-2))
#synth IsDedekindDomain (TraceOneInt (-2))
