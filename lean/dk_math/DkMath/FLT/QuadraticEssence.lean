/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.ThreeTraceOneBridge
import DkMath.FLT.Five.TraceOneBridge

#print "file: DkMath.FLT.QuadraticEssence"

/-!
# FLT3 / FLT5 quadratic essence

This facade exposes only the two proved coordinate specializations: the cubic
kernel at parameter `-1` and the quintic kernel at parameter `1`.  It asserts no
general-prime FLT theorem and does not alter either existing endpoint proof.
-/
