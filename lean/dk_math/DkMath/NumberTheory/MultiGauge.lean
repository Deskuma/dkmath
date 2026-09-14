/-
Copyright (c) 2026 DkMath contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: DkMath contributors.
-/

import DkMath.NumberTheory.MultiGauge.Basic
import DkMath.NumberTheory.MultiGauge.PrimeTransport
import DkMath.NumberTheory.MultiGauge.Path
import DkMath.NumberTheory.MultiGauge.RawNormalization
import DkMath.NumberTheory.MultiGauge.RawRefinementPath
import DkMath.NumberTheory.MultiGauge.GnomonPetalTransition

#print "file: DkMath.NumberTheory.MultiGauge"

/-! # Generic multi-gauge divisibility facade

This facade exposes the arithmetic multi-gauge kernel, finite paths, raw
normalization/refinement, and the first unconditional primitive-shape provider:
the degree-two gnomon / Petal transition.
-/
