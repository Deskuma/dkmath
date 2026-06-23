/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.Basic
import DkMath.Analysis.CosmicResidual
import DkMath.Analysis.GapGN
import DkMath.Analysis.ErrorKernel
import DkMath.Analysis.GapFill
import DkMath.Analysis.RealBridge
import DkMath.Analysis.TaylorBridge
import DkMath.Analysis.DkReal
import DkMath.Analysis.DkReal.SemanticCF2D
import DkMath.Analysis.DkReal.SemanticCF2DPhase
import DkMath.Analysis.DkReal.SemanticCF2DDyadic
import DkMath.Analysis.DkReal.SemanticCF2DPath
import DkMath.Analysis.DkReal.SemanticCF2DNormalize
import DkMath.CosmicFormula.Rotation.CF2D.EuclideanPhase

#print "file: DkMath.Analysis"

/-!
# DkMath analysis

Public entry point for the DkMath interpretation of exact gaps, residuals,
correction kernels, interval fills, and future computable real structures.

Mathlib remains the standard analytic foundation. This layer exposes a
different decomposition and supplies explicit bridges to that foundation.
-/
