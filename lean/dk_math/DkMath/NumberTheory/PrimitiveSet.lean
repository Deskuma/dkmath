/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.Basic
import DkMath.NumberTheory.PrimitiveSet.HittingBridge
import DkMath.NumberTheory.PrimitiveSet.BranchBridge
import DkMath.NumberTheory.PrimitiveSet.DescentBridge

#print "file: DkMath.NumberTheory.PrimitiveSet"

/-!
Public-facing aggregator for the finite primitive-set hitting layer.

This module exposes:

- `PrimitiveOn`
- finite divisibility/descent-chain hitting lemmas
- finite chain-family hitting bounds
- source-controlled forest bridge
- divisibility-controlled descent provider
-/
