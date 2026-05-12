/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.Basic
import DkMath.NumberTheory.PrimitiveSet.Support
import DkMath.NumberTheory.PrimitiveSet.HittingBridge
import DkMath.NumberTheory.PrimitiveSet.BranchBridge
import DkMath.NumberTheory.PrimitiveSet.DescentBridge
import DkMath.NumberTheory.PrimitiveSet.PrimeDescent
import DkMath.NumberTheory.PrimitiveSet.PrimePath
import DkMath.NumberTheory.PrimitiveSet.PrimePathList
import DkMath.NumberTheory.PrimitiveSet.PathFamily
import DkMath.NumberTheory.PrimitiveSet.SubConservativeBridge
import DkMath.NumberTheory.PrimitiveSet.BranchPathFamily
import DkMath.NumberTheory.PrimitiveSet.ErdosFinite
import DkMath.NumberTheory.PrimitiveSet.WeightedPathFamily
import DkMath.NumberTheory.PrimitiveSet.WeightProvider
import DkMath.NumberTheory.PrimitiveSet.FiniteKernel
import DkMath.NumberTheory.PrimitiveSet.FiniteTransitionKernel
import DkMath.NumberTheory.PrimitiveSet.DivisorTransitionKernel
import DkMath.NumberTheory.PrimitiveSet.RealWeight
import DkMath.NumberTheory.PrimitiveSet.RealWeightedPath
import DkMath.NumberTheory.PrimitiveSet.RealLog
import DkMath.NumberTheory.PrimitiveSet.RealDivisorBridge

#print "file: DkMath.NumberTheory.PrimitiveSet"

/-!
Public-facing aggregator for the finite primitive-set hitting layer.

This module exposes:

- `PrimitiveOn`
- finite positive and lower-bound support predicates
- finite divisibility/descent-chain hitting lemmas
- finite chain-family hitting bounds
- source-controlled forest bridge
- divisibility-controlled descent provider
- prime-step descent provider
- multi-step prime reachability provider
- list-shaped prime path to divisibility-chain provider
- finite family of list-shaped prime paths
- subconservative branch bridge
- finite family of branch-controlled prime paths
- theorem-facing finite Erdos primitive input
- finite weighted path-family skeleton
- finite weight provider skeleton
- finite kernel skeleton
- finite transition kernel skeleton
- divisor transition kernel skeleton
- real-valued toy weight skeleton
- real-valued weight provider skeleton
- real/log route positivity lemmas
- bridge from prime-power divisor witnesses to real/log product-budget interface
-/
