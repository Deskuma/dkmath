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
import DkMath.NumberTheory.PrimitiveSet.DivisorPathList
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
import DkMath.NumberTheory.PrimitiveSet.ValuationBudget
import DkMath.NumberTheory.PrimitiveSet.RealDivisorBridge
import DkMath.NumberTheory.PrimitiveSet.LogCapacityKernel
import DkMath.NumberTheory.PrimitiveSet.VonMangoldtShadow
import DkMath.NumberTheory.PrimitiveSet.SubMarkovShadow
import DkMath.NumberTheory.PrimitiveSet.MarkovShadow
import DkMath.NumberTheory.PrimitiveSet.ShadowHittingBridge
import DkMath.NumberTheory.PrimitiveSet.CapacityKernelHittingBridge
import DkMath.NumberTheory.PrimitiveSet.FullChannelSet
import DkMath.NumberTheory.PrimitiveSet.GlobalLogCapacityKernel
import DkMath.NumberTheory.PrimitiveSet.FullChannelEquality
import DkMath.NumberTheory.PrimitiveSet.FullExponentSlot
import DkMath.NumberTheory.PrimitiveSet.FullChannelLogSum
import DkMath.NumberTheory.PrimitiveSet.FullExponentSlotBridge
import DkMath.NumberTheory.PrimitiveSet.FullExponentSlotCanonical
import DkMath.NumberTheory.PrimitiveSet.FullExponentSlotIndexBridge
import DkMath.NumberTheory.PrimitiveSet.KernelCandidateInventory
import DkMath.NumberTheory.PrimitiveSet.LogCapacityHittingBridge

#print "file: DkMath.NumberTheory.PrimitiveSet"

/-!
Public-facing aggregator for the finite primitive-set hitting layer.

This module exposes:

- `PrimitiveOn`
- finite positive and lower-bound support predicates
- finite divisibility/descent-chain hitting lemmas
- finite chain-family hitting bounds
- source-controlled forest bridge and concrete singleton/divisor-step constructors
- divisibility-controlled descent provider
- prime-step descent provider
- multi-step prime reachability provider
- list-shaped prime path to divisibility-chain provider
- list-shaped divisor path to divisibility-chain provider
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
- real-valued weight provider and weighted path-family bridge
- real/log route positivity lemmas
- valuation-budget vocabulary for repeated base primes
- bridge from prime-power divisor witnesses to real/log sub-probability,
  including the repeated-base valuation-budget route
- local log-capacity kernel whose normalized shadow is the R/log
  sub-probability theorem
- finite real-log von-Mangoldt shadow for prime-power witnesses
- sub-Markov shadow naming layer for state-indexed real providers
- Markov shadow naming layer for state-indexed real providers with total
  outgoing weight exactly one
- bridge from real Markov/sub-Markov shadows to primitive hitting bounds
- bridge from positive capacity kernels to primitive hitting bounds through
  normalized sub-Markov shadows
- full prime-power channel-set interface for the equality route
- global log-capacity kernel over source states `n > 1`
- full-channel log-cost completeness interface and Markov-shadow bridge
- full exponent-slot coverage interface for the equality route
- finite log-sum bridge from full exponent-slot coverage to full-channel
  log-cost completeness
- bridge from full exponent-slot channel extensionality to Markov shadow
- canonical exponent-slot kernel and Markov shadow
- bridge from arbitrary kernels with canonical exponent-slot index to Markov shadow
- code-level inventory for current kernel candidates
- bridge from log-capacity shadows to primitive hitting bounds
-/
