/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.GlobalLogCapacityKernel
import DkMath.NumberTheory.PrimitiveSet.MarkovShadow

#print "file: DkMath.NumberTheory.PrimitiveSet.FullChannelEquality"

namespace DkMath.NumberTheory.PrimitiveSet

open DkMath.Kernel

/--
The structural assumption needed to turn a full-channel log-capacity shadow
from sub-Markov into Markov.

This interface deliberately records the exact outgoing log-cost equality as an
assumption.  It separates the equality route from the earlier selected-channel
inequality route and leaves the future proof of full prime-power enumeration
outside this thin bridge.
-/
structure FullChannelLogCostComplete
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (C : FullPrimePowerChannelSet T) : Prop where
  outgoing_eq :
    ∀ s : LogCapacityState,
      (C.channels s.1).sum
        (fun q =>
          W.vonMangoldtShadowCost s.1 (C.channels s.1) (C.subset_index s.1) q) =
      Real.log (s.1 : ℝ)

namespace PrimePowerWitnessProvider

/-- Full log-capacity kernels have positive capacity at every state. -/
theorem fullGlobalLogCapacityKernel_capacity_pos
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (C : FullPrimePowerChannelSet T)
    (s : LogCapacityState) :
    0 < (W.fullGlobalLogCapacityKernel C).capacity s :=
  W.globalLogCapacityKernel_capacity_pos C.channels C.subset_index s

/--
The full-channel log-cost completeness assumption is exactly outgoing-cost
equality for the full global capacity kernel.
-/
theorem fullGlobalLogCapacityKernel_outgoingCost_eq_capacity
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (C : FullPrimePowerChannelSet T)
    (hcomplete : FullChannelLogCostComplete W C)
    (s : LogCapacityState) :
    (W.fullGlobalLogCapacityKernel C).outgoingCost s =
      (W.fullGlobalLogCapacityKernel C).capacity s := by
  simpa [fullGlobalLogCapacityKernel, globalLogCapacityKernel,
    CapacityKernel.outgoingCost] using hcomplete.outgoing_eq s

/--
Under full-channel log-cost completeness, the normalized outgoing mass is one.
-/
theorem fullGlobalLogCapacityKernel_normalizedOutgoing_eq_one
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (C : FullPrimePowerChannelSet T)
    (hcomplete : FullChannelLogCostComplete W C)
    (s : LogCapacityState) :
    (W.fullGlobalLogCapacityKernel C).normalizedOutgoing s = 1 := by
  rw [(W.fullGlobalLogCapacityKernel C).normalizedOutgoing_eq_outgoingCost_div s,
    W.fullGlobalLogCapacityKernel_outgoingCost_eq_capacity C hcomplete s]
  exact div_self (ne_of_gt (W.fullGlobalLogCapacityKernel_capacity_pos C s))

/--
The full global log-capacity shadow becomes a Markov shadow once full-channel
log-cost completeness is supplied.
-/
noncomputable def fullGlobalLogCapacityMarkovShadow
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (C : FullPrimePowerChannelSet T)
    (hcomplete : FullChannelLogCostComplete W C) :
    MarkovShadow LogCapacityState ℕ :=
  MarkovShadow.ofCapacityKernel (W.fullGlobalLogCapacityKernel C)
    (W.fullGlobalLogCapacityKernel_capacity_pos C)
    (W.fullGlobalLogCapacityKernel_outgoingCost_eq_capacity C hcomplete)

@[simp] theorem fullGlobalLogCapacityMarkovShadow_toSubMarkovShadow
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (C : FullPrimePowerChannelSet T)
    (hcomplete : FullChannelLogCostComplete W C) :
    (W.fullGlobalLogCapacityMarkovShadow C hcomplete).toSubMarkovShadow =
      W.fullGlobalLogCapacitySubMarkovShadow C :=
  rfl

theorem fullGlobalLogCapacityMarkovShadow_totalWeightAt_eq_one
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (C : FullPrimePowerChannelSet T)
    (hcomplete : FullChannelLogCostComplete W C)
    (s : LogCapacityState) :
    (W.fullGlobalLogCapacityMarkovShadow C hcomplete).toSubMarkovShadow.totalWeightAt s =
      1 :=
  (W.fullGlobalLogCapacityMarkovShadow C hcomplete).totalWeightAt_eq_one s

end PrimePowerWitnessProvider

end DkMath.NumberTheory.PrimitiveSet
