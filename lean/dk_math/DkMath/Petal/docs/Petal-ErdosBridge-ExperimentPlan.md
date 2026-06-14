# Petal / Erdos #1196 Bridge Experiment Plan

Status: **first public bridge implemented**

This document records the next experimental route after the Petal/Zsigmondy
contract work.

The immediate question is:

```text
Can the Petal GN carrier / Zsigmondy contract layer feed the partially built
Erdos #1196 formalization, and can the Erdos log-capacity machinery return
useful global conditions for Zsigmondy / FLT / ABC?
```

The answer is: **yes, for the finite log-capacity bridge**.  The current
workspace now contains the first public Petal/Erdos bridge:

```text
DkMath.Petal.ErdosBridge
```

This is still not a new unconditional Zsigmondy, FLT, ABC, or analytic Erdős
#1196 theorem.  It is the public bridge that lets Petal GN carrier channels be
consumed by the existing finite `PrimitiveSet` log-capacity machinery.

## Current Coordinates

### Petal Side

The Petal route currently supplies:

```text
GN / S0 location:
  AnchoredGNCarrier
  AnchoredS0Carrier

Zsigmondy handshake:
  PrimitivePrimeDivisor
    -> PrimitivePrimeFactorOfDiffPow
    -> boundary avoidance
    -> GN divisibility
    -> valuation transfer
    -> AnchoredGNCarrier

Multiplicity layer:
  local NoLift at q
  squarefree GN as a sufficient condition
  pairwise distinct selected labels as the current family noncollision input
```

Important files:

```text
DkMath.Petal.Anchor
DkMath.Petal.BezoutBridge
DkMath.Petal.ZsigmondyD3Bridge
DkMath.Petal.PrimitiveD3ValuationBridge
DkMath.NumberTheory.PrimitiveBeam
DkMath.NumberTheory.ValuationFlow.Primitive
DkMath.ABC.ValuationFlowBridge
```

The key reading is:

```text
Zsigmondy gives a primitive q.
Petal tells us where q is observed: on GN, not on the boundary.
Valuation transfer lets the body-difference height be read on GN.
NoLift / squarefree controls the multiplicity.
PairwiseDistinct controls family label collisions.
```

### Erdos #1196 Side

The primitive-set / Erdos route already contains a substantial finite
log-capacity skeleton:

```text
PrimitiveOn
Divisibility chains
Prime descent paths
Prime-power divisor transition kernels
Valuation budget
Real/log product budget
Log-capacity kernels
Sub-Markov / Markov shadows
Weighted hitting bounds
Source-mass truncation contracts
```

Important files:

```text
DkMath.NumberTheory.PrimitiveSet.Basic
DkMath.NumberTheory.PrimitiveSet.PrimeDescent
DkMath.NumberTheory.PrimitiveSet.DivisorTransitionKernel
DkMath.NumberTheory.PrimitiveSet.ValuationBudget
DkMath.NumberTheory.PrimitiveSet.RealDivisorBridge
DkMath.NumberTheory.PrimitiveSet.LogCapacityKernel
DkMath.NumberTheory.PrimitiveSet.FullExponentSlot
DkMath.NumberTheory.PrimitiveSet.FullExponentSlotCanonical
DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
DkMath.Kernel.Capacity
DkMath.Kernel.SubProbability
```

The key existing Erdos-side principle is:

```text
selected prime-power channels
  -> base-prime multiplicity budget in n
  -> sum log(base prime) <= log n
  -> normalized outgoing mass <= 1
```

This is the finite R/log capacity route.

The bridge now uses the following implemented `PrimitiveSet` support:

```lean
natPairwiseDistinctOn_injOn
natBaseMultiplicityBudgetOn_of_injOn_of_dvd
natBaseMultiplicityBudgetOn_of_pairwiseDistinct_of_dvd
```

## Conceptual Bridge

The bridge is:

```text
Erdos channel:
  q = p^k is a descent / capacity channel

Petal carrier:
  q is a GN-observed carrier, with anchor prime p
```

Thus:

```text
AnchoredGNCarrier
  -> candidate prime-power channel
  -> base prime cost log p
  -> log-capacity budget
```

This does not prove a new primitive-divisor theorem.  It gives a way to feed
Petal/Zsigmondy witnesses into the existing Erdos capacity machinery.

The currently implemented public route is:

```text
PetalPrimeChannel family
  + PetalCarrierLabelNoncollisionOn labels
  -> NatBaseMultiplicityBudgetOn against GN
  -> realLogRatioWeightProvider.SubProbability
```

`PetalCarrierLabelNoncollisionOn I qOf` is currently the Petal-facing name for
the lower-level `NatPairwiseDistinctOn I qOf` condition.  The intended next
step is to derive it from Petal address/carrier geometry.

The currently implemented local no-lift route is:

```text
PetalNoLiftPrimeChannel
  -> padicValNat q (GN d x u) = 1
```

These are separate facts.  NoLift gives local one-slot valuation for a selected
prime label; it does not prove family label distinctness.

The first public crossroads theorem is now:

```text
PetalNoLiftPrimeChannel family
  + PetalCarrierLabelNoncollisionOn labels
  -> petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
```

This theorem is intentionally finite and conditional.  It is a signpost for
the common route, not a proof that address geometry gives noncollision or that
Zsigmondy gives no-lift.

## Strong Claims We May Be Able to Extract

### Claim A: Zsigmondy Witness as an Erdos Channel

Status: **implemented**

Expected form:

```lean
Zsigmondy primitive q
  -> AnchoredGNCarrier q d (a - b) b q
  -> q is a valid prime-power channel with base q and exponent 1
```

This is low-risk because a prime q is already a prime power `q^1`.

Expected role:

```text
Zsigmondy witness can be inserted into the Erdos channel vocabulary.
```

### Claim B: Petal Carrier Cost is Log-Capacity Cost

Status: **implemented**

Expected form:

```lean
AnchoredGNCarrier q d x u q
  -> Nat.Prime q
  -> channel cost = log q
```

This is mostly vocabulary alignment.  The Erdos side already has real/log
nonnegativity for prime-valued base readers.

Expected role:

```text
Petal carrier has a capacity cost.
```

### Claim C: Finite Petal Carrier Family Has a Sub-Probability Budget

Status: **implemented, with two entry forms**

Expected form:

```lean
finite family of Petal carriers
  + base-prime multiplicity budget against n
  -> sum log(base prime) / log n <= 1
```

Implemented forms include:

```lean
petalCarrierFamily_logSubProbability_of_multiplicityBudget
petalPrimeChannelFamily_logSubProbability_GN_of_injOn
petalPrimeChannelFamily_logSubProbability_GN_of_pairwiseDistinct
```

This should reuse:

```lean
NatBaseMultiplicityBudgetOn
realLogRatioWeightProvider_subProbability_of_multiplicityBudget
basePrimeOf_logCapacity_outgoing_le
logCapacityKernel_normalized_subProbability
```

Expected role:

```text
Petal carrier families can be viewed as Erdos finite capacity kernels.
```

### Claim D: NoLift Separates Multiplicity from Capacity

Status: **implemented locally**

The Petal/Zsigmondy contract says:

```text
q is on GN
```

The Erdos capacity side counts:

```text
base prime occurrences / exponent slots
```

NoLift is the bridge between these readings:

```text
local NoLift at q
  -> the selected GN carrier consumes one exponent slot
```

Without NoLift, the same carrier may consume multiple exponent slots.

Expected role:

```text
NoLift controls whether a Petal carrier is a unit-cost Erdos channel.
```

Implemented core:

```lean
petalNoLiftPrimeChannel_padicValNat_GN_eq_one
petalNoLiftPrimeChannel_singleton_logSubProbability_GN_self
petalNoLiftPrimeChannelFamily_padicValNat_GN_eq_one
```

Important guardrail:

```text
NoLift is local.  A no-lift family does not imply that selected labels are
pairwise distinct.
```

## Claims Not Yet Justified

The following should **not** be claimed yet:

```text
Petal address antichain implies primitive-set antichain.
Petal carriers automatically satisfy the Erdos multiplicity budget.
Zsigmondy automatically supplies local NoLift.
Zsigmondy automatically supplies padicValNat <= 1.
GN carriers are automatically squarefree.
Petal address noncollision automatically supplies NatPairwiseDistinctOn.
Full analytic Erdős #1196 tail estimate.
```

These are research directions, not current theorems.

The known counterexample remains the guardrail:

```text
5^3 - 3^3 = 98 = 2 * 7^2
S0_nat 5 3 = 49 = 7^2
q = 7 is primitive and lies on GN/S0,
but its local height is 2.
```

So multiplicity hypotheses cannot be erased.

## Proposed Implementation Route

### Step 1: Add a Thin `Petal.ErdosBridge` File

Status: **implemented**

Candidate file:

```text
DkMath.Petal.ErdosBridge
```

Purpose:

```text
Expose Petal/Zsigmondy carriers as Erdos-style prime channels.
```

Initial API should avoid heavy new structures.

Candidate theorem names:

```lean
theorem zsigmondyPrimitivePrimeDivisor_primeChannel
theorem anchoredGNCarrier_primeChannel
theorem anchoredGNCarrier_basePrime
theorem anchoredGNCarrier_logCost_nonneg
```

The first useful theorem can be as small as:

```lean
theorem anchoredGNCarrier_prime
    {q d x u : ℕ} (h : AnchoredGNCarrier q d x u q) :
    Nat.Prime q
```

This already exists as `anchoredGNCarrier_anchor_prime`; the bridge can simply
re-export the reading under Erdos/channel vocabulary.

### Step 2: Define a Minimal Petal Channel Predicate

Status: **implemented**

Candidate:

```lean
def PetalPrimeChannel (d x u q : ℕ) : Prop :=
  AnchoredGNCarrier q d x u q
```

This is intentionally thin.  It avoids committing to a full Erdos transition
kernel before the experiment proves useful.

Optional stronger version:

```lean
def PetalNoLiftPrimeChannel (d x u q : ℕ) : Prop :=
  AnchoredGNCarrier q d x u q ∧
  ¬ q ^ 2 ∣ GN d x u
```

### Step 3: Connect Prime Channel to Log-Cost Nonnegativity

Status: **implemented**

Expected target:

```lean
theorem petalPrimeChannel_log_nonneg
    (h : PetalPrimeChannel d x u q) :
    0 ≤ Real.log (q : ℝ)
```

This should follow from `Nat.Prime.one_lt` and the existing real-log helpers in
`PrimitiveSet.RealLog`.

### Step 4: Finite Family Experiment

Status: **implemented without adding a separate family predicate**

The current implementation did not add a separate family predicate.  It uses
ordinary quantified hypotheses:

```lean
∀ i, i ∈ I -> PetalPrimeChannel (d i) (x i) (u i) (qOf i)
```

Then try to prove:

```lean
PetalCarrierFamilyOn I d x u qOf
  -> NatPrimeValuedOn I qOf
```

This is a direct entry into the existing Erdos valuation-budget API.

### Step 5: Capacity Budget as an Assumption

Status: **implemented**

Do not try to prove multiplicity budget from Petal geometry yet.

Instead, assume:

```lean
NatBaseMultiplicityBudgetOn I qOf n
```

Then prove the existing log-capacity conclusion:

```lean
(I.sum fun i => Real.log (qOf i : ℝ) / Real.log (n : ℝ)) ≤ 1
```

This makes the first experiment Lean-small and honest:

```text
Petal supplies prime-valued carriers.
Erdos supplies capacity once multiplicity budget is given.
```

The implementation then went further: when all selected channels lie on the
same GN surface and labels are pairwise distinct, Petal supplies the GN
multiplicity budget directly.

### Step 6: Research Target - Address Antichain to Multiplicity Budget

Status: **current research target, with public label-noncollision hook**

Now that Step 5 is implemented, investigate:

```text
Petal address noncollision
  -> PetalCarrierLabelNoncollisionOn I qOf
  -> NatPairwiseDistinctOn I qOf
  -> base-prime multiplicity budget
```

This is the genuinely new research question.

Possible shape:

```lean
PetalAddressAntichain family
  -> NatBaseMultiplicityBudgetOn I qOf n
```

The current public bridge has chosen one concrete parent for this route:

```text
GN d x u
```

Other parents, such as body difference, source state, or an abstract capacity
carrier, remain separate design questions.

## Proposed Documentation / Naming Policy

Use the following wording consistently:

```text
Petal carrier:
  location of a primitive witness on GN

Erdos channel:
  capacity-consuming prime or prime-power descent label

NoLift:
  local multiplicity control for a selected carrier

Multiplicity budget:
  global exponent-slot bound needed by the R/log route
```

Avoid saying:

```text
Zsigmondy proves the Erdos budget.
Petal proves NoLift.
Petal address already proves antichain.
```

Those are not established.

## Recommended Next Checkpoint

Implement the address-facing noncollision layer:

```text
Petal address / carrier noncollision
  -> PetalCarrierLabelNoncollisionOn I qOf
  -> NatPairwiseDistinctOn I qOf
```

This is now the missing input needed by:

```lean
petalPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
petalPrimeChannelFamily_logSubProbability_GN_of_pairwiseDistinct
```

The downstream signposts from this checkpoint are:

```text
Erdos:
  address/carrier noncollision -> finite GN log-capacity family

FLT:
  NoLift one-slot -> d-th-power valuation obstruction

ABC:
  distinct one-slot channels -> support/rad lower-bound bridge
```

## Final Assessment

The first public bridge is implemented:

```text
Petal / Zsigmondy / GN:
  local primitive witness location

Erdos #1196 / PrimitiveSet:
  global log-capacity control
```

The implemented bridge proves translation and budget-consumption theorems.  It
also proves the duplicate-free GN-family route through `NatPairwiseDistinctOn`.

The next research target is:

```text
Can Petal address / carrier noncollision supply `NatPairwiseDistinctOn`?
```

That is the point where Petal may start producing genuinely strong conditions
useful for Zsigmondy, FLT, and ABC.
