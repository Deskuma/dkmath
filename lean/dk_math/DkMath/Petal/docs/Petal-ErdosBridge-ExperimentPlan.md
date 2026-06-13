# Petal / Erdos #1196 Bridge Experiment Plan

Status: **planning**

This document records the next experimental route after the Petal/Zsigmondy
contract work.

The immediate question is:

```text
Can the Petal GN carrier / Zsigmondy contract layer feed the partially built
Erdos #1196 formalization, and can the Erdos log-capacity machinery return
useful global conditions for Zsigmondy / FLT / ABC?
```

The answer is: **yes, but only as a staged experiment**.  The current workspace
already contains enough infrastructure to test the connection, but not enough
to claim a new unconditional Zsigmondy or FLT theorem.

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

## Strong Claims We May Be Able to Extract

### Claim A: Zsigmondy Witness as an Erdos Channel

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

Expected form:

```lean
finite family of Petal carriers
  + base-prime multiplicity budget against n
  -> sum log(base prime) / log n <= 1
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

## Claims Not Yet Justified

The following should **not** be claimed yet:

```text
Petal address antichain implies primitive-set antichain.
Petal carriers automatically satisfy the Erdos multiplicity budget.
Zsigmondy automatically supplies local NoLift.
Zsigmondy automatically supplies padicValNat <= 1.
GN carriers are automatically squarefree.
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

Expected target:

```lean
theorem petalPrimeChannel_log_nonneg
    (h : PetalPrimeChannel d x u q) :
    0 ≤ Real.log (q : ℝ)
```

This should follow from `Nat.Prime.one_lt` and the existing real-log helpers in
`PrimitiveSet.RealLog`.

### Step 4: Finite Family Experiment

Define an experimental family predicate, not a public final API:

```lean
def PetalCarrierFamilyOn
    {ι : Type*} (I : Finset ι)
    (d x u : ι -> ℕ) (qOf : ι -> ℕ) : Prop :=
  ∀ i, i ∈ I -> PetalPrimeChannel (d i) (x i) (u i) (qOf i)
```

Then try to prove:

```lean
PetalCarrierFamilyOn I d x u qOf
  -> NatPrimeValuedOn I qOf
```

This is a direct entry into the existing Erdos valuation-budget API.

### Step 5: Capacity Budget as an Assumption

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

### Step 6: Research Target - Address Antichain to Multiplicity Budget

Only after Step 5, investigate:

```text
Petal address noncollision
  -> base-prime multiplicity budget
```

This is the genuinely new research question.

Possible shape:

```lean
PetalAddressAntichain family
  -> NatBaseMultiplicityBudgetOn I qOf n
```

This is not yet ready for implementation.  It requires deciding what the
parent `n` is: body difference, GN, source state, or an abstract capacity
carrier.

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

Implement:

```text
DkMath.Petal.ErdosBridge
```

with only:

```lean
def PetalPrimeChannel
def PetalNoLiftPrimeChannel
theorem petalPrimeChannel_prime
theorem petalPrimeChannel_natPrimeValuedOn
theorem petalPrimeChannel_log_nonneg
```

Then add one finite-family theorem:

```lean
theorem petalCarrierFamily_logSubProbability_of_multiplicityBudget
```

This theorem should assume the multiplicity budget and reuse the existing
PrimitiveSet log-capacity machinery.  That gives the first concrete Petal ->
Erdos bridge without overclaiming.

## Final Assessment

The project is ready to enter an experimental bridge phase:

```text
Petal / Zsigmondy / GN:
  local primitive witness location

Erdos #1196 / PrimitiveSet:
  global log-capacity control
```

The first experiment should prove translation and budget-consumption theorems,
not new unconditional number theory.

If this bridge succeeds, the next research target is:

```text
Can Petal address noncollision supply the multiplicity budget required by the
Erdos log-capacity route?
```

That is the point where Petal may start producing genuinely strong conditions
useful for Zsigmondy, FLT, and ABC.
