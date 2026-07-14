# summary: No.064

## 失敗は成功のもと False 補題重点実装計画

## 0. Source Notes

This summary consolidates:

- `review-petal-064.md`
- `note01-petal-064.md`
- `note02-petal-064.md`
- `note03-petal-064.md`

The previous checkpoint closed the direct route:

```text
PrimitiveBeam / Zsigmondy witness family
  -> PetalCarrierLabelMapData / PetalNoLiftCarrierLabelMapData
  -> finite GN log-capacity route
```

The current reading step is not about adding another large positive theorem.
It is about recording which assumptions are still missing, and which bad
assumptions force contradiction.

## 1. Current Checkpoint

`DkMath.Petal.ErdosBridge` now has direct wrappers:

```text
petalPrimeChannelFamily_logSubProbability_GN_of_bodyPrimitivePrimeFactor_family
petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_bodyPrimitivePrimeFactor_family
petalPrimeChannelFamily_logSubProbability_GN_of_zsigmondyPrimitivePrimeDivisor_family
petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_zsigmondyPrimitivePrimeDivisor_family
```

These theorems are route-closure theorems.  They do not add new arithmetic
strength; they make the existing constructor + log-capacity path callable from
PrimitiveBeam and Zsigmondy witness families.

Important boundary:

```text
Zsigmondy supplies carrier location.
NoLift is a separate local contract.
```

The NoLift wrappers still require:

```lean
∀ i, i ∈ I → ¬ (qOf i) ^ 2 ∣ GN ...
```

This is intentional.  A primitive divisor is a new prime divisor, not
automatically a one-slot divisor.

## 2. Three Independent Axes

The notes repeatedly point to one design rule:

```text
Do not mix label recovery, NoLift, and final FLT/ABC exit theorems.
```

They play different roles.

### 2.1. Label recovery

Current shape:

```lean
∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j
```

Meaning:

```text
If the same prime label is selected twice,
then it must recover the same Petal value/address.
```

This is a family noncollision condition.  It prevents double-counting the same
prime slot in finite log-capacity and multiplicity-budget arguments.

Known safe supply routes:

```text
mOf = qOf
qOf = f (mOf) with local injective recovery
qOf = petalNthPrimeLabel (mOf)
```

The real target is eventually:

```text
Primitive/Zsigmondy carrier structure
  -> address/value reconstruction
  -> label recovery
```

But this is not available yet.  Keep it as an explicit family-level contract
until a genuine reconstruction theorem is found.

### 2.2. NoLift

Current shape:

```lean
PetalNoLiftPrimeChannel d x u q :=
  PetalPrimeChannel d x u q ∧ ¬ q ^ 2 ∣ GN d x u
```

Meaning:

```text
q divides the GN surface, but q^2 does not.
```

Existing consequence:

```text
PetalNoLiftPrimeChannel d x u q
  -> padicValNat q (GN d x u) = 1
```

NoLift is local valuation control.  It is not label recovery and not family
noncollision.

Safe supply candidates:

```text
explicit local no-lift hypothesis
Squarefree (GN d x u)
d = 3 explicit computation
gcd / localization / unitization side conditions
Wieferich-lift exclusion / descent
```

General Zsigmondy alone should not be treated as a NoLift supplier.

### 2.3. Final exits

There are two different exits.

FLT exit:

```text
NoLift gives v_q(GN) = 1.
A d-th-power or FLT transfer gives d <= v_q(GN).
If 1 < d, these collide.
```

ABC exit:

```text
distinct prime carrier labels
  -> support/rad lower-bound material
```

ABC may not need NoLift.  It primarily needs prime-valued distinct support.
NoLift strengthens local valuation interpretation, but it is a separate axis.

## 3. False / Obstruction Theorems

The main philosophical shift in note03 is:

```text
Positive route:
  bridge theorem

Negative route:
  obstruction theorem

Both are part of the map.
```

A False theorem is not a corrupt axiom.  The safe pattern is:

```lean
theorem bad_assumption_leads_to_false
    (hbad : BadAssumption ...) : False := by
  ...
```

Do not add:

```lean
axiom hbad : BadAssumption ...
```

The theorem records that a proposed route breaks when a bad extra hypothesis is
introduced.  It identifies the boundary of a valid construction.

## 4. Minimal Obstruction API

The first useful file is probably:

```text
DkMath/Petal/Obstruction.lean
```

Implemented first checkpoint:

```text
DkMath.Petal.Obstruction
```

Implemented theorem set:

```lean
petalAddressNoncollision_contradiction_of_same_address_ne_index
labelRecovery_contradiction_of_same_label_ne_value
valueInjective_contradiction_of_same_value_ne_index
labelRecovery_valueInjective_eq_of_same_label
petalCarrierLabelMapData_eq_of_same_label
petalNoLiftCarrierLabelMapData_eq_of_same_label
petalCarrierLabelMapData_label_injOn
petalNoLiftCarrierLabelMapData_label_injOn
petalCarrierLabelMapData_labelNoncollision
petalNoLiftCarrierLabelMapData_labelNoncollision
petalCarrierLabelMapData_contradiction_of_same_label_ne_index
petalNoLiftCarrierLabelMapData_contradiction_of_same_label_ne_index
petalCarrierLabelNoncollision_contradiction_of_same_label_ne_index
noLift_contradiction_of_square_dvd_GN
padicValNat_eq_one_contradiction_of_two_le
petalNoLift_contradiction_of_padicValNat_two_le
petalNoLift_obstruction_of_padicValNat_ge
```

This first set focuses on the smallest route-breaking witnesses and the
positive safety chain behind them:

```text
same address under address noncollision
same label but different value under label recovery
same value but different index under value injectivity
same label -> same value -> same selected index
label injectivity and duplicate-free support from carrier-label map data
duplicate selected prime label under carrier-label noncollision
q^2 | GN under NoLift
two-slot valuation under one-slot p-adic reading
d-level valuation lower bound under NoLift when 1 < d
```

Potential later files:

```text
DkMath/NumberTheory/ValuationFlow/Obstruction.lean
DkMath/FLT/PrimeProvider/Obstruction.lean
DkMath/ABC/BridgeObstruction.lean
```

Start small.  The first Petal-facing obstruction lemmas should be thin and
obvious, because their value is naming the breakpoints.

Candidate theorem set:

```lean
theorem labelRecovery_contradiction_of_same_label_ne_value
theorem valueInjective_contradiction_of_same_value_ne_index
theorem noLift_contradiction_of_square_dvd_GN
theorem padicValNat_eq_one_contradiction_of_two_le
theorem squarefree_contradiction_of_square_prime_dvd
theorem disjointChannels_contradiction_of_duplicate_label
```

The most immediately useful FLT-facing one is:

```lean
theorem petalNoLift_obstruction_of_padicValNat_ge
    (hd1 : 1 < d)
    (hNoLift : PetalNoLiftPrimeChannel d x u q)
    (hge : d ≤ padicValNat q (GN d x u)) :
    False
```

This should be kept separate from the theorem that supplies `hge`.  The
obstruction theorem is only the collision point:

```text
NoLift upper/exact value
  + valuation lower bound
  -> False
```

## 5. Range Failure as a Guide to Assumptions

The user's guiding analogy:

```text
N + u^2 + ε = (P + u + ν)^2
```

In a controlled cosmic-formula range, the allowed `ε` range is absorbed by the
allowed `ν` range.  Once `ε` exceeds that range, the formula breaks.

This suggests a general proof-search pattern:

```text
1. Define the valid range.
2. Prove the positive bridge inside the range.
3. Prove an obstruction theorem outside the range.
4. Use the obstruction theorem to discover which assumptions are necessary.
```

For Petal/GN/Zsigmondy, the analogous boundaries are:

```text
same label but different value/address
same value/address but different selected index under injectivity
NoLift plus q^2 | GN
padicValNat q GN = 1 plus 2 <= padicValNat q GN
squarefree plus repeated prime square divisibility
support/rad bridge plus duplicate or unsupported prime channel
```

The point is not to avoid false routes silently.  The point is to name the exact
condition where the route stops being valid.

## 6. Implementation Direction

Recommended next checkpoints:

```text
1. Add DkMath.Petal.Obstruction with the minimal contradiction lemmas.
2. Add a thin FLT-facing valuation obstruction:
   NoLift + d <= padicValNat q GN + 1 < d -> False.
3. Consider splitting family NoLift into a separate predicate:
   PetalNoLiftOn I d x u qOf.
4. Add a constructor:
   PetalCarrierLabelMapData + PetalNoLiftOn -> PetalNoLiftCarrierLabelMapData.
5. Investigate ABC wrappers:
   PetalCarrierLabelMapData -> existing support/rad lower-bound bridge.
6. Investigate NoLift suppliers:
   squarefree GN, d=3 explicit computation, localization/unitization,
   Wieferich-lift exclusion.
```

The priority is not a huge theorem.  The priority is a set of small gates:

```text
carrier location gate
label recovery gate
NoLift gate
valuation obstruction gate
ABC support/rad gate
```

Each gate should have both a positive bridge and, where useful, a negative
obstruction theorem.

## 7. Working Principle

The current DkMath path should keep this rule:

```text
Primitive/Zsigmondy gives carrier.
Label recovery gives finite-family noncollision.
NoLift gives one-slot p-adic control.
FLT consumes valuation contradiction.
ABC consumes distinct support/rad growth.
```

False lemmas are the guardrails.  They are not dead ends to hide; they are
records of the assumptions that make a route impossible.

## 8. ABC Negotiation Checkpoint

Implemented first support/rad negotiation layer:

```text
DkMath.Petal.ABCBridge
```

Implemented theorem set:

```lean
petalCarrierLabelSupport
petalCarrierLabelMapData_labelSupport_prime_dvd_GN
petalNoLiftCarrierLabelMapData_labelSupport_prime_dvd_GN
petalCarrierLabelMapData_labelSupport_card_eq
petalNoLiftCarrierLabelMapData_labelSupport_card_eq
petal_two_pow_card_le_prod_of_two_le
petalCarrierLabelMapData_two_pow_card_le_labelSupport_prod
petalNoLiftCarrierLabelMapData_two_pow_card_le_labelSupport_prod
petalCarrierLabelMapData_labelSupport_prod_le_supportMass_GN
petalNoLiftCarrierLabelMapData_labelSupport_prod_le_supportMass_GN
petalCarrierLabelMapData_labelSupport_prod_le_rad_GN
petalNoLiftCarrierLabelMapData_labelSupport_prod_le_rad_GN
petalCarrierLabelMapData_two_pow_card_le_supportMass_GN
petalNoLiftCarrierLabelMapData_two_pow_card_le_supportMass_GN
petalCarrierLabelMapData_two_pow_card_le_rad_GN
petalNoLiftCarrierLabelMapData_two_pow_card_le_rad_GN
petalCarrierLabelMapData_two_pow_le_supportMass_GN_of_card_eq
petalCarrierLabelMapData_two_pow_le_rad_GN_of_card_eq
petalNoLiftCarrierLabelMapData_two_pow_le_supportMass_GN_of_card_eq
petalNoLiftCarrierLabelMapData_two_pow_le_rad_GN_of_card_eq
petalCarrierLabelMapData_two_pow_le_supportMass_GN_of_card_le
petalCarrierLabelMapData_two_pow_le_rad_GN_of_card_le
petalNoLiftCarrierLabelMapData_two_pow_le_supportMass_GN_of_card_le
petalNoLiftCarrierLabelMapData_two_pow_le_rad_GN_of_card_le
petal_two_pow_card_le_supportMass_GN_of_bodyPrimitivePrimeFactor_family
petal_two_pow_card_le_rad_GN_of_bodyPrimitivePrimeFactor_family
petal_two_pow_card_le_supportMass_GN_of_zsigmondyPrimitivePrimeDivisor_family
petal_two_pow_card_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family
petal_two_pow_le_rad_GN_of_bodyPrimitivePrimeFactor_family_card_eq
petal_two_pow_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family_card_eq
petal_two_pow_le_supportMass_GN_of_bodyPrimitivePrimeFactor_family_card_le
petal_two_pow_le_rad_GN_of_bodyPrimitivePrimeFactor_family_card_le
petal_two_pow_le_supportMass_GN_of_zsigmondyPrimitivePrimeDivisor_family_card_le
petal_two_pow_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family_card_le
```

The bridge reads Petal carrier-label data as ABC finite support:

```text
Petal carrier labels on GN
  -> finite support of prime divisors of GN
  -> label noncollision preserves selected cardinality
  -> 2^(selected channel count) <= product of label support
  -> supportMass/rad lower bound
```

This is intentionally separate from NoLift.  ABC support/rad consumes prime
support; NoLift is kept for p-adic valuation obstruction.

The second checkpoint makes the bridge count-facing:

```text
PetalCarrierLabelMapData on I
  -> card(labelSupport) = card(I)
  -> every label prime has 2 <= q
  -> 2^card(I) <= product(labelSupport)
  -> 2^card(I) <= supportMass(GN d x u)
  -> 2^card(I) <= rad(GN d x u)
```

This is the ABC analogue of the Erdos finite-family count spine.  It gives a
small, reusable lower bound without requiring a concrete prime enumeration and
without consuming NoLift.

The third checkpoint adds direct PrimitiveBeam / Zsigmondy wrappers:

```text
PrimitiveBeam family in body coordinates
  -> 2^card(I) <= supportMass(GN d x u)
  -> 2^card(I) <= rad(GN d x u)

Zsigmondy primitive-divisor family
  -> 2^card(I) <= supportMass(GN d (a - b) b)
  -> 2^card(I) <= rad(GN d (a - b) b)
```

These are thin wrapper theorems.  They do not add arithmetic strength beyond
the constructor route; they make the ABC negotiation callable directly from the
two main primitive-prime provider families.

The fourth checkpoint adds named-cardinality endpoints:

```text
I.card = k
  -> 2^k <= supportMass(GN)
  -> 2^k <= rad(GN)
```

This is the first small step toward concrete family constructions.  The
construction-specific proof of `I.card = k` remains outside `ABCBridge`; this
file now has the API needed to consume it immediately.

The fifth checkpoint adds lower-cardinality endpoints:

```text
k <= I.card
  -> 2^k <= supportMass(GN)
  -> 2^k <= rad(GN)
```

This is more flexible than exact cardinality.  Experimental constructions often
produce "at least k independent carriers" before they produce an exact count,
so the `_of_card_le` API lets that weaker result already feed ABC.

## 9. Range Family Construction Checkpoint

Implemented first concrete range-indexed construction layer:

```text
DkMath.Petal.RangeFamily
```

This fixes the finite family shape as:

```text
I = Finset.range k
mOf i = i + 1
```

Implemented theorem set:

```lean
rangeSuccValue_injOn
rangeLabel_injOn_of_pairwise_ne
rangeLabel_pairwise_ne_contradiction_of_same_label_ne_index
petalCarrierLabelMapData_of_bodyPrimitivePrimeFactor_range_succIndex
petalCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_range_succIndex
petal_range_two_pow_le_supportMass_GN_of_bodyPrimitivePrimeFactor_family
petal_range_two_pow_le_rad_GN_of_bodyPrimitivePrimeFactor_family
petal_range_two_pow_le_supportMass_GN_of_zsigmondyPrimitivePrimeDivisor_family
petal_range_two_pow_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family
petal_range_two_pow_le_supportMass_GN_of_bodyPrimitivePrimeFactor_pairwise
petal_range_two_pow_le_rad_GN_of_bodyPrimitivePrimeFactor_pairwise
petal_range_two_pow_le_supportMass_GN_of_zsigmondyPrimitivePrimeDivisor_pairwise
petal_range_two_pow_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_pairwise
```

The construction still leaves the serious arithmetic hypotheses explicit:

```text
label injectivity on Finset.range k
PrimitiveBeam or Zsigmondy witnesses for each index
```

But once those are supplied, the range cardinality is automatic, so the ABC
endpoint is concrete:

```text
k range-indexed primitive carriers
  -> 2^k <= supportMass(GN)
  -> 2^k <= rad(GN)
```

Follow-up checkpoint:

The range layer now also accepts pairwise label noncollision:

```text
i < k, j < k, i != j -> qOf i != qOf j
```

This is converted into `Set.InjOn qOf ↑(Finset.range k)`, so concrete
experiments can avoid constructing the subtype-level injectivity proof by hand.

False/obstruction checkpoint:

```lean
rangeLabel_pairwise_ne_contradiction_of_same_label_ne_index
```

This records the failure mode of the range pairwise route:

```text
pairwise label separation
same label at two distinct in-range indices
  -> False
```

The theorem does not prove that any proposed family is good.  It proves exactly
where a candidate `qOf` fails when a duplicate label is found.
