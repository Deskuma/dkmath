# DKMK-020: report

DKMK-020 is the threshold/support policy chapter.

DKMK-019 completed the LogCapacity source facade and produced a caller-facing
path-family theorem:

```text
(W.logCapacitySourcePathFamily IOf hIOf s threshold).weightedHitMass A
  <= 1 + error
```

The remaining issue was that the support and threshold inputs were still loose
at the theorem boundary:

```text
IOf
hIOf
threshold
```

DKMK-020 packages those inputs into a named policy object.

## 1. Starting Point

The DKMK-019 endpoint hid the raw construction chain:

```text
positiveRatIncrementBelow (...)
finiteStepTailNatMassSpace (...)
globalLogCapacityKernel_applyAtToPrimePowerQuotientPathFamily (...)
```

but callers still had to provide:

```text
IOf : Nat -> Finset Nat
hIOf : forall n q, q in IOf n -> q in T.toDivisorTransitionKernel.index n
threshold : Nat -> Nat
```

This was acceptable for route validation, but not yet a stable public policy
surface.

## 2. Policy Object

DKMK-020B introduced:

```lean
LogCapacitySourcePolicy
```

with the data:

```text
support family
index proof
threshold map
```

In Lean this bundles the loose inputs into:

```text
P : LogCapacitySourcePolicy T
```

The structure is intentionally data-only.  It does not claim threshold
optimality, support compatibility, or monotonicity.

## 3. Policy-Facing Facade

DKMK-020B also introduced:

```lean
PrimePowerWitnessProvider.logCapacityPolicyPathFamily
PrimePowerWitnessProvider
  .logCapacityPolicyPathFamily_weightedHitMass_le_one_add_error
```

The final route now reads:

```text
(W.logCapacityPolicyPathFamily P s).weightedHitMass A <= 1 + error
```

This is the desired policy-facing theorem form.

## 4. Validity Decision

DKMK-020C decided not to add validity fields to `LogCapacitySourcePolicy`.

The current route uses exactly:

```text
P.IOf
P.hIOf
P.threshold
```

No current theorem consumes:

```text
support compatibility
threshold monotonicity
threshold support-locality
policy validity
```

Adding those as structure fields now would force unused obligations on every
future policy constructor.

## 5. Future Extension Point

If later routes need stronger policy facts, they should be added as separate
predicates:

```text
LogCapacitySourcePolicy.Valid P
LogCapacitySourcePolicy.SupportCompatible P
LogCapacitySourcePolicy.ThresholdMonotone P
```

This preserves the light data object while allowing stronger theorems to ask
for stronger assumptions.

## 6. Decision

DKMK-020 is complete as the threshold/support policy API chapter.

It answers the chapter question:

```text
Can the LogCapacity source route expose support and threshold choices through
a named policy input?
```

Answer:

```text
Yes.  The loose support family, index proof, and threshold map are now bundled
as LogCapacitySourcePolicy, and the final weighted-hit theorem is policy-facing.
```

## 7. Non-Goals

DKMK-020 did not add:

```text
threshold optimization
canonical support selection
support compatibility theorem
threshold monotonicity theorem
new analytic source family
Mertens theorem
big-O route
```

This was a policy/API stabilization chapter, not a threshold optimization
chapter.

## 8. Next Branch

Two natural next directions remain.

Source expansion:

```text
test whether additional analytic sources can be routed through the same
LogCapacitySourcePolicy-facing surface
```

Policy validity survey:

```text
identify which later theorem, if any, actually requires Valid,
SupportCompatible, or ThresholdMonotone predicates
```

The next chapter should likely be a short survey before adding more policy
conditions.
