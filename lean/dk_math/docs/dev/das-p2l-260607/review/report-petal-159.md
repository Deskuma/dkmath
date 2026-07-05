# Report Petal 159

## Checkpoint

Checkpoint 159 stayed on the main Collatz/Petal root and added the first
overlap vocabulary for pressure-accounting addresses.

Modified implementation file:

- `DkMath/Collatz/PetalBridge/PressureAccounting.lean`

No `OneCycle`, `ValuationFlowBridge`, `ABC`, or `NumberTheory` files were
modified.

## Nat Interval Layer

A new half-open interval overlap predicate was added.

```lean
def NatIntervalsOverlap (a lenA b lenB : Nat) : Prop :=
  a < b + lenB ∧ b < a + lenA
```

This is paired with the existing ordered non-overlap predicate:

```lean
def NatIntervalBefore (a len b _len' : Nat) : Prop :=
  a + len ≤ b
```

The following exclusion facts were proved:

```lean
theorem NatIntervalsOverlap.not_of_before
theorem NatIntervalsOverlap.not_of_reverseBefore
```

The core experimental lemma was also proved:

```lean
theorem NatIntervalsOverlap.of_not_before_not_reverseBefore
```

This says that if neither ordered direction is available, the two half-open
intervals overlap.  The theorem keeps explicit length-positivity hypotheses at
the API boundary, even though the arithmetic proof itself is forced by the two
negated `before` inequalities.

## Address Layer

The address-level overlap predicate was added.

```lean
def SourcePressureIntervalPulseAddressOverlap
    {n : OddNat} {k r : Nat}
    (A B : SourcePressureIntervalPulseAddress n k r) : Prop :=
  NatIntervalsOverlap A.start A.len B.start B.len
```

The following address-level theorems were proved:

```lean
theorem SourcePressureIntervalPulseAddressOverlap.not_of_before
theorem SourcePressureIntervalPulseAddressOverlap.not_of_reverseBefore
theorem SourcePressureIntervalPulseAddressOverlap.of_not_before_not_reverseBefore
```

These theorems read only the explicit `start` and `len` fields of supplied
addresses.  They do not merge intervals or introduce union accounting.

## Witness Layer

The witness-level wrapper was added.

```lean
def SourcePressureLocalIslandWitnessOverlap
    {n : OddNat} {k r : Nat}
    (W1 W2 : SourcePressureLocalIslandWitness n k r) : Prop :=
  SourcePressureIntervalPulseAddressOverlap
    (sourcePressureIntervalPulseAddress_of_localIslandWitness W1)
    (sourcePressureIntervalPulseAddress_of_localIslandWitness W2)
```

The following witness-level theorems were proved:

```lean
theorem SourcePressureLocalIslandWitnessOverlap.not_of_before
theorem SourcePressureLocalIslandWitnessOverlap.not_of_reverseBefore
theorem SourcePressureLocalIslandWitnessOverlap.of_not_before_not_reverseBefore
```

The overlap constructor keeps explicit length-positivity hypotheses:

```lean
0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len
0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len
```

This keeps the theorem local to converted address intervals and avoids hiding
any positivity requirement in the witness layer.

## Boundary Notes

`not before` alone is still not overlap evidence.

The valid refinement is:

```text
not A before B
not B before A
positive lengths
--------------------------------
A overlaps B
```

This checkpoint does not introduce:

- maximality,
- uniqueness of pressure families,
- coverage,
- prefix behavior,
- union accounting,
- Collatz convergence.

All statements remain local to explicitly supplied intervals, addresses, or
witnesses.

## Verification

The following build gate was run during implementation:

```bash
lake build DkMath.Collatz.PetalBridge.PressureAccounting
```

It passed after replacing a fragile `unfold` proof with explicit `change`
normal forms around the `NatIntervalsOverlap.*` theorem namespace.

Final verification gate:

```bash
lake build DkMath.Collatz.PetalBridge.PressureAccounting
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
rg -n "\\bsorry\\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
rg -n "\\bsorry\\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
git diff --check
```

See the final Codex response for the pass/fail status of the final gate.

## Next Inference

The safe next theorem shape is not a union theorem.  The next useful layer is a
small classification lemma for explicit pairs:

```text
before A B
or before B A
or overlap A B
```

with explicit positive lengths for the overlap branch.  This would give callers
a trichotomy-style local diagnostic without claiming maximal families,
coverage, or Collatz convergence.
