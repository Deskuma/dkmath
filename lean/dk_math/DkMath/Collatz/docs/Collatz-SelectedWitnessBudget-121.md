# Collatz Selected Witness Budget 121

Checkpoint 121 closes the first direct bridge from a selected pressure witness
to a delayed-budget opportunity.

The important restriction is that this is still a one-witness theorem.  It does
not claim independent accounting for multiple selected depths.

## Lean Bridge

Checkpoint 120 gave:

```lean
exists_positive_sourceContinuationMass_of_pressureDepthCount_pos
exists_positive_sourceContinuationMass_of_outrunsMoreThanHalf
```

Checkpoint 121 adds caller-facing names:

```lean
exists_towerEntryDepth_of_pressureDepthCount_pos
exists_towerEntryDepth_of_outrunsMoreThanHalf
```

Meaning:

```text
positive pressure-depth count
  -> selected local tower-entry depth
  -> positive source continuation mass
```

## Depth-Two Budget Package

The existing depth-two budget theorem was:

```lean
sourcePressureDepthTwo_delayed_budget_with_tailSeven_remainder
```

Checkpoint 121 packages it with positive mass:

```lean
depthTwoPressureRange_positive_and_budget
exists_depth_two_budget_of_pressureOnRange_two_one
```

The theorem reads:

```text
SourceContinuationPressureOnRange n k 2 1
  -> 0 < orbitWindowContinuationSiblingMassPow2 n k 2
  -> (k + 1) + orbitWindowContinuationSiblingMassPow2 n k 2
       <= sumS n ((k + 1) + 1)
          + orbitWindowResidueCountMod8EqSevenTail n k
```

This is the first stable form of:

```text
selected pressure witness
  -> positive continuation mass
  -> delayed budget with explicit remainder
```

## Python Orbit Observation

New script:

```text
python/Collatz/PetalBridge/orbit_pressure_remainder_scan.py
```

Generated:

```text
python/Collatz/PetalBridge/results/orbit_pressure_remainder_scan.csv
python/Collatz/PetalBridge/results/orbit_pressure_remainder_scan.md
```

Default command:

```text
python3 python/Collatz/PetalBridge/orbit_pressure_remainder_scan.py \
  --max-n 999 --steps 64 --r-start 2 --depth-len 8
```

The output records:

```text
n
steps
sumS
pressure_depth_count
first_pressure_depth
continuation_mass_at_first_pressure
retention_mass_at_first_pressure
L1..L5 remainders
L1..L5 falling colors
```

Default observed summary:

```text
rows: 500
rows with pressure witness: 237
rows with L5 remainder: 18
max pressure depth count: 6
max L5 remainder: 3
```

## Reading

The scan shows that pressure witnesses are common in finite windows, while deep
all-ones remainders are much rarer.

This supports the next formal split:

```text
pressure witness exists
  -> one delayed budget opportunity

many pressure witnesses
  -> requires a separate no-overlap / address-separated condition
```

The second statement is not yet proved and should not be assumed.

## Next Work

The next useful formal object is likely a selected-depth package:

```text
selected pressure depths as a finite list or Finset
```

but it should initially expose only witness facts, not independent budget
claims.

Safer immediate theorem:

```text
two pressure witnesses exist if pressureDepthCount >= 2
```

Riskier theorem:

```text
two pressure witnesses give two independent delayed budgets
```

The latter needs an explicit disjointness or separated-address hypothesis.
