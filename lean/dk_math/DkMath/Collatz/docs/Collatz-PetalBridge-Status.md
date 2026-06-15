# Collatz Petal Bridge Status

This note records the current contact point between the accelerated Collatz
formalization and the Petal range-family route.

## Current Collatz Surface

Implemented Collatz modules already provide:

```text
DkMath.Collatz.Basic
  C
  OddNat
  threeNPlusOne

DkMath.Collatz.V2
  v2
  v2_3n_plus_1_ge_1
  v2_shift_invariant support lemmas

DkMath.Collatz.Accelerated
  s n = v2 (3n + 1)
  T n = (3n + 1) / 2^(v2 (3n + 1))
  iterateT
  sumS
  driftReal

DkMath.Collatz.Shift
  shift
  v2_shift_invariant
```

This means the implemented Collatz side is currently strongest around:

```text
odd state
2-adic height
accelerated transition
orbit segment
block-shift invariance
```

## Petal Contact Point

`DkMath.Petal.RangeFamily` recently introduced a range-indexed observation
layer:

```text
I = Finset.range k
mOf i = i + 1
qOf i = selected label at index i
```

It now has both sides of the test:

```text
pairwise label separation
  -> Set.InjOn qOf ↑(Finset.range k)

same label at two distinct in-range indices
  -> False
```

This is a natural match for Collatz orbit segments.

## New Window

The bridge file is:

```text
DkMath.Collatz.PetalBridge
```

It defines:

```lean
oddOrbitLabel
OddOrbitLabelsPairwiseSeparated
```

where:

```text
oddOrbitLabel n i = the natural value of iterateT i n
```

The first theorem set is deliberately thin:

```lean
oddOrbitLabel_injOn_of_pairwiseSeparated
iterateT_eq_of_oddOrbitLabel_eq
oddOrbitLabelsPairwiseSeparated_contradiction_of_same_label_ne_index
same_iterateT_of_oddOrbitLabel_collision
```

## Interpretation

For Petal / ABC:

```text
pairwise separated orbit labels
  -> independent range-family labels are available

duplicate label
  -> the independent range-family route closes as False
```

For Collatz dynamics:

```text
duplicate label
  -> same accelerated odd state
  -> merge / fold / cycle candidate
```

So the same event has two readings:

```text
Petal route:
  obstruction to independent counting

Collatz route:
  dynamical collision signal
```

## Does This Change the Current Petal Situation?

Not yet at the level of `supportMass` or `rad` lower bounds.

The new bridge does not prove that Collatz orbit labels are prime labels,
primitive carriers, or Zsigmondy witnesses.  Therefore it does not immediately
feed the `2^k <= supportMass/rad(GN)` endpoint.

What it changes is the diagnostic layer:

```text
Collatz orbit segment
  -> Petal range-label separation test
  -> either separated segment or collision obstruction
```

This gives a clean place to attach future hypotheses:

```text
orbit labels are usable carrier labels
orbit labels are mapped to prime labels
orbit collision implies a specific fold/cycle condition
2-adic height controls Petal address movement
```

## Next Candidate Work

The next safe steps are:

```text
1. Define a Collatz orbit segment as a finite range family.
2. Add a collision-vs-separated predicate split.
3. Connect v2_shift_invariant to a Petal address/residue reading.
4. Only after that, test whether Collatz labels can feed ABC support/rad.
```

The main caution is that Collatz state labels are not prime labels.  Any bridge
to `ABCBridge` must insert an additional label transform or carrier witness
layer before using the Petal radical lower-bound theorems.
