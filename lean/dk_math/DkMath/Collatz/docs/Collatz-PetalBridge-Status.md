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
OrbitWindow
rawHeightLabel
oddOrbitLabel
orbitWindowHeight
orbitWindowHeightSeq
OddOrbitLabelsPairwiseSeparated
OrbitWindowSeparated
OrbitWindowCollision
```

where:

```text
OrbitWindow n k = Finset.range k
oddOrbitLabel n i = the natural value of iterateT i n
orbitWindowHeight n i = v2 (3 * oddOrbitLabel n i + 1)
orbitWindowHeightSeq n k = the ordered list of the first k height labels
```

The first theorem set is deliberately thin:

```lean
orbitWindow_eq_range
rawHeightLabel_eq_s
orbitWindowHeight_eq_s_iterateT
orbitWindowHeightSeq_length
orbitWindowHeightSeq_sum_eq_sumS
orbitWindowHeightSeq_sum_ge_of_forall_ge
orbitWindowHeightSeq_take_sum_eq_sumS
orbitWindowHeightSeq_take_length
orbitWindowHeightSeq_get?_eq_some
orbitWindowHeightSeq_take_get?_eq_some
orbitWindowHeightSeq_prefix_sum_ge_of_forall_ge
orbitWindowHeight_eq_of_oddOrbitLabel_eq
orbitWindowHeight_eq_of_collision
orbitWindowHeight_eq_of_same_iterateT
orbitWindowHeightCountEq
orbitWindowHeightCountGe
orbitWindowHeightCountEq_le_window
orbitWindowHeightCountGe_le_window
orbitWindowHeightCountEq_eq_window_of_forall_eq
orbitWindowHeightCountGe_eq_window_of_forall_ge
orbitWindowHeightSeq_sum_ge_countGe_mul_threshold
rawHeightLabel_shift_eq
oddOrbitLabel_injOn_of_pairwiseSeparated
iterateT_eq_of_oddOrbitLabel_eq
oddOrbitLabelsPairwiseSeparated_contradiction_of_same_label_ne_index
same_iterateT_of_oddOrbitLabel_collision
exists_same_iterateT_of_orbitWindowCollision
not_orbitWindowCollision_of_separated
orbitWindowSeparated_contradiction_of_collision
orbitWindowSeparated_or_collision
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

The current window-level split is:

```text
OrbitWindowSeparated n k
or
OrbitWindowCollision n k
```

This is only a finite observation split.  It does not prove that a Collatz
orbit converges or cycles; it merely fixes the two observation modes available
inside a chosen finite window.

The first address-like observation is now the 2-adic height:

```text
rawHeightLabel n = v2 (3n + 1)
orbitWindowHeight n i = rawHeightLabel (oddOrbitLabel n i)
```

The ordered height profile is now explicitly connected to the existing
Collatz accumulated-height API:

```text
(orbitWindowHeightSeq n k).sum = sumS n k
```

This means the Petal observation window can read the same data in two ways:

```text
ordered local profile:
  [height at time 0, height at time 1, ...]

accumulated drift input:
  sumS n k
```

The profile form is useful for address/window diagnostics, while `sumS` is the
existing Collatz side used by drift and growth estimates.

The next small API layer records how to use the profile:

```text
all heights >= threshold
  -> k * threshold <= sumS n k

take r from a k-window, with r <= k
  -> prefix sum = sumS n r

read index i in a k-window, with i < k
  -> the list entry is orbitWindowHeight n i

same orbit label at i and j
  -> same height at i and j
```

This gives the window a usable sequence interface:

```text
local entries
  -> prefix sums
  -> threshold lower bounds
  -> collision/fold height equality
```

The bridge now also has the first occupation-count vocabulary:

```text
orbitWindowHeightCountEq n k h
  = number of entries with height exactly h

orbitWindowHeightCountGe n k threshold
  = number of entries with height at least threshold
```

The current count API is intentionally minimal:

```text
exact-height count <= k
threshold count <= k
all heights equal h
  -> exact-height count = k
all heights >= threshold
  -> threshold count = k

height >= threshold appears c times
  -> c * threshold <= sumS n k
```

This is the first distribution layer.  It does not yet decompose `sumS` by
height classes, but it already gives future drift estimates a direct lower
bound from a threshold regime count.

The bridge theorem

```lean
rawHeightLabel_shift_eq
```

repackages `v2_shift_invariant`: inside a sufficiently large `2^k` shift
block, the raw height label is conserved.  This is the current entry point for
reading Collatz block-shift invariance as a Petal-style address conservation
phenomenon.

This gives a clean place to attach future hypotheses:

```text
orbit labels are usable carrier labels
orbit labels are mapped to prime labels
orbit collision implies a specific fold/cycle condition
2-adic height controls Petal address movement
ordered height profile controls accumulated Collatz drift
height-threshold hypotheses give integer lower bounds for `sumS`
label collisions preserve the next height observation
height occupation counts measure exact and lower-bound regimes
threshold occupation counts give direct lower bounds for `sumS`
```

## Next Candidate Work

The next safe steps are:

```text
1. Connect the ordered height profile to a Petal address/residue reading.
2. Add a window occupation/address transition layer.
3. Refine exact-height counts into distribution estimates for `sumS`.
4. Use threshold occupation lower bounds as the Collatz-side drift input.
5. Test whether an external label transform can turn orbit labels into carrier labels.
6. Only after that, test whether Collatz labels can feed ABC support/rad.
```

The main caution is that Collatz state labels are not prime labels.  Any bridge
to `ABCBridge` must insert an additional label transform or carrier witness
layer before using the Petal radical lower-bound theorems.
