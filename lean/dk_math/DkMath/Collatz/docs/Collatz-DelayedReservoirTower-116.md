# Collatz Delayed Reservoir Tower 116

Checkpoint 116 builds the first recursive edge of the delayed-reservoir tower.

Checkpoint 115 established:

```text
tail exact height 1
  = tail 3 mod 8
    + tail 7 mod 8
```

with the reading:

```text
3 mod 8:
  delayed-peeling color

7 mod 8:
  continuing color
```

Checkpoint 116 asks what happens to the continuing color.

## Static Refinement

The continuing `7 mod 8` color splits into two children modulo `16`:

```lean
orbitWindowResidueCountMod16EqSevenTail
orbitWindowResidueCountMod16EqFifteenTail
tailResidueCountMod8EqSeven_split_mod16_seven_fifteen
```

Conceptually:

```text
tail 7 mod 8
  = tail 7 mod 16
    + tail 15 mod 16
```

The `7 mod 16` child is the next delayed-peeling child.
The `15 mod 16` child is the next continuing child.

## Dynamic Recursion Edge

The pointwise theorem already existed:

```lean
orbitWindowNextHeight_eq_one_of_mod_eight_eq_seven
```

Checkpoint 116 lifts it to count level:

```lean
tailMod8Seven_le_nextTailHeightCountEq_one
```

This says:

```text
tail 7 mod 8 at this step
  -> next tail exact height 1
```

Using the checkpoint 115 split again gives:

```lean
tailMod8Seven_le_nextTailMod8Three_add_nextTailMod8Seven
```

So:

```text
tail 7 mod 8
  -> next tail 3 mod 8 + next tail 7 mod 8
```

This is the first theorem-level recursive edge of the delayed-reservoir tower.

## One-Step Grammar

The combined grammar is:

```lean
tailExactHeightOneReservoir_step_grammar
```

It reads:

```text
current tail exact height 1
  <= next tail height >= 2
     +
     next tail exact height 1
```

This is a finite count inequality.  It does not assert that every individual
entry is independent or injective; it packages the already-proved color
transitions as a count-level budget.

## Budget With Remainder

The stronger budget keeps the continuing color visible:

```lean
tailExactHeightOneReservoir_budget_with_remainder
```

Reading:

```text
base layer + current exact-height-one reservoir
  <= next accumulated sumS
     +
     current 7 mod 8 continuing remainder
```

The source-continuation version is:

```lean
sourceContinuationMass_depth_two_delayed_budget_with_tailSeven_remainder
```

Reading:

```text
base layer + source continuation mass at depth 2
  <= next accumulated sumS
     +
     tail 7 mod 8 continuing remainder
```

This is the useful compromise discovered at this checkpoint:

```text
do not claim that all continuation mass immediately peels;
charge the delayed-peeling part to sumS and carry the continuing part as an
explicit remainder.
```

## Interpretation

The delayed-reservoir tower is no longer just a visual metaphor.

The theorem-supported local grammar is:

```text
exact-height-one reservoir
  -> falling color
  -> continuing color

continuing color
  -> next reservoir
  -> falling color
  -> continuing color
```

The next likely resolution step is:

```text
tail 15 mod 16
  -> split into tail 15 mod 32 and tail 31 mod 32
```

and then prove the matching recursive edge.

## Next Targets

Useful next theorem families:

```text
1. tail 15 mod 16 split modulo 32
2. count-level transition from tail 15 mod 16 to next tail reservoir
3. general finite remainder tower for levels 0, 1, 2
```

The current advice is to add one concrete level at a time.  The low-resolution
API is still being discovered, and premature generalization may hide the
usable theorem names.
