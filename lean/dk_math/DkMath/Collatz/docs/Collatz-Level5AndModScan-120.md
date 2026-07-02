# Collatz Level-5 And Mod Scan 120

Checkpoint 120 has two purposes:

```text
1. extend the concrete delayed-reservoir tower to level 5
2. stop climbing blindly by adding a Python observation table through mod 1024
```

The Lean side remains conservative.  The Python side is an observation tool
that helps choose the next theorem targets.

## Level-5 Tower Extension

Checkpoint 119 fixed:

```text
tail 63 mod 64
  -> next tail 31 mod 64 + next tail 63 mod 64
```

Checkpoint 120 adds:

```text
tail 127 mod 128
  -> next tail 63 mod 128 + next tail 127 mod 128
```

New shifted-tail counts:

```lean
orbitWindowResidueCountMod256EqOneHundredTwentySevenTail
orbitWindowResidueCountMod256EqTwoHundredFiftyFiveTail
```

Static split:

```lean
tailResidueCountMod128EqOneHundredTwentySeven_split_mod256
```

Reading:

```text
tail 127 mod 128
  = tail 127 mod 256
    + tail 255 mod 256
```

Pointwise aliases:

```lean
oddOrbitLabel_succ_mod128_eq63_of_mod256_eq127
oddOrbitLabel_succ_mod128_eq127_of_mod256_eq255
```

Count-level recursion edge:

```lean
tailMod128Eq127_le_nextTailMod128Eq63_add_nextTailMod128Eq127
```

Level aliases:

```lean
TailRemainderLevel5
TailFallingLevel5
tailRemainderLevel4_static_split
tailRemainderLevel4_step_grammar
tailRemainderLevel5_step_grammar
```

## Pressure Count To Witness

Checkpoint 119 could extract pressure at a selected depth:

```text
SourceContinuationPressureOnRange n k r len
  and j < len
  -> local pressure at r+j
```

Checkpoint 120 adds the count-facing entrance:

```lean
exists_sourcePressureDepth_of_pressureDepthCount_pos
exists_positive_sourceContinuationMass_of_pressureDepthCount_pos
exists_positive_sourceContinuationMass_of_outrunsMoreThanHalf
```

The important reading is:

```text
positive pressure-depth count
  -> there exists a selected depth
  -> source continuation mass is positive there
```

This is deliberately existential.  It does not claim that several selected
depths are independent.  The independence/disjointness problem remains a later
budget theorem.

## Python Observation Window

The new script is:

```text
python/Collatz/PetalBridge/retention_tower_mod_scan.py
```

Default output:

```text
python/Collatz/PetalBridge/results/retention_tower_mod_scan.csv
python/Collatz/PetalBridge/results/retention_tower_mod_scan.md
```

The scan checks the exact height-one residue law through `mod 1024`.

For depth `d >= 3`:

```text
parent:       2^d - 1 mod 2^d
recovery:     2^d - 1 mod 2^(d+1)
continuation: 2^(d+1) - 1 mod 2^(d+1)

T1(recovery)     = 2^(d-1) - 1 mod 2^d
T1(continuation) = 2^d - 1 mod 2^d
```

where:

```text
T1(x) = (3*x + 1) / 2
```

Observed levels:

```text
7 mod 16     -> 3 mod 8
15 mod 16    -> 7 mod 8
15 mod 32    -> 7 mod 16
31 mod 32    -> 15 mod 16
31 mod 64    -> 15 mod 32
63 mod 64    -> 31 mod 32
63 mod 128   -> 31 mod 64
127 mod 128  -> 63 mod 64
127 mod 256  -> 63 mod 128
255 mod 256  -> 127 mod 128
255 mod 512  -> 127 mod 256
511 mod 512  -> 255 mod 256
511 mod 1024 -> 255 mod 512
1023 mod 1024 -> 511 mod 512
```

All checked rows matched the expected law.

## Inference

The table confirms that the delayed-reservoir tower is not a special accident
of low modulus.  The existing generic Lean theorems:

```lean
next_recovery_residue_of_mod
next_continuation_residue_of_mod
oddOrbitLabel_succ_recovery_residue_of_mod
oddOrbitLabel_succ_continuation_residue_of_mod
```

are the right long-term surface.

Concrete aliases are still useful at active frontier levels because they make
the proof state readable:

```text
127 mod 256 -> 63 mod 128
255 mod 256 -> 127 mod 128
```

but future levels should be promoted only when a downstream theorem needs that
named level.

## Next Work

The tower can continue mechanically, but the next mathematical gain is not
another named modulus.  The better target is:

```text
selected pressure depths
  + no-overlap / separated address condition
  -> non-duplicated tower-entry budget
```

The new existential pressure-count bridge gives the first selected local depth.
The next step is to determine which separation predicate can safely turn
several selected depths into several independent budget entries.
