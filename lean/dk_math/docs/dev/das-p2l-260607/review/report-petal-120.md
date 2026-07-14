# Report Petal 120

## Summary

Checkpoint 120 advanced two tracks:

```text
Lean:
  level-5 delayed-reservoir tower
  pressure-count positive -> selected local tower-entry witness

Python:
  mod 1024 retention-tower scan
  CSV and Markdown observation table
```

The main result is that the concrete tower can still be climbed, but the Python
table makes it clear that future progress should not depend on naming every
modulus by hand.  The stronger next direction is selected-depth accounting with
an explicit no-overlap or separated-address condition.

## Lean Changes

File:

```text
lean/dk_math/DkMath/Collatz/PetalBridge.lean
```

### New Level-5 Tail Counts

Added:

```lean
orbitWindowResidueCountMod256EqOneHundredTwentySevenTail
orbitWindowResidueCountMod256EqTwoHundredFiftyFiveTail
```

These count shifted-tail labels in:

```text
127 mod 256
255 mod 256
```

They refine the previous continuing channel:

```text
127 mod 128
```

### New Level Aliases

Added:

```lean
TailRemainderLevel5
TailFallingLevel5
```

Readings:

```text
TailRemainderLevel5 = shifted-tail 127 mod 128
TailFallingLevel5   = shifted-tail 63 mod 128
```

### Static Split

Added:

```lean
tailResidueCountMod128EqOneHundredTwentySeven_split_mod256
tailRemainderLevel4_static_split
```

Meaning:

```text
tail 127 mod 128
  = tail 127 mod 256
    + tail 255 mod 256

level 4 remainder
  = level 5 falling + level 5 remainder
```

### Orbit-Level Transition Aliases

Added:

```lean
oddOrbitLabel_succ_mod128_eq63_of_mod256_eq127
oddOrbitLabel_succ_mod128_eq127_of_mod256_eq255
```

Meaning:

```text
127 mod 256 -> next 63 mod 128
255 mod 256 -> next 127 mod 128
```

These are concrete aliases over the raw arithmetic anchors:

```lean
next_mod_onehundredtwentyeight_of_mod_twohundredfiftysix_eq_onehundredtwentyseven
next_mod_onehundredtwentyeight_of_mod_twohundredfiftysix_eq_twohundredfiftyfive
```

### Count Recursion Edge

Added:

```lean
tailMod128Eq127_le_nextTailMod128Eq63_add_nextTailMod128Eq127
tailRemainderLevel4_step_grammar
tailRemainderLevel5_step_grammar
```

Meaning:

```text
tail 127 mod 128
  -> next tail 63 mod 128 + next tail 127 mod 128
```

This is the level-5 version of the delayed-reservoir recursion.

## Pressure Count Witness

Added:

```lean
exists_sourcePressureDepth_of_pressureDepthCount_pos
exists_positive_sourceContinuationMass_of_pressureDepthCount_pos
exists_positive_sourceContinuationMass_of_outrunsMoreThanHalf
```

This closes the safe existence bridge:

```text
0 < sourceContinuationPressureDepthCount
  -> exists selected local pressure depth
  -> exists positive source continuation mass
```

and:

```text
SourceOutrunsMoreThanHalfOnDepthRange
  -> exists positive source continuation mass
```

This theorem is deliberately existential.  It does not claim that several
selected depths can be counted independently.

## Python Observation

New script:

```text
python/Collatz/PetalBridge/retention_tower_mod_scan.py
```

Generated:

```text
python/Collatz/PetalBridge/results/retention_tower_mod_scan.csv
python/Collatz/PetalBridge/results/retention_tower_mod_scan.md
```

Command used:

```text
python3 python/Collatz/PetalBridge/retention_tower_mod_scan.py --max-modulus 1024
```

Observed law:

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

Observed rows through `mod 1024` all matched.

## Data Table

Source:

```text
python/Collatz/PetalBridge/results/retention_tower_mod_scan.csv
```

Compact view:

```text
d=3:  7 mod 16      -> 3 mod 8,    15 mod 16     -> 7 mod 8
d=4:  15 mod 32     -> 7 mod 16,   31 mod 32     -> 15 mod 16
d=5:  31 mod 64     -> 15 mod 32,  63 mod 64     -> 31 mod 32
d=6:  63 mod 128    -> 31 mod 64,  127 mod 128   -> 63 mod 64
d=7:  127 mod 256   -> 63 mod 128, 255 mod 256   -> 127 mod 128
d=8:  255 mod 512   -> 127 mod 256, 511 mod 512  -> 255 mod 256
d=9:  511 mod 1024  -> 255 mod 512, 1023 mod 1024 -> 511 mod 512
```

## Documentation Updated

Updated:

```text
lean/dk_math/DkMath/Collatz/README.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

Added:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-Level5AndModScan-120.md
```

## Verification

Passed:

```text
python3 python/Collatz/PetalBridge/retention_tower_mod_scan.py --max-modulus 1024
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge.lean
git diff --check -- <touched checkpoint 120 files>
```

The rebuilt `DkMath.Collatz.PetalBridge` produced no local warning after
shortening the new level-5 theorem name and removing an unused simp argument.

The `rg` no-sorry check returned no matches for `PetalBridge.lean`.

Known unrelated warning remains:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

## Inference

The mod scan shows that the delayed-reservoir law is structurally stable at
least through `mod 1024`, and the Lean file already contains generic theorems
for the underlying residue motion.

Therefore, the next high-value target is not another concrete level name.  The
next target is the accounting problem:

```text
pressureDepthCount positive / large
  -> selected local depths
  -> independent or non-overlapping tower-entry budget
```

Checkpoint 120 supplies the first selected local witness.  A future checkpoint
should decide which separation predicate controls duplicate use of the same
orbit-window mass.

## Suggested Next Implementation

Do not immediately add level 6 unless a reviewer specifically wants another
concrete smoke test.

The better next theorem family is:

```lean
def SelectedSourcePressureDepths ...

theorem selectedSourcePressureDepth_mem_iff ...
theorem selectedSourcePressureDepth_count_eq_pressureDepthCount ...
```

or, if list packaging feels too early, stay thinner:

```lean
theorem exists_two_sourcePressureDepths_of_two_le_pressureDepthCount
```

but only if the resulting two depths are still treated as selected witnesses,
not as independent budget carriers.

The missing condition to investigate is:

```text
selected depths are address-separated
or selected tower-entry target channels are disjoint
or one selected depth is enough for the immediate drift theorem
```

This is the next contract point between the pressure-count side and the
delayed-reservoir tower side.
