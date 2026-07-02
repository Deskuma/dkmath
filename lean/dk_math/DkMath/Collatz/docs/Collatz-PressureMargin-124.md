# Collatz Pressure Margin - Checkpoint 124

Checkpoint 124 investigates whether selected pressure depths form a prefix.

The tempting conjecture was:

```text
deep selected pressure
  -> shallow selected pressure
```

Checkpoint 124 does not prove this.  Instead, it separates what is now proved
from what fails experimentally.

## Retention Nesting

Checkpoint 123 proved nesting for continuation carriers.  Checkpoint 124 adds
the retention counterpart.

Pointwise theorem:

```lean
retention_allOnes_mod_pow_two_of_le
```

Source count theorem:

```lean
sourceRetentionMass_anti_mono_depth
```

Tail count theorem:

```lean
tailRetentionMass_anti_mono_depth
```

Together these say:

```text
deeper all-ones retention mass <= shallower all-ones retention mass
```

This is a carrier inclusion theorem, not a pressure theorem.

## Pressure Margin

Pressure is a ratio condition:

```text
retention mass < 2 * continuation mass
```

To avoid truncated natural subtraction, checkpoint 124 introduces the
integer-valued margin:

```lean
SourcePressureMarginInt
```

with bridge theorem:

```lean
isSourcePressureDepth_iff_margin_pos
```

Meaning:

```text
IsSourcePressureDepth n k r j
  <-> 0 < SourcePressureMarginInt n k (r+j)
```

This is the correct API for future pressure-prefix and pressure-frontier
experiments.

## Prefix Predicate

Checkpoint 124 also adds a thin predicate:

```lean
SelectedPressurePrefix
```

Basic API:

```lean
selectedPressurePrefix_zero
selectedPressurePrefix_le_len
isSourcePressureDepth_of_selectedPressurePrefix
selectedPressurePrefix_of_pressureOnRange
```

This is intentionally light.  It records what a prefix means, but it does not
claim that arbitrary selected depths automatically form a prefix.

## Python Prefix Scan

New experiment:

```text
python/Collatz/PetalBridge/selected_pressure_prefix_scan.py
python/Collatz/PetalBridge/results/selected_pressure_prefix_scan.csv
python/Collatz/PetalBridge/results/selected_pressure_prefix_scan.md
```

Default scan:

```text
odd n <= 9999
steps = 128
r_start = 2
depth_len = 10
depths 2..11
```

Observed:

```text
rows: 5000
nonempty selected rows: 2681
nonempty prefix rows: 2492 / 2681
prefix failure rows: 189
max selected count: 10
max selected depth: 11
max frontier depth: 12
```

Example failure:

```text
n = 1567
selected depths: 3
missing depth: 2
margins: 2:-2; 3:1; 4:0; 5:-1; ...
```

This shows that the checkpoint 123 prefix observation was window-limited.

## Interpretation

The proved theorem is:

```text
carrier nesting
```

The disproved or unsupported theorem is:

```text
unconditional pressure prefix
```

The reason is that pressure is a comparison between two nested quantities.
Both continuation and retention masses shrink with depth, but their ratio need
not be monotone.

The next useful theorem should therefore be conditional:

```text
deep positive pressure margin
  + margin/retention control between shallow and deep layers
  -> shallow selected pressure
```

or it should explicitly formalize the obstruction:

```text
deeper pressure can be positive while shallower pressure margin is nonpositive
```

Checkpoint 124 therefore redirects the path from an unconditional prefix theorem
to margin-controlled pressure-frontier theory.

## Checkpoint 125 Follow-up

Checkpoint 125 implements the obstruction surface suggested here.

New names:

```lean
SourcePressurePrefixFailure
sourcePressurePrefixFailure_iff_margin
not_selectedPressurePrefix_of_prefixFailure
SourcePressureSelectedSetDownClosed
downClosed_iff_no_prefixFailure
```

The intended reading is:

```text
prefix failure
  = shallow margin <= 0 and deeper margin > 0
```

This makes non-prefix pressure profiles first-class data.  Future work should
classify these failures by margin jump, retention drop, and continuation drop
before proposing another monotonicity theorem.
