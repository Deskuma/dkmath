# Collatz Frequency Height Bridge 113

## Purpose

Checkpoint 113 begins the route from cause-side frequency toward the original
Collatz height and drift data.

It does not yet prove a new drift lower bound.  Instead, it makes the existing
frequency layer easier to consume from later height arguments.

The key route is:

```text
cause-side outruns-heavy
  -> descriptive pressure-heavy
  -> controlled/pressure count imbalance
  -> positive pressure count
  -> future height-count lower bound
```

## New Cause-To-Pressure Aliases

Source:

```lean
sourcePressureMoreThanHalf_of_outrunsMoreThanHalf
```

Tail:

```lean
tailPressureMoreThanHalf_of_outrunsMoreThanHalf
```

These are one-way aliases extracted from the checkpoint 112 equivalences:

```lean
sourceOutrunsMoreThanHalf_iff_pressureMoreThanHalf
tailOutrunsMoreThanHalf_iff_pressureMoreThanHalf
```

They let later proofs state the hypothesis in cause-side terms and immediately
use the descriptive pressure-frequency API.

## Count Imbalance

The next bridge consumes the existing pressure-more-than-half comparison
theorems:

```lean
sourceControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf
tailControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf
```

These say:

```text
if outruns is more than half of the depth range,
then pressure depths outnumber controlled depths.
```

This is descriptive count imbalance, but triggered by a cause-side hypothesis.

## Positive Pressure Count

Checkpoint 113 also records the minimal existence consequence:

```lean
sourcePressureDepthCount_pos_of_outrunsMoreThanHalf
tailPressureDepthCount_pos_of_outrunsMoreThanHalf
```

These are useful when a later proof only needs:

```text
there exists at least one pressure depth
```

rather than a full count imbalance.

## Recovery-Side Partition Test

The checkpoint also adds partition-consumption lemmas for the opposite side:

```lean
sourceDominanceDepthCount_pos_of_outrunsAtMostHalf_and_not_all_outruns
tailDominanceDepthCount_pos_of_outrunsAtMostHalf_and_not_all_outruns
```

The original experimental shape included a separate `0 < len` hypothesis.
Lean showed that this hypothesis is unnecessary: the assumption

```text
outrunsDepthCount < len
```

already excludes the empty-range obstruction.  The final API therefore uses
only the stronger and more informative not-all-outruns hypothesis.

## Existing Height Hooks

The search pass found the current landing points for a future height bridge:

```lean
orbitWindowHeightSeq_sum_eq_sumS
orbitWindowHeightSeq_sum_ge_of_forall_ge
orbitWindowHeightSeq_sum_ge_countGe_mul_threshold
orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two
orbitWindowHeightSeq_sum_ge_sum_countGe_range
orbitWindowHeightSeq_sum_ge_window_add_sum_countGe_tail
orbitWindowHeightSeq_sum_ge_window_add_of_countGe_two_ge
orbitWindowHeightSeq_sum_ge_window_add_tailCountGe_two
orbitWindowHeightSeq_sum_ge_succ_window_add_tailCountGe_two
```

The low residue bridges are also already present:

```lean
orbitWindowHeightCountGe_two_eq_residueCount_mod4_eq_one
orbitWindowHeightCountGeTail_two_eq_tailResidueCount_mod4_eq_one
orbitWindowHeightCountGe_three_eq_residueCount_mod8_eq_five
orbitWindowHeightSeq_sum_ge_window_add_of_residue_mod4_count_ge
orbitWindowHeightSeq_sum_ge_window_add_countGe_two_add_of_residue_mod8_count_ge
```

This means the missing bridge is more specific:

```text
pressure-heavy or outruns-heavy depth range
  -> lower bound on a source/tail height count
```

Once that exists, the `sumS` lower-bound API can consume it.

## Next Candidate

The next checkpoint should search for a theorem connecting pressure/retention
mass to one of these height-count objects:

```text
orbitWindowHeightCountGe n k 2
orbitWindowHeightCountGeTail n k 2
orbitWindowResidueCountMod4EqOne n k
orbitWindowResidueCountMod4EqOneTail n k
```

The strongest likely near-term route is tail-facing:

```text
pressure or continuation mass
  -> tail retention / tail residue mass
  -> tail height >= 2 count
  -> sumS n (k + 1) lower bound
```

This keeps the argument in finite `Nat` arithmetic and avoids importing real
drift estimates too early.
