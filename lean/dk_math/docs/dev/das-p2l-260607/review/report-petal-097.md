# Report Petal 097: Full Pow-Two Residue Partition

## Checkpoint

This checkpoint follows `__next_implementation-097.md`.

The requested target was to make the generic power-of-two residue count usable
as a finite distribution layer:

```lean
orbitWindowResidueCountPow2_sum_eq_window
```

The mathematical reading is:

```text
At fixed depth, every observed odd orbit label belongs to exactly one
residue cell modulo 2^depth.
```

This is the count-level footing needed before normalized frequencies such as
`count / window size` are introduced.

## Implemented Lean Surface

Added in `DkMath.Collatz.PetalBridge`:

```lean
theorem orbitWindowResidueCountPow2_succ
theorem orbitWindowResidueCountPow2Tail_succ
theorem orbitWindowResidueCountPow2_depth_zero_eq_window
theorem orbitWindowResidueCountPow2_eq_zero_of_modulus_le_residue
theorem pow2_residue_indicator_sum_eq_one
theorem orbitWindowResidueCountPow2_sum_eq_window
```

The two successor lemmas record the exact update rule for source-window and
shifted-tail generic residue counts.  The source version is then used by the
full partition proof.

The depth-zero lemma is the sanity check:

```text
mod 1 has only the residue cell 0, so all k labels fall into that cell.
```

The out-of-range lemma records that residue cells beyond `2^depth - 1` have
zero occupation.

The indicator lemma isolates the key finite-distribution fact:

```text
For a single label x, summing over all residue cells gives exactly 1.
```

Finally, induction on the window size gives:

```lean
theorem orbitWindowResidueCountPow2_sum_eq_window
    (n : OddNat) (k depth : Nat) :
    (Finset.range (2 ^ depth)).sum
      (fun residue => orbitWindowResidueCountPow2 n k depth residue) = k
```

## Documentation Sync

Updated:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

The status document now lists the new theorem names and records the generic
pow-two residue count API:

```text
successor formulas
depth-zero cell
out-of-range zero cells
single-label indicator sum
full source residue partition
```

## Inference

This closes the first generic finite partition layer.

Before this checkpoint, the bridge could count specific named cells such as
`1 mod 4`, `3 mod 8`, or `7 mod 8`, and it had a generic `CountPow2` carrier.
After this checkpoint, the generic carrier has a conservation law:

```text
sum of all cells = window size
```

This is the right abstraction boundary for the next phase:

```text
residue occupation count
  -> finite distribution
  -> normalized frequency / density witness
  -> drift or obstruction statement
```

No real-valued frequency has been introduced yet.  The present theorem keeps
the observation layer purely finite and natural-valued.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge
```

Known upstream warning remains unchanged:

```text
DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

No new `sorry` was added to `DkMath.Collatz.PetalBridge`.

## Next Implementation Candidates

The next small Lean target is the tail analogue:

```lean
theorem orbitWindowResidueCountPow2Tail_sum_eq_window
    (n : OddNat) (k depth : Nat) :
    (Finset.range (2 ^ depth)).sum
      (fun residue => orbitWindowResidueCountPow2Tail n k depth residue) = k
```

It should follow the same proof pattern using
`orbitWindowResidueCountPow2Tail_succ`.

The second useful target is a reusable pointwise-to-count helper:

```lean
theorem orbitWindowResidueCountPow2_le_tail_of_pointwise
```

This would compress the repeated pattern:

```text
pointwise source residue transition
  -> source count <= shifted-tail target count
```

Once both exist, the bridge can express local Collatz transition experiments
as finite channel-flow statements rather than one-off count inductions.
