# report-petal-238

## Checkpoint

`petal-238`

## Summary

Implemented Branch B: one small Beam-facing predicate plus one seed-existence
theorem.

The raw theorem statement would have been too large because the local pulse box
contains:

```text
membership
sign transition at three depths
addressed-depth target
height boxes at three depths
jump boxes at two adjacent edges
```

So the implementation introduces a named predicate and proves that every Beam
seed exposes one witness satisfying it.

## Added Predicate

```lean
def SourcePressureBeamCenteredLocalPulseBox
    (n : OddNat) (k r : ℕ)
    (L : List (SourcePressureLocalIslandWitness n k r))
    (W : SourcePressureLocalIslandWitness n k r) : Prop
```

It contains:

```text
W ∈ L
SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0
0 < SourcePressureMarginInt n k (r + W.val)
SourcePressureBeamAddressedDepthTarget L W.val
SourcePressureMarginInt n k (r + W.val + 1) ≤ 0

height box at r + (W.val - 1)
height box at r + W.val
height box at r + W.val + 1

jump box at edge W.val - 1
jump box at edge W.val
```

The predicate deliberately stays local and witness-relative.

## Added Theorem

```lean
theorem exists_sourcePressureBeamPulse_witness_center_local_box_of_seed
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hseed : SourcePressureBeamSeed L) :
    ∃ W : SourcePressureLocalIslandWitness n k r,
      SourcePressureBeamCenteredLocalPulseBox n k r L W
```

This is the local pulse box wrapper expected by cp238:

```text
seed
  -> ∃ W,
       centered local pulse
       inside finite height box
       with finite jump box
```

## Consumed Theorems

The new theorem is a thin composition of:

```lean
exists_sourcePressureBeamPulse_witness_center_margin_signs_of_seed
sourcePressureMarginInt_bounds_window
sourcePressureNetDropInt_bounds_window
```

Interpretation:

- cp235 supplies the centered sign transition.
- cp236 supplies finite local height boxes `[-k, 2k]`.
- cp237 supplies finite adjacent jump boxes `[-3k, 3k]`.

## Important Scope Boundary

This is a finite local pulse box theorem.

It does not claim:

```text
propagation
list-wide coverage
witness-family aggregation
canonical witness selection
overlap repair
disjointness
monotone trend
global Big bounds
Collatz convergence
```

The result only says that one seed exposes one witness whose native pulse has
the local sign, height, and jump diagnostics simultaneously.

## Big / Core / Beam / Gap Classification

- Core:
  the finite definitions and earlier boxed estimates are now reusable:
  margin height `[-k, 2k]` and net jump `[-3k, 3k]`.

- True Beam:
  the seed-level local pulse now has a single public predicate expressing
  sign transition plus finite boxes.

- Boundary:
  the theorem is existential over one witness `W ∈ L` and local to depths
  around `W.val`.

- False Beam:
  no global trend or propagation is obtained merely from the local box.

- Gap:
  the next mathematical question is whether and how boxed local pulses can be
  transported, chained, or blocked.  That is not part of this checkpoint.

## Next Branch Prediction

Two next branches are plausible:

1. Sharpen jump bounds.
   The current `[-3k, 3k]` net-drop box is coarse but robust.  A sharper theorem
   may exist if retention and continuation drops are not independent in a
   local pulse.

2. Begin controlled propagation analysis.
   Now that the local pulse box is packaged, the next propagation theorem can
   consume a single clean predicate rather than separately carrying sign,
   height, and jump facts.

The safer next checkpoint is a controlled propagation-obstruction split:

```text
local pulse box
  -> either a bounded next-step continuation candidate
     or an explicit obstruction/failure predicate
```

That would preserve the current project discipline: prove local transport only
when Lean supplies the hypotheses, and otherwise record the false branch as an
obstruction.

## Verification

Commands run:

```text
lake build DkMath.Collatz.PetalBridge.PressureDecay
lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
rg -n "sorry|admit" <pressure-file-scope>
git diff --check
```

Results:

```text
PressureDecay build: pass
PressureBeam.Pulse build: pass
PressureBeam build: pass
PetalBridge build: pass
no-sorry grep: no matches in inspected pressure scope
git diff --check: pass
```
