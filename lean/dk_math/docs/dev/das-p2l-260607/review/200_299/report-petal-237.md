# report-petal-237

## Checkpoint

`petal-237`

## Summary

Implemented Branch A and Branch B.

The checkpoint requested finite local jump bounds for retention drop,
continuation drop, and net pressure drop.  The actual definitions in
`PressureDecay.lean` are edge-indexed by `j`, so the implemented public surface
keeps the adjacent-edge parameter:

```lean
SourceRetentionDropInt n k r j
SourceContinuationDropInt n k r j
SourcePressureNetDropInt n k r j
```

This is the correct API shape for the current source code: `r` is the base
pressure depth, while `j` selects the adjacent transition
`r + j -> r + j + 1`.

## Implemented Theorems

### Retention drop

```lean
theorem sourceRetentionDropInt_le_window
    (n : OddNat) (k r j : ℕ) :
    SourceRetentionDropInt n k r j ≤ (k : ℤ)

theorem neg_window_le_sourceRetentionDropInt
    (n : OddNat) (k r j : ℕ) :
    - (k : ℤ) ≤ SourceRetentionDropInt n k r j

theorem sourceRetentionDropInt_bounds_window
    (n : OddNat) (k r j : ℕ) :
    - (k : ℤ) ≤ SourceRetentionDropInt n k r j ∧
      SourceRetentionDropInt n k r j ≤ (k : ℤ)
```

Meaning:

```text
retention adjacent jump ∈ [-k, k]
```

The proof uses the existing finite-window bound
`orbitWindowRetentionMassPow2_le_window`.

### Continuation drop

```lean
theorem sourceContinuationDropInt_le_window
    (n : OddNat) (k r j : ℕ) :
    SourceContinuationDropInt n k r j ≤ (k : ℤ)

theorem neg_window_le_sourceContinuationDropInt
    (n : OddNat) (k r j : ℕ) :
    - (k : ℤ) ≤ SourceContinuationDropInt n k r j

theorem sourceContinuationDropInt_bounds_window
    (n : OddNat) (k r j : ℕ) :
    - (k : ℤ) ≤ SourceContinuationDropInt n k r j ∧
      SourceContinuationDropInt n k r j ≤ (k : ℤ)
```

Meaning:

```text
continuation adjacent jump ∈ [-k, k]
```

The proof uses the existing finite-window bound
`orbitWindowContinuationSiblingMassPow2_le_window`.

### Net pressure drop

```lean
theorem sourcePressureNetDropInt_le_three_mul_window
    (n : OddNat) (k r j : ℕ) :
    SourcePressureNetDropInt n k r j ≤ 3 * (k : ℤ)

theorem neg_three_mul_window_le_sourcePressureNetDropInt
    (n : OddNat) (k r j : ℕ) :
    - (3 * (k : ℤ)) ≤ SourcePressureNetDropInt n k r j

theorem sourcePressureNetDropInt_bounds_window
    (n : OddNat) (k r j : ℕ) :
    - (3 * (k : ℤ)) ≤ SourcePressureNetDropInt n k r j ∧
      SourcePressureNetDropInt n k r j ≤ 3 * (k : ℤ)
```

Meaning:

```text
net pressure adjacent jump ∈ [-3k, 3k]
```

This follows from:

```lean
SourcePressureNetDropInt
  = SourceRetentionDropInt - 2 * SourceContinuationDropInt
```

and the two component jump boxes.

## Height Bounds vs Jump Bounds

cp236 established finite local height bounds:

```text
SourcePressureMarginInt n k r ∈ [-k, 2k]
```

Those theorems bound the pressure margin at a single depth.

cp237 establishes finite local jump bounds:

```text
SourceRetentionDropInt n k r j      ∈ [-k, k]
SourceContinuationDropInt n k r j   ∈ [-k, k]
SourcePressureNetDropInt n k r j    ∈ [-3k, 3k]
```

These theorems bound one adjacent transition.  They do not claim propagation,
coverage, global descent, or convergence.

## Big / Core / Beam / Gap Classification

- Core:
  existing finite-window mass bounds:
  `orbitWindowRetentionMassPow2_le_window` and
  `orbitWindowContinuationSiblingMassPow2_le_window`.

- True Beam:
  the finite jump boxes are now theoremized.  They give a verified local
  diagnostic for each adjacent pressure step.

- Boundary:
  the bound is local to `(r, j)` and to the finite observation window `k`.

- False Beam:
  no monotonicity, no global trend, and no coverage theorem follows from these
  bounds alone.

- Gap:
  the interaction between cp235 sign transition, cp236 height box, and cp237
  jump box is not yet bundled into a single pulse diagnostic theorem.

## Next Branch Prediction

The next natural branch is to combine:

```text
cp235 sign transition
+ cp236 height box
+ cp237 jump box
```

into a thin local pulse wrapper.

That wrapper should stay local and witness-based.  A useful target would expose
one seed/pulse witness together with:

```text
left margin sign
center margin sign
right margin sign
margin height box
net-drop jump box
```

The wrapper should not claim propagation, list coverage, overlap repair,
canonical witness selection, or Collatz convergence.

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
