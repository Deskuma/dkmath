# Report Petal 087: Collatz Tail Transition Window

## Checkpoint

This checkpoint implements the next-label transition layer requested in
`__next_implementation-087.md`.

The previous checkpoint had already proved the orbit-level transition:

```text
oddOrbitLabel % 8 = 3 -> (T current).val % 4 = 1
oddOrbitLabel % 8 = 7 -> (T current).val % 4 = 3
```

This checkpoint lifts that observation to the actual label sequence
`oddOrbitLabel n (i + 1)`.

## Implemented Lean Surface

File:

```text
lean/dk_math/DkMath/Collatz/PetalBridge.lean
```

New shifted-tail count definitions:

```lean
orbitWindowResidueCountMod4EqOneTail
orbitWindowResidueCountMod4EqThreeTail
```

New basic bounds:

```lean
orbitWindowResidueCountMod4EqOneTail_le_window
orbitWindowResidueCountMod4EqThreeTail_le_window
```

New next-label transition bridge:

```lean
iterateT_succ_eq_T_iterateT
oddOrbitLabel_succ_eq_T_iterateT
oddOrbitLabel_succ_mod_four_eq_one_of_mod_eight_eq_three
oddOrbitLabel_succ_mod_four_eq_three_of_mod_eight_eq_seven
```

New next-height consequences:

```lean
orbitWindowNextHeight_two_le_of_mod_eight_eq_three
orbitWindowNextHeight_eq_one_of_mod_eight_eq_seven
```

New count-level transition inequalities:

```lean
orbitWindowResidueCountMod8EqThree_le_tailMod4EqOne
residueCountMod8EqSeven_le_nextResidueCountMod4EqThree
```

New two-step drift experiment:

```lean
sumS_two_steps_ge_three_of_mod_eight_eq_three
```

## Mathematical Reading

The `3 mod 8` height-one channel is not merely weak peeling.  It is a delayed
peeling edge:

```text
time i:
  oddOrbitLabel n i % 8 = 3
  height = 1

time i + 1:
  oddOrbitLabel n (i + 1) % 4 = 1
  height >= 2
```

Therefore the first two observations already satisfy:

```text
oddOrbitLabel n 0 % 8 = 3 -> 3 <= sumS n 2
```

The `7 mod 8` channel has the complementary behavior:

```text
time i:
  oddOrbitLabel n i % 8 = 7

time i + 1:
  oddOrbitLabel n (i + 1) % 4 = 3
  height = 1
```

Thus the exact height-one layer splits into two different transition edges:

```text
3 mod 8 -> next extra peeling
7 mod 8 -> next exact height-one
```

## Count-Level Interpretation

The new tail counts make the transition statistical:

```text
count(current 3 mod 8 in 0..k-1)
  <= count(next 1 mod 4 in 1..k)

count(current 7 mod 8 in 0..k-1)
  <= count(next 3 mod 4 in 1..k)
```

This is the first finite directed-edge observation for the Collatz Petal
window.  The bridge is no longer only a static occupation table; it now records
one-step flow between residue channels.

## Documentation Sync

Updated:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

The status note now records:

```text
tail residue count definitions
next-label transition theorems
next-height delayed-peeling interpretation
count-level transition inequalities
two-step drift experiment
```

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge
```

The targeted build still reports the existing upstream warning:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean: declaration uses `sorry`
```

No new `sorry` was introduced in this checkpoint.

## Next Implementation Candidates

The next useful step is to turn this one-step edge into a prefix/tail drift
budget.

Candidate A:

```lean
theorem orbitWindowHeightSeq_sum_ge_window_add_tailMod4EqOne
    (n : OddNat) (k : ℕ) :
    k + orbitWindowResidueCountMod4EqOneTail n k ≤ sumS n (k + 1)
```

This should be treated carefully because the tail window is `1..k`, while
`sumS n (k + 1)` observes `0..k`.  It will likely need a small prefix/tail
count bridge.

Candidate B:

```lean
theorem orbitWindowResidueCountMod8EqThree_delayed_drift
    (n : OddNat) (k : ℕ) :
    k + orbitWindowResidueCountMod8EqThree n k ≤ sumS n (k + 1)
```

This would combine:

```text
3 mod 8 count <= next 1 mod 4 tail count
next 1 mod 4 tail count -> height >= 2 on the shifted window
```

Candidate C:

Define shifted-tail height counts:

```lean
noncomputable def orbitWindowHeightCountGeTail
    (n : OddNat) (k threshold : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (threshold <= orbitWindowHeight n (i + 1)))
```

Then prove:

```text
tail CountGe 2 = tail residue mod 4 = 1
mod8EqThree <= tail CountGe 2
```

This is probably the cleanest next bridge before deriving larger drift
inequalities.
