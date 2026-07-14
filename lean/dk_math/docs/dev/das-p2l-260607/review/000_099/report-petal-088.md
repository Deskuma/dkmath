# Report Petal 088: Tail Height Count and Delayed Drift

## Checkpoint

This checkpoint follows `__next_implementation-088.md`.

The previous checkpoint proved that the `3 mod 8` source channel maps into
the shifted tail residue class `1 mod 4`.  This checkpoint converts that tail
residue information back into a height count and then pushes it into the
Collatz accumulated-height budget `sumS`.

## Implemented Lean Surface

File:

```text
lean/dk_math/DkMath/Collatz/PetalBridge.lean
```

New shifted-tail height count:

```lean
orbitWindowHeightCountGeTail
```

New basic count API:

```lean
orbitWindowHeightCountGeTail_le_window
orbitWindowHeightCountGe_succ
orbitWindowHeightCountGeTail_succ
orbitWindowHeightCountGeTail_le_countGe_succ
```

The key inclusion is:

```text
tail CountGe threshold over times 1..k
  <= ordinary CountGe threshold over times 0..k
```

New tail height/residue bridge:

```lean
orbitWindowHeightCountGeTail_two_eq_tailResidueCount_mod4_eq_one
```

New delayed-peeling height bridge:

```lean
orbitWindowResidueCountMod8EqThree_le_tailHeightCountGe_two
```

New drift budget theorems:

```lean
orbitWindowHeightSeq_sum_ge_succ_window_add_tailCountGe_two
orbitWindowHeightSeq_sum_ge_window_add_tailCountGe_two
orbitWindowResidueCountMod8EqThree_delayed_drift
orbitWindowResidueCountMod8EqThree_delayed_drift_strong
```

New restart/localization helpers:

```lean
oddOrbitLabel_zero_eq
oddOrbitLabel_iterateT_zero_eq
sumS_two_steps_ge_three_of_mod_eight_eq_three_at
```

## Main Result

The strong delayed-drift theorem passed:

```lean
theorem orbitWindowResidueCountMod8EqThree_delayed_drift_strong
    (n : OddNat) (k : ℕ) :
    (k + 1) + orbitWindowResidueCountMod8EqThree n k ≤ sumS n (k + 1)
```

Reading:

```text
source window:
  times 0..k-1
  count labels congruent to 3 mod 8

tail window:
  times 1..k
  these source entries force height >= 2

accumulated window:
  times 0..k
  base layer contributes k + 1
  delayed 3 mod 8 events contribute one extra unit each
```

So `3 mod 8` is now a counted delayed-peeling source, not just a pointwise
transition edge.

## Proof Shape

The useful intermediate bridge is:

```lean
orbitWindowHeightCountGeTail_le_countGe_succ
```

This avoids proving a new drift theorem by induction.  Instead:

```text
tail CountGe 2 <= ordinary CountGe 2 over k + 1
ordinary drift theorem:
  (k + 1) + ordinary CountGe 2 <= sumS n (k + 1)
```

Then monotonicity of addition gives the tail version.

This is a good pattern for future shifted-window work:

```text
shifted local count
  -> included in ordinary longer-window count
  -> reuse existing sumS budget theorem
```

## Localized Two-Step Experiment

The two-step theorem was also localized:

```lean
theorem sumS_two_steps_ge_three_of_mod_eight_eq_three_at
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 8 = 3) :
    3 ≤ sumS (iterateT i n) 2
```

This uses the restart identity:

```lean
oddOrbitLabel (iterateT i n) 0 = oddOrbitLabel n i
```

This is useful because future local graph arguments can restart the accelerated
system at any observed time.

## Documentation Sync

Updated:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

The status note now records:

```text
tail height count
tail height/residue bridge
tail inclusion into the ordinary longer window
strong delayed drift from the 3 mod 8 source channel
localized two-step delayed-peeling theorem
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

Candidate A: tail exact-height-one count for the `7 mod 8` retaining channel.

```lean
noncomputable def orbitWindowHeightCountEqTail
    (n : OddNat) (k h : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (orbitWindowHeight n (i + 1) = h))
```

Then:

```text
residueCountMod8EqSeven <= tail CountEq 1
```

This would formalize the obstruction side:

```text
7 mod 8 -> next exact height one
```

Candidate B: two-step `7 -> 7` retention experiment.

```lean
theorem sumS_two_steps_eq_two_of_mod_eight_eq_seven_and_next_mod_eight_eq_seven
    (n : OddNat)
    (h0 : oddOrbitLabel n 0 % 8 = 7)
    (h1 : oddOrbitLabel n 1 % 8 = 7) :
    sumS n 2 = 2
```

This is stronger and more brittle, but it would isolate a true height-one
retention pattern.

Candidate C: define a small finite transition graph vocabulary.

Current edges:

```text
3 mod 8 -> next 1 mod 4 -> next height >= 2
7 mod 8 -> next 3 mod 4 -> next height = 1
```

The next abstraction could name these as source/receiver channels before
expanding to mod `16` or longer paths.
