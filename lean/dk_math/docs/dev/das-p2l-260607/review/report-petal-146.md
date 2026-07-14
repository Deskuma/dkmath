# report-petal-146

Date: 2026-07-04

## Checkpoint

Implemented the first `PressureAccounting` experiment for
`DkMath.Collatz.PetalBridge`.

The goal was to move from address projections to local interval accounting:
an interval-pulse address should expose endpoint signs, boundary net-drop
signs, and a finite telescoping balance sheet.

This checkpoint remains local.  It does not introduce maximality, uniqueness,
coverage, prefix behavior, or Collatz convergence.

## Code Changes

Added:

- `lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean`

Updated:

- `lean/dk_math/DkMath/Collatz/PetalBridge.lean`

The aggregate file now imports `DkMath.Collatz.PetalBridge.PressureAccounting`.

## Endpoint Facts Added

For an address

```lean
A : SourcePressureIntervalPulseAddress n k r
```

the following endpoint facts were added:

- `sourcePressureIntervalPulseAddress_start_margin_pos`
- `sourcePressureIntervalPulseAddress_end_margin_pos`
- `sourcePressureIntervalPulseAddress_before_start_nonpos`
- `sourcePressureIntervalPulseAddress_after_end_nonpos`

These make the interval-pulse address readable as:

```text
before start: nonpositive
start:        positive
end:          positive
after end:    nonpositive
```

## Boundary Net-Drop Sign Facts Added

The local crossing/falling forms now have direct signed net-drop consequences:

- `sourcePressureIntervalPulseAddress_left_netDrop_pos`
- `sourcePressureIntervalPulseAddress_right_netDrop_neg`

The left theorem is the integer fact:

```text
M <= 0 and 0 < M + Delta  imply  0 < Delta
```

The right theorem is the integer fact:

```text
0 < M and M + Delta <= 0  imply  Delta < 0
```

## Generic Telescoping Theorem

Proved:

```lean
theorem sourcePressureMargin_add_len_eq_start_add_sum_netDrop
    (n : OddNat) (k r a len : Nat) :
    SourcePressureMarginInt n k (r + a + len) =
      SourcePressureMarginInt n k (r + a) +
        (Finset.range len).sum (fun i =>
          SourcePressureNetDropInt n k r (a + i))
```

The originally suggested shape used `r + (a + len)`.  Lean naturally normalized
the induction target to `r + a + len`, so this accepted theorem uses that form.
The address-level specialization below restores the grouped endpoint shape
where useful.

## Address-Level Accumulated Accounting

Proved:

- `sourcePressureIntervalPulseAddress_margin_after_eq_start_add_sum_netDrop`
- `sourcePressureIntervalPulseAddress_sum_netDrop_neg`

The main interval accounting result is:

```lean
theorem sourcePressureIntervalPulseAddress_sum_netDrop_neg
    {n : OddNat} {k r : Nat}
    (A : SourcePressureIntervalPulseAddress n k r) :
    (Finset.range A.len).sum (fun i =>
      SourcePressureNetDropInt n k r (A.start + i)) < 0
```

This confirms the intended reading:

```text
positive pulse
  -> finite interval with negative accumulated net pressure drive
```

## Notes

The file intentionally uses explicit `Finset.sum` notation rather than
`∑ i in ...`, because this project has prior notes that the binder notation can
be parser-fragile in fresh files.  The final theorem statements remain ordinary
finite sums over `Finset.range`.

## Verification

Passed:

- `lake build DkMath.Collatz.PetalBridge.PressureDecay`
- `lake build DkMath.Collatz.PetalBridge.PressureFrontier`
- `lake build DkMath.Collatz.PetalBridge.PressureAccounting`
- `lake build DkMath.Collatz.PetalBridge`
- `rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureDecay.lean`
- `rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean`
- `rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean`
- `git diff --check`

The three `rg` commands returned no matches.  The aggregate build still reports
the pre-existing unrelated warning that
`DkMath.NumberTheory.ZsigmondyCyclotomicResearch` contains a declaration using
`sorry`.

## Next Implementation Candidates

The next natural step is to build a small interval-accounting carrier around
the accepted telescoping theorem.  Good candidates:

- bundle the endpoint signs and negative accumulated net-drop into one theorem,
- define a thin `SourcePressureAccountedInterval` predicate for later finite
  collections,
- or connect a list of interval-pulse addresses to total pressure-drive
  accounting, without claiming coverage or maximality.

The safe next move is still local: reuse address witnesses as carriers and only
sum over intervals that are explicitly provided.
