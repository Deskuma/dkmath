# Wallis-Cosmic Growth Route

This note records the growth route after the Wallis-Cosmic finite and limit
bridges.

The goal is not to use Stirling's approximation as the conceptual source.
Instead, DkMath reads the central binomial growth from exact finite products.

## Exact identity

The Lean module `DkMath.Pascal.WallisGrowthBridge` now proves:

```text
centralRatioQ m ^ 2
  = (2*m + 1) * wallisPartialQ m
```

and the cosmic version:

```text
centralRatioQ m ^ 2
  = (2*m + 1) * cosmicPartialQ m
```

This comes from two exact finite facts:

```text
centralRatioQ m * mirrorOddRatioPartialQ m = wallisPartialQ m
centralRatioQ m / mirrorOddRatioPartialQ m = 2*m + 1
```

The second identity is the telescoping mirror ratio.

## Growth reading

The limit module already proves:

```text
wallisPartialQ m -> pi / 2
```

Therefore the squared central ratio has the growth line:

```text
centralRatioQ m ^ 2 ~ pi * m
```

and hence:

```text
centralRatioQ m ~ sqrt (pi * m)
```

Since:

```text
centralRatioQ m = 4^m / Nat.choose (2*m) m
```

inverting gives the central-binomial growth law:

```text
Nat.choose (2*m) m ~ 4^m / sqrt (pi * m)
```

## Next formal checkpoint

The next theorem should be the squared normalized limit:

```lean
Filter.Tendsto
  (fun m : Nat => (((centralRatioQ m : Q) : R) ^ 2 / (m : R)))
  Filter.atTop
  (nhds Real.pi)
```

This should use:

```text
centralRatioQ m ^ 2 = (2*m + 1) * wallisPartialQ m
wallisPartialQ m -> pi / 2
(2*m + 1) / m -> 2
```

The `m = 0` issue is an `atTop` bookkeeping problem, so it should be handled
as a separate no-sorry checkpoint.
