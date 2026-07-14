# Research Report and Next Implementation: No.082 cp

## Current status: `height >= 1` and the three-layer experiment are closed

The previous target has been implemented in `DkMath.Collatz.PetalBridge`.

Closed core API:

```lean
orbitWindowHeight_one_le
orbitWindowHeightCountGe_one_eq_window
orbitWindowHeightSeq_sum_ge_window_add_countGe_two
orbitWindowHeightPrefixCountGe_one_eq
orbitWindowHeightPrefix_sum_ge_window_add_countGe_two
```

Closed extra API:

```lean
orbitWindowHeightCountGe_antitone
```

Closed experiment:

```lean
orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two_add_countGe_three
```

This means the current Lean state has:

```text
CountGe 1 = k
k + CountGe 2 <= sumS n k
CountGe 1 + CountGe 2 + CountGe 3 <= sumS n k
```

The next implementation should therefore move from fixed two/three-layer
experiments to a general finite layer-cake theorem.

## Next target: finite layer-cake helper

Start with the finite threshold-count helper:

```lean id="z4i2au"
private theorem range_threshold_count_le
    (H x : ℕ) :
    ((Finset.range H).filter (fun t => t + 1 ≤ x)).card ≤ x
```

Meaning:

```text id="fo0cre"
Among thresholds 1, 2, ..., H, at most x thresholds are <= x.
```

This is the local per-entry bound needed for finite layer-cake:

```text
one height x contributes to the layers t+1 <= x,
and the number of such layers is <= x.
```

## Main theorem candidate

Then try:

```lean id="cmslrx"
theorem orbitWindowHeightSeq_sum_ge_sum_countGe_range
    (n : OddNat) (k H : ℕ) :
    (Finset.range H).sum
        (fun t => orbitWindowHeightCountGe n k (t + 1))
      ≤ sumS n k
```

Meaning:

```text id="swywnk"
CountGe 1 + CountGe 2 + ... + CountGe H <= sumS
```

This theorem generalizes the currently proved two-layer and three-layer
experimental theorems.

## Prefix generalization after the main theorem

If the full-window theorem closes, add the prefix version:

```lean
theorem orbitWindowHeightPrefix_sum_ge_sum_countGe_range
    (n : OddNat) {r k H : ℕ} (hr : r ≤ k) :
    (Finset.range H).sum
        (fun t => orbitWindowHeightPrefixCountGe n k r (t + 1))
      ≤ sumS n r
```

This should rewrite prefix counts to standalone counts using:

```lean
orbitWindowHeightPrefixCountGe_eq_countGe
```

## Collatz-specific corollary

Once general finite layer-cake exists, specialize the first layer:

```text
CountGe 1 = k
```

For `H >= 1`, this should produce:

```text
k + CountGe 2 + ... + CountGe H <= sumS n k
```

This is the route from local occupation statistics to a drift budget.

## Implementation order

Recommended order:

```text id="ryo4pz"
1. range_threshold_count_le
2. orbitWindowHeightSeq_sum_ge_sum_countGe_range
3. orbitWindowHeightPrefix_sum_ge_sum_countGe_range
4. Collatz-specific corollary with CountGe 1 = k
```
