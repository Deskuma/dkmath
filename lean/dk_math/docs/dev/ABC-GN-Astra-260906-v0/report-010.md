# LUNA-010 — realized-modulus dyadic bookkeeping

## Scope and files

This checkpoint freezes exact finite shell bookkeeping for the realized cubic
modulus space. It does not estimate shell counts or assert an incidence
theorem.

Changed production files:

- `DkMath/ABC/GNExcessCubicRealizedDyadic.lean`
- `DkMath/ABC.lean` (public import)

Changed campaign records:

- `README.md`, `ROADMAP.md`, `validation-010.txt`, and this report.

## Shell objects

`GNExcessCubicRealizedLargeModulusShell X D` is the finite filter of realized
moduli in the half-open interval `[D,2D)`. Its membership theorem exposes both
the realized-space condition and the two endpoint inequalities. The shell is
proved to be a subset of the realized space.

`GNExcessCubicRealizedLargeModulusShellCount` is its cardinality, and
`GNExcessCubicRealizedLargeModulusShellMoment` is the exact finite sum of
`(M : ℝ)^(3/8)` over the shell.

## Deterministic shell bounds

For every `X,D`, the module proves:

```text
shell.card * D^(3/8) ≤ shellMoment X D
shellMoment X D ≤ shell.card * (2D)^(3/8).
```

The first uses `D ≤ M`; the second uses `M < 2D` and `Real.rpow` monotonicity.
`GNExcessCubicRealizedLargeModulusShell_moment_le_of_card_le` consumes an
explicit real theorem argument `(shell.card : ℝ) ≤ B` and returns the upper
moment bound. No provider class or global count assumption is introduced.

## Dyadic indices and exact partition

`GNExcessCubicRealizedLargeDyadicIndexSpace X` is the image of the realized
modulus space under `Nat.log 2`. For every positive realized modulus `M`, the
module proves

```text
2^(Nat.log 2 M) ≤ M < 2^(Nat.log 2 M + 1).
```

The shells at `2^k` are pairwise disjoint and their finite `biUnion` is exactly
the realized modulus space. Consequently,
`GNExcessCubicRealizedLargeModulusMoment_eq_sum_dyadicShellMoments` gives the
main exact identity:

```text
realizedModulusMoment X
  = ∑ k in realizedDyadicIndexSpace X,
      shellMoment X (2^k).
```

The provider-free consumer
`GNExcessCubicRealizedLargeModulusMoment_le_of_dyadicShellCardBounds` turns
explicit shell-card hypotheses into the finite global upper sum with endpoint
weight `(2^(k+1))^(3/8)`. It does not instantiate any research target.

## Finite support guards

`GNExcessCubicRealizedLargeModulusShell_eq_empty_of_height_lt` proves that a
shell is empty above `3*(X+1)^2`. The theorem
`GNExcessCubicRealizedLargeModulusShell_eq_empty_of_below_large` proves that a
shell is empty when `2D ≤ X+2`, because all its members would be below the
large-modulus boundary. The optional endpoint theorem records, for every
realized dyadic index, `X+1 < 2^(k+1)` and `2^k ≤ 3*(X+1)^2`.

## Verification and trust boundary

Focused build:

```text
lake build DkMath.ABC.GNExcessCubicRealizedDyadic  PASS
```

Aggregator build:

```text
lake build DkMath.ABC                             PASS
```

The principal shell-bound, exact-reindex, global-consumer, and empty-shell
theorems audit to `propext`, `Classical.choice`, and `Quot.sound`, or a subset.
No `sorry`, `admit`, new axiom, `abc_main_axiom`, or `native_decide` was added.

## Remaining research frontier

The bookkeeping ambiguity is removed. The remaining theorem is genuinely
arithmetic: estimate the exact finite quantity
`GNExcessCubicRealizedLargeModulusShellCount X D` in the realized large range.
No such estimate is packaged or assumed here.
