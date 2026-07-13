# Petal / Float Window Report - Checkpoint 319

## Status

`cp-319` closes the saturated canonical-block branch through the requested
finite dynamic-pressure aggregation surface.  All new Lean declarations are
proved without `sorry`.

## Implemented module

New module:

```text
DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentSaturatedSuccessor
```

It is exported by `DkMath.Collatz.PetalBridge.FloatWindow`.

## Exact facts now proved

Saturation is equivalent to the two structural conditions

```text
L = v + 1
claimCount = L.
```

Its terminal-depth pressure is exactly zero.  The exponential comparison
`3^L < 2^(2L-1)` for `L >= 3`, combined with the exact normal form and unit
bit-width drift, proves that every saturated block has

```text
L = 2
v = 1
endpoint height = 2.
```

Writing `u` for the odd core gives

```text
x0 = 4*u - 1
x1 = (9*u - 1) / 2
v2(9*u - 1) = 1
u mod 4 = 3
u mod 8 = 3 or 7.
```

Two consecutive saturated blocks are impossible.  This is an exact arithmetic
theorem and no longer a finite-audit observation.  Consequently the correct
successor theorem is

```text
saturated(k)
  -> drift(k+1) <= 0
     or terminal-pressure(k+1) > 0.
```

The false unconditional statement `saturated -> next drift <= 0` remains
rejected.  The positive successors seen in the cp-318 audit inhabit the
positive-pressure branch.

## Pressure depth and finite decomposition

For positive drift with terminal valuation `v >= 2`, pressure at depth `v-1`
equals the ledger upper bound `L-v` and therefore dominates the drift.

At `v = 1`, a positive length-two block is saturated; a nonsaturated positive
block has length at least three and positive terminal-depth pressure.

The implementation now exposes actual finite index sets for:

```text
positive drift
positive terminal pressure
saturation
nonpositive drift.
```

Every positive block belongs to exactly one of the pressure and saturation
families.  Saturated indices are isolated, and the exact packing bound is

```text
2 * saturated.card <= intervalLength + 1.
```

This remains valid for an open observed excursion and assumes no future
repayment endpoint.

## Dynamic-depth aggregation

The selected pressure coordinate remains a dependent pair `(block, depth)`:

```text
saturated       -> terminal depth
nonsaturated,
  v >= 2        -> v - 1
nonsaturated,
  v = 1         -> 0.
```

The finite theorem now has the requested form:

```text
sum positive drift
  <= sum selected dynamic-depth pressure
       + saturatedIndices.card.
```

Thus the dynamic-depth sum itself was not an obstruction.

## Successor grammar

For a saturated core `u`, Lean proves

```text
nextStart + 1 = (9*u + 1) / 2
nextLength = v2 ((9*u + 1) / 2)
u mod 8 = 3 -> nextLength = 1
u mod 8 = 7 -> 2 <= nextLength.
```

This is the exact two-branch successor grammar requested at this checkpoint.

## First remaining obstruction

The next global step cannot simply reinterpret the finite pressure sum as
repaid mass.  Pressure witnesses selected at different block-dependent depths
may refer to overlapping continuation resources.  The current theorem is a
correct sum of local numerical contributions; it does not yet prove that those
contributions are disjoint physical payments.

The next required bridge is therefore one of:

1. an injection from selected `(block, depth)` pressure units to distinct
   payment resources; or
2. a uniform multiplicity bound for reuse of a payment resource, followed by
   the corresponding corrected charging inequality.

Until such an incidence theorem is proved, replacing dynamic local pressure by
a globally available repayment mass would overstate the current result.

## Verification

The focused module build passed.  The public aggregate and top-level build
gates are run after this report is created and are recorded in the completion
message.
