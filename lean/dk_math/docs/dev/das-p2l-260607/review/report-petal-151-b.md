# report-petal-151-b

Checkpoint: 151-b / 152 sub root

Subject: converge the interruption around OneCycle valuation-flow reading.

## Summary

The interruption branch has been contained as a thin bridge:

```text
DkMath.Collatz.PetalBridge.OneCycle
  -> DkMath.Collatz.PetalBridge.ValuationFlowBridge
  -> DkMath.ABC.ValuationFlowBridge
```

The new file does not expand the general Collatz theory.  It records the
valuation-flow reading of the already proved one-cycle boundary result.

## Added File

```text
lean/dk_math/DkMath/Collatz/PetalBridge/ValuationFlowBridge.lean
```

This file imports:

```lean
import DkMath.Collatz.PetalBridge.OneCycle
import DkMath.ABC.ValuationFlowBridge
```

The ABC import is intentional.  The bridge is not a replacement for
`DkMath.ABC.ValuationFlowBridge`; it is a Collatz-facing window into that
language.

## Implemented Theorems

The bridge exposes the one-cycle result through names that match the
valuation-flow interpretation:

```lean
theorem oneCycle_unit_boundary_only
theorem oneCycle_unit_product_nat
theorem oneCycle_unit_product_int
theorem oneCycle_no_prime_channel_on_base
theorem oneCycle_no_prime_channel_on_scaleGap
theorem oneCycle_no_prime_channel_on_unitProduct
```

It also fixes the support/rad reading of the unit-product boundary:

```lean
theorem oneCycle_supportMass_unitProduct_eq_one
theorem oneCycle_rad_unitProduct_eq_one
theorem oneCycle_no_supportMass_growth
```

The key meaning is:

```text
3 * n + 1 = 2^h * n and 0 < n
  -> n = 1 and h = 2
  -> n * (2^h - 3) = 1
  -> no prime support channel remains on the product
  -> supportMass and rad are both 1
```

## Aggregate Import

The aggregate module was updated:

```text
lean/dk_math/DkMath/Collatz/PetalBridge.lean
```

It now imports:

```lean
import DkMath.Collatz.PetalBridge.ValuationFlowBridge
```

## Non-Claims

This checkpoint does not prove general Collatz convergence.

This checkpoint does not classify all cycles.

This checkpoint only records that the one-step scaled cycle equation has no
nontrivial prime-support channel: the only positive solution is the unit
boundary.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.ValuationFlowBridge
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/ValuationFlowBridge.lean
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/OneCycle.lean
git diff --check
```

The `rg` checks returned no matches.

## Next Inference

The sub-root branch should now stay closed unless a later proof needs a more
general valuation-flow API.

The main-root work should resume in `PressureAccounting`: sorted explicit
families, failure witnesses, and budget wrappers are the next stable surface.
