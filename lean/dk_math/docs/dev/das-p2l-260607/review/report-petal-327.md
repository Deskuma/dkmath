# Petal / FloatWindow Report cp-327

## Status

The local zero-successor carrier, exact successor substitution, modulo-sixteen
classification, and one-step persistence grammar are complete without
`sorry`.  Work stops at the persistence-grammar condition named by the
checkpoint: residue data does not determine the following block's claim
count.

## Zero-successor discharge

A zero-drift successor of length at least two now has an explicit embedding

```text
Fin 2 -> CanonicalAbstractDyadicBudgetCarrier n (k + 1).
```

It uses the low two abstract slots.  Therefore every such successor is paid at
the abstract dyadic level.  This remains a potential statement, not an actual
bit repayment.

The sole locally insufficient successor candidate is exactly:

```text
successor length = 1
successor terminal valuation = 1
successor claim count = 1
successor endpoint is CarryTwoDebtAt
```

## Exact arithmetic substitution

For a saturated predecessor with odd core `u` and a length-one successor, Lean
proves:

```text
successor start         = (9*u - 1) / 2
successor odd core      = (9*u + 1) / 4
successor terminal word = (27*u - 1) / 4
```

The first equality was already public.  The latter two are now public bridge
theorems, avoiding repeated unfolding of the canonical block normal form.

## Modulo-sixteen classification

The candidate implication strengthens to an equivalence:

```text
successor terminal valuation = 1
  <-> predecessor odd core % 16 = 11
```

This is proved arithmetically from the exact terminal word.  No numerical
enumeration is used.

`CanonicalLengthOneBalancedCarrySuccessor` packages the exceptional local
class.  Its caller-facing equivalent form keeps two independent requirements:

```text
predecessor odd core % 16 = 11
and
CarryTwoDebtAt at the successor endpoint.
```

The residue condition does not imply the claim condition, and the API does not
silently identify them.

## One-step persistence grammar

For the exceptional class, the following block starts at

```text
(27*u - 1) / 8.
```

The modulo-sixteen class splits exactly modulo thirty-two:

```text
u % 32 = 11 or u % 32 = 27.
```

Lean proves:

- `u % 32 = 11` gives following block length `1`, hence that following block
  is not saturated;
- `u % 32 = 27` gives following block length at least `2`.

## Genuine obstruction

> **cp-328 correction.** This diagnosis is superseded.  The predicate
> `CanonicalLengthOneBalancedCarrySuccessor` is empty: a saturated
> predecessor forces own-width carry one at the successor start, which is the
> deepest successor source coordinate.  Thus that depth is a claim hole, and
> a length-one successor has claim count zero.  The modulo formulas remain
> arithmetically useful, but their nonvacuous hypothesis is now
> `CanonicalLengthOneTerminalOneSuccessor`.

The `% 32 = 27` branch is not decided by arithmetic length data.  Saturation
of the following block additionally needs its terminal valuation and claim
count.  No existing theorem transports those claim facts from the predecessor
residue or from the exceptional successor endpoint.

Consequently a modulo-64 split by itself would not close persistence.  The
next required theorem is a claim-transport bridge connecting the successor
endpoint/carry structure to the claim carrier of block `k + 2`.

Per the checkpoint stopping rule, the later independent tasks were not used to
bypass this obstruction:

- one-hole position refinement;
- abstract dyadic forest module;
- global root-resource specification;
- challenge-facing conditional width theorem.

These remain valid future tasks after the local claim-transport interface is
designed or the persistence branch is explicitly separated from them.

## Verification

The following gates passed:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude
lake build DkMath.Collatz.PetalBridge
lake build DkMath
git diff --check
```

The changed Lean file contains no `sorry` and no `maxHeartbeats` override.
