# Petal / FloatWindow implementation report: checkpoint 341

## Status

Checkpoint 341 is implemented without adding `sorry`.

This checkpoint turns the canonical endpoint identity into an exact cumulative
conservation layer.  It also isolates high-drift events as finite diagnostic
objects and separates the reusable signed-counter argument from the finite
control signature.

The branch stops at an honest obstruction: the canonical counter candidate has
the required exact recurrence, but its preservation guard is equivalent to the
width-prefix bound that the certificate would be intended to prove.  Therefore
no canonical certificate instance is constructed.

## Implemented modules

### `CanonicalEndpointDrift.lean`

The primary one-block conservation theorem is now the direct identity

```text
endpoint drift + claim holes + terminal valuation = block length.
```

Lean theorem:

```lean
endpointAccountingTerm_add_claimHoles_add_terminalValuation_eq_blockLength
```

All four quantities are compared in `Int`, so negative realized drift is not
lost through natural-number subtraction.  The previous rearranged theorem is
retained as a corollary.

The correct interpretation is now fixed:

- block length is the total potential drift budget;
- endpoint accounting is the realized signed drift;
- claim holes and terminal valuation are the two exact absorption channels.

A long block alone does not imply large realized drift.

### `CanonicalEndpointConservation.lean`

Four half-open window ledgers over `[q, q + M)` were added:

- `canonicalEndpointDriftWindowSum`;
- `canonicalClaimHolesWindowSum`;
- `canonicalTerminalValuationWindowSum`;
- `canonicalBlockLengthWindowSum`.

Their zero and singleton forms are explicit.  The main finite conservation law
is

```lean
canonicalEndpointBudgetWindow_conservation
```

and the drift telescope is

```lean
canonicalEndpointDriftWindowSum_eq_startState_bitWidth_sub
```

Combining them gives shifted and prefix width-budget laws:

```text
width growth + cumulative holes + cumulative terminal valuation
  = cumulative block length.
```

This is an exact integer identity, not an asymptotic estimate.

The exact high-drift threshold is also fixed:

```text
K <= drift
  iff
K + holes + terminal valuation <= block length.
```

Consequences proved in Lean:

- high drift forces block length at least `K`;
- high drift leaves at most `block length - K` for combined absorption;
- unbounded drift for one fixed root implies unbounded block lengths for that
  same root.

No converse is claimed.

Rootwise boundedness now has an exact structural restatement:

```text
RootwiseEndpointDriftBound n
  iff
there is a uniform additive B such that
  block length <= holes + terminal valuation + B.
```

This reformulates the fixed-root problem but does not produce `B`.

Scaled and unscaled cumulative absorption bounds were added.  In particular,
if cumulative holes and terminal valuation absorb cumulative length up to `C`,
then cumulative width growth is at most `C`.  Complete absorption forces
nonpositive width growth on the selected finite window.

### Canonical counter candidate

The candidate

```text
credit(M) = cumulative holes + cumulative valuation - cumulative length
```

has been defined.  Lean proves

```text
credit(M) = root bit width - current canonical bit width
```

and the exact recurrence

```text
credit(M + 1) = credit(M) - endpoint drift(M).
```

The decisive diagnostic equivalences are:

```text
0 <= credit(M)
  iff current width <= root width

drift(M) <= credit(M)
  iff 0 <= credit(M + 1).
```

Thus the candidate is algebraically correct, but the guard is not yet an
independent arithmetic theorem.  Instantiating the counter certificate here
would be circular.

### `CanonicalHighDrift.lean`

The finite event carrier

```lean
canonicalHighDriftBlocksUpTo n K M
```

contains exactly the block indices below `M` whose drift is at least `K`.
Membership also has the equivalent block-budget form.  Prefix monotonicity,
threshold antitonicity, event-count monotonicity, and the block-length lower
bound are proved.

This carrier is deliberately finite.  No union over all horizons, eventual
stabilization, finite total event count, or repeated high-drift theorem is
inferred from it.

### `FiniteControlCounter.lean`

The arithmetic soundness argument was factored into

```lean
SignedCounterCertificate
```

with weight, credit, nonnegative initial credit, exact recurrence, and local
preservation guard.  It proves

```text
sum of prefix weights = initial credit - final credit
sum of prefix weights <= initial credit.
```

`FiniteControlSignedCounterCertificate` is retained as an observational
wrapper carrying the finite signature, and projects to the core certificate.
The old zero-initial theorem remains as a corollary.  Existing users and the
alternating witness are unchanged at their public surface.

## Finite audit

The canonical recurrence was sampled for roots

```text
27, 31, 47, 59, 123, 255, 511, 1023, 2047, 4095
```

until a repeated state or 1000 blocks.  For each block the audit recorded:

```text
index, drift, block length, claim holes, terminal valuation,
scalar queue before/after, candidate credit before,
spacing from the previous event with drift >= 2.
```

Selected high-drift observations are:

| root | block | drift | length | holes | valuation | queue before/after | credit before | prior spacing |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 27 | 1 | 2 | 5 | 2 | 1 | 0 / 2 | 0 | - |
| 31 | 0 | 2 | 5 | 2 | 1 | 0 / 2 | 0 | - |
| 511 | 0 | 5 | 9 | 3 | 1 | 0 / 5 | 0 | - |
| 1023 | 0 | 3 | 10 | 4 | 3 | 0 / 3 | 0 | - |
| 2047 | 0 | 6 | 11 | 4 | 1 | 0 / 6 | 0 | - |
| 2047 | 19 | 4 | 7 | 2 | 1 | 0 / 4 | 4 | 17 |
| 2047 | 21 | 2 | 6 | 3 | 1 | 5 / 7 | -5 | 2 |
| 4095 | 0 | 4 | 12 | 4 | 4 | 0 / 4 | 0 | - |
| 4095 | 18 | 4 | 7 | 2 | 1 | 0 / 4 | 5 | 17 |
| 4095 | 19 | 2 | 6 | 3 | 1 | 4 / 6 | -4 | 1 |

These are finite observations only.  They show that repeated threshold events
occur in the tested finite traces and that candidate credit may already be
negative before a later event.  They do not prove repeated high drift for all
time, unbounded drift, or failure of a rootwise bound.

## Facts now fixed

1. Canonical endpoint drift is exactly the residual block budget after two
   absorption channels.
2. This identity conserves exactly on every finite shifted window.
3. Cumulative drift is exactly canonical width change.
4. High-drift membership is equivalent to a local residual-budget inequality.
5. Rootwise boundedness is exactly a uniform additive absorption estimate.
6. A finite high-drift carrier supports honest finite counting and monotonicity.
7. Counter soundness does not logically depend on finite control state.
8. The canonical arithmetic credit has the correct recurrence, but its local
   guard remains the missing theorem.

## Branch decision

No independent canonical preservation guard was found.  No theorem establishes
repeated unbounded drift for a fixed root.  The finite audit does not justify an
all-time statement.  Therefore:

- do not instantiate a canonical `SignedCounterCertificate` yet;
- do not refute `RootwiseEndpointDriftBound`;
- keep the fixed-root question open.

The next mathematically meaningful branch is to search for an arithmetic guard
that does not mention candidate-credit nonnegativity or the desired prefix
width bound.  Promising inputs are the already formalized reflected queue,
source-age deficit, terminal valuation, and claim-hole incidence.  A valid next
bridge must imply

```text
endpoint drift(M) <= credit(M)
```

from independently proved local data.  If this cannot be done, the exact
conservation and finite event carrier are the correct stopping surface.

## Verification

The checkpoint passed:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointConservation
lake build DkMath.Collatz.PetalBridge.FloatWindow.CanonicalHighDrift
lake build DkMath.Collatz.PetalBridge.FloatWindow.FiniteControlCounter
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath.Collatz.PetalBridge
lake build DkMath
git diff --check
```
