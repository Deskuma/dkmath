# ABC/GN Balance Calibration — Checkpoint 007

## Scope and outcome

This report treats the attached `instruction-007.md` as the bounded
checkpoint contract.  The audit found no existing public sum/difference
coordinate kernel with the required API, while both PowerSwap and ABC/GN have
real production consumers of the same exact linear transform.

Outcome A — GENERIC KERNEL JUSTIFIED.

A small dependency-neutral real-valued kernel was added.  PowerSwap and
ABC/GN now consume it through exact bridge modules.  Existing domain-specific
definitions and stable proofs remain intact; no ABC estimate, PowerSwap
analytic claim, or Hensel existence statement was added.

## Existing abstraction audit

The following sources were inspected before editing:

| Source | Result |
|---|---|
| `DkMath/Lib/README.md` | describes `DkMath.Lib.*` as a stable intermediate layer and contains no existing two-channel API |
| `DkMath/PowerSwap/Contours.lean:20-34` | defines `gapU`, `gapV`, `gapP`, and `gapQ` directly as real expressions |
| `DkMath/ABC/GNBalanceCalibration.lean:29-43` | defines GN support/depth mass, total mass, and signed balance directly |
| `DkMath/ABC/GNBalanceDepthLayers.lean:29-36` | defines the local mass and balance coordinates directly |
| repository search over `DkMath/Lib`, `DkMath/PowerSwap`, and `DkMath/ABC` | no equivalent public sum/difference/center kernel found |

The commonality is therefore substantive enough for a minimal stable kernel,
but not for a structure, matrix abstraction, category-theoretic layer, or
generic normed-space API.

## Generic kernel

Production file: `DkMath/Lib/TwoChannel.lean`.

The namespace is `DkMath.Lib.TwoChannel`, and the kernel depends only on
`Mathlib` (`:7`).  Its definitions are:

```text
mass(u,v)    = u + v
balance(u,v) = u - v
center(u,v)  = (u + v) / 2.
```

The exact public API includes:

- `left_eq_half_mass_add_balance` and
  `right_eq_half_mass_sub_balance` (`:32-40`);
- `center_eq_half_mass` and the center reconstruction forms
  `left_eq_center_add_half_balance` / `right_eq_center_sub_half_balance`
  (`:42-55`);
- `balance_eq_zero_iff` (`:57-60`);
- swap symmetry `mass_swap`, `center_swap`, `balance_swap` (`:62-75`);
- right-channel transport `mass_right_add`, `balance_right_add` and the
  left-channel counterparts (`:77-95`).

These are coordinate identities only.  `balance = 0` is not named or
interpreted as an optimum, extremum, stability condition, or ABC boundary.

## PowerSwap bridge

Production file: `DkMath/PowerSwap/TwoChannelBridge.lean`.

The exact bridge theorem names are:

- `gapP_eq_twoChannel_center` (`:27-29`);
- `gapQ_eq_twoChannel_balance` (`:31-33`);
- `gapU_eq_gapP_add_half_gapQ` and `gapV_eq_gapP_sub_half_gapQ`
  (`:35-43`).

Thus the existing PowerSwap coordinates are identified as

```text
gapP = center gapU gapV
gapQ = balance gapU gapV
```

and the two original channels are recovered from `gapP` and `gapQ`.  The
existing `gapF_eq_soft_hyperbolic_form` proof was deliberately left untouched.

## ABC/GN bridge

Production file: `DkMath/ABC/GNBalanceTwoChannelBridge.lean`.

The exact bridge theorem names are:

- `GNChannelMass_eq_twoChannel_mass` (`:29-32`);
- `GNChannelBalance_eq_twoChannel_balance` (`:34-37`);
- `GNChannelSupportMass_eq_twoChannel_reconstruction` and
  `GNChannelDepthMass_eq_twoChannel_reconstruction` (`:39-53`);
- `GNNonExceptionalLocalMass_eq_twoChannel_mass` (`:57-63`);
- `GNNonExceptionalLocalBalance_eq_twoChannel_balance` (`:65-71`).

The GN orientation remains exactly the existing one:

```text
U = GNChannelSupportMass
V = GNChannelDepthMass
M = U + V
Q = U - V.
```

The existing reconstruction theorem names in `GNBalanceCalibration.lean` were
not removed or rewritten.  The optional outer ABC bridge was not duplicated:
its orientation is intentionally different, and no identification of outer
ABC balance with GN balance is made.

## BCAL-006 transport interpretation

The local bridge identifies the BCAL coordinates as

```text
support coordinate = log q
depth coordinate   = (v_q(GN) - 1) * log q.
```

Therefore the exact Level-A successor laws from
`GNBalanceDepthTransport.lean` have the generic right-channel orientation:
the support coordinate stays fixed while the depth coordinate increases by
`log q`, so mass increases and balance decreases by one `log q` unit.

The existing Level-A theorems were not refactored through the generic kernel;
their direct factorization proof is smaller and clearer than introducing
additional coercion plumbing.  The consumer-side coordinate bridge is enough
to record the exact structural reuse.  It does not turn the generic transport
law into a Hensel lift-existence theorem.

## Dependency direction and deliberate non-actions

The dependency graph is:

```text
DkMath.Lib.TwoChannel
        ↓                    ↓
PowerSwap.TwoChannelBridge   ABC.GNBalanceTwoChannelBridge
        ↓                    ↓
PowerSwap facade             ABC facade
```

`DkMath.Lib.TwoChannel` imports only `Mathlib`; it imports no ABC, GN,
PowerSwap, shell, Hensel, or valuation module.  No import cycle was introduced.
The public facades were updated at `DkMath/Lib.lean:8`,
`DkMath/PowerSwap.lean:14`, and `DkMath/ABC.lean:57`.

No existing public definition was replaced solely for uniformity.  No new
ABC contract, estimate, calibration constant, Hensel existence theorem,
cardinality equality, density statement, optimization claim, or cross-domain
mathematical identification was added.

## Validation

The following validations passed in the nested Lake project `lean/dk_math`:

- `lake env lean DkMath/Lib/TwoChannel.lean`
- `lake env lean DkMath/PowerSwap/TwoChannelBridge.lean`
- `lake env lean DkMath/ABC/GNBalanceTwoChannelBridge.lean`
- `lake build DkMath.Lib.TwoChannel`
- `lake build DkMath.Lib`
- `lake build DkMath.PowerSwap`
- `lake build DkMath.ABC`
- `#print axioms` audit for the generic kernel and all consumer bridge
  endpoints: only `[propext, Classical.choice, Quot.sound]`
- forbidden-token scan of the new kernel and bridge modules for `sorry`,
  `admit`, `axiom`, and `unsafe`: no matches
- trailing-whitespace scan: no matches
- `git diff --check`: passed

The ABC facade replayed the pre-existing warning at
`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147` (`sorry`), outside
this checkpoint.
