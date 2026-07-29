# FLT7-RAMIFIED-013 implementation report

## Outcome

**Outcome A: the exact `13 = 10 + 3` theta-depth ledger and the
real-cubic axis drop are complete.**

The implementation is in:

```text
SevenRealCubicAxisDrop.lean
```

It starts from `RamifiedRealCubicExactPowerPacket`, retains the exact
RAMIFIED-012 source equations, and constructs
`RamifiedRealCubicAxisDropPacket`.

## 013A: exact theta-depth ledger

The module first defines the residue homomorphism

```text
thetaResidue : SevenRealCubicInt ->+* ZMod 7
```

and proves:

```text
theta | x <-> thetaResidue(x) = 0
Prime theta.
```

Exact divisibility is represented without division:

```text
HasExactThetaDepth x k :=
  theta^k | x and not theta^(k+1) | x.
```

The normalization identities give:

```text
normalizedAxis    ~ theta
normalizedWitness = unit * normalizedAxis * integer seven-unit
7 = theta^3 * thetaSevenUnit
IsUnit thetaSevenUnit.
```

Since the signed inner witness is not divisible by seven, Lean proves:

```text
HasExactThetaDepth
  (normalizedAxis^6 * normalizedWitness^7) 13.
```

For

```text
Delta = XR - XL
Phi   = Phi_7(XR,XL),
```

Frobenius modulo theta first gives `theta | Delta`. The checked expansion

```text
Phi_7(XL+d,XL)
  = 7*XL^6 + 21*XL^5*d + 35*XL^4*d^2
    + 35*XL^3*d^3 + 21*XL^2*d^4
    + 7*XL*d^5 + d^6
```

shows that its leading term has exact depth three and every remaining term
has greater depth. Hence:

```text
HasExactThetaDepth Phi 3.
```

Exact multiplicativity and cancellation in

```text
XR^7 - XL^7 = Delta * Phi
```

then give:

```text
HasExactThetaDepth Delta 10.
```

`RamifiedRealCubicDepthLedgerPacket` records explicit cores:

```text
Delta = theta^10 * gapCore
Phi   = theta^3  * quotientCore
theta does not divide gapCore
theta does not divide quotientCore.
```

## 013B: coprime cores and seventh-power extraction

Lean proves the left and right sources are coprime. A common prime dividing
their difference divides either the ramified axis or the loaded integer
second coordinate. The axis branch contradicts the nonzero theta residue of
the left source. The coordinate branch contradicts primitive integer
coprimality.

Since the sources are exact seventh powers:

```text
IsCoprime XL XR.
```

The homogeneous quotient satisfies the gap congruence:

```text
Delta | Phi_7(XR,XL) - 7*XL^6.
```

Thus a prime common to `gapCore` and `quotientCore` divides `7*XL^6`.
Root coprimality excludes the `XL` branch. In the `7` branch,

```text
7 = theta^3 * unit
```

makes the prime associated to theta, contradicting the axis-free gap core.
Therefore:

```text
IsCoprime gapCore quotientCore.
```

After the common `theta^13` factor is cancelled, their product is associated
to the seventh power of the signed inner second-coordinate root. Mathlib's
PID coprime-power extractor gives:

```text
exists T, Associated (T^7) gapCore.
```

If `T^7*u = gapCore`, the arbitrary unit is absorbed by:

```text
droppedAxis    = u^(-2) * theta
descentWitness = u * theta * T.
```

Lean verifies the unit identity

```text
(u^(-2))^3 * u^7 = u
```

and obtains the final packet fields:

```text
Associated droppedAxis theta
Prime droppedAxis
HasExactThetaDepth droppedAxis 1
Delta = droppedAxis^3 * descentWitness^7.
```

No second unit-class classification is required; this is exactly where the
coprimality of the exponents `3` and `7` is used.

## Signed norm shadow

The determinant norm is iterated over powers and odd seventh powers are
injective over the integers. The exact source equations therefore also give:

```text
Norm(XL) = signedLeftRoot
Norm(XR) = signedRightRoot

signedRightRoot - signedLeftRoot =
  Norm(XR) - Norm(XL).
```

This confirms the first half of the RAMIFIED-009B prediction. It does not
prove its depth-four conclusion: determinant norm is nonlinear, so

```text
Norm(XR) - Norm(XL)
```

cannot be replaced by `Norm(XR-XL)` without a new checked identity. The
axis-drop equation alone therefore does not transport theta depth ten to
integer seven-adic depth four.

## Public endpoint

The module exports:

```text
RamifiedRealCubicExactPowerPacket.nonempty_depthLedger
RamifiedRealCubicExactPowerPacket.nonempty_axisDrop
RamifiedRealCubicNormPacket.nonempty_axisDrop.
```

The facade `DkMath.FLT.Seven` imports the new module.

## Axiom and implementation audit

The exported checkpoint theorems depend only on:

```text
propext
Classical.choice
Quot.sound
```

There is no `sorryAx`, new axiom, or `native_decide`.

## Inference and next prediction

RAMIFIED-013 is the final checkpoint of the **ramified algebraic phase**.
It is not the final FLT7 checkpoint.

The next problem is no longer unit classification, class number, or theta
depth. It is a fusion/reconstruction problem:

```text
real-cubic axis drop
  -> compatible signed integer/quadratic chart
  -> new primitive Fermat counterexample
  -> strict well-founded decrease
  -> recursive descent closure.
```

The safest next checkpoint is an integer-shadow compatibility audit. It
should either:

1. derive the signed-root depth and routing from an explicit coordinate
   expansion of `Norm(XR)-Norm(XL)`, or
2. retain RAMIFIED-009B as an independent integer proof and fuse its output
   with `RamifiedRealCubicAxisDropPacket`.

Only after the chart constructor and strict decrease are both inhabited may
the result be connected to `AwayDescentClosureProvider`.

## Stop boundary

This checkpoint does not claim:

- `Norm(XR)-Norm(XL) = Norm(XR-XL)`;
- the signed integer root gap has seven-adic depth four;
- a new primitive integer or quadratic Fermat counterexample;
- a strict well-founded descent measure;
- an inhabited recursive descent provider;
- a terminal contradiction or unconditional FLT7.
