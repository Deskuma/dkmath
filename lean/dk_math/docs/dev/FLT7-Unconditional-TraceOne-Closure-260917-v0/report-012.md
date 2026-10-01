# FLT7TC-005R7 — Higher-depth canonical split and unified receiver frontier

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

The attached `instruction-012.md` was treated as the bounded implementation
contract, separately from the user's request.  This checkpoint extends the
R6 normalized routing board and keeps the receiver boundary explicit.

## Proved

`RamifiedPrimarySecondCoordinateCanonicalSplit` is constructed from the R6
primary routing packet.  Its normalized cells satisfy the expected equations:

```text
c31 = c32 = c33 = 1
c21 = 1
c11 = 7^(5 + 7*k)
c13 = gcd(|root.snd|, |Q|).
```

The terminal-independent compensation core is
`gcd(|root.snd|, |Q|)`.  The canonical split exposes the vertical and
horizontal unit roots, the compensation core, and the quotient remainder.

The exact cubic-gap identity is checked:

```text
|R-L| = 7^(6 + 7*k) * verticalUnitRoot^7
        * (compensationCore * residualRoot).
```

With the explicit gap/residual coprimality needed for the vertical factor, the
receiver is equivalent to the generalized cubic-gap seventh-power shape.  The
receiver is also equivalent to independent seventh powers of the compensation
core and residual root.  A depth-zero same-summit calibration identifies the
new compensation core with the historical terminal gcd and reduces the
receiver propositionally to the historical receiver.

## Conditional inner-root layer

Given an inhabited generalized receiver, the new
`RamifiedPrimaryQuadraticInnerRootPacket` provides:

- primitive inner coordinates;
- `root = innerRoot^7`;
- `norm(innerRoot) = residualNormRoot` and its 7-unit property;
- the normalized inner second-coordinate product
  `|inner.snd| * |innerSndCore| = 7^4 * (7^k * M)^7`;
- `v7(|inner.snd|) = 4 + 7*k`;
- for counterexample provenance, the equivalent relation
  `v7(|inner.snd|) + 3 = 7 * v7(|distinguishedEndpoint|)`;
- the conditional `7^4 * seventh-power` factor split.

This is a conditional algebraic extraction, not a descent of a counterexample.

## Bounded receiver audit

No theorem was added that derives the receiver from
`PrimitiveCounterexampleRamifiedProvenance`.  The checked gap-unit bridge only
provides an explicit 7-adic unit relation between endpoint and cubic gaps; it
does not provide a global integer seventh-power unit.  Therefore receiver
existence remains the precise global frontier.

The exact-depth downstream boundary is visible in the existing uses of
`RamifiedQuadraticInnerRootPacket.innerRootSnd_depth_eq_four`: the real-cubic
axis-drop and strict-descent-failure audits require exact depth four.  The new
higher-depth API supplies `4 + 7*k`, so those consumers cannot be ported by
rewriting `4 + 7*k` as `4`.

## Outcome

**Outcome B — GENERALIZED CANONICAL SPLIT / RECEIVER EQUIVALENCES GREEN;
CONDITIONAL INNER-ROOT GENERALIZATION GREEN; RECEIVER EXISTENCE REMAINS THE
PRECISE GLOBAL FRONTIER.**

## Validation

Focused builds completed successfully for:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneHigherDepthRamifiedCanonicalReceiver
lake build DkMathTest.FLT.SevenPrimeTraceOneHigherDepthRamifiedCanonicalReceiverApiAudit
lake build DkMathTest.FLT.SevenPrimeTraceOneHigherDepthRamifiedCanonicalReceiverAxiomAudit
lake build DkMath.FLT.Seven
```

The axiom audit is limited to inherited `[propext, Classical.choice,
Quot.sound]`.  No `sorry`, `admit`, `unsafe`, project `axiom`, or circular
final FLT7 import was added.
