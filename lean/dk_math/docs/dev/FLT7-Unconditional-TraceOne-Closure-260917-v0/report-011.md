# FLT7TC-005R6 — Higher-depth ramified routing

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

The attached `instruction-011.md` was treated as the bounded implementation
contract, separately from the user's request.  This checkpoint generalizes
the arithmetic routing layer from an arbitrary primitive ramified summit.  It
does not supply the old terminal carrier, a seventh-power shape receiver, a
quadratic inner root, or an FLT7 contradiction.

## Implemented surface

`RamifiedGapRootPrimaryDecomposition p` factors the positive gap root as

```text
gapRoot = 7^k * gapUnit,
k = v7(gapRoot),
7 ∤ gapUnit.
```

The module `PrimeTraceOneHigherDepthRamifiedRouting.lean` adds terminal-free
versions of the exact second-coordinate identities and coprimality facts:

- the cancelled product for `root.snd * seventhPowerSndCore`;
- root/snd-core, root-norm/root-snd, and root-norm/snd-core coprimality;
- `gapRoot` coprimality with the endpoint and gap quotient;
- the natural absolute-value product identity.

These facts produce
`RamifiedPrimarySecondCoordinateRoutingPacket p`, whose right columns are

```text
7^(5 + 7*k), gapUnit^7, |gapQuotient.snd|.
```

The construction uses `nonempty_coprimeTripleRouting` and retains the exact
row/column coprimality.  At depth zero, the normalized columns reduce to the
historical `7^5`, `gapRoot^7` columns.  For depth at least two, Lean proves
`7 ∣ gapRoot`, as required by the higher-depth branch.

For counterexample-origin provenance, the new API proves

```text
primaryDepth + 1 = v7(|distinguishedEndpoint|)
```

and supplies the generalized routing packet without introducing a second
summit choice.

## Boundary retained

The generic routing board is now available, but no theorem identifies its
normalized compensation cell with a seventh-power receiver.  Consequently
the canonical receiver/inner-root extraction and the expected depth
`4 + 7*k` remain open.  No contradiction or unconditional FLT7 theorem is
claimed.

## Outcome

**Outcome B — HIGHER-DEPTH PRIMARY ROUTING GREEN; RECEIVER/INNER-ROOT
BOUNDARY REMAINS OPEN.**

## Validation

Focused builds completed successfully for:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneHigherDepthRamifiedRouting
lake build DkMathTest.FLT.SevenPrimeTraceOneHigherDepthRamifiedRoutingApiAudit
lake build DkMathTest.FLT.SevenPrimeTraceOneHigherDepthRamifiedRoutingAxiomAudit
lake build DkMath.FLT.Seven
```

The axiom audit reports only inherited `[propext, Classical.choice,
Quot.sound]`.  No `sorry`, `admit`, `unsafe`, or project `axiom` was added.
