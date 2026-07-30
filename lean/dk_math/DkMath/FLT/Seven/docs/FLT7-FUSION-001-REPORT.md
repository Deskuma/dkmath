# FLT7-FUSION-001 report

## Outcome

Outcome A. The RAMIFIED exit has been symmetrized and its independent signed
integer depth-four shadow is inhabited on the same packet.

## Lean facts fixed

`SevenRealCubicAxisDrop.lean` adds:

```text
exists_quotientCore_associated_pow_seven
RamifiedRealCubicBalancedAxisSplitPacket
nonempty_balancedAxisSplit
```

Thus both algebraic factors have an axis-cube/seventh-power presentation,
with both axes associated to `theta`.

`SevenRamifiedSignedRootDepth.lean` adds the signed homogeneous quotient, its
first- and second-order difference identities, and
`RamifiedSignedRootDepthPacket`. The constructor proves:

```text
IsCoprime l r
r-l = 7^4*d
Phi_7(r,l) = 7*E
7 does not divide d
7 does not divide E
d*E = a*(a+n)*m^7.
```

The quotient exactness is checked directly: after `r-l=7k`, the quotient is
`7*(l^6 + 7*k*f)`, so its divided core is congruent to `l^6` modulo seven.
The left signed root is a seven-unit by primitive inner coordinates.

## Boundary and prediction

No additivity of the determinant norm was assumed. The algebraic theta-depth
10 and signed integer seven-depth 4 coexist in one packet but are proved by
different mechanisms.

The strongest immediate next candidates are:

1. prove `IsCoprime d E` and instantiate the canonical 2-by-3 routing;
2. formulate a coordinate-level norm first-variation theorem explaining the
   depth conversion without using it for nonvanishing;
3. begin FUSION-002 by classifying real-cubic elements whose seventh power has
   third coordinate zero.

The current packet supplies no new primitive Fermat chart and no strict
well-founded decrease. Full cyclotomic lifting, descent closure, and public
FLT7 remain outside FUSION-001.
