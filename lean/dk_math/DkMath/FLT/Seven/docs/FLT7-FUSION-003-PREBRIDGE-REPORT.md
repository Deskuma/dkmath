# FLT7-FUSION-003 pre-bridge report

Date: 2026-07-30

## Result

FUSION-003 reaches **Outcome C with a completed pre-bridge packet**.

The theta-depth-ten leading residue and the full six-sector group API are
proved. The signed routing board is reduced to its active unit shadow and its
two independent cycle invariants. The remaining direct-chart bridge is now
precise: no current packet theorem determines those two cycle ratios from the
single FUSION slope `tau`.

The implementation therefore enters the cyclotomic alternative only through
the reversible relative-index torsor. It does not select a factor.

## 1. Exact gap-core residue

For the paired roots, Lean proves

```text
U_right - U_left = 2*m mod 7
V_right - V_left = 0 mod 7.
```

The root coordinate decompositions are then compared directly with

```text
rootGap = theta^10 * gapCore.
```

Expanding the theta-linear coordinate of `theta^10 * gapCore` gives the
leading formula

```text
thetaResidue(gapCore) = -2*m.
```

This proof does not infer a residue from exact depth alone. It separately
uses the constant, linear, and square coordinate depths and computes the
coefficient surviving after division by `theta^10`.

## 2. Six-sector group decomposition

The finite address is upgraded to actual unit subgroups

```text
SevenBinarySector  = {u : (ZMod 7)ˣ | u^2 = 1}
SevenTernarySector = {u : (ZMod 7)ˣ | u^3 = 1}.
```

Lean constructs the multiplicative equivalence

```text
(ZMod 7)ˣ ≃ SevenBinarySector × SevenTernarySector
s |-> (s^3,s^2)
(r,c) |-> r/c.
```

For the paired roots:

```text
left binary  = -(right binary)
left ternary = right ternary.
```

Both addresses reconstruct their signed slopes through the inverse
equivalence.

The modulo-seven Jacobian reconnaissance is also fixed:

```text
det J = A^12
A != 0 -> det J != 0.
```

This records a nonsingular local branch but does not introduce a full
seven-adic Hensel framework.

## 3. Provenance audit

`PrimitiveRamifiedSummitPacket` contains the common arithmetic summit but no
field retaining whether it came from Row-Y or Row-Z. Thus the old downstream
packet chain cannot recover the original away row.

A minimal `RamifiedSummitProvenancePacket` is now constructed immediately
before commonization. It stores:

```text
row
row = original terminal row
row = Y or row = Z
common summit.
```

Row-Sum is eliminated by the existing contradiction. The mathematical summit
is not duplicated.

No theorem

```text
tau^3 = awaySevenBaseRowSignUnit row
```

is asserted. The two expressions arise from different normalized-unit
constructions, and an explicit equality connecting those units is still
missing.

## 4. Signed routing audit

For `RamifiedSignedRootRoutingPacket`, Lean proves:

```text
c31 = c32 = c33 = 1
7 does not divide any of c11,c12,c13,c21,c22,c23.
```

The six active cells therefore define a unit board over `ZMod 7`. The signed
integer margins erased by `Int.natAbs` are retained in a separate orientation
packet before any comparison with `tau`.

The two cycle invariants are defined as

```text
kappa12 = (u11*u22)/(u12*u21)
kappa23 = (u12*u23)/(u13*u22).
```

The routing constructor is also strengthened with a coherent existence
theorem whose result records that the returned board belongs to the supplied
signed-depth packet. This allows an inhabited
`RamifiedFusionRoutingAuditPacket` on the same paired jet.

## 5. Branch decision

The current normalized equation supplies row and column margins, but no
theorem relates either `kappa12` or `kappa23` to `tau`. Since the two cycle
coordinates are still independent API data, direct routing reconstruction is
not claimed.

The safe cyclotomic normalization is implemented:

```text
relativeCyclotomicIndex(k) = k / fusionSlopeUnit.
```

It is an equivalence of the six-element unit torsor, and Lean proves

```text
relativeCyclotomicIndex(k) = 1
  <-> k = fusionSlopeUnit.
```

This theorem is only a change of coordinates. It does not prove that relative
index one is the distinguished Kummer factor.

## 6. Next gate

The next checkpoint must prove one of:

1. explicit formulas `kappa12 = f(tau)` and `kappa23 = g(tau)`, enabling
   direct integer-chart reconstruction; or
2. a divisibility, association, or seventh-power property for one relative
   cyclotomic index, enabling a justified Kummer-factor selection.

Absent one of these, the six factors remain an unpointed torsor.

## 7. Excluded claims

This checkpoint does not prove:

- `tau^3` equals the surviving away-row sign;
- either routing cycle ratio is determined by `tau`;
- a selected routing cell;
- a distinguished cyclotomic factor;
- reconstructed primitive Fermat data;
- a strict well-founded decrease;
- an inhabited descent provider;
- FLT7.
