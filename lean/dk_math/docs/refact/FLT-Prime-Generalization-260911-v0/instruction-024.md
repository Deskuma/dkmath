# FLT prime-generalization Phase 24 — universal `RZ` transport and common-prime support

## Goal

Phase 23 isolated the exact blocker correctly: the characteristic-zero
`PrimeTraceOneCoordinatePacket` is constructed in a selected cyclotomic field,
and its `map_RZ` / `gauss_difference` identities are not currently universal
identities that can simply be specialized to characteristic `q`.

This phase should **not** attempt to transport the full `SZ`/Gauss identity.
The common-prime-support argument can be shortened substantially: it only
needs a characteristic-independent realization of the packet's `RZ` identity

```text
RZ  ->  Rpoly = qrFactorPoly + qnrFactorPoly.
```

The Phase-23 positive-characteristic Gauss nonvanishing theorem remains a
valid reusable result, but it is not required for the shortest proof below.

Preferred final classifications:

```text
PGEN-PRIME-RPOLY-UNIVERSAL-TRANSPORT-GREEN
PGEN-PRIME-COORDINATE-COMMON-PRIME-SUPPORT-GREEN
PGEN-PRIME-COORDINATE-COPRIME-FLT-GREEN
```

Stretch classification, only if the earlier layers close cleanly:

```text
PGEN-PRIME-TRACEONE-STRIPPED-IDEAL-BRIDGE-GREEN
```

Do not claim general FLT, class-group torsion-freeness, a class-number theorem,
regular-prime theory, or real-sector elimination.

---

## A. Test-first API audit for a universal cyclotomic carrier

First determine the smallest pinned Mathlib carrier that supports all of the
following:

1. an integral universal primitive `p`-th cyclotomic root;
2. a map to a characteristic-zero cyclotomic realization used by Phase 22;
3. a specialization map to an arbitrary field `K` containing a primitive
   `p`-th root `xi`;
4. enough injectivity on the characteristic-zero anchor to pull an equality
   back to the universal carrier.

Audit at least:

```text
AdjoinRoot (Polynomial.cyclotomic p Z)
AdjoinRoot.root
AdjoinRoot.mk
AdjoinRoot.lift / liftHom / evalRoot   -- exact pinned names only
CyclotomicRing
Polynomial.isRoot_cyclotomic_iff
IsPrimitiveRoot.isRoot_cyclotomic     -- if present
IsPrimitiveRoot.adjoinEquivRingOfIntegers
IsPrimitiveRoot.adjoinEquivRingOfIntegersOfPrimePow
```

Also pin the exact APIs for:

```text
MvPolynomial.map
MvPolynomial.eval
map_finset_prod / map_prod
Finset.prod_eq_zero_iff
IsPrimitiveRoot.pow_inj
ZMod / CharP cast-zero lemmas
```

Do not assume an API name from documentation. Record the exact declarations
that compile in this checkout.

If `CyclotomicRing` is a substantially cleaner universal carrier than
`AdjoinRoot`, use it. Otherwise prefer the minimal `AdjoinRoot` quotient.

---

## B. Define only the universal QR/QNR `R` object

The existing `CyclotomicQRProduct.rootFactor` is field-valued, but the raw
factor expression needs only a commutative ring. Introduce, if necessary, a
small neutral ring-valued version local to the new module.

Suggested production module:

```text
DkMath/NumberTheory/CyclotomicQRUniversalTransport.lean
```

Over the chosen universal cyclotomic ring `C_p`, define:

```text
zetaU
universalRootFactorPoly
universalQrFactorPoly
universalQnrFactorPoly
universalRpoly := universalQrFactorPoly + universalQnrFactorPoly
```

Do **not** define a universal `quadraticGauss` or universal `Dpoly/SZ` unless it
falls out essentially for free. They are not required for this phase.

Prove functoriality: for a ring hom `f : C_p ->+* K` sending `zetaU` to a
primitive root `xi`, mapping `universalQrFactorPoly` / `universalQnrFactorPoly`
produces the existing QR/QNR factor polynomials at `xi` (or an equivalent
ring-valued local definition).

---

## C. Anchor the Phase-22 `RZ` in the universal ring

Let `P : PrimeTraceOneCoordinatePacket L p zeta hzeta` be a Phase-22 packet in
a characteristic-zero cyclotomic field `L`.

The target theorem is an equality in the universal integral cyclotomic
carrier:

```text
map (Z -> C_p) P.RZ = universalRpoly p.
```

Preferred proof architecture:

1. map both sides into the characteristic-zero cyclotomic ring of integers or
   other audited faithful realization;
2. use `P.map_RZ` on the left;
3. prove that the mapped universal QR/QNR products are the existing
   `Rpoly (p := p) zeta` on the right;
4. pull the equality back using injectivity / a ring equivalence.

This is the core missing theorem from Phase 23.

Do not replace it by a receiver assumption.

If the selected Phase-22 `L` is inconvenient for obtaining the required
faithful map, it is acceptable to construct a **canonical packet** in one
standard characteristic-zero cyclotomic realization and then prove that its
`RZ` may be used for the downstream common-prime theorem. Do not assert
uniqueness of arbitrary existential packet witnesses without proof.

Preferred status after this part:

```text
PGEN-PRIME-RPOLY-UNIVERSAL-TRANSPORT-GREEN
```

If this part cannot be established, stop and report the exact missing API or
mathematical injectivity statement. Do not proceed by pretending that
`P.map_RZ` is characteristic-independent.

---

## D. Specialize `RZ` to an arbitrary primitive root

From Part C derive a clean theorem of the form:

```text
packet_RZ_map_eq_Rpoly_of_primitive_root
```

Conceptually:

```text
for any field K,
for any xi : K with IsPrimitiveRoot xi p,
map (Z -> K) P.RZ = Rpoly_at xi.
```

The exact statement may use the local ring-valued QR/QNR polynomial instead
of the existing field-only `Rpoly` if that produces cleaner elaboration.

The essential point is that this theorem must work in positive
characteristic `q != p`; it must not require `CharZero K`.

Use `Polynomial.isRoot_cyclotomic_iff` or the audited equivalent to construct
the specialization hom from the universal cyclotomic carrier.

---

## E. Odd common-prime support without Gauss transport

Now prove the central residue theorem.

Let `q` be prime with

```text
q != 2
q != p
```

and let `z y : N` (or integer casts with equivalent positivity bookkeeping)
be primitive endpoint coordinates:

```text
Nat.Coprime z y.
```

Suppose the evaluated packet coordinates have a common prime divisor:

```text
(q : Z) | eval P.AZ (z,y)
(q : Z) | eval P.SZ (z,y).
```

Use `P.half_relation` to obtain

```text
(q : Z) | eval P.RZ (z,y).
```

Use `P.coord_norm_eq` to show the prime cyclotomic shell vanishes modulo `q`.

### E1. Show `y != 0 mod q`

If `q | y`, shell-zero forces `q | z`; this contradicts `Nat.Coprime z y`.
Therefore `(y : ZMod q) != 0`.

### E2. Construct the primitive root directly in `ZMod q`

Set

```text
t := (z : ZMod q) / (y : ZMod q).
```

From shell-zero prove:

```text
Phi_p(t) = 0,
t^p = 1,
t != 1.
```

Since `p` is prime and `q != p`, conclude:

```text
IsPrimitiveRoot t p.
```

Avoid introducing an algebraic closure unless the pinned APIs make the direct
`ZMod q` route harder.

### E3. QR/QNR contradiction from `R` alone

Specialize Part D to `K := ZMod q`, `xi := t`.

Let

```text
U := qr product at (z,y)
V := qnr product at (z,y).
```

Because `1` is a nonzero quadratic residue modulo odd `p`, the QR product has
the factor

```text
z - t^1 * y = 0,
```

so

```text
U = 0.
```

The reduced packet coordinate gives

```text
R = U + V = 0,
```

hence

```text
V = 0.
```

Since `ZMod q` is a field, product-zero yields a QNR exponent `b` with

```text
z = t^b * y.
```

But also `z = t * y`; cancel nonzero `y` and obtain

```text
t = t^b.
```

Use primitive-root power injectivity to get `b = 1` in `ZMod p`, contradicting
that `b` lies in the QNR finset while `1` is a QR.

Thus no odd prime `q != p` can divide both packet coordinates.

Preferred public theorem shape:

```text
common_coordinate_prime_eq_exponent_or_two
```

or, if the `q = 2` case is also completed in this module,

```text
common_coordinate_prime_eq_exponent
```

Preferred status:

```text
PGEN-PRIME-COORDINATE-COMMON-PRIME-SUPPORT-GREEN
```

---

## F. Eliminate `q = 2` separately

Do not force characteristic two through QR/QNR/Gauss machinery.

For odd prime `p` and primitive `Nat.Coprime z y`, prove the homogeneous prime
cyclotomic shell is odd.

Modulo two, primitive input means one of:

```text
z odd, y even
z even, y odd
z odd, y odd
```

In the first two cases exactly one endpoint monomial survives. In the last
case all `p` terms are `1`, and odd `p` makes their sum `1 mod 2`.

Therefore

```text
Odd (GTailCyclotomicShell p (z-y) y)
```

(or the equivalent homogeneous-shell statement, chosen to avoid truncated
subtraction).

If both `A` and `S` were even, their TraceOne norm would be even (indeed
multiple of four), contradicting the odd shell.

This removes the characteristic-two common prime.

---

## G. FLT-side elimination of the remaining prime `p`

Now consume the actual Phase-1 input rather than trying to prove a stronger
unconditional coordinate theorem.

Given

```text
P0 : PrimeAdicFactorPacket p g u x
```

set endpoint coordinates

```text
z := g + u
y := u.
```

Derive

```text
Nat.Coprime z y
```

from `P0.coprime_gap_unit`.

Instantiate the coordinate packet at `(z,y)` and use Parts E/F. Any common
coordinate prime must be `p`.

If `p` divides both TraceOne coordinates, then

```text
p^2 | natAbs (norm coord).
```

Use packet norm equality together with

```text
P0.residual_not_prime_sq
```

(or `residual_exact_one`) to contradict this.

Therefore the actual FLT-side TraceOne coordinate is primitive:

```text
IsCoprime coord.fst coord.snd
```

or the corresponding integer gcd statement.

Preferred classification:

```text
PGEN-PRIME-COORDINATE-COPRIME-FLT-GREEN
```

It is acceptable that the theorem is conditional on the existing
`PrimeAdicFactorPacket`; that is the correct upstream interface.

---

## H. Stretch: axis stripping preserves coordinate primitivity

Only attempt after Parts C-G are green.

Add a neutral TraceOne lemma:

```text
w = discrAxis s * r
IsCoprime w.fst w.snd
--------------------------------
IsCoprime r.fst r.snd
```

The proof should use the explicit axis multiplication coordinates. A common
integer divisor of `r.fst` and `r.snd` divides both linear combinations that
form the two coordinates of `w`, so parent primitivity forces residual
primitivity.

Combine with Phase 21:

```text
axis-terminal r
+ coordinate-coprime r
=> IsCoprime (Ideal.span {r}) (Ideal.span {conj r}).
```

Then use

```text
norm r = k^p
```

to prove

```text
Ideal.span {r} * Ideal.span {conj r}
  = (Ideal.span {k})^p
```

and feed the result to Phase 15:

```text
exists_eq_pow_of_isCoprime_mul_eq_pow
```

to obtain

```text
exists I, Ideal.span {r} = I^p.
```

Preferred stretch classification:

```text
PGEN-PRIME-TRACEONE-STRIPPED-IDEAL-BRIDGE-GREEN
```

Do not principalize `I` here; class-group p-torsion remains the next genuine
arithmetic obligation.

---

## I. Required regressions

Keep p=3,5,7,11,13 coverage.

At minimum:

```text
p=3   packet / universal-R transport API only; preserve Eisenstein exception
p=5   real TraceOne carrier common-prime probe
p=7   compare generic FLT-side coprimality with existing specialized theorem
p=11  imaginary TraceOne carrier probe
p=13  real TraceOne carrier probe
```

For p=7, use the existing `PrimitiveCoordinateCoprime` theorem as a regression,
not as a proof of the generic result.

---

## J. Axiom and source audit

Add focused `#print axioms` coverage for:

```text
universal R transport
arbitrary primitive-root R specialization
common-prime support
FLT-side coordinate coprimality
stretch ideal-power endpoint, if implemented
```

No new:

```text
sorry
sorryAx
admit
axiom
unsafe
```

Do not add a theorem hypothesis that simply assumes the missing universal
identity or coordinate coprimality.

---

## K. Suggested focused builds

Adjust exact module names to the implementation, but include at least:

```text
lake build DkMath.NumberTheory.CyclotomicQRProduct
lake build DkMath.NumberTheory.CyclotomicQRTraceOneBridge
lake build DkMath.NumberTheory.CyclotomicQRUniversalTransport
lake build DkMath.FLT.Prime.AdicPowerSplit
lake build DkMath.NumberTheory.TraceOneConjugateCoprime
lake build DkMath.Lib.NumberTheory.IdealPowerFactor
lake build DkMathTest.FLT.Prime.PrimeTraceOneUniversalTransportApiAudit
lake build DkMathTest.FLT.Prime.PrimeTraceOneUniversalTransportProbe
lake build DkMathTest.FLT.Prime.PrimeTraceOneUniversalTransportAxiomAudit
lake build DkMath.FLT.Seven

git diff --check
```

Record exact warning output. The pre-existing
`ZsigmondyCyclotomicResearch.lean:147` `sorry` warning is unrelated unless the
new dependency path changes that fact.

---

## L. Stop boundaries

Stop and report precisely if any of the following occurs:

1. no faithful characteristic-zero anchor from the universal cyclotomic
   carrier to the Phase-22 realization can be built;
2. the universal `RZ` equality cannot be pulled back without an unproved
   uniqueness statement;
3. a primitive-root specialization hom cannot be built in characteristic
   `q != p`;
4. the QR/QNR contradiction fails because an exact exponent/root API is
   missing;
5. the `q = 2` parity statement requires an unproved upstream positivity or
   subtraction assumption;
6. the FLT packet cannot be connected to the coordinate packet without adding
   a new receiver assumption.

In any blocked case, report the smallest missing theorem/API and retain all
green lower layers.

The central principle of this phase is:

```text
transport only RZ universally;
do not solve a harder SZ/Gauss transport problem than the common-prime proof needs.
```
