# FLT prime-generalization Phase 23 — cyclotomic residue transport and primitive-coordinate closure

## Goal

Close the smallest honest open boundary left by Phase 22:

```text
PGEN-PRIME-COORDINATE-COPRIME-STILL-OPEN
```

The Phase-22 `PrimeTraceOneCoordinatePacket` now retains enough provenance to attempt the missing bridge.  The objective of this phase is **not** to assume coordinate coprimality, but to derive it from the QR/QNR construction together with the existing FLT-side p-adic exactness.

The preferred proof architecture is:

```text
Phase-22 integral coordinate packet
  -> transport its R/S Gauss identities to characteristic q != p
  -> simultaneous coordinate vanishing mod q forces QR and QNR products both to vanish
  -> impossible because a primitive p-th root cannot be reached by both a QR and a QNR exponent
  -> every common coordinate prime q is the exponent prime p
  -> Phase-1 residual_not_prime_sq eliminates q = p at the FLT endpoint
  -> evaluated TraceOne coordinates are primitive
  -> Phase-21 axis stripping preserves coordinate primitivity
  -> Phase-21 terminal residual has coprime conjugate principal ideals
  -> Phase-15 ideal p-th-power extraction becomes available
```

Do not prove or claim general FLT, class-group p-torsion-freeness, a class-number theorem, regular-prime theory, or real-sector elimination.

---

## A. Test-first API audit

Before production implementation, add a focused audit for the exact pinned APIs needed below.  Do not guess names.

Audit at least:

- `PrimeTraceOneCoordinatePacket`
- `PrimeTraceOneCoordinatePacket.coord`
- packet fields `map_RZ`, `gauss_form`, `gauss_difference`, `half_relation`, `norm_eq`
- `CyclotomicQRProduct.qrFinset`, `qnrFinset`, `rootFactor`
- `rootPowerMap_injective_on_nonzero`
- `qr_product_mul_qnr_product`
- `Rpoly`, `Dpoly`, `qrFactorPoly`, `qnrFactorPoly`
- `quadraticGauss`
- the pinned Gauss-sum square theorem(s), including what assumptions remain valid in positive characteristic
- `Polynomial.isRoot_cyclotomic_iff`
- `Polynomial.isRoot_cyclotomic_iff_charZero` only as comparison; do not accidentally use the char-zero theorem in the residue-field proof
- algebraic-closure construction for `ZMod q`
- `IsAlgClosed.exists_root`
- `primitiveRoots`, `IsPrimitiveRoot`
- `ZMod` cast-zero/divisibility lemmas
- `Polynomial.isUnit_resultant_iff_isCoprime`
- `Polynomial.resultant` map/base-change lemmas
- `CyclotomicRing`, `AdjoinRoot`, `IsPrimitiveRoot.adjoinEquivRingOfIntegers`, and any lift/evaluation API that can transport an integral cyclotomic identity to another characteristic
- `GTail_one_eq_GTailCyclotomicShell_of_ne_zero`
- `PrimeAdicFactorPacket.residual_not_prime_sq`
- `PrimeAdicFactorPacket.coprime_gap_unit`
- `PrimeAdicPowerSplit.residual_eq`
- Phase-21 axis stripping and ideal-coprimality endpoints
- Phase-15 `exists_eq_pow_of_isCoprime_mul_eq_pow`

Record the exact declarations actually used in `report-023.md`.

---

## B. Build a characteristic-independent residue transport for the packet identities

This is the central task of the phase.

The Phase-22 packet currently proves, over a characteristic-zero cyclotomic field `L`,

```text
map RZ = Rpoly ζ
C(Gζ) * map SZ = Dpoly ζ
RZ = 2*AZ + SZ.
```

For the common-prime argument we need the corresponding identities after reduction to a field of characteristic `q`, for `q != p`.

### Preferred route

Construct a universal/canonical cyclotomic realization over integers, then specialize it to any field containing a primitive p-th root.

Acceptable implementations include:

1. a `CyclotomicRing` route;
2. an `AdjoinRoot (cyclotomic p ℤ)` route;
3. coefficientwise divisibility by the cyclotomic polynomial, derived from the existing characteristic-zero identities and then specialized to another field.

Do **not** assume that a characteristic-zero equality of mapped integer polynomials automatically survives mod `q`.  Prove the base-change statement.

The desired reusable theorem shape is morally:

```lean
packet.map_RZ_in_any_primitive_root
packet.gauss_difference_in_any_primitive_root
```

with hypotheses sufficient for a field `K`, a primitive root `xi : K`, and a nondegenerate characteristic.

For example, after mapping packet coefficients through `ℤ -> K`:

```text
map RZ = Rpoly xi
C(Gxi) * map SZ = Dpoly xi.
```

It is fine if the precise theorem is stated through a canonical cyclotomic quotient/ring and then specialized by a separate corollary.

### Positive-characteristic Gauss square

If the existing `quadraticGauss_sq` is restricted to `[Algebra ℚ K]`, add only the minimal positive-characteristic analogue actually needed here.

For a residue characteristic `q` with

```text
q prime,
q != 2,
q != p,
xi primitive p-th root,
```

prove enough to conclude

```text
quadraticGauss xi hxi != 0.
```

A square identity

```text
G^2 = signedPrimeDiscriminant p
```

after casting to `K` is preferred if the pinned Gauss-sum API supports it cleanly.  Do not introduce a char-zero assumption into this theorem.

If the pinned Gauss-sum theorem cannot be reused in positive characteristic, stop and classify the exact blocker.  Do not postulate `G != 0`.

Suggested intermediate status:

```text
PGEN-PRIME-COORDINATE-RESIDUE-TRANSPORT-GREEN
```

---

## C. Common-prime support away from p

Let `P` be a Phase-22 coordinate packet.  Evaluate at primitive integer endpoints `z,y`.

Target theorem, up to exact type choices:

```text
Nat.Coprime z y ->
q.Prime ->
q != p ->
q | A_P(z,y) ->
q | S_P(z,y) ->
False
```

or equivalently:

```text
q prime and q divides both coordinates -> q = p.
```

### C1. Handle q = 2 separately

Do not force the QR/QNR argument through characteristic two.

A direct parity proof is preferred:

- `p` is odd;
- if `Nat.Coprime z y`, then the homogeneous prime shell
  `GTailCyclotomicShell p (z-y) y` / endpoint shell is odd;
- if both TraceOne coordinates are even, their norm is even (indeed divisible by `4` from the explicit norm form);
- contradict `packet.coord_norm_eq`.

State a reusable shell-parity lemma if useful.

### C2. Odd q != p: QR/QNR contradiction

Work in an algebraic closure of `ZMod q` (or another pinned algebraically closed extension).

1. Obtain a primitive p-th root `xi` using the cyclotomic polynomial and `q != p`.
2. Cast `z,y` and the packet polynomials into this field.
3. From common divisibility of evaluated `AZ` and `SZ`, get

   ```text
   A = 0,
   S = 0,
   R = 2*A + S = 0.
   ```

4. Use the residue-transport theorem from Part B:

   ```text
   Rpoly(xi)(z,y) = 0,
   quadraticGauss(xi) * S = Dpoly(xi)(z,y) = 0.
   ```

5. Since `G != 0`, conclude `Dpoly = 0`.
6. Expand

   ```text
   Rpoly = QR + QNR,
   Dpoly = QR - QNR.
   ```

   Since `q != 2`, conclude both evaluated QR and QNR products vanish.
7. Use product-zero to obtain

   ```text
   a in qrFinset p,  rootFactor xi a z y = 0,
   b in qnrFinset p, rootFactor xi b z y = 0.
   ```

8. Show the cast of `y` is nonzero.  If it were zero, either root-factor equation forces the cast of `z` to be zero, contradicting `Nat.Coprime z y` and primality of `q`.
9. Cancel `y` from

   ```text
   z = xi^a * y,
   z = xi^b * y
   ```

   to obtain `xi^a = xi^b`.
10. Use `rootPowerMap_injective_on_nonzero` and QR/QNR disjointness to contradict the memberships of `a` and `b`.

This theorem should not depend on FLT, `PrimeAdicFactorPacket`, class groups, or TraceOne Dedekind instances.

Preferred status:

```text
PGEN-PRIME-COORDINATE-COMMON-PRIME-SUPPORT-GREEN
```

---

## D. Optional stronger resultant/Bézout endpoint

The following empirical finite cases are worth probing but are **not required** for GREEN in Part C:

```text
p=5,7,11,13: Res(Phi_p(t), S_p(t,1)) = 1
```

If the universal cyclotomic transport from Part B makes the proof short, prove a stronger theorem that the dehomogenized `SZ` is coprime to `cyclotomic p ℤ`, or that the relevant resultant is a unit.

Do not spend the whole phase forcing this if the common-prime-support theorem is already reachable.

Possible stronger status:

```text
PGEN-PRIME-COORDINATE-BEZOUT-GREEN
```

If the resultant proof requires new class-number/cyclotomic-unit theory, record that and stay with Part C.

---

## E. Eliminate the remaining common prime p using the FLT p-adic packet

Now specialize to the actual FLT-side arithmetic source.

Let

```text
F : PrimeAdicFactorPacket p g u x
```

and evaluate the Phase-22 coordinates at

```text
z := g + u,
y := u.
```

Use

```text
F.coprime_gap_unit
```

to prove `Nat.Coprime (g+u) u`.

From Part C, every common coordinate prime equals `p`.

If `p` divides both evaluated integer coordinates, then the explicit TraceOne norm formula implies

```text
p^2 | natAbs(norm(coord)).
```

Use

```text
packet.coord_norm_eq
GTail_one_eq_GTailCyclotomicShell_of_ne_zero
```

to identify this norm with the FLT residual, and contradict

```text
F.residual_not_prime_sq.
```

Conclude the actual evaluated coordinates are coprime over `ℤ`:

```text
IsCoprime coord.fst coord.snd.
```

This is the first theorem in the series that is allowed to consume the FLT-side p-adic packet.

Preferred status:

```text
PGEN-PRIME-COORDINATE-COPRIME-FLT-GREEN
```

Do not claim the stronger arbitrary-endpoint coprimality theorem unless it is independently proved.

---

## F. Coordinate primitivity after discriminant-axis stripping

Add a neutral theorem showing that multiplying by `discrAxis s` cannot create coordinate primitivity from a nonprimitive residual.

Desired direction:

```text
IsCoprime (discrAxis s * r).fst (discrAxis s * r).snd
  -> IsCoprime r.fst r.snd.
```

Prove this directly from the explicit coordinate multiplication formula / Bézout witness.  Do not require a `GCDMonoid`.

Then combine:

1. Part E parent-coordinate coprimality;
2. Phase-21 one-axis stripping from
   `natAbs(norm w) = p * b^p` and `p ∤ b`;
3. the new stripping-preserves-primitivity lemma;
4. Phase-21 axis terminality;
5. `ideal_isCoprime_span_conj_of_coordinate_coprime_of_axis_terminal`.

The result should produce a terminal residual `r` with

```text
IsCoprime (Ideal.span {r}) (Ideal.span {conj r}).
```

---

## G. Stretch goal: connect directly to Phase 15 ideal p-th-power extraction

If Part F is green and the remaining ideal algebra is routine, continue.

From

```text
norm r = k^p
```

obtain the element identity

```text
r * conj r = (ofInt k)^p
```

and hence

```text
Ideal.span {r} * Ideal.span {conj r}
  = Ideal.span {ofInt k} ^ p.
```

Apply

```lean
DkMath.Lib.NumberTheory.exists_eq_pow_of_isCoprime_mul_eq_pow
```

to obtain

```text
∃ I, Ideal.span {r} = I^p.
```

Package this as the first fully connected arbitrary-prime bridge from the GTail/TraceOne front-end into the Phase-15 ideal-power kernel.

Preferred stretch status:

```text
PGEN-PRIME-TRACEONE-STRIPPED-IDEAL-BRIDGE-GREEN
```

Stop before class-group principalization unless all additional hypotheses are explicit.  Do not insert `classGroupPTorsionFreeAt` as an unproved fact.

---

## H. Finite regressions

Retain and extend p=3,5,7,11,13 probes.

At minimum:

- p=3: preserve the Eisenstein exception and do not force the p>=5 geometry onto it;
- p=5: check the generic coordinate packet and the new common-prime machinery at a concrete primitive endpoint;
- p=7: compare the new generic FLT-coordinate-coprime endpoint with the existing `cyclotomicSeven_coordinates_isCoprime` theorem;
- p=11,13: keep compatibility with the explicit `A11/B11`, `A13/B13` norm formulas where available.

For the optional resultant probe, also verify the already visible small cases rather than asserting a general formula from numerics.

---

## I. Axiom and source audit

Add a focused axiom audit for every new public production endpoint.

Required:

```text
no new sorry
no sorryAx
no admit
no explicit axiom
no unsafe
```

The expected inherited set remains the usual `propext`, `Classical.choice`, and `Quot.sound` where the construction requires them.

Run `git diff --check`.

---

## J. Stop classifications

Use the strongest justified status only.

```text
PGEN-PRIME-COORDINATE-RESIDUE-TRANSPORT-GREEN
  packet R/S provenance is proved stable under specialization to residue characteristic q != p.

PGEN-PRIME-COORDINATE-COMMON-PRIME-SUPPORT-GREEN
  any common evaluated coordinate prime at a primitive endpoint is p.

PGEN-PRIME-COORDINATE-BEZOUT-GREEN
  optional stronger resultant/Bézout unit theorem.

PGEN-PRIME-COORDINATE-COPRIME-FLT-GREEN
  Phase-1 p-adic exactness eliminates p for the actual PrimeAdicFactorPacket endpoint.

PGEN-PRIME-TRACEONE-STRIPPED-IDEAL-BRIDGE-GREEN
  axis stripping + conjugate coprimality + ideal p-th-power extraction are connected.
```

If the residue-transport theorem is blocked, classify the exact missing API/theorem and stop there.  In particular, do not replace it by an assumption that the Phase-22 packet identities hold in characteristic `q`.

---

## K. Suggested focused builds

Adjust exact test module names to the implementation, but include at least:

```text
lake build DkMath.NumberTheory.CyclotomicQRProduct
lake build DkMath.NumberTheory.CyclotomicQRGaussNormalization
lake build DkMath.NumberTheory.CyclotomicQRTraceOneBridge
lake build DkMath.NumberTheory.TraceOneConjugateCoprime
lake build DkMath.FLT.Prime.AdicPowerSplit
lake build DkMath.Lib.NumberTheory.IdealPowerFactor
lake build DkMathTest.FLT.Prime.<Phase23ApiAudit>
lake build DkMathTest.FLT.Prime.<Phase23Probe>
lake build DkMathTest.FLT.Prime.<Phase23AxiomAudit>
lake build DkMath.FLT.Seven
git diff --check
```

## Non-goals

Do not prove or claim:

- general FLT;
- `classGroupPTorsionFreeAt` for arbitrary prime-discriminant TraceOne orders;
- class-number formulas;
- regular-prime theorems;
- real `Fin p` sector elimination;
- a general unit resultant formula unless actually kernel-checked.
