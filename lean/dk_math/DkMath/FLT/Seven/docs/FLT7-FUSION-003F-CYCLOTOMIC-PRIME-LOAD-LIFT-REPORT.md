# FLT7-FUSION-003F cyclotomic prime-load lift report

Date: 2026-07-30

## Result

FUSION-003F Events 1–10 are implemented. This checkpoint has **Outcome A**.
The two unresolved row-two cells are not asserted to be seventh powers.
Instead, their scalar loads are allocated canonically and integrally among the
three real-pair cores, and the load-free residual in every core is extracted
as a seventh power up to a unit.

The implementation is split into the following modules:

```text
SevenRamifiedFusionCyclotomicPrimeAddress
SevenRamifiedFusionRealPairLoadAllocation
SevenRamifiedFusionLoadedBranchRecovery
SevenRamifiedFusionLoadNorm
SevenRamifiedFusionLoadedCore
SevenRamifiedFusionPrimeLoadAddress
SevenRamifiedFusionPrimeLoadValuation
SevenRamifiedFusionDirectChartObstruction
```

## 1. Quotient-prime cyclotomic address

For every prime `q` dividing the signed integer `quotientRoot`, Lean constructs
the canonical unit

```text
t = signedRightRoot / signedLeftRoot in (ZMod q)^x.
```

The construction uses the signed roots themselves. It proves

```text
t^7 = 1
t != 1
orderOf t = 7
q % 7 = 1
q % 14 = 1.
```

No residue enumeration is used. Nonvanishing of the two signed roots follows
from their integral Bezout identity. The inequality `t != 1` uses the exact
gap identity, coprimality of `gapRoot` and `quotientRoot`, and `q != 7`.

The public packet

```lean
RamifiedSignedRootDepthPacket.QuotientPrimeMuSevenAddress
```

stores only the prime and divisibility certificate. Its `ratio` is
definitionally reconstructed from the signed roots, preventing an arbitrary
orientation witness from entering the packet.

The same support result is exposed directly for primes dividing either
`routing.c21` or `routing.c22`.

## 2. Real-pair residue coordinate and evaluation

For a quotient-prime address, define

```text
beta = 1 + t + t^-1.
```

Lean proves

```text
beta^3 - 2*beta^2 - beta + 1 = 0
beta != 3.
```

The first identity comes from the seventh cyclotomic sum. The second uses the
fact that the defining cubic evaluates to `7` at `3`, while `q != 7`.

This produces the explicit ring homomorphism

```lean
evalAlphaRoot : SevenRealCubicInt ->+* ZMod q
```

with `alpha` mapped to `beta`. Direct coordinate expansion and the cubic
relation prove multiplicativity. At the canonical address Lean then proves

```text
evalAlphaRoot(P_0) = 0
evalAlphaRoot(C_0) = 0
evalAlphaRoot(theta) != 0.
```

Thus the local address belongs to the normalized real-pair core and not to
the ramified prime above seven.

## 3. Canonical integral load allocation

Inside the principal real cubic order, fix the local gcd choice supplied by
`IsBezout.toGCDDomain` and define

```text
load21_i = gcd((c21 : O), C_i)
load22_i = gcd((c22 : O), C_i).
```

The generic theorem

```lean
associated_gcd_three_of_dvd_product
```

shows that a divisor of a product of three pairwise-coprime elements is,
up to a unit, the product of its three gcd projections. Applied to the pair
cores, it gives

```text
load21_0*load21_1*load21_2 ~ c21
load22_0*load22_1*load22_2 ~ c22.
```

The two scalar cells are coprime after mapping into the cubic order. Hence
their two projections in one core are coprime, and their product divides that
core. The stripped core `D_i` is selected from this divisibility witness, not
by field division:

```text
C_i = (load21_i*load22_i)*D_i.
```

Since `D_i` divides `C_i`, the three stripped cores remain pairwise coprime.

## 4. Unconditional residual seventh powers

The exact signed routing identity supplies

```text
|quotientRoot| = c21*c22*t^7.
```

Combining this with the core-product identity, both load-product identities,
and the exact integral reconstruction above permits cancellation of the
nonzero combined load product:

```text
D_0*D_1*D_2 ~ t^7.
```

The existing PID coprime-power extractor then gives, for all three indices,

```text
root_i^7 ~ D_i.
```

`RealPairLoadedPowerSplit` retains:

```text
the canonical gcd load families
their equality with the public load definitions
the residual roots and their stripped-core associations
the loaded core association
both three-way scalar load-product associations.
```

The synthesis theorem is

```lean
nonempty_ramifiedFusionLoadedCorePacket
```

and is unconditional for every coherent signed routing packet.

## 5. Galois coherence

A ring automorphism need not preserve the selected gcd literally. The correct
general statement is therefore:

```text
sigma(gcd(a,b)) ~ gcd(sigma(a),sigma(b)).
```

The scalar loads are fixed by `sigma`, while the pair cores form a
unit-twisted orbit. Lean consequently proves the full cycles

```text
sigma(load21_0) ~ load21_1
sigma(load21_1) ~ load21_2
sigma(load21_2) ~ load21_0

sigma(load22_0) ~ load22_1
sigma(load22_1) ~ load22_2
sigma(load22_2) ~ load22_0.
```

The combined two-cell loads satisfy the same associated cycle.

## 6. Exact load norms

The Galois cycle makes the three absolute norms in each load family equal.
Taking norms of the load-product association gives their cube:

```text
product_i |norm(load21_i)| = c21^3
product_i |norm(load22_i)| = c22^3.
```

Injectivity of the natural-number cube therefore proves the stronger
indexwise identities

```text
|norm(load21_i)| = c21
|norm(load22_i)| = c22
|norm(load21_i*load22_i)| = c21*c22.
```

The stripped-core norm ledger is exact:

```text
c21*c22*|norm(D_i)| = |quotientRoot|.
```

After cancelling the nonzero two-cell load, all three stripped cores have the
same absolute norm, and that norm is a natural seventh power.

This is the sign- and integrality-preserving norm identity predicted at the
end of FUSION-003E.

## 7. Branch A recovery

If witnesses

```text
c21 = a^7
c22 = b^7
```

are supplied, pairwise coprimality of each three-load family and its product
association extract every individual load as a seventh power up to a unit.
Multiplying those two load roots by the unconditional residual root gives a
seventh root for the original core.

The endpoint

```lean
nonempty_realPairCoreAssociatedPowerSplit_via_loaded_absorption
```

therefore recovers the existing conditional
`RealPairCoreAssociatedPowerSplit` through the new loaded route. This is the
requested Event 10 specialization; no theorem from the unrelated
RAMIFIED-006 routing board is reused.

## 8. Prime-to-gcd-load ideal address beyond the requested stop

The first immediate post-003F prediction was also implemented. A

```lean
QuotientPrimeGCDLoadAddress
```

retains a choice of the `c21` or `c22` family and a prime divisor `q` of that
cell. It reconstructs the canonical `mu_7` address and its evaluation kernel.
At this address Lean proves:

```text
q % 14 = 1
C_0 is in the kernel
theta is not in the kernel
the addressed scalar and its gcd load are in the kernel
the competing coprime scalar and load are outside the kernel
the same-family loads at indices 1 and 2 are outside the index-0 kernel
span(addressedLoad) <= evalKernel.
```

The evaluation is surjective. Consequently the kernel is maximal, its
contraction to the integers is exactly `(q)`, and its residue quotient has
cardinality `q`. The addressed load also retains the exact norm identity from
the previous section.

The follow-up valuation module defines the exact factor count

```text
e_P = multiplicity of evalKernel in span(addressedLoad)
```

and proves

```text
evalKernel^k divides span(addressedLoad) iff k <= e_P
addressedLoad belongs to evalKernel^k iff k <= e_P
1 <= e_P
q^e_P divides the addressed scalar cell
e_P <= padicValNat q cell.
```

The equality with the full rational `q`-adic exponent is exposed with its
exact remaining condition:

```text
e_P = padicValNat q cell
  iff
q^(e_P+1) does not divide cell.
```

The subsequent Galois-splitting refinement removes this checkpoint-local
qualification: after proving that the three cyclic kernels split `(q)`
completely, `SevenRamifiedFusionPrimeLoadExactValuation` proves the
unconditional equality

```text
e_P = padicValNat q cell.
```

`SevenRamifiedFusionPrimeLoadGlobalFactorization` then reconstructs the
principal load ideal as the finite product of all supported kernel powers.

This is a genuine ideal-level fusion of

```text
integer gcd address
  -> local mu_7 ratio
  -> real-pair core kernel
  -> cubic PID gcd load.
```

## 9. Direct signed-chart obstruction

The first apparent global shortcut after the loaded split is now ruled out
formally. The exact signed identities give

```text
signedRightRoot^7 - signedLeftRoot^7
  = 7^5 * gapRoot * quotientRoot.
```

Both remaining factors are prime to seven, so Lean proves

```text
7^6 does not divide
  signedRightRoot^7 - signedLeftRoot^7.
```

An integer seventh power divisible by seven is divisible by `7^7`.
Consequently there is no integer `c` with

```text
signedRightRoot^7 - signedLeftRoot^7 = c^7,
```

and hence no direct chart

```text
SignedFermatSevenChart signedRightRoot (-signedLeftRoot) c.
```

This is **Outcome D** for the naive direct signed-root chart. The obstruction
is mathematical, not a missing Lean API.

## 10. Exact boundary and next prediction

FUSION-003F does not prove that `c21` or `c22` is a seventh power. It proves
the stronger and more useful unconditional decomposition

```text
C_i ~ load21_i * load22_i * residualRoot_i^7
```

with canonical integral loads, exact scalar-product allocation, Galois
coherence, and exact norms.

In general one must not strengthen

```text
span(addressedLoad) <= evalKernel
```

to equality. A routing cell and hence its gcd load may contain several
rational primes or prime powers, whereas `evalKernel` is one degree-one prime
selected by `q` and the canonical ratio. The later cyclic-kernel splitting
does, however, prove the exact multiplicity equality and the finite global
factorization without making this false single-kernel equality.

Post-003F continuation now constructs:

- a concrete rank-six quadratic carrier with explicit conjugate seventh roots;
- the oriented factor identity and all canonical local ratio evaluations;
- two distinct maximal comaximal conjugate degree-one kernels over the common
  real-cubic address.

It still does not construct:

- the reverse ideal containment needed for exact conjugate-fibre product
  equality;
- a primitive reconstructed integer or quadratic Fermat chart;
- a strict well-founded decrease;
- an inhabited recursive descent provider;
- FLT7.

The ROADMAP stop gate remains active until the reconstructed primitive chart
and its strict global decrease are both inhabited.

The predicted degree-six bridge was realized as a quadratic extension of the
real cubic order with

```text
zeta^2 - (alpha - 1)*zeta + 1 = 0.
```

It should prove

```text
(R-zeta*L)*(R-zeta^-1*L) = realPairCarrier 0
```

and extends each canonical local address by `zeta |-> ratio`. The remaining
local stop point is the reverse containment identifying the extended common
real prime with the product of its two conjugate degree-one primes.
