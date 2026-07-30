# FLT7-FUSION-003E real-pair coprimality and norm-gate report

Date: 2026-07-30

## Result

FUSION-003E is implemented through the exact routing obstruction. The new
module is:

```text
DkMath.FLT.Seven.SevenRamifiedFusionRealPairCoprimalityNormGate
```

Outcome A applies to the real-pair coprimality, Galois naturality, norm gate,
column-three split, and conditional PID extraction. Outcome C applies only to
the two surviving row-two routing cells.

## 1. Direct Bezout bridge

Writing

```text
r = signedRightRoot
l = signedLeftRoot
d = gapRoot,
```

the packet supplies `IsCoprime l r` and `r-l = 7^4*d`. If
`u*l + v*r = 1`, Lean verifies the two substitutions

```text
(u+v)*r - u*7^4*d = 1
(u+v)*l + v*7^4*d = 1.
```

They combine to give

```text
IsCoprime (r*l) d.
```

This proof uses no prime factorization and no scalar-prime transport from the
cubic order.

After mapping into `SevenRealCubicInt`, an explicit modulo-seven Bezout
identity proves the scalar `R = r*l` coprime to the Eisenstein axis. Together
with `R` coprime to `d` and the unit `thetaSevenUnit`, this gives

```text
IsCoprime R H
IsCoprime R C_i
```

for the common high term `H` and every normalized pair core `C_i`.

## 2. Pairwise core coprimality

Lean proves generically for distinct `i,j : Fin 3`:

```text
IsUnit (pairAxisUnit i - pairAxisUnit j)
C_i - C_j = -(pairAxisUnit i - pairAxisUnit j) * R.
```

The affine Bezout transformation then yields

```text
Pairwise (fun i j => IsCoprime C_i C_j).
```

Thus the coprimality gap reported at FUSION-003D is closed without the
previously predicted integer-to-cubic prime-divisor transport.

## 3. Galois naturality and exact norm

The real pair carriers cycle exactly:

```text
sigma(P_0) = P_1
sigma(P_1) = P_2
sigma(P_2) = P_0.
```

After cancelling the nonzero Eisenstein axis from `P_i = theta*C_i`, Lean
obtains the unit-twisted core orbit:

```text
C_1 = pairAxisUnit 1 * sigma(C_0)
C_2 = pairAxisUnit 2 * sigma^2(C_0).
```

The cubic norm is invariant under `sigma`, the two displayed pair-axis units
have norm one, and `norm theta = -7`. Combining these facts with the carrier
product gives, for every `i`,

```text
norm C_i = -quotientRoot.
```

Consequently a hypothesis `C_i = unit * x^7` forces `quotientRoot` to be a
signed integer seventh power. This is intentionally a guard, not an
unconditional extraction.

## 4. Coherent routing audit

For the coherent signed `3 x 3` routing board, Lean proves that all three
cells in the pure seventh-power column split:

```text
c13 = a^7
c23 = b^7
c33 = 1^7.
```

The quotient row therefore has the exact form

```text
|quotientRoot| = c21 * c22 * b^7.
```

The two remaining cells are exposed as their canonical gcd addresses:

```text
c21 = gcd(|quotientRoot|, |innerFst|)
c22 = gcd(|quotientRoot|, |innerFst + innerSnd|).
```

Most importantly, both directions are formalized:

```text
quotientRoot is a signed seventh power
  iff
c21 is a natural seventh power and c22 is a natural seventh power.
```

This is the exact norm/routing gate; no scalar load is hidden.

## 5. Conditional Branch A is complete

Assuming witnesses that `c21` and `c22` are seventh powers, Lean now:

1. reconstructs a signed seventh-power `quotientRoot`;
2. proves `C_0*C_1*C_2` is associated to a seventh power;
3. combines that product with pairwise core coprimality;
4. applies the principal-ideal-domain extraction separately to all three
   cores.

The resulting packet contains

```text
Associated (root_i^7) C_i
```

for `i = 0,1,2`. The stronger special case `c21 = c22 = 1` is also exposed
as a direct constructor.

## 6. Exact stopping point and prediction

The current terminal provenance does not identify the signed-routing
`c21,c22` with seventh powers. The earlier
`RamifiedSecondCoordinateRoutingPacket.c21_eq_one` concerns a different
RAMIFIED-006 routing board with different margins; transferring that result
would require a new coherence theorem and cannot be done by matching field
names.

The normalized product equation and pairwise-coprime column margins alone
permit arbitrary prime loads to be routed into `c21` or `c22`. Therefore they
do not imply the missing seventh-power statements.

The next useful checkpoint should be one of:

```text
FUSION-003F-A:
  prove a provenance/coherence comparison that controls the two gcd addresses;

FUSION-003F-B:
  attach explicit signed scalar loads to a loaded-core packet, with a proved
  norm equation before attempting division or extraction.
```

Branch B must preserve signs and integrality. Merely dividing a cubic core by
a natural routing cell is not currently justified, and multiplying by a
scalar changes the cubic norm by its cube, not linearly. No loaded core is
invented in this checkpoint.

## 7. Excluded claims

This checkpoint does not prove:

- that `c21` or `c22` is unconditionally a seventh power;
- an oriented degree-six cyclotomic factor;
- a primitive reconstructed Fermat chart;
- strict descent or a descent provider;
- FLT7.

