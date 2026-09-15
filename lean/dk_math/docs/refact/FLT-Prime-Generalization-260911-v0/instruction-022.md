# FLT prime-generalization Phase 22 — arbitrary-prime primitive-coordinate / cyclotomic bridge

## Status entering this phase

Phase 21 ended with:

```text
PGEN-TRACEONE-CONJUGATE-COPRIME-KERNEL-GREEN
PGEN-PRIME-COORDINATE-COPRIME-CYCLOTOMIC-BRIDGE-MISSING
```

The neutral TraceOne arithmetic is now available:

- arbitrary odd-prime TraceOne coordinates from the QR/QNR/Gauss construction,
- prime discriminant axis and axis-depth stripping,
- maximal-order / Dedekind structure,
- ideal-level conjugate-coprime kernel once suitable primitive-coordinate data is supplied,
- ideal p-th-power extraction / class-group principalization,
- unit-sector normalization.

The remaining upstream bridge is that the Phase-13 coordinates are currently exposed only through a norm endpoint.  The proof provenance needed to recover coordinate primitivity is not retained by the public theorem.

This phase must attack that bridge honestly.  Do **not** add a receiver hypothesis saying the coordinates are coprime.

## Goal

For the integer coordinate pair produced by the arbitrary-prime QR/QNR/Gauss construction, prove enough primitivity to feed the Phase-21 conjugate-coprime kernel.

Preferred strongest endpoint:

```text
Nat.Coprime z y
  -> IsCoprime (A_p(z,y)) (S_p(z,y))
```

A weaker but sufficient fallback is:

```text
q prime
q | A_p(z,y)
q | S_p(z,y)
Nat.Coprime z y
  -> q = p
```

combined with the already-proved FLT-side fact

```text
padicValNat p (GTail p 1 g u) = 1
```

which excludes simultaneous p-divisibility of both coordinates because it would force `p^2` to divide their TraceOne norm.

If either route closes, connect the result through one-axis stripping to the Phase-21 ideal conjugate-coprime endpoint.

---

## A. Test-first pinned API audit

Audit the current checkout before production changes.  In particular inspect exact signatures for:

```text
Polynomial.resultant
Polynomial.IsCoprime
Polynomial.isCoprime_iff_resultant_isUnit   -- if present / exact pinned equivalent
MvPolynomial.eval
MvPolynomial.aeval
MvPolynomial.rename
MvPolynomial.bind₁
MvPolynomial.coeff
MvPolynomial.map
Ideal.Quotient
Ideal.IsPrime
Ideal.IsMaximal
IsPrimitiveRoot
primitiveRoots
ZMod
CharP
```

Also pin the existing DkMath declarations:

```text
exists_integral_gauss_form
map_modTwo_eq_of_integral_gauss_form
exists_half_difference
exists_prime_traceOne_coordinates
GTail_one_eq_GTailCyclotomicShell_of_ne_zero
PrimeAdicFactorPacket.residual_exact_one
PrimeAdicFactorPacket.residual_not_prime_sq
PrimeAdicPowerSplit.residual_eq
common_divisor_dvd_discrAxis_of_coordinate_coprime
ideal_isCoprime_span_conj_of_coordinate_coprime_of_axis_terminal
PrimeDiscriminantPacket.exists_terminal_discrAxis_mul_of_natAbs_norm_eq_prime_mul_pow
```

Do not rely on online Mathlib names without checking the pinned checkout.

---

## B. Preserve Phase-13 coordinate provenance

The existing endpoint

```lean
exists_prime_traceOne_coordinates
```

returns only `AZ`, `SZ` plus the evaluated norm equality.  That is too weak for a cyclotomic coprimality proof.

Add a production packet/theorem that retains the actual Phase-13 construction data.  Suggested shape (adapt exact fields to the implementation):

```lean
structure PrimeTraceOneCoordinatePacket
    (L : Type*) [Field L] [Algebra ℚ L]
    (p : ℕ) [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p) where
  RZ SZ AZ : MvPolynomial (Fin 2) ℤ
  map_RZ :
    MvPolynomial.map (algebraMap ℤ L) RZ = Rpoly (p := p) ζ
  gauss_form :
    MvPolynomial.C 4 * primeCyclotomicShellPoly p =
      RZ ^ 2 - MvPolynomial.C (signedPrimeDiscriminant p) * SZ ^ 2
  gauss_difference :
    MvPolynomial.C (quadraticGauss ζ hζ) *
      MvPolynomial.map (algebraMap ℤ L) SZ = Dpoly (p := p) ζ
  half_relation :
    RZ = MvPolynomial.C 2 * AZ + SZ
```

Expose an existence theorem constructed from the existing Phase-13 proof.  Do not duplicate the Gauss descent.

Also expose the evaluated coordinate element, for example:

```lean
def coord (P : PrimeTraceOneCoordinatePacket ...) (z y : ℤ) :
    TraceOneInt (signedPrimeParameter p) :=
  ⟨eval ... P.AZ, eval ... P.SZ⟩
```

and recover the old norm endpoint as a corollary.

The packet is allowed to be existential/noncomputable.  The important point is that the QR/QNR provenance is no longer discarded.

---

## C. Strong route first: resultant / Bézout-unit audit

Before building a heavier residue-field proof, test whether the coordinate polynomials are already universally Bézout-coprime.

Dehomogenize at `Y = 1`:

```text
A_p(T) := AZ(T,1)
S_p(T) := SZ(T,1)
```

Audit/probe the known explicit cases where formulas are available.

The current explicit p=7,11,13 coordinate formulas numerically/algebraically suggest:

```text
resultant(A_7,S_7)   = -1
resultant(A_11,S_11) = -1
resultant(A_13,S_13) =  1
```

Treat this only as a probe hint, not as an assumption.

Check p=5 as well if an exact TraceOne formula is available without inventing a GoldenInt transport.

If the pinned resultant API and the QR/QNR provenance permit a general proof that the resultant is a unit (or directly that the dehomogenized pair is `IsCoprime` over `ℤ[T]`), pursue it.

If successful, homogenize/evaluate carefully to obtain integer coordinate coprimality for primitive `(z,y)`.  Handle the cases where a prime divides `y` separately rather than silently dividing by `y`.

Desired classification for this route:

```text
PGEN-PRIME-COORDINATE-BEZOUT-GREEN
```

Do **not** spend the entire phase forcing a general resultant theorem if the API becomes substantially heavier than the fallback route below.

---

## D. Fallback route: common-prime support from QR/QNR

If the unit-resultant route is not immediately available, prove the weaker support theorem.

Target shape:

```lean
theorem prime_eq_exponent_of_dvd_both_primeTraceOneCoordinates
    {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hp2 : p ≠ 2)
    (hzy : Nat.Coprime z y)
    (hqA : (q : ℤ) ∣ Aeval)
    (hqS : (q : ℤ) ∣ Seval) :
    q = p
```

or an equivalent statement saying every common prime divisor divides `p`.

### Intended cyclotomic mechanism

From

```text
R = 2*A + S
D = G_p*S = QR - QNR
R = QR + QNR
```

simultaneous divisibility of `A,S` forces the two QR/QNR half-products to vanish after reduction at a prime over `q` (with a separate treatment of `q = 2` if required).

For `q ≠ p`, reduction of the primitive p-th root must retain order `p`; otherwise `ζ - 1` would lie above a rational prime different from the unique ramified prime `p`.  A QR factor and a QNR factor cannot vanish at the same primitive endpoint unless both original endpoint coordinates vanish modulo `q`, contradicting `Nat.Coprime z y`.

This description is guidance, not permission to assume unavailable ideal facts.  If the prime-over-q route is too expensive in the pinned APIs, record the exact missing theorem and try a polynomial/resultant formulation instead.

Possible equivalent target:

```text
q ∣ gcd(Aeval, Seval) -> q ∣ p
```

Desired classification:

```text
PGEN-PRIME-COORDINATE-COMMON-PRIME-SUPPORT-GREEN
```

---

## E. Eliminate the remaining ramified prime with the Phase-1 p-adic theorem

This part should be independent of how Part C/D is proved.

For

```lean
P : PrimeAdicFactorPacket p g u x
```

set the cyclotomic endpoints

```text
z := g + u
y := u
```

and prove

```text
Nat.Coprime z y
```

from `P.coprime_gap_unit`.

Instantiate a Phase-13 coordinate packet at `(z,y)` and identify its norm with

```text
GTail p 1 g u
```

using `GTail_one_eq_GTailCyclotomicShell_of_ne_zero` (or the exact pinned bridge).

If a prime `q` divides both integer coordinates, Part C/D should reduce to `q = p` (unless the strong route already gives contradiction directly).

Then show:

```text
p | Aeval -> p | Seval -> p^2 | norm coord
```

by the explicit TraceOne norm polynomial.  Contradict:

```lean
P.residual_not_prime_sq
```

or equivalently `P.residual_exact_one`.

Target:

```lean
theorem primeAdicFactorPacket_traceOneCoordinates_isCoprime
    (P : PrimeAdicFactorPacket p g u x) :
    ... -> IsCoprime Aeval Seval
```

Package the coordinate witness conveniently; avoid making downstream clients repeatedly unpack existential Phase-13 polynomials.

Desired classification:

```text
PGEN-PRIME-COORDINATE-COPRIME-GREEN
```

---

## F. Axis-stripped conjugate coprimality from parent coordinates

Phase 21 currently has a theorem requiring coordinate coprimality of the element whose conjugate ideals are being compared.  For the FLT route, the useful pattern is slightly different:

```text
C = discrAxis s * beta
coordinates(C) are coprime
beta is axis-terminal
```

This is exactly the pattern already used by the specialized p=7 proof.

Add a neutral ideal-level wrapper:

```lean
theorem ideal_isCoprime_span_conj_of_parent_coordinate_coprime_of_axis_stripped
    (hcoords : IsCoprime C.fst C.snd)
    (hC : C = discrAxis s * beta)
    (hterminal : ¬ discrAxis s ∣ beta)
    ... :
    IsCoprime (Ideal.span ({beta} : Set (TraceOneInt s)))
      (Ideal.span ({conj beta} : Set (TraceOneInt s)))
```

Proof idea:

- any common divisor / common ideal contribution of `beta` and `conj beta` also contributes to `C` and `conj C`,
- parent-coordinate coprimality forces it into the discriminant axis,
- beta terminality excludes that axis contribution.

Prefer reusing the Phase-21 neutral lemmas; do not reintroduce a GCDMonoid requirement.

---

## G. Compose with one-axis norm stripping

For a `PrimeAdicPowerSplit`, the residual has

```text
GTail p 1 g u = p * b^p
p ∤ b.
```

Using the Phase-13 coordinate element `C` with this norm and the Phase-21 theorem

```lean
PrimeDiscriminantPacket.exists_terminal_discrAxis_mul_of_natAbs_norm_eq_prime_mul_pow
```

obtain

```text
C = discrAxis s * beta
norm beta = k^p
¬ discrAxis s ∣ beta
```

(with the exact sign conventions already handled by the Phase-21 theorem).

Combine with Part E/F to obtain:

```text
IsCoprime (span {beta}) (span {conj beta})
```

This is the actual bridge needed by Phase 15.

If the ideal product identity is straightforward from `beta * conj beta = ofInt (norm beta)`, also package the immediate input theorem for `IdealPowerFactor`, but do not over-expand scope into class-group or sector elimination.

Suggested endpoint packet:

```lean
structure PrimeTraceOneStrippedIdealPacket (...) where
  beta : TraceOneInt (signedPrimeParameter p)
  parent_eq : C = discrAxis _ * beta
  terminal : ¬ discrAxis _ ∣ beta
  norm_eq_pow : norm beta = k ^ p
  conjugateIdeals_coprime :
    IsCoprime (Ideal.span {beta}) (Ideal.span {conj beta})
```

Desired classification if this closes:

```text
PGEN-PRIME-TRACEONE-STRIPPED-IDEAL-BRIDGE-GREEN
```

---

## H. Finite regressions

Add focused tests for:

```text
p=3   preserve the Eisenstein exception; do not force the generic one-axis story if hypotheses differ
p=5   TraceOneInt 1 coordinate support / p-adic exclusion
p=7   compare with PrimitiveCoordinateCoprime and QuadraticConjugateCoprime
p=11  TraceOneInt (-3)
p=13  TraceOneInt 3
```

For p=7, explicitly compare the new generic result with the existing specialized theorem instead of merely compiling both independently.

For p=11/13, use the explicit coordinate formulas already present in the repository when useful for resultants / gcd sanity checks.

---

## I. Axiom / source audit

Require:

```text
git diff --check
```

Scan all fresh Phase-22 production/test sources for:

```text
sorry
sorryAx
admit
axiom
unsafe
```

Print axioms of every new public theorem.  Standard inherited
`propext`, `Classical.choice`, `Quot.sound` are acceptable; report anything else.

Production modules must remain neutral where practical.  A theorem that explicitly consumes `PrimeAdicFactorPacket` may import `DkMath.FLT.Prime.AdicPowerSplit`, but the underlying polynomial/cyclotomic coordinate lemmas should remain under `DkMath.NumberTheory` and not depend on FLT receivers.

---

## J. Stop conditions and classifications

Use the strongest honest classification achieved:

```text
PGEN-PRIME-COORDINATE-BEZOUT-GREEN
PGEN-PRIME-COORDINATE-COMMON-PRIME-SUPPORT-GREEN
PGEN-PRIME-COORDINATE-COPRIME-GREEN
PGEN-PRIME-TRACEONE-STRIPPED-IDEAL-BRIDGE-GREEN
```

If blocked, use a precise boundary such as:

```text
PGEN-PRIME-COORDINATE-RESULTANT-API-BLOCKED
PGEN-CYCLOTOMIC-REDUCTION-AT-Q-BRIDGE-MISSING
PGEN-PRIME-COORDINATE-COPRIME-STILL-OPEN
```

Do not replace a failed proof with a structure field assumption or receiver theorem that simply postulates coprimality.

## Report

Write:

```text
docs/refact/FLT-Prime-Generalization-260911-v0/report-022.md
```

The report must clearly distinguish:

1. what is proved for the raw arbitrary-prime coordinate polynomials,
2. what additionally uses `PrimeAdicFactorPacket.residual_exact_one`,
3. what is proved only after discriminant-axis stripping,
4. what remains conditional or open.
