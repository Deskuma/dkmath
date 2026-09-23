# Review-005 — GAGE-005 FLT2 gauge calibration

Result: APPROVED — Outcome A

## 1. Judgment

GAGE-005 successfully exposes the exponent-2 arithmetic landing mechanism without hiding it behind the final Pythagorean classification.

The implementation reaches the intended chain:

~~~text
primitive square solution
  -> exactly one leg even
  -> square body = Gap * Beam
  -> gcd(Gap,Beam) = 2
  -> strip the common gauge 2
  -> coprime half-gap / half-beam
  -> normalized body is a square
  -> each stripped factor is a square
~~~

This is exactly the calibration required before connecting odd-prime exponent gauge to the cyclotomic resolver.

## 2. Exact shared gauge

The theorem:

~~~text
Nat.gcd (z-y) (z+y) = 2
~~~

is proved in the intended way:

- upper bound from the generic PowerGapBeam gcd theorem at degree 2;
- lower bound from odd y and odd z, hence both factors even.

The proof does not use the final Pythagorean parametrization.

## 3. Gauge stripping

The implementation proves exact multiplication identities for:

~~~text
A = (z-y)/2
B = (z+y)/2
X = x/2
~~~

before using them. This avoids accidental dependence on truncating Nat division.

`Nat.Coprime A B` is obtained from the exact gcd=2 theorem, and:

~~~text
X^2 = A*B
~~~

is obtained by cancelling the shared factor 4.

## 4. Square landing

`DkMath.Lib.NumberTheory.power_factor_split` is reused exactly as intended to obtain:

~~~text
A = r^2
B = s^2
~~~

and the public packet records:

~~~text
z-y = 2*r^2
z+y = 2*s^2.
~~~

No duplicate coprime-power extraction proof was added.

## 5. Orientation

`primitiveSquareSolution_oriented_gauge_split` correctly keeps the result symmetric by allowing leg exchange. The public meaning is therefore not tied to an arbitrary choice of which leg is even.

## 6. Relationship to GAGE-004

The implementation preserves the intended separation:

~~~text
GAGE-004  midpoint correction at exponent 2 is zero
GAGE-005  primitive square landing has exact shared gauge 2 and splits after stripping it
~~~

Neither theorem is incorrectly used as a substitute for the other.

## 7. GAGE-006 design freeze

GAGE-006 should create the odd-prime bridge under the FLT prime architecture, not under the generic Gauge facade.

Preferred owner:

~~~text
DkMath/FLT/Prime/PrimeGaugeBridge.lean
~~~

The crucial observation is that:

~~~text
PrimeExponentGauge p = InnerRowSupportPrime p p
~~~

already contains `p.Prime`. Therefore the new bridge can consume `PrimeExponentGauge p` directly and locally construct the `Fact p.Prime` instance required by the existing cyclotomic/ideal machinery.

The bridge should not merely re-assume `p.Prime` as an unrelated input.

Proceed to instruction-006.md.