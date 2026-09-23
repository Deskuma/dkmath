# Exponent Unit Gauge v0 — closure summary

Branch: `research/Exponent-Unit-Gauge-260923-v0`

Status: **COMPLETE — GAGE-000 through GAGE-007 approved**

## 1. What v0 established

The campaign separates two different observations that were previously scattered across DkMath:

~~~text
ExponentGauge
  observes the exponent through Pascal/binomial prime support and p-adic depth

ValueGauge
  observes a value through prime-valuation residues modulo an exponent period
~~~

and then connects them to landing/resolution mechanisms without claiming a general FLT theorem.

## 2. Exponent-side result

The Pascal row now exposes:

~~~text
prime row -> PrimeExponentGauge p
prime-power row -> PrimePowerExponentGauge p e
common inner support prime + 1<n -> n is a positive power of that same prime
interior Pascal gcd -> prime-power purity detector
~~~

The arithmetic is primarily reused from the existing PascalPrimeDial/BinomialPrimePower layer and pinned Mathlib Lucas/Kummer/gcd results.

## 3. Value-side result

The value-side gauge is:

~~~text
p |-> v_p(a) mod n
~~~

implemented as a semantic facade over existing StructuralArithmetic prime-coordinate projection.

Exact n-th powers land in the zero residue sector, and multiplication by an n-th power preserves the ValueGauge observation.

`ValueGaugePure` includes an explicit nonzero guard.

## 4. Exponent two calibration

The denominator-free midpoint defect:

~~~text
M_d(x,u)
  = 2^(d-1) * ((x+u)^d - x^d)
    - d*u*(2*x+u)^(d-1)
~~~

has the calibrated values:

~~~text
M_2 = 0
M_3 = u^3
M_4 = 4*u^3*(2*x+u).
~~~

For primitive positive square landing:

~~~text
x^2 = (z-y)(z+y)
gcd(z-y,z+y) = 2
~~~

and after stripping the shared gauge 2:

~~~text
A = (z-y)/2
B = (z+y)/2
X = x/2

gcd(A,B) = 1
X^2 = A*B
A = r^2
B = s^2.
~~~

Thus exponent two is calibrated as exact positive landing with a visible gauge-2 split.

## 5. Odd-prime resolver

`PrimeExponentGauge p` is now a public entry point into the existing prime cyclotomic chain:

~~~text
PrimeExponentGauge p
  -> p.Prime
  -> homogeneous Phi_p evaluation
  -> GTail / GN
  -> cyclotomic principal-ideal absNorm
  -> ValueGauge preservation
  -> TraceOne scalar norm
~~~

The p = 3, 5, 7 dedicated scalar calibrations are exposed through the same gauge vocabulary.

Only scalar compatibility is claimed between cyclotomic and TraceOne carriers.

## 6. Landing vocabulary

The neutral public API now includes:

~~~text
PowerLanding
CorePowerLanding
AdditiveLanding
PositiveAdditiveLanding
~~~

with the necessary implication:

~~~text
nonzero PowerLanding -> ValueGaugePure
~~~

and the TraceOne arbitrary-power/Core-image receiver is adapted to `CorePowerLanding`.

## 7. Fixed-exponent status

~~~text
2 : positive additive landing + exact shared-gauge-2 square split
3 : positive additive non-landing, via completed FLT3 endpoint
5 : positive additive non-landing, via completed FLT5 endpoint
7 : exponent gauge + cyclotomic/TraceOne resolver only;
    terminal positive additive non-landing remains open in this campaign
~~~

## 8. The structural identity exposed by the campaign

For endpoint coordinates y,z and gap x := z-y:

~~~text
z^d - y^d
  = (z-y) * (z^(d-1) + z^(d-2)y + ... + y^(d-1))
  = x * GN_d(x,y).
~~~

The gap `x = z-y` is exponent-independent. The exponent-dependent structure is carried by the GN/cofactor side.

For prime p, that carrier is connected to the homogeneous cyclotomic polynomial and then to norm/ideal/TraceOne scalar realizations.

## 9. What v0 deliberately does not prove

- perfect-power reconstruction from zero ValueGauge residues;
- generic higher-degree midpoint positivity/uniqueness;
- universal additive non-landing for all prime exponents;
- terminal exponent-7 positive non-landing;
- arbitrary-prime class-group/unit-sector elimination;
- quotient `K*/(K*)^n` machinery;
- general FLT.

## 10. Closure

The v0 objective is met: DkMath now has a coherent, kernel-checked vocabulary and bridge architecture for exponent gauge, value gauge, exponent-two calibration, odd-prime cyclotomic resolution, and landing boundaries.

Further work should begin as a new campaign rather than extending GAGE-007.