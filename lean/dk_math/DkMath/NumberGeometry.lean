/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberGeometry.Radical
import DkMath.NumberGeometry.GaugeTransition
import DkMath.NumberGeometry.PrimeScale
import DkMath.NumberGeometry.Bridge.UnitCycle
import DkMath.NumberGeometry.Bridge.LogGauge
import DkMath.NumberGeometry.Phase.TwoPrime
import DkMath.NumberGeometry.Phase.SevenTreasure
import DkMath.NumberGeometry.Bridge.SilverRatio
import DkMath.NumberGeometry.Examples.EgyptianCircle

#print "file: DkMath.NumberGeometry"

/-!
# NumberGeometry

Public facade for the neutral two-point Euclidean geometry theory developed in
NGEO-000 through NGEO-012.

The starting datum is deliberately minimal: two points A, B in the Euclidean
plane. Their basic invariant is the squared distance

~~~text
M(A,B) = dist(A,B)^2.
~~~

For an active pair A != B, this quantity is used as a relative square-mass
unit. A point P lies on natural shell n when

~~~text
M(A,P) = n * M(A,B).
~~~

Thus the discrete counting variable is carried by square mass rather than by
ordinary distance. If the base distance is r, shell n has squared radius
n * r^2; in this sense the geometric counting law has the form

~~~text
total square mass = count * unit distance^2.
~~~

The theory then separates two complementary kinds of arithmetic.

## Additive counting inside one gauge

Natural shells encode repeated addition of one base square-mass unit:

~~~text
n -> n + 1.
~~~

The radical bridge explains why square roots can disappear after passage to
square mass. Orthogonal data satisfy the schematic identity

~~~text
||u + sqrt(m) v||^2 = ||u||^2 + m ||v||^2
~~~

when the cross term vanishes. The Silver-ratio and Egyptian-circle modules are
concrete calibrations of this general landing mechanism.

## Multiplicative transition between gauges

For two kernels K1 and K2, the denominator-free relation
MassScalesBy u K1 K2 means

~~~text
massGauge K2 = u * massGauge K1.
~~~

These transitions compose multiplicatively. A natural shell can therefore be
promoted to the base gauge of a new two-point geometry: if P is on shell n of
K, then retargeting K to P produces a new kernel whose mass gauge is n times
the old one.

Prime-labelled transitions are the irreducible natural multipliers in this
geometry. A PrimeScaleStep p K1 K2 records a prime p together with

~~~text
massGauge K2 = p * massGauge K1.
~~~

Finite prime-scale chains multiply their labels, repeated labels produce prime
powers, and every nonempty active prime chain strictly increases square mass.
Consequently an active prime-scale dynamics has no nontrivial closed cycle.

## Positive units and logarithmic coordinates

An active mass gauge is a positive real number, so it embeds exactly into the
existing DkMath.DHNT.Unit infrastructure. The corresponding ratio is

~~~text
massGaugeRatio K1 K2 = massGauge K2 / massGauge K1.
~~~

The optional logarithmic observer

~~~text
G(K) = log (massGauge K)
~~~

turns multiplicative transitions into additive increments:

~~~text
MassScalesBy u K1 K2
  -> G(K2) - G(K1) = log u.
~~~

For a prime step this becomes log p. Since square mass is distance squared,

~~~text
log (massGauge K) = 2 * log (dist K.source K.target),
~~~

so a prime square-mass step has distance-log increment (1 / 2) * log p.
The factor 1 / 2 is therefore the inverse exponent of the square map.

## Signed 2 * p phases

The phase layer is algebraic and independent of FLT. A primitive signed
2 * p phase has generator eta with

~~~text
eta^(2*p) = 1,
eta^p     = -1.
~~~

Its orbit splits into even and odd sectors

~~~text
evenPhase j = eta^(2*j),
oddPhase  j = eta^(2*j + 1),
~~~

with

~~~text
(evenPhase j)^p =  1,
(oddPhase  j)^p = -1.
~~~

Hence phase multiples satisfy the signed power equations

~~~text
X^p - Y^p = 0   -- even sector
X^p + Y^p = 0   -- odd sector.
~~~

Squaring the 2 * p generator gives the p-phase generator

~~~text
zeta = eta^2.
~~~

For p = 7, FourteenPhase proves that the fourteen states split into two
disjoint seven-element sectors, so the equality 14 = 7 + 7 is represented by
an exact finite phase decomposition rather than by informal counting.

The FLT/Seven-owned one-way bridge is intentionally not imported by this
facade. That bridge proves inside the existing degree-six seventh-cyclotomic
carrier that the concrete lift

~~~text
eta14 = -(zeta^4)
~~~

has primitive order fourteen and satisfies

~~~text
eta14^2  = zeta,
eta14^7  = -1,
eta14^14 = 1.
~~~

Thus the generic square map from a fourteen-phase generator to a seventh-phase
generator is realized exactly by the existing cyclotomic carrier, while the
neutral NumberGeometry theory remains independent of FLT.

## Scope

The facade exposes the checked geometry, gauge, prime-scale, unit-cycle,
logarithmic, radical, and signed-phase layers. It does not claim that these
structures alone prove FLT, classify all arithmetic landing points, or provide
a canonical successor point on a shell. Those require additional arithmetic
or geometric input beyond the two-point kernel.
-/
