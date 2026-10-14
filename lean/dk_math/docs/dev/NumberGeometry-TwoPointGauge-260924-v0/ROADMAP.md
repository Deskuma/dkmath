# ROADMAP — Number Geometry: Two-Point Unit Gauge v0

Status: NGEO-000 ready for implementation audit

Branch: `research/NumberGeometry-TwoPointGauge-260924-v0`

## Design rule

Start from the smallest checked geometry:

~~~text
A, B in R^2
~~~

Do not begin with polygons, integer lattices, primes, cyclotomic fields, or FLT.
All later arithmetic must land into the geometry through relative square-mass
relations.

Prefer existing theorem owners over duplicate implementations.

## NGEO-000 — Inventory and ownership boundary

Goal: determine exactly which existing DkMath APIs should own the new theory
and freeze the smallest production architecture.

Required audit targets:

~~~text
DkMath.SilverRatio.Sqrt2Lemmas
DkMath.SilverRatio.SilverRatioCircle
DkMath.SilverRatio.SilverRatioUnit
DkMath.CosmicFormula.Rotation.CF2D.Basic
DkMath.Units.NPUnit
DkMath.UnitCycle.Core
DkMath.DHNT.UnitNatLayers
~~~

Questions:

- should the geometric point type reuse `CF2D.Vec ℝ`, remain `ℝ × ℝ`, or
  receive a thin NumberGeometry wrapper?
- where should `q2` / square mass be owned?
- can `SilverRatio.Circle.dist_sq` become a thin specialization of a generic
  pair-mass theorem without moving its current theorem ownership?
- which similarity facts already exist in mathlib?
- what is the cheapest representation for translation, orthogonal action, and
  real scaling?
- what should remain deferred to bridges?

Deliverable: `report-000.md`, Outcome A/B, with exact file/API proposal.

## NGEO-001 — TwoPointKernel and PairMass

Introduce the minimal active-pair geometry.

Targets:

~~~text
TwoPointKernel
pairVec / gap
pairMass
Active / separated
~~~

Required theorems:

~~~text
pairMass_nonneg
pairMass_eq_zero_iff
pairMass_pos_iff_separated
pairMass_self
~~~

Keep this checkpoint entirely over `R^2`.

Do not define prime scale, logarithms, or 2p phases here.

## NGEO-002 — Relative unit gauge and counting shells

Formalize the relative counting rule.

Targets:

~~~text
DistanceGauge / MassGauge
OnNatShell K n P
NormalizedMass (only where denominator is justified)
~~~

Calibration:

~~~text
A is shell 0
B is shell 1
OnNatShell K n P -> dist(A,P)^2 = n * dist(A,B)^2
~~~

Establish the geometric-successor mass law:

~~~text
shell n -> shell (n+1) means one base square-mass unit is added.
~~~

Do not require explicit `sqrt n` existence in every theorem if the
denominator-free square-mass statement is cleaner.

## NGEO-003 — Similarity transport

Prove that the counting structure does not depend on absolute location,
orientation, reflection, or scale.

At minimum cover:

~~~text
translation
orthogonal / rotation transport
real scaling
composition into a similarity transform
~~~

Main target:

~~~text
normalized mass is similarity invariant
~~~

Prefer square-mass statements:

~~~text
M(T(P),T(Q)) = c^2 * M(P,Q)
~~~

before quotient forms.

## NGEO-004 — Level sets and shared-point transport

Introduce the geometry of square-mass boundaries without taking "circle" as a
primitive.

Targets:

~~~text
MassLevelSet A rho
map_levelSet
sharedPoint
sharedPoint_transport
intersection_naturality
~~~

Connect the level-set reading back to the existing
`SilverRatio.Circle.concyclic4` API through a bridge, not by rewriting the
existing file wholesale.

## NGEO-005 — Radical decomposition and landing

Formalize the algebraic mechanism:

~~~text
q2(u + sqrt(m) * v)
  = q2(u) + m*q2(v) + 2*sqrt(m)*dot(u,v)
~~~

and the orthogonal specialization:

~~~text
dot(u,v) = 0
  -> q2(u + sqrt(m)*v) = q2(u) + m*q2(v).
~~~

This checkpoint should expose a reusable "radical landing" theorem.

First calibrations should include simple instances such as:

~~~text
(-1, sqrt 2) -> square mass 3
~~~

without claiming a classification of all landing points.

## NGEO-006 — Silver / Egyptian calibration

Use the generic NumberGeometry API to restate selected facts from the existing
constructions.

Targets:

- recover the relevant square-mass values in the White-Silver-Ratio geometry;
- recover the `sqrt 3 <-> 3` style Egyptian-circle calibration;
- identify which observations are now exact Lean theorems and which remain
  only GeoGebra/research observations;
- avoid copying old coordinate proofs if the new generic theorems can reduce
  them.

This checkpoint is an example/bridge layer, not the core.

## NGEO-007 — Gauge transitions

For active kernels `K1,K2`, introduce relative gauge transitions.

Prefer denominator-free relations first:

~~~text
MassScalesBy u K1 K2 : M(K2) = u * M(K1)
~~~

with a positive-real ratio API where useful.

Targets:

~~~text
refl
inverse
composition
mass/distance square relation
~~~

The central composition law is multiplicative.

## NGEO-008 — PrimeScale and prime-scale chains

Introduce the first discrete arithmetic landing into the continuous gauge
space.

Target:

~~~text
PrimeScaleStep K1 K2
  := exists p, Nat.Prime p and M(K2) = p * M(K1)
~~~

Investigate and formalize the precise statement that prime mass-scale steps are
nontrivially indecomposable among natural-number scale factors.

Then define finite prime-scale chains and prove multiplication of mass scales.

Repeated steps should calibrate prime powers.

Do not claim new prime-distribution theorems.

## NGEO-009 — Units / UnitCycle bridge

Connect geometric gauge composition to existing DkMath dynamic-unit
infrastructure.

Audit:

~~~text
DkMath.Units.NPUnit
DkMath.UnitCycle.Core
DkMath.DHNT.UnitNatLayers
~~~

Targets where appropriate:

~~~text
closed gauge cycle -> product of ratios = 1
strictly expanding positive gauge -> no nontrivial cycle
~~~

Reuse `UnitCycle` theorem ownership where possible instead of duplicating
no-cycle logic.

## NGEO-010 — Logarithmic gauge coordinates

Add the optional analytic coordinate:

~~~text
G(K) = log(MassGauge K)
~~~

for positive active gauges.

Targets:

~~~text
multiplicative gauge composition -> additive log increments
prime mass step p -> Delta G = log p
distance gauge step sqrt p -> Delta log r = (1/2) log p
~~~

This checkpoint should remain a bridge/interpretation layer.

## NGEO-011 — General 2p phase

Build the algebraic phase layer independently of FLT.

For suitable `p` and primitive `2p`-phase element `eta`, target:

~~~text
eta^(2*p) = 1
eta^p = -1
~~~

and the even/odd phase split corresponding to:

~~~text
X^p - Y^p
X^p + Y^p.
~~~

Prefer reuse of existing cyclotomic/root-of-unity APIs.

## NGEO-012 — Seven Treasure calibration

Specialize NGEO-011 to `p = 7`.

Targets:

- fourteen phases;
- even/odd seven-phase decomposition;
- exact relation to the existing degree-six seventh-cyclotomic carrier where
  already supported;
- separate geometric observations from proved algebraic statements.

No FLT7 theorem in this checkpoint.

## Deferred after v0

- systematic classification of all shared-point arithmetic landings;
- full algebraic treatment of the uploaded GeoGebra constructions;
- generic cyclotomic bridge for all primes if current APIs do not make it
  lightweight;
- FLT7 re-entry;
- any claim that the 2p geometry itself proves FLT;
- higher-dimensional analogues.

## Validation discipline

Every production checkpoint:

~~~text
focused lake build for changed modules
facade build
lake build DkMath when practical
git diff --check
#print axioms for substantive new theorems
~~~

No:

~~~text
sorry
admit
sorryAx
new declared axiom
unsafe proof shortcut
~~~

Each checkpoint writes:

~~~text
instruction-NNN.md
report-NNN.md
~~~

and stops at the requested checkpoint.
