# instruction-004 — LUNA Mordell-coordinate production bridge

## Mission

LUNA-004 productionizes only the exact algebraic coordinate transform that was
scratch-proved in ASTRA-001 and later used in the external Mordell analysis.

This checkpoint must NOT formalize Helfgott–Venkatesh, integral-point counts,
rank bounds, asymptotic shell estimates, or any balanced-box theorem.

The goal is only:

~~~text
production Pell/square-cube witness
  ->
exact Mordell equation
~~~

plus a cheap injectivity fact for the coordinate map when (S,u) is fixed.

## Repository

~~~text
repository: Deskuma/dkmath
branch: wip/ABC-GN-astra-260906-v1
campaign: lean/dk_math/docs/dev/ABC-GN-Astra-260906-v1/
~~~

Read:

~~~text
report-003.md
report-002.md
report-001.md
scratch-001.lean
~~~

Inspect:

~~~text
DkMath/ABC/GNExcessCubicShellParameterBounds.lean
DkMath/ABC/GNExcessCubicPellParameterIncidence.lean
DkMath/ABC/GNExcessCubicSquarefulPell.lean
~~~

Treat production Lean as authoritative.

## Part I — production module

Add:

~~~text
DkMath/ABC/GNExcessCubicMordellTransport.lean
~~~

Import:

~~~text
DkMath.ABC.GNExcessCubicShellParameterBounds
~~~

The module is an exact algebraic bridge only.

No analytic theorems.

## Part II — generic integer Mordell transport

Port the ASTRA-001 scratch theorem mordell_transport.

Preferred production name:

~~~text
cubicPell_to_Mordell_identity
~~~

For integers y,S,r,u, assume:

~~~text
y^2 + 3 = 4*S*r^3*u^2.
~~~

Prove:

~~~text
(4*S*u^2*y)^2
=
(4*S*u^2*r)^3 - 48*S^2*u^4.
~~~

Use the short scratch proof:

~~~text
multiply the conic equation by 16*S^2*u^4
and close with ring/nlinarith.
~~~

This is an exact polynomial identity.

Do not mention elliptic-curve point counts in the theorem docstring.

## Part III — natural-number version

If useful for production consumers, add a natural-number theorem:

~~~text
y^2 + 3 = 4*S*r^3*u^2
=>
(4*S*u^2*y)^2 + 48*S^2*u^4
=
(4*S*u^2*r)^3.
~~~

Recommended name:

~~~text
cubicPell_to_Mordell_identity_nat
~~~

The integer subtraction form may be derived separately.

Do not duplicate long proofs.

## Part IV — production square-cube coordinate wrapper

For a represented shell witness a, use canonical production coordinates:

~~~text
M = GNExcessCubicFullRepeatedModulus a

r = oddPart M

u = GNExcessCubicSquarefulQuotient M

S = GNExcessCubicComplement a

y = 2*a+3.
~~~

Production already gives:

~~~text
M = u^2*r^3

evenPart M = r*u

y^2 + 3 = 4*(r*S)*(evenPart M)^2.
~~~

Rewrite this exactly as:

~~~text
y^2 + 3 = 4*S*r^3*u^2.
~~~

Recommended theorem:

~~~text
GNExcessCubicRealizedLargeModulusShellWitness_squareCube_conic
~~~

Input:

~~~text
a in GNExcessCubicRealizedLargeModulusShellWitnessSpace X D.
~~~

Conclusion should use the canonical r,u,S,y expressions directly rather than
existential coordinates if practical.

This theorem is a bridge only.

## Part V — production Mordell identity

Main theorem:

for every shell witness a, with the same canonical expressions,

~~~text
Y = 4*S*u^2*y
Z = 4*S*u^2*r
~~~

prove:

~~~text
Y^2 = Z^3 - 48*S^2*u^4
~~~

over Int, or equivalently the subtraction-free Nat identity.

Recommended name:

~~~text
GNExcessCubicRealizedLargeModulusShellWitness_mordell_identity
~~~

Prefer a theorem whose statement is directly reusable by future research.

If the Nat form is cleaner as the public theorem, expose both Nat and Int
wrappers.

Do not define a new elliptic-curve structure.

Do not create a provider.

## Part VI — fixed-(S,u) coordinate injectivity

ASTRA-001 observed that the Mordell transform is injective in (a,r) when
positive S,u are fixed.

Formalize only the elementary coordinate fact.

For positive natural S,u, prove:

~~~text
4*S*u^2*r1 = 4*S*u^2*r2
and
4*S*u^2*(2*a1+3) = 4*S*u^2*(2*a2+3)

=>

r1 = r2 and a1 = a2.
~~~

Recommended theorem:

~~~text
mordellCoordinates_injective_fixed_SU
~~~

This is just cancellation plus injectivity of a |-> 2*a+3.

Do not claim that every integral Mordell point comes from a production witness.

Do not claim injectivity when S or u is allowed to vary.

## Part VII — optional production image

Only if very cheap, define a shell witness image under the exact Mordell
coordinate pair (Z,Y).

This is optional.

Do not build fibers or counts around it.

The main checkpoint is the algebraic bridge, not another incidence hierarchy.

## Part VIII — negative boundaries

Document explicitly:

~~~text
PROVED:

production shell witness
->
exact Mordell equation with coefficient -48*S^2*u^4.

fixed positive (S,u):
the coordinate map (a,r) -> (Z,Y) is injective.

NOT PROVED:

every Mordell integral point is a production witness.

uniform integral-point count.

Helfgott-Venkatesh specialization in Lean.

rank bound.

31/24 + epsilon moment bound.

balanced-box power saving.

ABC.
~~~

## Part IX — do not add Eisenstein production API here

Do not port the scratch eisensteinNorm or Eisenstein square-product identity
in this checkpoint.

Reason:

the repository already has genuine Eisenstein-ring infrastructure in the FLT3
development, and a future extraction should reuse/canonicalize that rather
than create an ad hoc coordinate-only duplicate inside ABC.

Keep ASTRA-001 Eisenstein identities in scratch for now.

## Part X — public import

Import:

~~~text
DkMath.ABC.GNExcessCubicMordellTransport
~~~

from DkMath/ABC.lean immediately after
GNExcessCubicShellParameterBounds.

Do not reorder unrelated imports.

## Part XI — report

Create:

~~~text
lean/dk_math/docs/dev/ABC-GN-Astra-260906-v1/report-004.md
~~~

Title:

~~~text
# LUNA-004 — Mordell-coordinate production bridge
~~~

Report:

1. files changed
2. generic integer identity
3. Nat identity status
4. production square-cube conic wrapper
5. production Mordell identity
6. fixed-(S,u) injectivity
7. optional image status
8. explicit no-counting boundary
9. focused build
10. ABC aggregator build
11. forbidden scan
12. axiom audit
13. remaining research frontier

Do not include commit hashes.

## Part XII — validation

Run:

~~~text
lake build DkMath.ABC.GNExcessCubicMordellTransport
lake build DkMath.ABC
~~~

Scan changed production Lean for:

~~~text
sorry
admit
axiom
abc_main_axiom
native_decide
unsafe
~~~

No new occurrences.

Audit principal declarations.

Expected trust boundary:

~~~text
propext
Classical.choice
Quot.sound
~~~

or a subset.

No external theorem may enter the dependency graph.

## Stop condition

Stop when production Lean contains:

~~~text
production shell witness
=>
exact Mordell coordinate identity
~~~

and, if cheap:

~~~text
fixed positive (S,u)
=>
Mordell coordinate map is injective in (a,r).
~~~

Do not formalize any integral-point count.
Do not derive any asymptotic shell estimate.
Do not begin balanced-box counting.
Do not open LUNA-005 automatically.
