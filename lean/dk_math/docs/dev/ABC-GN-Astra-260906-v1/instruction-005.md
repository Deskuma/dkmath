# instruction-005 — LUNA fixed-(S,u) Mordell incidence ledger

## Mission

LUNA-005 converts the exact Mordell transport from LUNA-004 into a finite
production incidence ledger.

The key deterministic organization is:

~~~text
shell witnesses
  ->
fixed coefficient parameters (S,u)
  ->
one Mordell curve
  ->
finite coordinate image (Z,Y).
~~~

For each fixed positive pair (S,u), the LUNA-004 coordinate map is injective.

This checkpoint should freeze that exact finite partition and image-card
identity.

Do not formalize any integral-point estimate, Helfgott–Venkatesh theorem,
rank bound, asymptotic estimate, or balanced-box saving.

---

## Repository

~~~text
repository: Deskuma/dkmath
branch: wip/ABC-GN-astra-260906-v1
campaign: lean/dk_math/docs/dev/ABC-GN-Astra-260906-v1/
~~~

Read:

~~~text
report-004.md
report-003.md
report-001.md
~~~

Inspect:

~~~text
DkMath/ABC/GNExcessCubicMordellTransport.lean
DkMath/ABC/GNExcessCubicShellParameterBounds.lean
DkMath/ABC/GNExcessCubicRealizedIncidence.lean
~~~

Treat current production Lean as authoritative.

---

## Part I — production module

Add:

~~~text
DkMath/ABC/GNExcessCubicMordellIncidence.lean
~~~

Import:

~~~text
DkMath.ABC.GNExcessCubicMordellTransport
~~~

This module should contain finite-set organization and exact polynomial
membership only.

No external mathematics.

---

## Part II — canonical Mordell parameter

Define the fixed-curve parameter carried by a shell witness:

~~~text
MordellParameter(a)
=
(
  GNExcessCubicComplement a,
  GNExcessCubicSquarefulQuotient
    (GNExcessCubicFullRepeatedModulus a)
)
=
(S,u).
~~~

Recommended name:

~~~text
GNExcessCubicMordellParameter
~~~

Then define the represented parameter space:

~~~text
GNExcessCubicRealizedLargeModulusShellMordellParameterSpace X D
~~~

as the image of the shell witness space under this map.

Provide exact membership:

~~~text
(S,u) is represented
iff
there exists a shell witness a with
Complement(a)=S
and
SquarefulQuotient(M(a))=u.
~~~

No parameter-count bound.

---

## Part III — fixed-(S,u) witness fiber

Define:

~~~text
GNExcessCubicRealizedLargeModulusShellMordellParameterFiber X D S u
~~~

as the shell witness space filtered by:

~~~text
Complement(a)=S
and
SquarefulQuotient(M(a))=u.
~~~

Provide exact membership theorem.

Prove:

~~~text
if (S,u) is in the represented parameter space,
then the fiber is nonempty.
~~~

Do not estimate the fiber cardinality yet.

---

## Part IV — positivity packet for represented parameters

For:

~~~text
(S,u) in MordellParameterSpace X D
~~~

prove:

~~~text
0 < S
0 < u.
~~~

Use existing production facts:

~~~text
Complement positive for shell witnesses

SquarefulQuotient positive for realized large moduli.
~~~

Recommended theorem:

~~~text
GNExcessCubicRealizedLargeModulusShellMordellParameter_pos
~~~

This positivity is needed only to consume
mordellCoordinates_injective_fixed_SU.

Do not add unnecessary bounds here.

---

## Part V — exact parameter-fiber partition

Prove pairwise disjointness of the fixed-(S,u) fibers.

Then prove:

~~~text
biUnion over represented (S,u) fibers
=
shell witness space.
~~~

Recommended theorem:

~~~text
GNExcessCubicRealizedLargeModulusShellWitnessSpace_eq_biUnion_mordellParameterFibers
~~~

Then derive the exact count ledger:

~~~text
ShellWitnessCount X D
=
sum over represented (S,u)
  MordellParameterFiber(X,D,S,u).card.
~~~

Recommended theorem:

~~~text
GNExcessCubicRealizedLargeModulusShellWitnessCount_eq_sum_mordellParameterFiberCards
~~~

This is an exact finite identity only.

---

## Part VI — fixed-(S,u) Mordell coordinate map

For fixed S,u define the coordinate map on a witness a:

~~~text
r(a) = oddPart (FullRepeatedModulus a)

Z = 4*S*u^2*r(a)

Y = 4*S*u^2*(2*a+3).
~~~

Recommended definitions:

~~~text
GNExcessCubicMordellZ S u a
GNExcessCubicMordellY S u a
GNExcessCubicMordellCoordinate S u a
~~~

Keep them transparent/simple.

Do not define an elliptic curve object.

---

## Part VII — finite coordinate image

Define:

~~~text
GNExcessCubicRealizedLargeModulusShellMordellCoordinateSpace
    X D S u
~~~

as the image of the fixed-(S,u) witness fiber under the coordinate map.

Provide exact membership:

~~~text
(Z,Y) is in the coordinate space
iff
there exists a in the fixed-(S,u) fiber
with
Z = 4*S*u^2*r(a)
and
Y = 4*S*u^2*(2*a+3).
~~~

No larger ambient solution set is required.

---

## Part VIII — every image point lies on the fixed Mordell equation

For:

~~~text
(Z,Y) in MordellCoordinateSpace X D S u
~~~

prove:

~~~text
Y^2 + 48*S^2*u^4 = Z^3.
~~~

Recommended theorem:

~~~text
GNExcessCubicRealizedLargeModulusShellMordellCoordinateSpace_equation
~~~

The proof should:

1. recover the witness from image membership;
2. use fixed-fiber equalities to rewrite canonical S,u;
3. consume the production Mordell identity from LUNA-004.

This theorem is one-way only.

Do NOT prove the converse.

---

## Part IX — coordinate image card equals fixed fiber card

For represented positive (S,u), prove the coordinate map is injective on the
fixed fiber using:

~~~text
mordellCoordinates_injective_fixed_SU.
~~~

Then prove:

~~~text
MordellCoordinateSpace(X,D,S,u).card
=
MordellParameterFiber(X,D,S,u).card.
~~~

Recommended theorem:

~~~text
GNExcessCubicRealizedLargeModulusShellMordellCoordinateSpace_card
~~~

This is the main LUNA-005 deliverable.

No integral-point upper bound follows.

---

## Part X — exact two-level cardinal ledger

Combine Parts V and IX.

For represented parameters, expose an exact statement of the form:

~~~text
ShellWitnessCount X D
=
sum over represented (S,u)
  MordellCoordinateSpace(X,D,S,u).card.
~~~

Recommended theorem:

~~~text
GNExcessCubicRealizedLargeModulusShellWitnessCount_eq_sum_mordellCoordinateCards
~~~

This theorem is the production interface that future analytic research may
consume.

It contains no analytic estimate itself.

---

## Part XI — optional relation to (r,S) image

LUNA-003 already gives:

~~~text
shell witness count
=
represented (r,S) pair count.
~~~

If extremely cheap, add one theorem documenting that the two exact ledgers
have the same total cardinality.

Do not construct a complicated equivalence unless immediately available.

This is optional.

---

## Part XII — negative boundaries

Document explicitly:

~~~text
PROVED:

shell witnesses partition exactly by fixed (S,u).

for each represented fixed positive (S,u),
the witness fiber injects into its exact Mordell coordinate image.

every image coordinate satisfies
Y^2 + 48*S^2*u^4 = Z^3.

shell witness count
=
sum of exact fixed-(S,u) Mordell coordinate image cards.

NOT PROVED:

the coordinate image equals all integral points on the Mordell curve.

any bound on the number of integral points.

any uniform bound in S,u.

Helfgott-Venkatesh in Lean.

rank estimates.

17/12 or 31/24 moment estimates in Lean.

balanced-box power saving.

ABC.
~~~

---

## Part XIII — no analytic provider

Do NOT add a structure/class/axiom such as:

~~~text
MordellPointBound
HasMordellPointBound
MordellProvider
HVProvider
~~~

Future analytic theorems should be ordinary explicit theorem arguments or
separate proved modules.

---

## Part XIV — public import

Import:

~~~text
DkMath.ABC.GNExcessCubicMordellIncidence
~~~

from DkMath/ABC.lean immediately after
GNExcessCubicMordellTransport.

Do not reorder unrelated imports.

---

## Part XV — report

Create:

~~~text
lean/dk_math/docs/dev/ABC-GN-Astra-260906-v1/report-005.md
~~~

Title:

~~~text
# LUNA-005 — fixed-(S,u) Mordell incidence ledger
~~~

Report:

1. files changed
2. Mordell parameter definition
3. represented parameter space
4. fixed parameter fiber
5. positivity packet
6. exact fiber partition
7. witness-count ledger
8. coordinate definitions
9. coordinate image
10. fixed Mordell equation theorem
11. coordinate injectivity
12. coordinate image card identity
13. two-level total card ledger
14. optional (r,S) relation status
15. explicit no-counting boundary
16. focused build
17. ABC aggregator build
18. forbidden scan
19. axiom audit
20. remaining research frontier

Do not include commit hashes.

---

## Part XVI — validation

Run:

~~~text
lake build DkMath.ABC.GNExcessCubicMordellIncidence
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

Audit principal declarations:

~~~text
parameter-space membership

fiber partition

fixed Mordell equation

coordinate image card identity

total card ledger.
~~~

Expected trust boundary:

~~~text
propext
Classical.choice
Quot.sound
~~~

or a subset.

No external theorem may enter the dependency graph.

---

## Stop condition

Stop when production Lean exposes the exact finite decomposition:

~~~text
ShellWitnessCount X D
=
sum over represented fixed (S,u)
  # {
    production Mordell coordinates (Z,Y)
  }
~~~

with every coordinate satisfying:

~~~text
Y^2 + 48*S^2*u^4 = Z^3.
~~~

Do not bound those coordinate sets.
Do not formalize Helfgott–Venkatesh.
Do not begin balanced-box counting.
Do not open LUNA-006 automatically.
