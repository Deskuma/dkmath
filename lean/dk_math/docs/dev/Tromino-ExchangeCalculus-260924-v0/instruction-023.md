# TRM-024 — Combinatorial V/E/F counting and Euler characteristic

## Goal

Count the combinatorial vertices, edges, and face-step orbits of the supplied
FlowNetwork/FlowCrossing/FlowLocalRotation data.

TRM-023 already provides explicit finite face orbits forming an equal-or-
disjoint partition of FlowNetworkPort.

TRM-024 should define computable:

- V = number of regions;
- E = number of crossing edge-orbits;
- F = number of faceStep orbits;
- chi = V - E + F as an integer-valued combinatorial Euler characteristic.

This checkpoint must **not** assert chi = 2, genus zero, planarity, sphere
embedding, or any topological realization theorem.

The purpose is to establish the finite counting layer only.

## Production

Create:

DkMath/Tromino/EulerCount.lean

Depend on FaceOrbit.

## A. Vertex count

Define:

```lean
def regionVertexCount (N : FlowNetwork) : Nat := N.regionCount
```

This is the combinatorial V.

Keep the name explicit enough that it is not confused with FlowNetworkPort
count.

## B. Crossing edge-pair

For C : FlowCrossing N and p : FlowNetworkPort N define:

```lean
def crossingEdgePair (C : FlowCrossing N)
    (p : FlowNetworkPort N) : Finset (FlowNetworkPort N) :=
  {p, C.cross p}
```

Prove:

- p belongs;
- C.cross p belongs;
- crossingEdgePair C (C.cross p) = crossingEdgePair C p;
- card = 2, using C.changesRegion / crossing non-self;
- if q belongs to crossingEdgePair C p, then crossingEdgePair C q =
  crossingEdgePair C p.

Then derive equal-or-disjoint behavior for crossingEdgePair.

This is the edge-orbit analogue of faceOrbit, but every orbit has length 2.

## C. Edge-orbit family

Define a computable deduplicated family:

```lean
def crossingEdgeOrbits (C : FlowCrossing N) :
    Finset (Finset (FlowNetworkPort N)) :=
  Finset.univ.image (crossingEdgePair C)
```

Define:

```lean
def crossingEdgeCount (C : FlowCrossing N) : Nat :=
  (crossingEdgeOrbits C).card
```

Prove:

- every port lies in one member of crossingEdgeOrbits;
- distinct members are disjoint;
- every member has card 2.

Preferred counting theorem:

```text
2 * crossingEdgeCount C = totalPortCount N
```

or the symmetric form.

If multiplication orientation causes arithmetic noise, expose both the orbit
partition theorem and the count theorem separately.

Do not define E merely as totalPortCount / 2 without proving the orbit meaning.

## D. Face-orbit family

Using TRM-023 define:

```lean
def faceOrbits (R : FlowLocalRotation N) (C : FlowCrossing N) :
    Finset (Finset (FlowNetworkPort N)) :=
  Finset.univ.image (faceOrbit R C)
```

Define:

```lean
def faceCount (R : FlowLocalRotation N) (C : FlowCrossing N) : Nat :=
  (faceOrbits R C).card
```

Prove:

- faceOrbit R C p belongs to faceOrbits;
- every member of faceOrbits is faceOrbit R C p for some p;
- every port is covered by one member;
- distinct members are disjoint.

The equal-or-disjoint theorem from TRM-023 should make this direct.

## E. Sum of face lengths

Prove the partition counting theorem:

```text
sum F in faceOrbits R C, F.card
=
totalPortCount N.
```

This is important.

Combined with:

```text
(faceOrbit R C p).card = firstFaceReturn R C p
```

it gives the standard combinatorial statement that the sum of face lengths
equals the number of darts/ports.

Do not yet interpret these as geometric face boundary lengths.

If direct Finset partition summation is awkward, it is acceptable to first
prove a generic lemma for a finite equal-or-disjoint covering family and use
it for both edge and face orbit families.

A small reusable finite-partition helper is welcome if it remains local or is
placed in an appropriate generic DkMath utility module.

## F. Edge partition sum

Similarly prove:

```text
sum E in crossingEdgeOrbits C, E.card
=
totalPortCount N
```

and hence:

```text
2 * crossingEdgeCount C = totalPortCount N.
```

This gives the combinatorial dart-count identity:

```text
D = 2E
```

where D = totalPortCount.

## G. Integer Euler characteristic

Define:

```lean
def combinatorialEulerCharacteristic
    (R : FlowLocalRotation N) (C : FlowCrossing N) : Int :=
  (regionVertexCount N : Int)
    - (crossingEdgeCount C : Int)
    + (faceCount R C : Int)
```

Use Int deliberately so subtraction is not truncated.

Expose simp/readability theorem:

```text
chi = V - E + F
```

Do not define genus from chi yet.

## H. Rotation-system wrapper — optional

If useful, provide a thin wrapper taking:

```lean
R : FlowRotationSystem N
```

and forwarding to R.toFlowLocalRotation.

Do not require cyclicity merely to count faceStep orbits; the weak
FlowLocalRotation is enough for V/E/F.

## I. One-face 2×3 fixture

Reuse TRM-022/023:

- 2 regions;
- 3 ports per region;
- totalPortCount = 6;
- crossing edge count = 3;
- faceCount = 1;
- face length sum = 6.

Kernel-check:

```text
V = 2
E = 3
F = 1
chi = 0
```

This is an important calibration.

Do not call chi = 0 a genus-1 embedding theorem.
It is only the combinatorial characteristic of the supplied permutations.

This example is useful precisely because it demonstrates that arbitrary
rotation-system data need not have sphere characteristic.

## J. Multi-face 2×4 fixture

Reuse TRM-023's identity-rotation fixture.

There should be:

- V = 2;
- E = 4;
- four 2-port face orbits, if the faceStep decomposition is indeed one
  crossing pair per index;
- F = 4;
- chi = 2.

Kernel-check the actual values rather than assuming them.

If the actual faceCount differs, report the computed value and explain from
the orbit decomposition.

This fixture is potentially the first chi = 2 combinatorial example, but do
not call it planar/spherical without a realization certificate.

## K. Face-length histogram — optional

If cheap, define a computable multiset/Finset observer of face lengths, e.g.

```text
faceLengthMultiset
```

containing F.card for F in faceOrbits.

Prove its sum is totalPortCount.

This is optional and should not block the checkpoint.

## L. Quotient relation calibration

TRM-023 has faceOrbitSetoid.

Optionally prove:

```text
faceCount R C
=
Nat.card (Quotient (faceOrbitSetoid R C))
```

only if Mathlib provides a clean finite quotient cardinality API.

Do not introduce noncomputable quotient enumeration merely for this theorem.

The computable faceOrbits family is the primary counting API.

## M. Interpretation boundary

Record explicitly:

- V counts regions;
- E counts crossing involution 2-orbits;
- F counts faceStep permutation orbits;
- chi = V - E + F is a **combinatorial** characteristic of the supplied
  permutation data.

TRM-024 does not prove:

- the data embed in the sphere;
- chi = 2;
- genus = (2-chi)/2;
- orientability;
- connectedness;
- Euler's topological formula;
- any planar graph theorem.

A later checkpoint must define a realization / genus-zero certificate or a
pure combinatorial-map genus theory with the required assumptions.

## N. Computability / axioms

All counting definitions must be computable:

- crossingEdgePair
- crossingEdgeOrbits
- crossingEdgeCount
- faceOrbits
- faceCount
- combinatorialEulerCharacteristic

No sorry, admit, unsafe, new axiom, or noncomputable production declaration.

## O. Audit

Create:

DkMathTest/Tromino/EulerCountAxiomAudit.lean

Audit at least:

1. crossingEdgePair card 2;
2. crossing edge-orbit equality under cross;
3. edge-orbit equal-or-disjoint;
4. edge family coverage;
5. 2E = totalPortCount;
6. face family coverage;
7. face-family equal/disjoint;
8. sum face lengths = totalPortCount;
9. 2×3 fixture V/E/F/chi;
10. 2×4 fixture V/E/F/chi;
11. demonstrate that chi depends on rotation-system data and is not
    automatically 2.

## P. Validation

Build:

- DkMath.Tromino.FaceOrbit
- DkMath.Tromino.EulerCount
- DkMathTest/Tromino.EulerCountAxiomAudit

Regression-build:

- DkMathTest/Tromino.FaceOrbitAxiomAudit
- DkMathTest/Tromino.RotationSystemAxiomAudit
- DkMathTest/Tromino.GraphColoringBridgeAxiomAudit

Run git diff --check, forbidden-construct scan, and #print axioms.

## Q. Report

Create:

docs/dev/Tromino-ExchangeCalculus-260924-v0/report-023.md

Record:

- edge-orbit representation;
- face-orbit family representation;
- partition-counting method;
- D = 2E;
- sum face lengths = D;
- V/E/F definitions;
- integer chi definition;
- exact 2×3 and 2×4 fixture values;
- evidence that chi is combinatorial and not automatically 2;
- recommended next genus-zero / surface-realization checkpoint.

## Stop condition

Stop once V, E, F, dart/port count, and chi are computably defined and
kernel-checked from the supplied crossing/rotation permutations.

Do not proceed to genus, planarity, sphere realization, Euler topological
theorem, noncrossing pairing, planar extraction, ghost completion,
BoundaryIR, optimization, or Four-Color theorem claims without review.
