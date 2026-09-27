# TRM-023 — Face orbit materialization / finite partition

## Goal

Materialize the periodic face-step dynamics from TRM-022 as explicit finite
face-orbit objects on FlowNetworkPort.

Do not jump to Euler characteristic or genus yet.

This checkpoint should prove:

- every port belongs to a finite face orbit;
- the orbit cardinality equals the primitive/first face-return length;
- two face orbits are equal or disjoint;
- the family of face orbits partitions all FlowNetworkPorts.

Keep the primary carrier FlowNetworkPort so parallel-edge multiplicity is
preserved.

Do not claim the orbits are topological faces of a planar embedding yet.

## Production

Create:

DkMath/Tromino/FaceOrbit.lean

Depend on RotationSystem.

## A. Total port count

Define a computable observer:

```lean
def totalPortCount (N : FlowNetwork) : Nat :=
  Fintype.card (FlowNetworkPort N)
```

If useful, prove the sum formula

```text
totalPortCount N
=
sum r : Fin N.regionCount, (N.signature r).arity.
```

Do not make this formula a blocker.

## B. Bounded explicit orbit

For:

- R : FlowLocalRotation N
- C : FlowCrossing N
- p : FlowNetworkPort N

define a finite face orbit.

Preferred robust definition:

```text
faceOrbit R C p :=
  (Finset.range (totalPortCount N)).image
    (fun n => (faceStep R C)^[n] p)
```

or use firstFaceReturn as the upper bound if that gives cleaner proofs.

Requirements:

- computable;
- contains p;
- closed under faceStep;
- all members are actual iterates of p;
- every iterate of p belongs to faceOrbit.

If totalPortCount = 0 is impossible when p exists, handle that locally.

## C. First-return orbit

Also define, if useful:

```text
primitiveFaceOrbit R C p :=
  (Finset.range (firstFaceReturn R C p)).image
    (fun n => (faceStep R C)^[n] p)
```

The preferred end-state is one canonical public orbit object.
If both are defined, prove they are equal.

## D. Distinctness before first return

Using firstFaceReturn_primitive, prove:

If:

```text
i < firstFaceReturn R C p
j < firstFaceReturn R C p
(faceStep R C)^[i] p = (faceStep R C)^[j] p
```

then:

```text
i = j.
```

This is the key combinatorial lemma.

A proof may use injectivity of faceEquiv to cancel the smaller number of
iterations and primitive minimality.

Avoid brute-force finite enumeration.

## E. Orbit cardinality

Prove:

```text
(faceOrbit R C p).card = firstFaceReturn R C p.
```

If the public faceOrbit uses totalPortCount, first prove equality with the
primitive-range image.

This theorem is central for later face counting.

## F. Orbit membership characterization

Prove:

```text
q ∈ faceOrbit R C p
iff
∃ n : Nat, (faceStep R C)^[n] p = q.
```

The reverse direction must reduce arbitrary n modulo / by the primitive
period, or use finite permutation periodicity.

This theorem should make face orbit independent of the chosen bounded
enumeration.

## G. Same-orbit relation

Define:

```lean
def SameFaceOrbit (R : FlowLocalRotation N) (C : FlowCrossing N)
    (p q : FlowNetworkPort N) : Prop :=
  q ∈ faceOrbit R C p
```

Prove equivalence-relation behavior:

- reflexive;
- symmetric;
- transitive.

If useful, package a Setoid:

```lean
def faceOrbitSetoid ...
```

The Setoid may be non-data / theorem-level. Do not force a quotient Fintype
yet if that introduces unnecessary classical machinery.

## H. Orbit equality / disjointness

Prove:

If q ∈ faceOrbit R C p then:

```text
faceOrbit R C q = faceOrbit R C p.
```

Then derive:

For arbitrary p q:

```text
faceOrbit R C p = faceOrbit R C q
or
Disjoint (faceOrbit R C p) (faceOrbit R C q).
```

Equivalent "nonempty intersection iff equal" is also useful.

This is the finite partition theorem needed before counting faces.

## I. Coverage

Prove:

Every port belongs to its own orbit.

If practical, expose a set/Finset family coverage theorem:

```text
Finset.univ ⊆ union of all faceOrbit p
```

or the simpler pointwise statement:

```text
∀ p, p ∈ faceOrbit R C p.
```

The equality/disjointness theorem plus self-membership is sufficient as the
partition kernel.

Do not create a duplicate-heavy Finset of all orbit Finsets unless a clean
deduplication scheme is available.

## J. Canonical representative — optional

If FlowNetworkPort has a convenient linear order, define the least port of
each orbit and a predicate:

```text
IsFaceRepresentative p
```

with exactly one representative per orbit.

This is optional.

Do not introduce a complicated custom ordering merely for this checkpoint.

A later Euler checkpoint can use quotient cardinality or representatives.

## K. Face length invariance

Prove:

If q ∈ faceOrbit R C p then:

```text
firstFaceReturn R C q = firstFaceReturn R C p.
```

Hence orbit cardinality/face length is independent of starting dart.

This is important for interpreting the orbit as one combinatorial face.

## L. Rotation-system fixture

Reuse the 2-regions × 3-ports fixture from TRM-022.

Kernel-check:

- faceOrbit p23 has card 6;
- every one of the six ports lies in that orbit;
- firstFaceReturn p23 = 6;
- choosing another port q in the orbit gives the same orbit;
- no smaller positive return exists.

If all six ports are one face orbit in that fixture, check the partition has
one orbit semantically.

## M. Multiple-face fixture

Add a small fixture with at least two distinct face orbits if cheap.

For example choose crossing/rotation data on 2 regions × 4 ports or another
small network where faceStep decomposes into two cycles.

Audit:

- one port from orbit A is not in orbit B;
- the two orbit Finsets are disjoint;
- their union covers all ports if easy.

This regression is important: the API must not accidentally assume one face.

## N. Interpretation boundary

Record:

A face orbit here means an orbit of the combinatorial permutation

    phi = rho ∘ alpha.

It is not yet a certified topological face of a sphere embedding.

TRM-023 proves only finite orbit/partition combinatorics.

Do not claim:

- planarity;
- genus zero;
- Euler formula;
- Jordan curve behavior;
- noncrossing pairing;
- arbitrary planar-map extraction.

## O. Computability / axioms

faceOrbit and all finite orbit observers should be computable.

No:

- sorry;
- admit;
- unsafe;
- new axiom;
- noncomputable production declaration.

Theorems may inherit Classical.choice from existing first-return proofs.

## P. Audit

Create:

DkMathTest/Tromino/FaceOrbitAxiomAudit.lean

Audit at least:

1. self-membership;
2. closure under faceStep;
3. arbitrary-iterate membership;
4. first-return distinctness;
5. orbit card = first return;
6. membership iff iterate;
7. same-orbit symmetry/transitivity;
8. same orbit => equal Finsets;
9. distinct orbits => disjoint;
10. face length invariance;
11. six-port fixture orbit card 6;
12. at least one multiple-orbit fixture if practical.

## Q. Validation

Build:

- DkMath.Tromino.RotationSystem
- DkMath.Tromino.FaceOrbit
- DkMathTest/Tromino.FaceOrbitAxiomAudit

Regression-build:

- DkMathTest/Tromino.RotationSystemAxiomAudit
- DkMathTest/Tromino.GraphColoringBridgeAxiomAudit

Run git diff --check, forbidden-construct scan, and #print axioms.

## R. Report

Create:

docs/dev/Tromino-ExchangeCalculus-260924-v0/report-022.md

Record:

- chosen orbit representation;
- first-return distinctness argument;
- cardinality theorem;
- membership characterization;
- SameFaceOrbit / Setoid status;
- equality/disjointness partition theorem;
- face-length invariance;
- one-face and multi-face fixtures;
- exact boundary before Euler/genus counting.

## Stop condition

Stop once faceStep orbits are explicit finite objects forming a partition of
FlowNetworkPort, with orbit cardinality equal to firstFaceReturn.

Do not proceed to Euler characteristic, face-count quotient/cardinality,
genus-zero certification, noncrossing pairing, planar extraction, ghost
completion, BoundaryIR, optimization, or Four-Color theorem claims without
review.
