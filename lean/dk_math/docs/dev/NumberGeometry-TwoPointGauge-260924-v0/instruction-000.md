# NGEO-000 — Inventory and ownership boundary

You are implementing checkpoint NGEO-000 on branch:

~~~text
research/NumberGeometry-TwoPointGauge-260924-v0
~~~

Read first:

~~~text
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/README.md
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/ROADMAP.md
~~~

## Objective

Do not start by implementing the full NumberGeometry hierarchy.

First audit the existing DkMath and mathlib geometry/algebra APIs and determine
the smallest non-duplicating production architecture for the new two-point
unit-gauge geometry.

The intended mathematical core is:

~~~text
A, B in R^2
  |
  v
pair square mass M(A,B)
  |
  +-- M = 0  -> geometric zero
  |
  +-- M > 0  -> active two-point seed / unit gauge
                  |
                  v
          relative square-mass counting
                  |
                  v
              n-shells
~~~

The core must not depend on integer lattices, primes, cyclotomic fields, or
FLT.

## Required source audit

Inspect at least these production modules in full enough context to identify
definitions, theorem ownership, and reusable proof shapes:

~~~text
DkMath.SilverRatio.Sqrt2Lemmas
DkMath.SilverRatio.SilverRatioCircle
DkMath.SilverRatio.SilverRatioUnit

DkMath.CosmicFormula.Rotation.CF2D.Basic

DkMath.Units.NPUnit
DkMath.UnitCycle.Core
DkMath.DHNT.UnitNatLayers
~~~

Also search the repository and mathlib imports already available in DkMath for
existing APIs covering:

- points or vectors in `R^2`;
- squared Euclidean norm / distance;
- translation;
- linear isometries / orthogonal maps;
- rotations in `R^2`;
- reflections;
- scalar dilation;
- similarities or affine isometries;
- level sets / spheres / circles if already convenient;
- set image of intersections under equivalences/injective maps;
- dot product / inner product;
- square-root identities suitable for radical landing;
- positive-real or unit-like multiplicative ratios.

Do not assume a custom similarity structure is required before checking
mathlib.

## Required inventory table

Create a table in `report-000.md` with columns:

~~~text
concept
existing owner/module
existing definition/theorem names
reuse status
missing theorem if any
proposed NumberGeometry owner
~~~

Include at least:

~~~text
Point / Vec representation
difference vector
pair square mass
zero/separation criterion
distance gauge
mass gauge
natural counting shell
normalized mass
translation invariance
orthogonal invariance
scaling law
similarity transport
mass level set
shared-point transport
dot product
radical q2 decomposition
radical landing by orthogonality
gauge transition
prime-scale bridge boundary
UnitCycle bridge boundary
2p phase bridge boundary
~~~

## Key architectural question 1 — point representation

Compare these options explicitly.

### Option A — reuse `CF2D.Vec ℝ`

Advantages to test:

- already owns `q2`;
- already has multiplicative `star`;
- already has `q2_scale`;
- already has unit-kernel actions and level sets.

Risks to test:

- `Vec.core/beam` vocabulary may be too CosmicFormula-specific for a generic
  geometry facade;
- subtraction / translation / standard mathlib linear maps may become awkward.

### Option B — use `ℝ × ℝ`

Advantages to test:

- matches `SilverRatio.Circle.Point`;
- simple explicit coordinate algebra.

Risks to test:

- may duplicate CF2D square-mass infrastructure;
- may make future linear-isometry reuse less natural.

### Option C — use a mathlib Euclidean-space representation

Examples to investigate, not assume:

~~~text
EuclideanSpace ℝ (Fin 2)
Fin 2 -> ℝ
other existing finite-dimensional Euclidean aliases
~~~

Assess interoperability cost with current DkMath code.

The report must recommend one v0 representation and explain why.

## Key architectural question 2 — theorem ownership

The new package should not steal ownership from established modules merely to
create a cleaner namespace.

Determine which of these should be:

~~~text
new generic production theorem
thin alias / bridge
existing theorem reused unchanged
example-only theorem
deferred
~~~

In particular audit:

~~~text
CF2D.Vec.q2
CF2D.Vec.q2_scale
CF2D.Vec.q2_star
CF2D.UnitKernel.q2_act
CF2D.LevelSet

SilverRatio.Circle.dist_sq
SilverRatio.Circle.concyclic4
SilverRatio.Circle.bcfg_concyclic
~~~

A likely good design is for NumberGeometry to own geometry semantics while
CF2D retains CosmicFormula-specific multiplication/action semantics, but this
must be justified by the audit.

## Key architectural question 3 — denominator-free API

The public counting predicate should likely avoid division:

~~~text
OnNatShell K n P :
  pairMass K.source P = n * pairMass K.source K.target
~~~

Audit whether this should be the primary API.

Normalized quotient forms may be added only when the base pair is active and
nonzero.

Do not make real division the primitive definition if it creates avoidable
nonzero side conditions.

## Key architectural question 4 — GeoZero / separation

The intended semantics are:

~~~text
pairMass A B = 0  <->  A = B
0 < pairMass A B <->  A != B
~~~

Find the shortest robust proof path for the chosen point representation.

Do not introduce an artificial Peano-style inductive type.  "GeoZero" and
"GeoSucc" are interpretation vocabulary; production mathematics should use
ordinary equality, separation, and positivity.

## Key architectural question 5 — similarity transport

Determine the smallest theorem family needed to prove:

~~~text
pairMass (T P) (T Q) = c^2 * pairMass P Q
~~~

for translation + orthogonal action + scalar dilation.

Then determine how to derive shell invariance without division:

~~~text
OnNatShell K n P
  -> OnNatShell (T K) n (T P).
~~~

Prefer compositional lemmas over one huge coordinate proof.

## Radical landing reconnaissance

Do not implement a large radical library in NGEO-000.

Confirm a practical proof route for the later identity:

~~~text
q2(u + sqrt(m) * v)
  = q2(u) + m*q2(v) + 2*sqrt(m)*dot(u,v)
~~~

and the orthogonal consequence:

~~~text
dot(u,v) = 0
  -> q2(u + sqrt(m)*v) = q2(u) + m*q2(v).
~~~

Record whether a generic nonnegative `m : ℝ`, natural `m : ℕ`, or a more
specialized first API is cheapest.

## Downstream bridge boundaries

Explicitly record, but do not implement, the intended dependency boundaries
for:

### Units / dynamic gauge

~~~text
DkMath.Units.NPUnit
DkMath.DHNT.UnitNatLayers
~~~

### UnitCycle

~~~text
DkMath.UnitCycle.Core
~~~

### Prime scale

A later discrete landing should look conceptually like:

~~~text
exists p : Nat, Nat.Prime p and MassGauge K2 = p * MassGauge K1
~~~

### 2p phase / cyclotomic

This is downstream.  No root-of-unity or FLT import belongs in the
NumberGeometry core.

## Suggested file layout to evaluate

Evaluate this layout against the audit:

~~~text
DkMath/NumberGeometry.lean

DkMath/NumberGeometry/
  Basic.lean
  TwoPointKernel.lean
  PairMass.lean
  Gauge.lean
  Similarity.lean
  CountingShell.lean
  SharedPoint.lean
  QuadraticRadical.lean
  RadicalLanding.lean
  GaugeTransition.lean
  PrimeScale.lean
  PrimeScaleChain.lean
  TwoPPhase.lean

  Examples/
    EgyptianCircle.lean
    SilverCircle.lean
    SevenTreasure.lean

  Bridge/
    CF2D.lean
    SilverRatio.lean
    Units.lean
    UnitCycle.lean
    Cyclotomic.lean
~~~

A thinner layout is preferred.

## Production change policy

NGEO-000 is primarily an audit.

### Outcome A

If the audit reveals a clear minimal core and one very small scaffold is useful,
you may add only that scaffold, for example a facade namespace/file with no
substantial theorem duplication.

### Outcome B

If theorem ownership or point representation still needs a design choice, make
no production Lean change.  Freeze the recommended API and defer implementation
to NGEO-001.

Do not force Outcome A.

## Hard constraints

- No FLT imports.
- No integer lattice assumption.
- No prime theorem in the core.
- No cyclotomic theorem in the core.
- No speculative claim that all shared points have arithmetic landing.
- No duplicate implementation of `CF2D.Vec.q2` unless the report shows why a
  new owner is necessary.
- No wholesale refactor of `SilverRatio`.
- No `sorry`.
- No `admit`.
- No `sorryAx`.
- No new declared axiom.
- No unsafe proof shortcut.

## Validation

If production Lean files are changed:

~~~text
lake build <each changed focused module>
lake build DkMath.NumberGeometry
lake build DkMath
git diff --check
~~~

Run `#print axioms` for every new substantive theorem.

If NGEO-000 changes documentation only, record that no Lean build was needed.

## Deliverable

Create:

~~~text
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-000.md
~~~

The report must contain:

1. Outcome A or B.
2. Exact inventory table.
3. Recommended point representation for v0.
4. Recommended theorem ownership.
5. Minimal public API proposed for NGEO-001.
6. Existing APIs to reuse unchanged.
7. Genuinely missing lemmas.
8. Recommended file/module layout.
9. Exact dependency boundaries to SilverRatio, CF2D, Units, UnitCycle, and DHNT.
10. Build / axiom / diff-check results.
11. Git diff summary.

Stop after NGEO-000.

Do not implement NGEO-001 in the same checkpoint.
