# Instruction 017 - Quadratic gnomon finite difference and centered shell folding

## Mission

Continue from Instruction 016.

A new geometric observation was made while inspecting the quadratic gnomon:

  (x+h)^2 - x^2 = 2*h*x + h^2

For h = 1, 1/2, 1/4, 1/8, the resulting affine functions form the expected quadratic finite-difference family.

However, an earlier DkMath audit already established that ordinary finite-difference identities, cosmicKernel, and the unit-one specialization do not by themselves provide a new Legendre arithmetic constraint.

Therefore Instruction 017 must not rebuild the finite-difference theory.

The genuinely new target is the centered half-lattice interpretation of the open Legendre shell and its exact connection to the existing CenteredPair fold.

The key observations to formalize and test are:

  (n+1)^2 - n^2 = 2*n + 1

  (n+1/2)^2 - (n-1/2)^2 = 2*n

and the existing centered offset pairing:

  left  = n-j
  right = n+1+j

whose midpoint is n+1/2 and whose offset sum is 2*n+1.

The goal is to determine whether this centered formulation exposes any structure beyond a coordinate change.

If it is only a reindexing, prove that cleanly and stop.
If it yields a new owner, support, residue, or folding invariant, isolate that invariant.

Use parser-safe plain text only in all new instruction/report artifacts.

## Prior result that must be respected

Read and reuse the earlier audit:

  lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/primitive-finite-difference-invariant-audit-260825.md

Its conclusion was:

- delta_u(x^2) = u*(2*x+u) is already supplied by existing CosmicFormula finite-difference APIs
- the derivative limit only keeps 2*x and loses finite-u information
- u=1 already reproduces the ordinary square shell
- no new prime-wave, support, carry, or coverage constraint was found
- adding a duplicate square-specific finite-difference abstraction was not recommended

Instruction 017 must not reopen those closed questions unless the new centered fold supplies an independent bridge.

## Required source audit

Audit at minimum:

DkMath.CosmicFormula.CosmicDifferenceKernel
DkMath.CosmicFormula.CosmicDerivativePower
DkMath.CosmicFormula.CosmicFormulaDerivativeBridge
DkMath.CosmicFormula.CosmicFormulaBasic
DkMath.CosmicFormula.CosmicFormulaBinom
DkMath.NumberTheory.Legendre.Basic
DkMath.NumberTheory.Legendre.CenteredPair
DkMath.NumberTheory.Legendre.OldSupportGcd
DkMath.NumberTheory.Legendre.GnomonSuccessor
DkMath.NumberTheory.Legendre.GnomonSupportTurnover
DkMath.NumberTheory.Legendre.GnomonResidueCover
DkMath.NumberTheory.Legendre.SquareAnchorCounterexamplePacket

Also audit any existing offset reflection or involution theorem before adding a new fold definition.

Record exact theorem names in source-inventory-017.md.

## Phase 1 - generic quadratic finite difference bridge

Do not define a new delta operator.

Using existing CosmicFormula APIs, expose only the thin theorem needed for this checkpoint:

  (x+h)^2 - x^2 = h*(2*x+h)

in the most reusable existing algebraic type supported by current APIs.

Also expose the normalized form, under h nonzero where division is meaningful:

  ((x+h)^2 - x^2) / h = 2*x+h

If these already exist under suitable names, do not duplicate them.

The purpose is only to anchor the geometry to the existing CosmicFormula structure.

## Phase 2 - forward, backward, and centered quadratic increments

For the quadratic f(x)=x^2, record the three exact forms:

  forward_h(x)  = (x+h)^2 - x^2
                = 2*h*x + h^2

  backward_h(x) = x^2 - (x-h)^2
                = 2*h*x - h^2

  centered_h(x) = (x+h/2)^2 - (x-h/2)^2
                = 2*h*x

Avoid introducing unnecessary real-analysis dependencies into the Legendre namespace.

Preferred strategy:

- keep the generic half-step identity in an algebraic or rational bridge module if needed
- derive the Nat-relevant h=1 statements using denominator-free integer identities

Do not force Nat subtraction into a fragile formulation.

## Phase 3 - denominator-free centered identity

Formalize the half-lattice identity without depending on floating-point or decimal values.

Preferred exact integer-scaled form:

  (2*n+1)^2 - (2*n-1)^2 = 8*n

This is equivalent to:

  (n+1/2)^2 - (n-1/2)^2 = 2*n

but avoids rational normalization in the core arithmetic theorem.

Also record:

  ((2*n+1)^2 - (2*n-1)^2) / 4 = 2*n

only if Nat or Int division can be handled cleanly and exactly.

Do not add a theorem whose proof depends on accidental truncation.

## Phase 4 - open Legendre shell as a centered half-square window

The ordinary open Legendre shell is:

  n^2 + 1
  ...
  n^2 + 2*n

Define or characterize the centered integer window around n^2:

  n^2 - n + 1
  ...
  n^2 + n

This window also has exactly 2*n integer seats.

Prove the translation correspondence:

  m in centered window
  iff
  m+n in ordinary Legendre open shell

with exact endpoint arithmetic.

Prefer a theorem over a duplicate Finset definition if the existing interval APIs make the statement easy.

If a Finset carrier materially helps later folding proofs, define one and prove its card is 2*n.

## Phase 5 - exact fold involution on ordinary shell offsets

The existing CenteredPair uses:

  leftOffset(n,j)  = n-j
  rightOffset(n,j) = n+1+j

for j < n.

Expose the corresponding shell-offset reflection:

  fold_n(r) = 2*n + 1 - r

for 1 <= r <= 2*n.

Prove:

- fold maps squareOffsets n to itself
- fold is an involution
- fold has no fixed point on integer shell offsets
- each orbit has exactly two elements
- the shell decomposes into exactly n fold pairs
- leftOffset(n,j) and rightOffset(n,j) are fold partners
- their sum is 2*n+1

Reuse CenteredPair definitions instead of replacing them.

If an equivalent reflection already exists, bridge to it.

## Phase 6 - centered coordinate index

Give each fold pair a canonical index j with:

  0 <= j < n

and:

  pair(j) = { n-j, n+1+j }

Prove the bijection between:

  j in range n

and the n unordered fold pairs of squareOffsets n.

Do not create a heavy quotient type unless necessary.
A Finset image or pair carrier is preferable.

## Phase 7 - odd internal gap ladder

For pair index j, the complete points differ by:

  2*j + 1

Reuse centeredPoint_difference and centeredCommonDivisor_iff.

Make explicit that as j runs from 0 to n-1, the internal pair gaps are exactly:

  1, 3, 5, ..., 2*n-1

This is the internal odd-gnomon ladder.

Prove an exact Finset image/cardinality theorem for these gaps if useful.

Distinguish carefully:

- outer square gnomon size 2*n+1
- open-shell seat count 2*n
- internal centered pair gaps up to 2*n-1
- next outer gnomon 2*n+3

## Phase 8 - CosmicFormula interpretation of centered gaps

Audit whether each centered pair difference can be written as a degree-2 GN or power-difference specialization without introducing new arithmetic content.

For example, for suitable endpoints A and B:

  A^2 - B^2 = (A-B)*(A+B)

and degree-2 GN should recover the endpoint sum.

If an existing GN endpoint bridge already supplies this, add only a Legendre-facing adapter theorem.

The report must answer whether:

  centered pair gap
  odd gnomon
  degree-2 GN
  finite-difference coefficient

are literally the same algebraic object under reparameterization, or only related.

Do not claim new number theory from this identification alone.

## Phase 9 - fold and residue-cover owner

Now use the genuinely arithmetic objects from Instruction 016.

For each fold pair r and fold_n(r), compare their canonical residue-cover owners.

Prove exact statements such as:

  same owner on both fold partners
  implies
  owner divides their offset difference

which should reduce to the existing CenteredPair support theorem.

Then specialize to canonical least owner.

Determine whether any stronger statement follows from minimality.

Possible targets:

- same least owner iff it is the least prime divisor of a specific odd gap under explicit hypotheses
- same least owner forces a relation between the left point and gap factorization
- parity forces one member to have owner 2 in a describable subfamily
- no stronger rule exists

Do not assume one of these is true.

Preserve smallest counterexamples to false strengthened rules.

## Phase 10 - fold-owner coloring

Define, if useful, the canonical owner coloring of the shell:

  color_n(r) = squareResidueCoverOwner n r

only on covered seats, or via the existing total minFac function with an explicit covered-seat hypothesis.

For each fold pair classify:

- same-owner pair
- different-owner pair

Prove:

  same-owner pair at index j
  implies
  owner divides 2*j+1

For prime internal gap 2*j+1 > n, derive disjoint support or distinct owner using the existing CenteredPair theorem.

The purpose is to turn the fold into a finite coloring constraint.

## Phase 11 - exact same-owner capacity by prime

For a fixed old prime p <= n, count the pair indices j with:

  p divides 2*j+1

inside:

  0 <= j < n

Derive an exact floor formula or exact residue-class Finset card.

This is not yet the count of actual same-owner pairs.
It is an upper capacity for where p could possibly own both members.

Connect the actual same-owner fiber injectively into this arithmetic capacity.

This is the first place where the centered fold may produce a genuinely new counting interface.

## Phase 12 - total fold-owner capacity test

Sum the per-prime same-owner capacities over p in primeScalesUpTo n.

Compare with the number n of fold pairs.

Account for overlap correctly:
a pair gap may have several prime divisors, but the canonical same owner is unique.

Prefer a canonical-owner sum rather than a raw union bound if possible.

Determine whether full cover imposes a nontrivial lower bound on the number of different-owner pairs.

If the result is merely a tautology or a weaker version of existing support-incidence counts, state that explicitly.

## Phase 13 - relation to Instruction 016 owner transition

Instruction 016 proved that the least owner changes in the successor lower channel.

Compare that cross-shell owner-change theorem with the within-shell fold-owner classification.

Ask whether the two constraints can be combined on the same seat trajectory.

Possible structure:

  within one shell:
  r <-> fold_n(r)

  across shells:
  r -> successorThresholdInsert n r

Search for a small commuting or noncommuting square of seat maps and owner labels.

Do not assume the maps commute.

If they do not commute, compute the exact displacement and support-divisibility condition.

A precise transport diagram is a valid result even without a contradiction.

## Phase 14 - second finite difference and plus-two gnomon growth

Record, using existing APIs where possible:

  G(n+1) - G(n) = 2

for:

  G(n) = 2*n+1

and relate it to the second finite difference of n^2.

The goal is documentation and structural identification only.

Do not infer prime distribution from constant second difference.

The report must explicitly state that constant curvature alone is not a Legendre provider.

## Phase 15 - test whether centered folding is more than reindexing

This phase is mandatory.

Compare the new fold package against existing:

- CenteredPair
- OldSupportGcd
- squareOffsetPrimeSupport
- residue-owner partition
- pair overlap / support capacity APIs

Classify every new theorem into one of:

A. exact duplicate or thin wrapper of existing theorem
B. useful geometric normalization with no new arithmetic content
C. genuinely new arithmetic bridge
D. genuinely new capacity or obstruction

Do not inflate category B into C or D.

If no C or D theorem survives, Outcome C is acceptable.

## Phase 16 - bounded diagnostics

For a bounded natural-anchor range, compute:

- number of fold pairs n
- number of actual same-owner pairs
- number of different-owner pairs
- same-owner counts by prime
- internal odd gap for each same-owner pair
- ratio of actual same-owner count to arithmetic capacity
- prime-gap pairs with forced distinct owners
- near-full-cover shells from Instruction 016 and their fold coloring

Include at least:

  n = 5
  n = 8
  n = 11
  n = 19
  n = 29
  n = 297
  n = 1031 if runtime permits without expensive recomputation

Do not infer asymptotics.

## Phase 17 - exact next-provider judgment

At the end choose one exact next theorem contract.

Possible forms:

1. fold capacity provider

  under full cover,
  actual same-owner pairs plus forced owner transitions violate a proven capacity

2. fold and successor incompatibility

  a seat trajectory cannot satisfy both within-shell and cross-shell owner constraints

3. residue-gap obstruction

  canonical owner coloring cannot realize all n fold pairs

4. no new provider

  centered folding is an exact and useful normalization, but all arithmetic consequences reduce to existing pair-support theorems

Do not disguise Legendre itself as the proposed provider.

## Implementation guidance

A reasonable module split is:

DkMath/NumberTheory/Legendre/QuadraticGnomonFold.lean
DkMath/NumberTheory/Legendre/CenteredOwnerFold.lean

If a generic algebraic bridge belongs outside Legendre, place it in the existing CosmicFormula hierarchy rather than importing Legendre into CosmicFormula.

Avoid adding Real dependencies to the main Legendre facade unless absolutely necessary.

Prefer Nat, Int, or denominator-free doubled-coordinate statements for the half-lattice geometry.

Do not define a new derivative API.

## Calibration requirements

Kernel-check at minimum:

- forward unit gnomon:
  (n+1)^2 - n^2 = 2*n+1

- centered doubled identity:
  (2*n+1)^2 - (2*n-1)^2 = 8*n

- shell fold:
  fold_n(fold_n(r)) = r for r in squareOffsets n

- centered pair bridge:
  fold_n(n-j) = n+1+j for j<n

- internal gap:
  right-left = 2*j+1

- one same-owner pair example if one exists in the bounded scan

- one forced-different-owner prime-gap example

- one false stronger conjecture with smallest counterexample if discovered

## Possible outcomes

Outcome A - CENTERED FOLD YIELDS A NEW OWNER CAPACITY OBSTRUCTION

The half-lattice fold produces a genuinely new arithmetic or counting constraint that rules out a nontrivial class of full-cover patterns.

Outcome B - CENTERED FOLD PRODUCES A NEW EXACT ARITHMETIC BRIDGE

The fold is more than notation and supplies a useful owner, support, residue, or transport theorem, but no uniform contradiction.

Outcome C - CENTERED FOLD IS A GEOMETRIC NORMALIZATION ONLY

The new identities and folding package are exact and useful for interpretation, but all arithmetic consequences reduce to existing CenteredPair, support, or residue-cover results.

Outcome P - ONE PRECISE FOLD OWNER BRIDGE REMAINS

The geometry is fully formalized but one explicit owner-capacity or transport theorem blocks classification.

## Non-goals

Do not claim:

- Legendre conjecture
- prime existence from differentiation
- prime existence from constant second difference
- PNT or RH
- Bertrand
- Jacobsthal bounds
- analytic sieve estimates
- a new derivative theory
- that half-integer geometry itself preserves divisibility

Do not duplicate existing CosmicFormula finite-difference APIs.

Do not convert an exact coordinate reindexing into a claimed arithmetic advance.

## Validation

For all new production declarations:

- focused builds
- lake build DkMath.NumberTheory.Legendre
- lake build DkMath
- forbidden-token scan
- print axioms for every new public declaration
- git diff --check

All new production declarations must remain free of sorryAx.

Preserve current file-header and file-marker conventions.

## Durable checkpoint protocol

Update findings after:

- previous finite-difference audit
- generic quadratic bridge audit
- denominator-free centered identity
- centered window translation
- fold involution
- centered pair bijection
- odd internal gap ladder
- GN interpretation
- owner comparison
- same-owner capacity
- fold plus successor transport
- bounded diagnostics
- final A/B/C/P judgment

Preserve false conjectures and smallest counterexamples.

## Final report

Answer explicitly:

1. Which finite-difference identities were already present and therefore not reimplemented?
2. What exact denominator-free theorem represents the half-lattice centered gnomon?
3. How is the 2*n-seat Legendre open shell equivalent to a centered half-square window?
4. What is the exact fold involution on shell offsets?
5. How does the existing CenteredPair arise from this fold?
6. Are the odd internal gaps 1,3,...,2*n-1 exactly the fold-pair differences?
7. How does degree-2 GN encode the same structure?
8. What exact constraint does a same canonical owner impose on a fold pair?
9. What is the exact per-prime same-owner capacity?
10. Does summing or canonically partitioning these capacities yield new leverage against full cover?
11. Can the fold constraint and Instruction 016 successor-owner change be combined nontrivially?
12. Is the centered formulation an arithmetic advance or only a geometric normalization?
13. What single next theorem should be attempted?

End with exactly one judgment:

Outcome A - CENTERED FOLD YIELDS A NEW OWNER CAPACITY OBSTRUCTION
Outcome B - CENTERED FOLD PRODUCES A NEW EXACT ARITHMETIC BRIDGE
Outcome C - CENTERED FOLD IS A GEOMETRIC NORMALIZATION ONLY
Outcome P - ONE PRECISE FOLD OWNER BRIDGE REMAINS
