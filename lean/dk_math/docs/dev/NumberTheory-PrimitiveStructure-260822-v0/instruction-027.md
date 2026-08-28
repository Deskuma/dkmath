# Codex Instruction — PRIM-R001 Legendre Module Decomposition / Facade Refactor

Branch: `wip/number-theory-primitive-structure-260822-v0`

Project: DkMath NumberTheory Primitive Structure

## Current verified state

PRIM-L019 is complete in:

```text
DkMath/NumberTheory/Legendre.lean
```

The file now contains the full Legendre application stack from the basic square-cell / square-offset vocabulary through:

- finite old-prime support and anchored phases;
- local wave occupancy and square-anchor carry;
- first-order incidence ledgers;
- pair overlap and near/far product localization;
- anchor-divisor / coprime localization;
- coprime packet decomposition;
- quotient coordinates and global quotient injectivity;
- quotient co-support and Direction/Depth dichotomy;
- fresh quotient directions;
- obstruction seat classification;
- coprime-local depth/pair ledgers;
- packet cross-pair coupling and the `p*q > n` sparsity threshold;
- the final `LegendreConjecture` / support-escape / non-full-cover equivalences.

The mathematics is intentionally still bounded: PRIM-L019 does not prove a contradiction or Legendre's conjecture.

The immediate problem is now engineering rather than mathematics: `Legendre.lean` has become a multi-thousand-line monolith.  The theorem layers are stable enough to expose natural module boundaries.

This checkpoint is **refactoring only**.

Do not add PRIM-L020 mathematics in this checkpoint.

---

# Goal

Split the current monolithic Legendre application into a dependency-ordered module hierarchy while preserving:

```text
namespace DkMath.NumberTheory.Legendre
```

and preserving all existing public declaration names and theorem statements.

After the refactor, the existing public import

```lean
import DkMath.NumberTheory.Legendre
```

must continue to expose the same Legendre API.

`DkMath/NumberTheory/Legendre.lean` should become a thin public facade rather than the theorem owner for thousands of lines of implementation.

Do not perform a repository-wide theorem redesign or rename pass.

---

# Required target structure

Create a directory:

```text
DkMath/NumberTheory/Legendre/
```

Use the following decomposition unless a concrete Lean dependency forces a very small adjustment.  If a name changes for dependency reasons, report it explicitly.

```text
DkMath/NumberTheory/Legendre/
  Internal/PairCombinatorics.lean
  Basic.lean
  Wave.lean
  PairOverlap.lean
  CoprimePacket.lean
  Quotient.lean
  QuotientSupport.lean
  Obstruction.lean
  LocalizedObstruction.lean
  PacketCross.lean
  Frontier.lean

DkMath/NumberTheory/Legendre.lean
```

Keep all non-internal declarations in:

```lean
namespace DkMath.NumberTheory.Legendre
```

The top-level facade should import the final module and contain only a short module docstring / public-entry documentation.

A preferred facade shape is conceptually:

```lean
import DkMath.NumberTheory.Legendre.Frontier

#print "file: DkMath.NumberTheory.Legendre"

/-!
## Legendre application facade

Public entry point for the square-anchored finite-prime localization stack.
-/
```

The exact docstring wording is flexible.

---

# Dependency shape

Prefer the following acyclic dependency graph:

```text
Internal.PairCombinatorics

Basic
  ↓
Wave
  ↓
PairOverlap
  ↓
CoprimePacket
  ↓
Quotient
  ↓
QuotientSupport
  ↓
Obstruction
  ↓
LocalizedObstruction

Quotient
  ↓
PacketCross

LocalizedObstruction + PacketCross
  ↓
Frontier
  ↓
DkMath.NumberTheory.Legendre facade
```

`PairOverlap` and `LocalizedObstruction` may both import `Internal.PairCombinatorics` as needed.

Do not introduce an import cycle merely to preserve historical source ordering.

---

# Module ownership

The ownership below is semantic.  Move coherent declaration blocks and their local helper lemmas together rather than mechanically cutting at a line number.

## 1. `Internal/PairCombinatorics.lean`

Move the finite unordered-pair helpers that are currently private but are reused by multiple later checkpoints after file splitting.

In particular inspect the current helpers around PRIM-L009:

```text
upperPairs
lowerPairs
card_upperPairs_eq_choose
```

`upperPairs` and `card_upperPairs_eq_choose` are reused by PRIM-L018, so they cannot remain file-private in `PairOverlap.lean` after the split.

Preferred solution:

```text
namespace DkMath.NumberTheory.Legendre.Internal
```

with internal helper names such as:

```lean
upperPairs
card_upperPairs_eq_choose
```

`lowerPairs` may remain private inside the internal file if it is only a proof helper.

These were previously private implementation details, so moving them to an `Internal` namespace does not constitute a public Legendre theorem redesign.

Do not duplicate the combinatorial proof in two modules.

## 2. `Basic.lean`

Own the stable square-anchored vocabulary and elementary finite support API.

This should include the coherent foundational declarations around:

```text
SquareCell
SquareOffset
SquareOffsetForbiddenBy
SquareOffsetCovered
squareOffsetCovered_iff_exists_prime_dvd
supportDisjointFrom_primeScalesUpTo_square_add_iff_not_covered
squareAnchorForbiddenResidue
squareOffsetForbiddenBy_iff_mod_eq_forbiddenResidue

squareOffsetPrimeSupport
mem_squareOffsetPrimeSupport
squareOffsetCovered_iff_primeSupport_nonempty
squareOffsetCovered_iff_primeSupport_card_pos
SquareOffsetOverlap
basic pair/product divisibility and phase lemmas
squareCell_iff_exists_squareOffset

LegendreConjecture
SquareAnchoredSupportEscape

squareOffsets
mem_squareOffsets
card_squareOffsets
```

Also place any basic finite cover-set definitions here if they do not depend on the wave-counting layer.

Do not move generic `Primitive` declarations into this directory.  `Legendre.Basic` remains an application layer consuming `DkMath.NumberTheory.Primitive`.

## 3. `Wave.lean`

Own the one-wave / first-order local occupancy layer, including PRIM-L006 through the square-anchor carry / first-order incidence material.

Expected concepts include:

```text
squareWaveOffsets
squarePrimeWaveOffsets
one-wave membership
large-modulus at-most-one occupancy
card_squareWaveOffsets_eq_div_sub_div
squareWaveCarry
carry 0/1 characterizations
card_squareWaveOffsets_eq_div_add_carry
prime-wave specializations
first-order incidence / baseline / carry ledgers
SquareOffsetsFullyCovered
covered / escaping square-offset finite sets if their current dependencies belong here
```

Keep the exact existing declaration names.

## 4. `PairOverlap.lean`

Own PRIM-L009 and PRIM-L010:

```text
squareOffsetPrimePairMultiplicity
squarePrimePairs
squarePrimePairOverlapCount
exact local/global pair double count
pair-overlap full-cover budget
product-wave arithmetic
near/far pair localization
active far pairs
near baseline / near carry
localized second-order normal form
```

Import the internal pair-combinatorics helper module rather than keeping a cross-file `private` dependency.

## 5. `CoprimePacket.lean`

Own PRIM-L011 and PRIM-L012:

```text
squareAnchorDivisorPrimes
squareAnchorNondivisorPrimes
anchor-divisor/nondivisor cover split
coprime offset window
card = 2 * Nat.totient n
nondivisor incidence
coprime base representatives
n-shift packet seats
base ∪ shift decomposition
squareOffsetAnchorNondivisorSupport
packet support disjointness
full-cover distinct left/right nondivisor witnesses
coprime-restricted incidence
```

This module is the owner of the canonical packet `(r, n+r)` geometry.

## 6. `Quotient.lean`

Own PRIM-L013 and PRIM-L014:

```text
squareOffsetSupportQuotient
exact factor reconstruction
n < quotient
coprimality transfer
coprime-wave quotient image
quotient-image cardinality preservation
global coprime-support incidence domain
global quotient projection
quotient collision rigidity
global injectivity for 4 ≤ n
global quotient cardinality frontier
```

Keep the collision helper lemmas local/private if they are only used inside this module.

## 7. `QuotientSupport.lean`

Own PRIM-L015 and PRIM-L016:

```text
squareQuotientAnchorNondivisorSupport
support transfer / erase equality
support cardinality sandwich
selected-prime depth iff p^2 divisibility
SquareBody quotient closure
Direction/Depth dichotomy
singleton support
exact quotient-prime iff singleton + depth one
FreshPrimeDirection bridge
SupportDisjointFrom bridge
old-prime × large-fresh-prime factorization
fresh-or-obstructed trichotomy
```

This is the bridge back from Legendre quotient coordinates into the generic Primitive direction semantics.

## 8. `Obstruction.lean`

Own PRIM-L017:

```text
simple/fresh seat
singleton-depth seat
multi-support seat
finite seat classes
covered coprime trichotomy
disjoint full-cover partition
2 * totient classification identity
simple-seat fresh quotient bridge
global p^2 depth budget
global pair obstruction budget
combined PRIM-L017 frontier
```

## 9. `LocalizedObstruction.lean`

Own PRIM-L018:

```text
coprime-local p^2 waves
local depth multiplicity
exact depth transpose
anchor-nondivisor canonical pairs
coprime-local pair overlap sets
exact choose-support double count
localized obstruction certificate
localized full-cover frontier
localized ≤ global domination
```

Reuse `Internal.PairCombinatorics` rather than cloning `upperPairs` / choose-cardinality machinery.

## 10. `PacketCross.lean`

Own PRIM-L019:

```text
squareAnchorNondivisorOrderedPrimePairs
squareAnchorPacketCrossOffsets
squareAnchorPacketCrossPairCount
exact Σ |leftSupport| * |rightSupport| transpose
Nat.totient n ≤ packetCrossPairCount under full cover
packet quotient factorization p*a + n = q*b
fixed-pair product-period divisibility
p*q > n => at most one packet hit
near/far packet cross-pair partition
far contribution cardinality bound
```

This module should import `Quotient` (and whatever thinner predecessor is actually sufficient) rather than importing the obstruction stack merely because PRIM-L019 was historically written after PRIM-L018.

Preserve the useful conceptual independence:

```text
within-seat obstruction branch
and
cross-seat packet branch
```

should meet only at the facade/frontier layer unless a theorem genuinely connects them.

## 11. `Frontier.lean`

Own the final public Legendre reduction/bridge theorems that currently sit at the end of the monolithic file, including:

```text
squareOffsetsFullyCovered_iff_coveredSquareOffsets_eq
not_squareOffsetsFullyCovered_iff_escaping_nonempty
squareAnchoredSupportEscape_iff_not_fully_covered
squareAnchoredSupportEscape_iff_raw
prime_of_squareAnchoredSupportEscape
legendreConjecture_of_squareAnchoredSupportEscape
legendreConjecture_iff_squareAnchoredSupportEscape
legendreConjecture_iff_squareOffsets_not_fully_covered
```

Import both terminal research branches:

```text
LocalizedObstruction
PacketCross
```

so the public facade exposes the whole current application API transitively.

Do not make these final equivalences depend logically on the newest obstruction/cross-pair theorems if they do not need them; the imports are for public aggregation, not proof inflation.

---

# Public API preservation

This is a hard requirement.

For every declaration that is currently public in:

```text
DkMath.NumberTheory.Legendre
```

preserve:

- namespace;
- declaration name;
- theorem/definition statement;
- semantic meaning.

Moving a declaration to another source file must not require downstream callers to rename it.

The top-level import path must remain:

```lean
import DkMath.NumberTheory.Legendre
```

Do not introduce nested public namespaces such as:

```text
Legendre.Wave.foo
Legendre.Quotient.foo
```

for existing theorems.  Source-file organization and Lean declaration namespace are separate concerns here.

The only intended namespace change is for formerly private reusable helper machinery moved into:

```text
DkMath.NumberTheory.Legendre.Internal
```

---

# Refactoring method

Prefer a move-first process rather than rewriting proofs.

Recommended sequence:

1. create `Internal/PairCombinatorics.lean`;
2. create `Basic.lean` and move the foundation;
3. move one dependency layer at a time in the order above;
4. build the moved module after each layer;
5. create `Frontier.lean`;
6. replace the monolithic `Legendre.lean` body with the facade import/docstring;
7. run full verification.

Where a proof breaks only because a formerly private helper crossed a file boundary, expose the smallest internal helper needed.  Do not opportunistically rewrite the mathematical argument.

If a declaration's actual dependency makes the proposed owner impossible without a cycle, move that declaration to the earliest natural module that satisfies the DAG and report the exception.

---

# Import hygiene

Each child module should import the nearest logical predecessor(s), not the top-level facade.

Never write a child import such as:

```lean
import DkMath.NumberTheory.Legendre
```

because that creates a facade cycle.

Prefer targeted imports such as:

```text
Basic -> Primitive.SquareBody / required Mathlib
Wave -> Legendre.Basic
PairOverlap -> Legendre.Wave + Internal.PairCombinatorics
CoprimePacket -> Legendre.PairOverlap
Quotient -> Legendre.CoprimePacket
QuotientSupport -> Legendre.Quotient
Obstruction -> Legendre.QuotientSupport
LocalizedObstruction -> Legendre.Obstruction + Internal.PairCombinatorics
PacketCross -> Legendre.Quotient
Frontier -> Legendre.LocalizedObstruction + Legendre.PacketCross
```

Do not spend this checkpoint aggressively minimizing every Mathlib import.  Correct acyclic module ownership is more important than import micro-optimization.

---

# Module documentation

Each new module should have a short module docstring stating:

- which semantic layer it owns;
- which earlier layer it depends on;
- that it remains bounded finite arithmetic where applicable;
- that no new Legendre proof is introduced by the refactor.

Do not copy the entire project history into every file.

Use the existing DkMath copyright header and `#print "file: ..."` convention.

---

# Non-goals

Do **not** do any of the following in PRIM-R001:

- add PRIM-L020 mathematics;
- strengthen any theorem;
- weaken any hypothesis;
- prove a new contradiction;
- prove `SquareAnchoredSupportEscape`;
- prove Legendre's conjecture;
- add third-order inclusion-exclusion;
- add matching/Hall machinery;
- introduce analytic estimates;
- introduce a new valuation framework;
- connect finite freshness to PrimitiveBeam/Zsigmondy origin;
- rename the public Legendre API for aesthetics;
- move generic Primitive modules into the Legendre directory;
- refactor unrelated NumberTheory modules.

This checkpoint is successful when the mathematics is materially unchanged but the source ownership is substantially cleaner.

---

# Verification

At minimum run the modules incrementally and then:

```sh
lake build DkMath.NumberTheory.Legendre.Basic
lake build DkMath.NumberTheory.Legendre.Wave
lake build DkMath.NumberTheory.Legendre.PairOverlap
lake build DkMath.NumberTheory.Legendre.CoprimePacket
lake build DkMath.NumberTheory.Legendre.Quotient
lake build DkMath.NumberTheory.Legendre.QuotientSupport
lake build DkMath.NumberTheory.Legendre.Obstruction
lake build DkMath.NumberTheory.Legendre.LocalizedObstruction
lake build DkMath.NumberTheory.Legendre.PacketCross
lake build DkMath.NumberTheory.Legendre.Frontier
lake build DkMath.NumberTheory.Legendre
lake build DkMath.NumberTheory.Primitive
lake build DkMath
git diff --check
```

Also audit all touched Lean files for new occurrences of:

```text
sorry
admit
native_decide
axiom
```

Report unrelated pre-existing occurrences separately; do not broaden scope to repair them.

---

# API smoke checks

After the facade is in place, verify that importing only:

```lean
import DkMath.NumberTheory.Legendre
```

still allows representative checks from every layer, for example:

```lean
#check DkMath.NumberTheory.Legendre.SquareCell
#check DkMath.NumberTheory.Legendre.squareWaveCarry
#check DkMath.NumberTheory.Legendre.squarePrimePairOverlapCount
#check DkMath.NumberTheory.Legendre.squareAnchorCoprimeOffsets
#check DkMath.NumberTheory.Legendre.squareOffsetSupportQuotient
#check DkMath.NumberTheory.Legendre.squareQuotientAnchorNondivisorSupport
#check DkMath.NumberTheory.Legendre.squareAnchorCoprimeSimpleFreshOffsets
#check DkMath.NumberTheory.Legendre.squareAnchorCoprimePrimePairOverlapCount
#check DkMath.NumberTheory.Legendre.squareAnchorPacketCrossPairCount
#check DkMath.NumberTheory.Legendre.legendreConjecture_iff_squareOffsets_not_fully_covered
```

Use the actual final declaration names if any spelling differs from this list.

---

# Acceptance criteria

PRIM-R001 is complete when:

1. the monolithic `Legendre.lean` theorem body has been decomposed into coherent dependency-ordered child modules;
2. the top-level `DkMath.NumberTheory.Legendre` import remains the public entry point;
3. all existing public declaration names and theorem statements are preserved;
4. no child module imports the top-level facade;
5. the import graph is acyclic;
6. formerly private helpers reused across new file boundaries are centralized in an `Internal` module rather than duplicated;
7. PRIM-L019 remains mathematically unchanged and available through the facade;
8. the final Legendre reduction/equivalence theorems live in `Frontier.lean`;
9. all requested builds and audits succeed;
10. no new mathematical checkpoint is mixed into the refactor.

Report:

- the final module tree;
- any deviations from the proposed ownership and why;
- any private helper that had to become `Internal`;
- the final line count of the facade and each child module;
- confirmation that the representative facade API checks succeed.
