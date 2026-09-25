
# TRM-012 — Same-label pairing / Tromino residual normal form

## Goal

Build the next boundary-flow layer above TRM-011.

TRM-011 proved:

BoundaryConserved S
<->
the A/B/C multiplicities have the same parity.

TRM-012 should turn finite boundary multiplicities into an explicit
same-label pairing certificate.

The preferred representation is a label-preserving involution on all boundary
ports:

mate (mate i) = i.

Non-fixed points form 2-cycles and are paired.
Fixed points are exactly the residual unpaired ports.

This gives one uniform object for both cases:

- even conserved boundary: no fixed points;
- odd conserved boundary: exactly three fixed points, one A, one B, one C.

Do not implement TransitionGraph, physical boundary extraction, planar
non-crossing pairing, XOR path transport, BoundaryIR, residual optimization,
or Four Color claims in this checkpoint.

## Existing owners

Reuse:

- DkMath.Tromino.BoundarySignature
- BoundarySignature
- boundaryDelta
- boundaryLabelCount
- BoundaryConserved
- boundaryConserved_iff_parity
- boundaryConserved_even_or_odd
- deltaA / deltaB / deltaC

Do not introduce a second boundary-label carrier.

## A. Mathlib pairing API audit

Before choosing implementation details, inspect Mathlib for:

- finite involutions / permutations;
- Finset.orderIsoFin;
- Fintype.equivFin;
- pairing/matching APIs;
- convenient even-cardinality pairing lemmas.

Prefer a deterministic, computable construction using the natural order on
Fin S.arity if the API is clean.

Do not introduce noncomputable data merely for convenience if an ordered
finite construction is reasonably available.

Record the API decision in report-011.md.

## B. BoundaryPairing certificate

Preferred production structure:

structure BoundaryPairing (S : BoundarySignature) where
  mate : Fin S.arity -> Fin S.arity
  involutive : Function.Involutive mate
  sameLabel : forall i, boundaryDelta S (mate i) = boundaryDelta S i

A theorem or field naming variant is acceptable.

Interpretation:

- mate i != i: port i is paired with the distinct same-label port mate i;
- mate i = i: port i is residual/unpaired.

Do not require fixed-point-freeness in the structure itself.

This representation is intentionally ready for the later transition layer:
the local transition map is already explicit.

## C. Residual ports

Define:

residualPorts P :=
  Finset.univ.filter (fun i => P.mate i = i)

and pairedPorts as its complement if useful.

Provide simp-friendly membership theorems:

i in residualPorts P <-> P.mate i = i.

For i not residual, prove:

- P.mate i != i;
- P.mate i is also non-residual;
- mate (mate i) = i;
- boundaryDelta S (mate i) = boundaryDelta S i.

Thus non-residual ports genuinely form same-label 2-cycles.

## D. Label-specific fibers

Define or reuse finite port fibers:

portsWithLabel S delta :=
  Finset.univ.filter (fun i => boundaryDelta S i = delta).

Prove:

(portsWithLabel S delta).card = boundaryLabelCount S delta.

This should be a thin bridge.

Pairing construction should operate independently inside each of the three
nonzero label fibers.

## E. Preferred canonical pairing construction

Preferred Outcome A:

Construct a computable canonicalBoundaryPairing S using the Fin order.

For each label fiber:

1. enumerate its ports in increasing Fin order;
2. pair adjacent entries:
   0 <-> 1,
   2 <-> 3,
   ...;
3. if the fiber cardinality is odd, leave exactly the final (or first)
   deterministic entry fixed.

Combine the three label-local maps.

Required properties:

- involutive;
- same-label;
- exactly count % 2 residual ports in each label fiber.

A rank-based implementation using an order equivalence to Fin fiber.card is
also acceptable.

Outcome B:

If Mathlib support makes a fully computable canonical map disproportionately
large, prove existence of a BoundaryPairing with the same residual-count
properties, using a generic finite even/odd pairing lemma.

If Outcome B is chosen:

- do not hide this choice;
- do not define a noncomputable canonical pairing;
- keep the existential theorem explicit;
- record what API would be needed for later executable TransitionGraph work.

Outcome A is preferred because the later solver should be executable.

## F. Residual parity theorem

For the constructed/certified pairing P, prove for each nonzero label:

number of residual A ports = countA % 2
number of residual B ports = countB % 2
number of residual C ports = countC % 2.

The exact theorem surface may use filtered residual Finsets.

This is stronger than only proving the conserved cases.

It means every finite boundary has a normal form:

same-label 2-cycles
+
at most one residual port of each label.

## G. Conserved even case

Using TRM-011 parity:

BoundaryConserved S
and all counts even

->
there exists / the canonical pairing has residualPorts = empty.

Expose a user-facing theorem:

conserved even boundary admits a perfect same-label pairing.

For the canonical construction, "perfect" means mate has no fixed points.

## H. Conserved odd case

Using TRM-011 parity:

BoundaryConserved S
and all counts odd

->
the residual has exactly three ports.

Prove:

- residualPorts.card = 3;
- exactly one residual port has deltaA;
- exactly one has deltaB;
- exactly one has deltaC.

If convenient, expose witnesses:

existsUnique residualA
existsUnique residualB
existsUnique residualC.

Do not require an order among the three residual ports.

This is the exact Tromino residual theorem:

paired transport + {A,B,C} residual.

## I. Main decomposition theorem

Package the two conserved cases.

Desired semantic theorem:

BoundaryConserved S
->
either

1. P is a perfect same-label pairing with no residual,

or

2. P has exactly the three A/B/C residual ports.

The theorem may return a disjunction over parity classes and the corresponding
residual facts.

Do not call this a graph/path theorem yet.

## J. Invalid/nonconserved normal form

For a nonconserved signature, the same pairing construction should still make
sense.

Example:

A A B C

has parity 0/1/1 and therefore leaves two residual ports, one B and one C.

Audit this explicitly.

This is valuable because the normal form diagnoses exactly which parity
obstruction remains.

## K. Duplicate-contact case

Use the TRM-011 duplicate signature:

A A

Both ports have the same contact/delta value but distinct Fin indices.

The pairing must pair those two distinct ports, leaving no residual.

This regression guards against accidentally reverting to Finset-of-contacts
semantics.

## L. Transition-readiness theorem

Expose a small theorem suitable for the next checkpoint:

for every non-residual port i,

- mate i is a distinct port;
- same boundary delta;
- mate (mate i) = i.

This should make TransitionGraph degree calculations almost mechanical later.

Do not build the transition graph yet.

## M. Computability / construct scan

Preferred result:

- all certificate data computable;
- no new noncomputable declaration.

If only existential Outcome B is practical, theorem proofs may use standard
Classical.choice dependencies, but no noncomputable production pairing value
should be introduced.

No:

- sorry;
- admit;
- unsafe;
- new axiom.

## N. Regression cases

Audit at least:

1. empty signature:
   residual empty;

2. even A A B B C C:
   residual empty;

3. odd A A A B B B C C C:
   residual card 3, one A/B/C each;

4. invalid A A B C:
   residual card 2, one B/C;

5. duplicate A A:
   the two indexed ports pair with each other, residual empty;

6. for every non-residual test port, mate is distinct, same-label, involutive.

## O. Proposed modules

Production:

DkMath/Tromino/BoundaryPairing.lean

Audit:

DkMathTest/Tromino/BoundaryPairingAxiomAudit.lean

Keep BoundarySignature.lean unchanged unless a small generic fiber lemma is
clearly owned there.

## P. Validation

Run focused builds for:

- DkMath.Tromino.BoundarySignature
- DkMath.Tromino.BoundaryPairing
- DkMathTest/Tromino/BoundaryPairingAxiomAudit

Run git diff --check.

Audit substantive public theorems with #print axioms.

## Q. Report

Create:

docs/dev/Tromino-ExchangeCalculus-260924-v0/report-011.md

Record:

- Mathlib pairing API findings;
- BoundaryPairing representation;
- canonical computable vs existential Outcome A/B;
- residualPorts representation;
- per-label residual parity theorem;
- conserved even theorem;
- conserved odd/Tromino-residual theorem;
- invalid/duplicate regressions;
- transition-readiness API;
- computability and axiom audit.

## Stop condition

Stop once every finite BoundarySignature has a same-label pairing normal form
whose residual multiplicity for A/B/C is exactly the original multiplicity
modulo 2, and conserved signatures reduce to either:

- perfect pairing, or
- perfect pairing plus one A/B/C Tromino residual.

Do not proceed to TransitionGraph, planar non-crossing pairing, physical
boundary extraction, XOR path transport, residual optimization, or Four Color
claims without review.
