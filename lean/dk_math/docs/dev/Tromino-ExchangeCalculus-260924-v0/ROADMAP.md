
# Roadmap — Tromino Exchange Calculus

## TRM-000 — Representation / ownership audit

Confirm current Mathlib Klein-four API and compare:
ZMod 2 × ZMod 2, Bool × Bool, Fin 4.

Audit DkMath for an existing production four-state exchange carrier.
Keep NumberGeometry read-only / pattern-only.

## TRM-001 — Four-state / exchange kernel

Proposed modules:

- DkMath/Tromino/State.lean
- DkMath/Tromino/Exchange.lean
- DkMathTest/Tromino/ExchangeAxiomAudit.lean

Target concepts:

- TrominoState
- waitingStates
- exchange

Target facts:

- state cardinality = 4
- waiting cardinality = 3
- zero exchange
- involutive exchange
- composition by addition
- commutativity
- unique exchange to a target
- nonzero exchange for a distinct target

## TRM-002 — Geometric / CosmicFormula calibration

Create a one-way bridge from the existing geometric theorem

area block2 = area L_tromino + area hole2

to DkMath.CosmicFormula.Mass.BodyGapSplit Nat.

Calibrate against degree 2, x = u = 1:

Big = 4
Body = 3
Gap = 1

Keep the state kernel independent of CosmicFormula.

## TRM-003 — Typed gap / restoration bridge

Audit whether BookOfMagic.GapCrystal already expresses the dependent typed-gap
semantics. Prefer a thin adapter over a duplicate abstraction.

## TRM-004 — Uniform exchange rescue

For a local piece translated by one global exchange delta, define forbidden
exchange elements induced by boundary contacts.

Prove only the conditional rescue statement:

forbidden ≠ univ → legal exchange exists.

If the current state conflicts and forbidden ≠ univ, produce a nonzero rescue.

## TRM-005 — Macro-cell / recursive substitution

Implement the v3 macro-cell idea and certified peel / restore.

## TRM-006 — Boundary IR

Boundary ports, state domains, macro nodes, restoration stack, optional cyclic
order.

## TRM-007 — Pairing / transition graph

XOR/parity, IN/OUT pairing, derived path/cycle graph, state integration.

## TRM-008 — Residual minimization

Escape degree, forced moves, contraction, irreducible residual, mod observers,
kernelization certificate.

## TRM-009 — Planar-map bridge assessment

Assess how much arbitrary planar-map coloring compiles into the Tromino IR.


## Roadmap refinement — 2026-09-25

TRM-004 completed the state-only forbidden-set rescue calculus. Before
MacroCell work, insert one bounded algebraic checkpoint:

### TRM-005 — Uniform piece exchange / boundary forbidden deltas

- indexed uniform exchange;
- internal distinctness preservation;
- one contact forbids one unique delta;
- finite forbiddenExchangeSet;
- boundaryCompatible iff delta is outside the forbidden set;
- conditional piece rescue and nonzero rescue.

The earlier MacroCell / recursive-substitution work moves one checkpoint later.
This refinement preserves the original direction: local exchange algebra is
completed before geometric recursion and BoundaryIR.


### TRM-006 — Atomic FourColorCell

After the piece-level forbidden-delta calculus, return to geometry with the
smallest colored object:

- audit executable compatibleExchanges;
- define a minimal colored finite shape;
- construct the canonical 2×2 block with all four states exactly once;
- prove uniform exchange preserves four-state completeness;
- introduce only the minimum grid-adjacency notion if ownership remains local.

MacroCell collapse/expand begins only after this atomic cell is stable.


### TRM-007 — FourColorMacroCell collapse / expand

The atomic complete four-state cell now becomes one explicit level-0 macro
unit.

- certify a complete four-state payload;
- lossless collapse / expand;
- record 4 atomic cells <-> 1 macro unit;
- transport uniform exchange through the abstraction;
- keep recursive scale/level out of this type.

A separate scaled/recursive macro abstraction will follow after this bounded
level-0 contract is stable.


### TRM-008 — MacroTrominoFrame / typed macro gap

Build the first level-1 macro composition:

- MacroShape: a finite macro-coordinate footprint with FourColorMacroCell
  payloads;
- canonical 2×2 macro frame;
- L-shaped three-macro body plus one typed MacroGapSlot;
- exact restoration certificate;
- macro count 3+1=4;
- lifted atomic count 12+4=16.

Do not yet generalize to arbitrary recursion depth. The next checkpoint will
choose the scaled/recursive representation after this one-level composition is
kernel-checked.


### TRM-009 — Recursive scaled macro levels

Generalize the one-level 3+1 frame into a level-indexed carrier:

- level 0 = FourColorMacroCell;
- level k+1 = four level-k children;
- body positions = 3;
- typed residual position = 1;
- atomic mass at level k = 4^(k+1);
- successor split = 3*4^(k+1) + 4^(k+1) = 4^(k+2);
- recursive uniform exchange preserves mass.

Keep physical flattening and boundary signatures for later checkpoints.


### TRM-010 — Recursive CosmicFormula scale bridge

Before boundary signatures, calibrate the arbitrary-level recursive mass law
against the degree-two equal-scale CosmicFormula.

For s(k)=2^(k+1):

- s(k)^2 = 4^(k+1);
- Cosmic Gap = 4^(k+1);
- Cosmic Body = 3*4^(k+1);
- Cosmic Big = 4^(k+2);

matching gapAtomicMass, bodyAtomicMass, and successor atomicMass exactly.

Also record the numeric Core/Beam/Gap refinement 1+2+1=4 without assigning
specific macro positions to Core or Beam.


### TRM-011 — Boundary signature / XOR conservation

Begin the structural boundary layer after completing recursive mass
calibration.

Key bridge:

forbiddenDelta(contact) = inside + outside

is reused as the boundary crossing delta. The same quantity has two roles:

- PieceExchange: one distinct forbidden exchange value;
- BoundaryFlow: one multiplicity-preserving boundary label.

Introduce an ordered finite BoundarySignature, boundarySum, A/B/C label
counts, and prove:

boundarySum = 0
iff
n_A, n_B, n_C have equal parity.

Pairing and TransitionGraph remain later checkpoints.


### TRM-012 — Same-label pairing / Tromino residual

Turn the TRM-011 parity theorem into an explicit pairing normal form.

Represent local pairing as a label-preserving involution on boundary ports:

- non-fixed 2-cycles = paired transport;
- fixed points = residual ports.

Target normal form for every boundary:

- each A/B/C fiber leaves exactly count mod 2 residual ports.

Hence a conserved boundary has exactly two forms:

- all-even: perfect same-label pairing;
- all-odd: same-label pairs plus one A/B/C residual port each.

Keep TransitionGraph and planarity for later checkpoints.


### TRM-013 — Closed transition network / alternating involutions

Use the TRM-012 local mate involution together with a second certified
involution for real boundary crossing.

For perfect/even local pairings:

- cross is fixed-point-free and changes region;
- local mate is fixed-point-free and stays in-region;
- each global port has exactly two distinct neighbors;
- transitionStep = localMate ∘ cross is a finite permutation;
- every transition orbit is periodic;
- the boundary delta label is constant along the orbit.

Residual/open endpoints and ghost completion remain a later checkpoint.


### TRM-014 — Closed-orbit XOR obstruction

Before introducing open residual endpoints, test whether the closed transition
kernel already guarantees XOR-integrable cycles.

It does not appear to do so abstractly.

For a primitive transition orbit with preserved nonzero label delta:

- cycle XOR = n copies of delta;
- characteristic two gives cycle XOR = 0 iff n is even.

Formalize primitive return length, transitionXor, state transport, and a
3-region / 6-edge alternating fixture whose transitionStep has primitive
period 3 and nonzero cycle XOR.

This isolates the extra global zero-holonomy condition required beyond local
conservation and perfect pairing.


### TRM-015 — Label-only boundary flow certificate

TRM-014 exposed a genuine global zero-holonomy obstruction. Before color
recovery, remove a logical circularity in the current certificate stack:
BoundarySignature still stores the absolute inside/outside states whose
differences it analyses.

Introduce a label-only FlowSignature:

- finite ordered ports;
- one nonzero TrominoState delta per port;
- no absolute states.

Reprove the conservation/parity theorem on this carrier and show that the
existing BoundarySignature API factors exactly through a computable erasure.

Pairing and transition migration to the label-only carrier remains the next
reviewed step.


### TRM-016 — FlowPairing migration

Move the TRM-012 pairing/residual normal form onto the label-only
FlowSignature while preserving the existing contact-based stack.

- FlowPairing = label-preserving involution;
- deterministic canonical pairing;
- residual count per label = multiplicity mod 2;
- conserved even -> perfect;
- conserved odd -> one A/B/C residual;
- BoundaryPairing adapter and canonical erasure calibration.

TransitionGraph and TransitionXor remain contact-based until the next reviewed
migration.


### TRM-017 — FlowTransition migration

Move the TRM-013 closed transition kernel onto FlowSignature/FlowPairing.

- FlowNetwork / FlowCrossing / ClosedFlowNetwork;
- two-neighbor transition relation;
- alternating transition permutation;
- label preservation and finite periodicity;
- adapters from contact-based BoundaryNetwork;
- exact pointwise agreement of the erased transition step.

TransitionXor remains contact-based until the next reviewed migration.
