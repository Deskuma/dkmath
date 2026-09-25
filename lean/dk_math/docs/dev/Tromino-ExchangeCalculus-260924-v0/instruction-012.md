
# TRM-013 — Closed transition network / alternating involutions

## Goal

Build the first global transition layer above BoundaryPairing.

TRM-012 already provides the local involution:

local mate
  - same label;
  - involutive;
  - fixed-point-free in the perfect/even case.

TRM-013 should add the second involution:

real boundary crossing.

For a finite family of region boundary signatures, each physical boundary edge
is represented by two half-ports, and crossing swaps those two half-ports.

In the closed/even case, the two involutions

cross
localMate

generate a finite degree-two transition system.

This checkpoint should formalize that closed kernel and prove that alternating
transition is a finite permutation whose orbits are periodic cycles.

Do not yet handle odd residual endpoints, ghost completion, physical planar
boundary extraction, XOR path integration, BoundaryIR, optimization, or Four
Color claims.

## Why closed/even first

A residual port in TRM-012 is a fixed point of local mate. Treating that
immediately as a graph endpoint requires a design decision about open
boundaries / ghost ports.

Avoid mixing those concerns here.

TRM-013 assumes a perfect local pairing at every region:

residualPorts = empty.

TRM-014 may then extend the same machinery to open/residual boundaries.

## Existing owners

Reuse:

- DkMath.Tromino.BoundarySignature
- DkMath.Tromino.BoundaryPairing
- BoundaryPairing
- canonicalBoundaryPairing
- residualPorts
- mate_sameLabel
- canonicalBoundaryPairing_transition_ready
- boundaryDelta

Do not reimplement local pairing.

## A. Finite region network

Introduce a finite collection of region signatures.

Preferred shape:

structure BoundaryNetwork where
  regionCount : Nat
  signature : Fin regionCount -> BoundarySignature

Then define the global half-port type:

NetworkPort N :=
  Sigma (fun r : Fin N.regionCount => Fin (N.signature r).arity)

Equivalent dependent representations are acceptable if they preserve:

- region identity;
- local port identity;
- finite enumerability;
- DecidableEq / Fintype when possible.

Prove / synthesize finite cardinality infrastructure as needed.

## B. Crossing involution

Extend BoundaryNetwork, or introduce a second certified structure, carrying:

cross : NetworkPort N -> NetworkPort N

with required laws:

1. cross_involutive:
   cross (cross p) = p

2. cross_changes_region:
   (cross p).1 != p.1

3. cross_sameLabel:
   boundaryDelta (signature (cross p).1) (cross p).2
     =
   boundaryDelta (signature p.1) p.2

The region-change condition deliberately excludes self-adjacent region edges
in this first kernel. Record this scope boundary.

It immediately implies cross p != p.

Do not encode planar geometry or coordinates.

## C. Local pairings per region

A closed transition network additionally carries:

pairing : forall r, BoundaryPairing (signature r)

perfect :
  forall r, residualPorts (pairing r) = empty

Preferred structure name:

ClosedBoundaryNetwork

or:

BoundaryTransitionNetwork

with an explicit perfectness field.

Do not force canonicalBoundaryPairing as the only allowed choice. Later
optimization may choose among different valid pairings.

A helper constructor using canonicalBoundaryPairing for known-even signatures
is welcome if cheap.

## D. Lift local mate globally

Define:

localMatePort :
  NetworkPort N -> NetworkPort N

by preserving the region index and applying that region's pairing.mate.

Prove:

- localMatePort is involutive;
- localMatePort preserves region;
- localMatePort preserves boundary delta;
- under perfectness, localMatePort p != p.

The last theorem should derive from residualPorts = empty rather than duplicate
pairing logic.

## E. Two-neighbor transition relation

Define the two transition neighbors of a port:

transitionNeighbors p :=
  { cross p, localMatePort p }.

Prove:

- cross p != p;
- localMatePort p != p;
- cross p != localMatePort p
  (because cross changes region while local mate preserves region);
- transitionNeighbors p has card 2.

Define an adjacency predicate:

TransitionAdj p q :=
  q = cross p or q = localMatePort p

(or symmetric orientation).

Prove:

- symmetric;
- irreflexive;
- every port has exactly two distinct transition neighbors.

If Mathlib SimpleGraph packaging is clean, optionally expose:

transitionGraph : SimpleGraph (NetworkPort N).

But do not make SimpleGraph API complexity a blocker. The explicit neighbor
Finset and adjacency theorem are sufficient for this checkpoint.

## F. Alternating transition permutation

Define one full local/cross alternation step.

Preferred convention:

transitionStep p := localMatePort (cross p)

Document the order exactly.

Since cross and localMatePort are both involutions, transitionStep is a
bijection with inverse:

cross (localMatePort p).

Define:

transitionEquiv : NetworkPort N ≃ NetworkPort N

if clean.

Required theorems:

- inverse formula;
- injective;
- surjective;
- boundary delta preserved by transitionStep.

Do not claim transitionStep itself is involutive; composition of two
involutions need not be.

## G. Finite periodic orbit theorem

Because NetworkPort is finite and transitionStep is a permutation, every port
lies on a finite periodic orbit.

Prove a theorem with semantic content:

for every p,
there exists n > 0 such that
  (transitionStep^[n]) p = p.

Prefer existing Equiv/Perm orbit API if available.

If Mathlib provides a stronger finite-order theorem, expose the smallest useful
corollary.

If the API is awkward, a direct Fintype pigeonhole proof is acceptable.

Do not yet identify the orbit with a SimpleGraph cycle object if that requires
substantial graph-library machinery.

## H. Label-homogeneous orbit

Prove:

boundary label is invariant under every transitionStep iteration.

At minimum:

delta (transitionStep p) = delta p.

If cheap, generalize to:

delta ((transitionStep^[n]) p) = delta p.

This is useful for later XOR transport and means each closed transition orbit
carries one nonzero A/B/C label.

## I. Relation to degree-two cycle intuition

Record precisely:

- the undirected local/cross adjacency has two neighbors at every port;
- the composed transition permutation walks two alternating edges at a time;
- finite permutation orbits are periodic.

This is the exact kernel-level meaning of the earlier "one-stroke / cycle"
intuition.

Do not claim the original planar map is Eulerian.

Do not claim a graph-theoretic connected component is already identified with
a Mathlib Cycle unless explicitly proved.

## J. Canonical small regression network

Construct a small closed network in the audit module.

Recommended model:

- two regions;
- each region has signature A A;
- local canonical pairing swaps the two local ports;
- cross swaps corresponding ports across the two regions.

Then audit:

- total NetworkPort count = 4;
- cross changes region and is involutive;
- local mate changes local port and is involutive;
- every transition neighbor set has card 2;
- transitionStep is periodic;
- label remains A throughout the orbit.

A second example with B B or mixed disjoint cycles is useful but optional.

## K. Perfect canonical constructor

If useful, provide a constructor theorem/helper:

If for every region the canonicalBoundaryPairing has no residual,
then the family of canonical pairings supplies the local pairing/perfect
fields of a ClosedBoundaryNetwork.

Do not require BoundaryConserved alone unless evenness is also available.
Recall a conserved odd signature has three residuals and is not closed.

## L. Computability

Keep all data definitions executable.

No new noncomputable declaration should be needed.

If Sigma/Fintype enumeration creates an avoidable classical dependency,
prefer explicit finite encodings rather than sacrificing executable transition
steps.

## M. Scope exclusions

No:

- residual/open endpoints;
- ghost ports;
- physical geometric extraction;
- planar cyclic embedding;
- non-crossing pairing;
- XOR path integration;
- color reconstruction;
- BoundaryIR;
- optimizer;
- Four Color theorem claim.

## N. Proposed modules

Production:

DkMath/Tromino/TransitionGraph.lean

Audit:

DkMathTest/Tromino/TransitionGraphAxiomAudit.lean

The filename may say Graph even if the core representation remains an
adjacency + permutation API rather than Mathlib SimpleGraph.

## O. Validation

Run focused builds for:

- DkMath.Tromino.BoundaryPairing
- DkMath.Tromino.TransitionGraph
- DkMathTest/Tromino/TransitionGraphAxiomAudit

Run git diff --check.

Audit substantive public theorems with #print axioms.

Scan for:

- sorry
- admit
- unsafe
- new axiom
- unintended noncomputable

## P. Report

Create:

docs/dev/Tromino-ExchangeCalculus-260924-v0/report-012.md

Record:

- NetworkPort representation;
- crossing structure and scope restriction;
- localMatePort lift;
- transitionNeighbors / degree-two theorem;
- whether SimpleGraph was packaged;
- transitionStep convention;
- transitionEquiv / inverse theorem;
- finite periodic-orbit theorem;
- label-invariance theorem;
- canonical regression network;
- computability / axiom audit;
- what remains for odd residual / ghost endpoint support.

## Stop condition

Stop once the perfect/even boundary network is a finite two-neighbor
transition system and every alternating transition orbit is provably periodic.

Do not proceed to residual/open paths, ghost completion, physical boundary
extraction, XOR path transport, BoundaryIR, optimization, or Four Color claims
without review.
