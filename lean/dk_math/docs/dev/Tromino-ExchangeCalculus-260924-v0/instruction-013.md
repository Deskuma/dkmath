
# TRM-014 — Closed-orbit XOR obstruction / primitive cycle compatibility

## Goal

Before adding open residual endpoints or ghost completion, determine exactly
when a closed transition orbit from TRM-013 is compatible with XOR state
integration.

TRM-013 proves:

- transitionStep is a finite permutation;
- every port has a positive period;
- boundaryDelta is constant along transitionStep iterations.

This does **not** by itself imply that the XOR accumulated around the first
return is zero.

TRM-014 should formalize the missing global obstruction.

For a port p with primitive/minimal positive period n and constant nonzero
label delta,

cycle XOR = n copies of delta.

Since TrominoState has characteristic two,

cycle XOR = 0
iff
n is even.

Therefore odd primitive transition cycles obstruct path-independent state
integration.

This checkpoint should also construct and kernel-check a concrete 3-region
counterexample with a primitive transition period 3.

Do not yet implement open paths, ghost completion, general color recovery,
physical boundary extraction, BoundaryIR, optimization, or Four Color claims.

## Research significance

This checkpoint answers an explicit question from the original BoundaryFlow
plan:

Does local boundary conservation plus local pairing force global cycle XOR
compatibility?

Expected answer in the current abstract network model:

No.

A closed network can satisfy:

- proper nonzero boundary labels;
- local conservation;
- perfect same-label pairing;
- involutive real crossings;
- degree-two transition structure;

while still containing an odd primitive transition orbit whose XOR is
nonzero.

The additional global condition is an even-parity / zero-holonomy condition on
primitive transition cycles.

Keep this conclusion carefully scoped to the current abstract network model.

## Existing owners

Reuse:

- DkMath.Tromino.TransitionGraph
- transitionStep
- transitionStep_sameLabel
- transitionStep_iterate_sameLabel
- transitionStep_periodic
- boundaryDelta
- boundaryDelta_ne_zero
- state_add_self
- deltaA / deltaB / deltaC

Do not modify BoundarySignature or BoundaryPairing unless a tiny generic lemma
is clearly owned there.

## A. Iterated crossing XOR

For N : ClosedBoundaryNetwork, p : NetworkPort ..., define the XOR accumulated
over n transition steps.

Recommended convention:

transitionXor N p n :=
  Finset.sum (Finset.range n)
    (fun j =>
      boundaryDelta
        (N.signature (((transitionStep N)^[j]) p).1)
        (((transitionStep N)^[j]) p).2)

This counts one physical boundary-crossing delta per transitionStep.

Document the convention carefully:

- j=0 contributes the label at the starting port;
- n steps contributes n labels;
- local mate itself adds no extra state difference; it only routes the port.

An equivalent recursive definition is acceptable if it gives cleaner proofs.

## B. Constant-label reduction

Using transitionStep_iterate_sameLabel, prove:

transitionXor N p n = n • boundaryDelta ... p

or an equivalent repeated-addition formula.

Do not prove this by enumerating A/B/C separately.

This theorem is the main bridge from transition dynamics to parity.

## C. Characteristic-two repeated-label theorem

Prove generically for delta : TrominoState:

n • delta = 0
iff
delta = 0 or n % 2 = 0.

A formulation split by delta != 0 is also acceptable:

delta != 0 ->
  (n • delta = 0 <-> n % 2 = 0).

Prefer deriving from the exponent-two law already available
(state_add_self / additive Klein four structure).

Expose a reusable theorem because it belongs to the four-state exchange
calculus, even if it remains in this module for now.

## D. Closed-return certificate

Introduce a small proposition:

def TransitionReturn (N) (p) (n : Nat) : Prop :=
  0 < n ∧ (transitionStep N)^[n] p = p

Then define the stronger primitive return:

def PrimitiveTransitionReturn (N) (p) (n : Nat) : Prop :=
  TransitionReturn N p n ∧
  forall m, 0 < m -> m < n -> (transitionStep N)^[m] p != p

Equivalent naming is acceptable.

Important:

Do not define cycle compatibility merely as "there exists a positive return
with zero XOR".

That condition would be too weak: every odd primitive period n also has the
even return 2n, whose repeated XOR is zero.

The primitive/minimal first-return length is essential.

## E. Primitive return existence

From finiteness / transitionStep_periodic, prove:

for every p,
there exists n,
  PrimitiveTransitionReturn N p n.

Use Nat.find/minimality if needed.

This theorem may be noncomputable at the proof level, but do not introduce a
noncomputable production data definition if avoidable.

If Mathlib permutation orbit API gives a computable orbit length/order, prefer
that.

Report the API decision.

## F. Primitive cycle XOR compatibility

Define:

PrimitiveCycleCompatible N p n :=
  PrimitiveTransitionReturn N p n ∧ transitionXor N p n = 0

or keep compatibility as a theorem parameter rather than a new structure.

Main theorem:

PrimitiveTransitionReturn N p n
->
(
  transitionXor N p n = 0
  <->
  n % 2 = 0
)

The proof uses:

- transition labels are nonzero because each BoundarySignature is proper;
- constant-label reduction;
- characteristic-two parity theorem.

This is the central theorem of TRM-014.

## G. State transport on a finite transition prefix

Define the minimal transport observer:

transportState
  (base : TrominoState)
  (N)
  (p)
  (n : Nat) : TrominoState :=
    base + transitionXor N p n

Prove:

- transport over zero steps = base;
- transport over concatenated lengths adds the corresponding XOR;
- if n is a primitive return, then returning to the starting port preserves
  base state iff the primitive cycle XOR is zero.

This is only prefix/orbit transport.

Do not yet define global region coloring or path-independence between arbitrary
network paths.

## H. 3-region odd-cycle counterexample

Construct an audit fixture with:

- three regions;
- each region signature is A A;
- canonical local pairing swaps the two local A ports;
- crossing is a perfect involution that forms one alternating undirected
  6-cycle.

One concrete crossing pattern may be:

local pairs:
  a0--a1
  b0--b1
  c0--c1

cross pairs:
  a1--b0
  b1--c0
  c1--a0

with symmetric reverse assignments.

Then transitionStep = localMate after cross should have a primitive 3-cycle,
for example on one parity class of ports.

Kernel-check:

1. crossing involutive;
2. crossing changes region;
3. labels preserved;
4. local pairings perfect;
5. transitionStep^[3] p = p;
6. transitionStep p != p;
7. transitionStep^[2] p != p;
8. transitionXor p 3 = deltaA != 0.

This is the explicit counterexample proving local closed-network conditions do
not force global XOR compatibility.

## I. Even-cycle positive calibration

Retain / adapt the existing two-region A A fixture.

Show its primitive period is 2 and:

transitionXor p 2 = 0.

This provides the positive comparison:

- period 2 -> compatible;
- period 3 -> obstructed.

## J. Global obstruction predicate

Optionally define a network-level property:

def CycleXorCompatible (N : ClosedBoundaryNetwork) : Prop :=
  forall p n,
    PrimitiveTransitionReturn N p n ->
    transitionXor N p n = 0

Then prove the equivalent parity reading:

CycleXorCompatible N
<->
every primitive transition return has even length.

If the quantification over duplicate points/orbits makes the theorem verbose,
the pointwise primitive theorem is sufficient and the network-level wrapper
may be deferred.

## K. Interpretation boundary

The result should be stated precisely:

Local conservation and same-label perfect pairing determine a finite
degree-two transition system, but they do not eliminate global holonomy.

The remaining obstruction is:

odd primitive transition orbit
<-> nonzero accumulated XOR
<-> failure to return to the same transported state.

Do not claim that planar geometry necessarily permits such odd transition
orbits. Planarity/non-crossing structure has not yet been added.

This distinction is important: a later planar theorem may rule out some
abstract counterexamples.

## L. Computability

Keep:

- transitionXor;
- transportState;
- explicit example networks

computable.

Primitive-period existence proofs may use standard classical/minimality
reasoning if necessary, but avoid a noncomputable solver-facing definition.

No:

- sorry;
- admit;
- unsafe;
- new axiom.

## M. Regression audit

Audit at least:

1. transitionXor n equals n repeated copies of the preserved label;
2. nonzero repeated label sums to zero iff n even;
3. two-region fixture: primitive period 2, XOR zero;
4. three-region fixture: primitive period 3, XOR deltaA != zero;
5. transport returns to base on the even cycle;
6. transport fails to return to base on the odd cycle;
7. primitive-cycle compatibility iff even primitive period.

## N. Proposed modules

Production:

DkMath/Tromino/TransitionXor.lean

Audit:

DkMathTest/Tromino/TransitionXorAxiomAudit.lean

Keep TransitionGraph.lean unchanged unless a tiny iteration helper clearly
belongs there.

## O. Validation

Run focused builds for:

- DkMath.Tromino.TransitionGraph
- DkMath.Tromino.TransitionXor
- DkMathTest/Tromino/TransitionXorAxiomAudit

Run git diff --check.

Audit substantive theorems with #print axioms.

Scan for:

- sorry
- admit
- unsafe
- new axiom
- unintended noncomputable

## P. Report

Create:

docs/dev/Tromino-ExchangeCalculus-260924-v0/report-013.md

Record:

- transitionXor convention;
- repeated-label theorem;
- characteristic-two parity theorem;
- primitive return representation;
- primitive-period API choice;
- primitive cycle compatibility theorem;
- two-region even calibration;
- three-region odd counterexample;
- transportState results;
- exact research conclusion and its scope;
- computability / axiom audit.

## Stop condition

Stop once the global obstruction is kernel-checked:

for a primitive closed transition orbit with nonzero preserved boundary label,

cycle XOR = 0
iff
primitive orbit length is even.

Include an explicit primitive odd-cycle counterexample.

Do not proceed to open residual paths, ghost completion, planar noncrossing
constraints, physical boundary extraction, arbitrary path independence,
BoundaryIR, optimization, or Four Color claims without review.
