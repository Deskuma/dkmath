
# TRM-015 — Label-only boundary flow certificate / contact erasure

## Goal

Separate the boundary-flow certificate from the already-known inside/outside
states stored in BoundaryContact.

Current direction:

BoundaryContact
  -> contactDelta = inside + outside
  -> BoundarySignature
  -> pairing / transition / XOR.

This is excellent for analysing an existing coloring, but it is not yet an
independent certificate from which colors can later be reconstructed, because
BoundarySignature already stores the inside/outside states.

TRM-015 should introduce the label-only boundary carrier:

arity + one nonzero TrominoState delta per port,

and prove that the conservation/parity kernel depends only on this erased
label data.

Do not yet refactor BoundaryPairing / TransitionGraph / TransitionXor onto the
new carrier. That migration is a later checkpoint.

Do not implement color recovery, open residual paths, ghost completion,
planarity, BoundaryIR, optimization, or Four Color claims.

## Existing owners

Reuse:

- DkMath.Tromino.State
- deltaA / deltaB / deltaC
- BoundaryContact
- BoundarySignature
- boundaryDelta
- BoundaryConserved
- boundaryLabelCount
- boundaryConserved_iff_parity
- boundaryConserved_even_or_odd

Preserve all current public APIs used by TRM-012 through TRM-014.

This checkpoint must be additive / compatibility-preserving.

## A. New label-only carrier

Preferred module:

DkMath/Tromino/FlowSignature.lean

Define:

structure FlowSignature where
  arity : Nat
  label : Fin arity -> TrominoState
  nonzero : forall i, label i != 0

The carrier must:

- preserve port identity;
- preserve multiplicity;
- remain finite and computable;
- contain no BoundaryContact;
- contain no inside/outside state.

Do not use color names.

## B. Contact erasure

Define a projection:

BoundarySignature.toFlowSignature : BoundarySignature -> FlowSignature

with:

arity := S.arity
label := boundaryDelta S
nonzero := boundaryDelta_ne_zero S.

Required exact simp/bridge theorems:

- erased arity = original arity;
- erased label i = boundaryDelta S i.

The projection must be computable.

## C. Flow label count and sum

On FlowSignature define independent observers:

flowSum F :=
  sum i : Fin F.arity, F.label i

FlowConserved F := flowSum F = 0

flowLabelCount F delta :=
  card {i | F.label i = delta}.

Prove:

- flowLabelCount F 0 = 0;
- countA + countB + countC = F.arity;
- every label is A or B or C.

Reuse existing nonzero-state classification.

Do not define these as aliases to BoundarySignature functions; the point is
that they work with label-only data.

## D. Generic coordinate parity formulas

Prove the label-only forms:

(flowSum F).1
  = (flowLabelCount F deltaA + flowLabelCount F deltaC : ZMod 2)

(flowSum F).2
  = (flowLabelCount F deltaB + flowLabelCount F deltaC : ZMod 2).

Use the existing proof pattern from BoundarySignature if helpful.

Avoid proof duplication where a small generic finite-label helper can be
factored cleanly.

Do not perform a broad refactor just to remove a few duplicated lines.

## E. Main label-only conservation theorem

Prove:

FlowConserved F
<->
  flowLabelCount F deltaA % 2 = flowLabelCount F deltaC % 2
  and
  flowLabelCount F deltaB % 2 = flowLabelCount F deltaC % 2.

Also derive the even/odd dichotomy:

FlowConserved F ->
  all three counts even
  or
  all three counts odd.

This is the true boundary-flow theorem independent of any prior coloring.

## F. Exact erasure calibration

For every S : BoundarySignature, prove:

flowSum S.toFlowSignature = boundarySum S

FlowConserved S.toFlowSignature <-> BoundaryConserved S

flowLabelCount S.toFlowSignature delta
  = boundaryLabelCount S delta.

Then prove the existing boundary parity theorem is reproduced by the
label-only theorem.

Preferred result:

the original contact-based API remains valid, while its mathematical content
factors through the erasure:

BoundarySignature
  -> FlowSignature
  -> parity/conservation theorem.

Do not delete or rename existing theorems.

## G. Information-loss theorem / observation

Make the information boundary explicit.

The erasure forgets inside/outside absolute states and retains only their
difference.

At minimum document this in the module/report.

If a clean theorem is easy, show that different BoundaryContacts can have the
same contactDelta.

For example, for any x and nonzero delta:

inside = x, outside = x + delta

all erase to label delta.

Do not attempt to prove a full quotient characterization yet.

## H. Gauge / translation invariance calibration

There is a natural sanity check:

simultaneously exchange both sides of a contact by the same gamma.

Define only if small and clean:

exchangeBoundaryContact gamma c

with:

inside  := exchange gamma c.inside
outside := exchange gamma c.outside.

Prove:

contactDelta (exchangeBoundaryContact gamma c) = contactDelta c.

This expresses that boundary delta is invariant under global state
translation.

If introducing this definition belongs better in PieceExchange, either:

- put a tiny helper there, or
- keep it locally in FlowSignature.

Do not start a general gauge-theory API.

This theorem strongly supports the interpretation that FlowSignature contains
relative information while absolute color origin is forgotten.

## I. FlowSignature constructors for tests

Provide small computable constructors or audit fixtures for:

- empty;
- A A B B C C;
- A A A B B B C C C;
- A A B C.

Check the same conserved/nonconserved results as TRM-011 without any
BoundaryContact values.

This is essential: it demonstrates that the parity theorem no longer relies
on pre-existing colors.

## J. BoundarySignature regression compatibility

In the audit module construct at least one contact-based signature, erase it,
and verify:

- labels coincide;
- counts coincide;
- conserved predicate coincides.

Keep duplicate-port multiplicity.

## K. No premature migration

Do not change:

- BoundaryPairing;
- TransitionGraph;
- TransitionXor

to consume FlowSignature yet.

Why:

TRM-015 first validates the independent label-only core and preserves the
current CI-green contact-based stack.

A later reviewed checkpoint can migrate pairing/transition to a generic or
label-only carrier with compatibility adapters.

## L. Research interpretation

Record clearly:

TRM-014 showed the global zero-holonomy obstruction.

TRM-015 separates the data needed to state that obstruction from the original
absolute states.

The future direction then becomes logically non-circular:

label-only flow
  -> pairing
  -> transition network
  -> zero-holonomy
  -> potential/state reconstruction.

Do not claim that the reconstruction theorem exists yet.

## M. Computability / forbidden constructs

All production data definitions should remain computable.

No:

- sorry;
- admit;
- unsafe;
- new axiom;
- unintended noncomputable.

## N. Proposed files

Production:

DkMath/Tromino/FlowSignature.lean

Audit:

DkMathTest/Tromino/FlowSignatureAxiomAudit.lean

Report:

docs/dev/Tromino-ExchangeCalculus-260924-v0/report-014.md

## O. Validation

Run focused builds for:

- DkMath.Tromino.BoundarySignature
- DkMath.Tromino.FlowSignature
- DkMathTest/Tromino/FlowSignatureAxiomAudit
- and a regression build of BoundaryPairing / TransitionGraph / TransitionXor
  if any shared helper file changes.

Run git diff --check.

Audit substantive public theorems with #print axioms.

## P. Report contents

Record:

- FlowSignature representation;
- BoundarySignature erasure API;
- independent flowSum / counts;
- label-only parity theorem;
- exact erasure calibration;
- gauge/translation-invariance result if implemented;
- information-loss interpretation;
- computability and axiom audit;
- confirmation that TRM-012/013/014 APIs were not migrated yet;
- recommended migration strategy for the next checkpoint.

## Stop condition

Stop once the conservation/parity kernel is independently expressible and
kernel-checked using only nonzero boundary delta labels, with no inside/outside
state data.

Do not proceed to pairing/transition migration, color recovery, open paths,
ghost completion, planarity, BoundaryIR, optimization, or Four Color claims
without review.
