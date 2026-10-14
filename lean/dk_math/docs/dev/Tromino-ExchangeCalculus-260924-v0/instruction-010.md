
# TRM-011 — Boundary signature / XOR conservation kernel

## Goal

Start the boundary-flow layer without introducing graph infrastructure.

The key repository-level observation is that the existing piece-exchange
quantity

forbiddenDelta contact = contact.inside + contact.outside

is exactly the characteristic-two boundary difference label that the older
BoundaryFlow plan called the XOR crossing label.

TRM-011 should make that identification explicit and build the first finite,
ordered boundary signature on top of it.

The central target theorem is the parity conservation law:

boundary XOR sum = 0
iff
the three nonzero delta labels occur with the same parity.

Do not implement pairings, TransitionGraph, path transport, planar embedding,
BoundaryIR, physical flattening, residual optimization, or Four Color claims
in this checkpoint.

## Dependency boundary

Reuse:

- DkMath.Tromino.State
- DkMath.Tromino.Exchange
- DkMath.Tromino.PieceExchange

In particular reuse:

- BoundaryContact
- forbiddenDelta
- forbiddenDelta_eq_zero_iff

Do not introduce a second competing boundary-difference definition unless it
is a thin alias with a clear theorem identifying it with forbiddenDelta.

Do not import RecursiveCosmicBridge. Boundary conservation is structural, not
a consequence of the mass calibration.

## Proposed production module

DkMath/Tromino/BoundarySignature.lean

Audit:

DkMathTest/Tromino/BoundarySignatureAxiomAudit.lean

## A. Bridge: forbidden delta = boundary crossing delta

Document and expose the interpretation:

For a contact c,

delta(c) = c.inside + c.outside.

This is simultaneously:

1. the unique uniform exchange that would make the contact conflict;
2. the state difference across the contact in the additive Klein four-group.

A thin alias such as:

contactDelta : BoundaryContact -> TrominoState := forbiddenDelta

is acceptable if it improves readability.

Required theorem:

contactDelta c = 0 <-> c.inside = c.outside.

And therefore:

c.inside != c.outside -> contactDelta c != 0.

Prefer reusing forbiddenDelta_eq_zero_iff rather than reproving additive
algebra.

## B. Three canonical nonzero directions

Introduce algebraic names for the three nonzero elements of TrominoState.

Do not use color names.

Suggested names:

deltaA := (1,0)
deltaB := (0,1)
deltaC := (1,1)

or directionX / directionY / directionXY if that fits repository naming
better.

Prove:

- each is nonzero;
- they are pairwise distinct;
- deltaA + deltaB = deltaC and cyclic variants;
- deltaA + deltaB + deltaC = 0;
- every nonzero TrominoState equals exactly one of deltaA/deltaB/deltaC.

The final characterization should be reusable by the parity proof.

Avoid defining a second four-state carrier.

## C. Ordered finite BoundarySignature

Use a finite indexed representation so multiplicity is retained.

Preferred representation:

structure BoundarySignature where
  arity : Nat
  contact : Fin arity -> BoundaryContact
  proper : forall i, (contact i).inside != (contact i).outside

The Fin index supplies a stable finite order that may later be interpreted as
cyclic order. Do not yet define non-crossing planarity.

Equivalent sigma/subtype designs are acceptable if they preserve:

- individual port identity;
- multiplicity;
- deterministic finite enumeration;
- computability.

Do not use Finset BoundaryContact as the primary representation because equal
contacts must be allowed to occur at multiple boundary ports.

## D. Boundary delta labels

Define:

boundaryDelta S i := contactDelta (S.contact i)

and prove:

boundaryDelta S i != 0.

Then prove the three-way classification:

boundaryDelta S i = deltaA
or boundaryDelta S i = deltaB
or boundaryDelta S i = deltaC.

If useful, expose a small finite nonzero-direction type later, but do not
introduce one unless it materially simplifies counting.

## E. XOR / additive boundary sum

Define the total boundary flow:

boundarySum S :=
  sum i : Fin S.arity, boundaryDelta S i

using Finset.univ.

Define:

BoundaryConserved S : Prop := boundarySum S = 0.

This is the local XOR conservation predicate.

Required basic laws:

- empty signature is conserved;
- concatenation/append law may be deferred unless the representation makes it
  trivial;
- exchange/color names are absent from this API.

## F. Label multiplicities

Define:

boundaryLabelCount S delta :=
  card {i | boundaryDelta S i = delta}.

Provide simp-friendly membership/count facts where useful.

Required facts:

- count zero = 0 for a proper BoundarySignature;
- the three nonzero counts sum to S.arity.

The latter may be stated:

countA + countB + countC = arity.

Do not collapse repeated ports: multiplicity is essential here.

## G. Coordinate parity formulas

Because TrominoState = ZMod 2 × ZMod 2, first prove the two coordinate
formulas for boundarySum.

Mathematical target:

first coordinate of boundarySum
  = (countA + countC : ZMod 2)

second coordinate of boundarySum
  = (countB + countC : ZMod 2).

The exact Lean statement may cast Nat counts into ZMod 2.

This is the clean bridge between finite multiplicity and XOR conservation.

Prefer a finite-sum/count argument over enumeration of all possible
signatures.

Enumeration of the three label values inside a per-port lemma is acceptable.

## H. Main parity theorem

Prove the central theorem in Nat parity form.

Preferred statement:

BoundaryConserved S
<->
  boundaryLabelCount S deltaA % 2 =
    boundaryLabelCount S deltaC % 2
  and
  boundaryLabelCount S deltaB % 2 =
    boundaryLabelCount S deltaC % 2.

Also expose a user-facing equivalent saying:

countA % 2 = countB % 2
and
countB % 2 = countC % 2

or an explicit three-way equality if cleaner.

The semantic statement is:

n_A ≡ n_B ≡ n_C (mod 2).

This is the main theorem of TRM-011.

## I. Even / odd dichotomy

Derive:

If BoundaryConserved S, then exactly one of the following parity classes holds:

1. all three counts are even;
2. all three counts are odd.

A theorem returning the disjunction is sufficient.

Do not implement the pairing theorem yet.

This dichotomy is the input for the next checkpoint:

- even -> complete same-label pairing;
- odd -> pairs plus one A/B/C residual.

## J. Relation to piece rescue

Expose a theorem/comment clarifying the dual use of contactDelta:

- as a member of forbiddenExchangeSet in PieceExchange;
- as a multiplicity-preserving boundary-flow label in BoundarySignature.

Do not replace forbiddenExchangeSet with boundary counts.

They have different semantics:

- forbiddenExchangeSet is a Finset image and intentionally forgets duplicate
  contacts;
- BoundarySignature counts every boundary port and must retain multiplicity.

This distinction must be explicit in docs and theorem naming.

## K. Regression examples

Construct small signatures, preferably in the audit module:

1. empty boundary:
   counts 0/0/0, sum 0, conserved;

2. even example:
   A A B B C C,
   counts 2/2/2,
   sum 0,
   conserved;

3. odd example:
   A A A B B B C C C,
   counts 3/3/3,
   sum 0,
   conserved;

4. invalid example:
   A A B C,
   counts 2/1/1,
   sum != 0,
   not conserved;

5. duplicate-contact observation:
   two identical proper contacts contribute multiplicity 2 to the signature
   count even though forbiddenExchangeSet would contain one distinct delta.

The last regression is important: it checks that the v2 rescue set and v1
boundary-flow multiplicity have not been conflated.

## L. Computability

Keep all signature data and count functions computable.

No noncomputable declaration should be needed.

Use decide/native finite computation in audit examples when convenient, but
prove the general parity theorem symbolically.

## M. Axiom / scope boundary

No:

- sorry;
- admit;
- unsafe;
- new axiom;
- unintended noncomputable.

No graph or planarity claims.

No claim yet that an arbitrary geometric region supplies a conserved
BoundarySignature.

TRM-011 defines the certificate and its algebra once such a signature is
given.

## N. Validation

Run focused builds for:

- DkMath.Tromino.PieceExchange
- DkMath.Tromino.BoundarySignature
- DkMathTest/Tromino/BoundarySignatureAxiomAudit

Run git diff --check.

Audit substantive theorems with #print axioms.

## O. Report

Create:

docs/dev/Tromino-ExchangeCalculus-260924-v0/report-010.md

Record:

- the exact contactDelta bridge;
- names/representation of the three nonzero directions;
- BoundarySignature representation;
- boundarySum;
- multiplicity definitions;
- coordinate parity formulas;
- main conservation/parity theorem;
- even/odd dichotomy;
- distinction between forbiddenExchangeSet and boundary multiplicity;
- regression results;
- computability / axiom audit.

## Stop condition

Stop when the finite ordered boundary certificate satisfies the theorem:

boundarySum = 0
iff
the A/B/C multiplicities have equal parity.

Do not proceed to pairing, transition graphs, XOR path transport, physical
boundary extraction, residual optimization, or Four Color claims without
review.
