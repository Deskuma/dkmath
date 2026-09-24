
# TRM-005 — Uniform piece exchange / boundary forbidden deltas

## Goal

Lift the state-only rescue calculus to a finite local piece boundary model.

This checkpoint should prove the first piece-level theorem from the v2 plan:

> one boundary contact forbids exactly one exchange delta.

Then collect those deltas over finitely many contacts and prove:

> if the resulting forbiddenExchangeSet is not the whole four-state carrier,
> one uniform exchange makes every recorded boundary contact compatible.

If the current placement already has a conflict, the rescuing exchange is
nonzero.

Keep this checkpoint algebraic. Do not introduce planar geometry, MacroCell,
BoundaryIR, graph traversal, optimization, or Four Color claims.

## Existing owners

Reuse:

- DkMath.Tromino.State
- DkMath.Tromino.Exchange
- DkMath.Tromino.ExchangeRescue

Do not import CosmicBridge or Restoration unless required by a concrete theorem.
The piece-boundary algebra should remain independent.

## Proposed production modules

Preferred:

- DkMath/Tromino/PieceExchange.lean

Optional split only if the file becomes too broad:

- DkMath/Tromino/BoundaryContact.lean

Audit:

- DkMathTest/Tromino/PieceExchangeAxiomAudit.lean

## A. Uniform exchange on an indexed coloring

For an arbitrary index type I and coloring

c : I -> TrominoState

define the uniform exchange

uniformExchange delta c i := exchange delta (c i).

Do not require a geometric Shape yet.

Prove the pointwise invariance of equality / inequality:

uniformExchange delta c i = uniformExchange delta c j
  <-> c i = c j

and therefore

uniformExchange delta c i != uniformExchange delta c j
  <-> c i != c j.

Prefer using exchangeEquiv/injectivity rather than characteristic-two
casework.

If useful, expose a generic properness predicate over an arbitrary adjacency
relation and prove uniform exchange preserves it. Keep such a predicate small
and local; do not build graph infrastructure.

## B. BoundaryContact

Introduce the smallest record carrying one inside/outside state contact.

Suggested semantic shape:

structure BoundaryContact where
  inside  : TrominoState
  outside : TrominoState

No geometric position is needed in this checkpoint.

A contact conflicts after delta exactly when

exchange delta contact.inside = contact.outside.

## C. Unique forbidden delta of one contact

Define the unique forbidden delta of a contact.

Mathematically:

forbiddenDelta(contact) = contact.inside + contact.outside.

Prove the exact iff:

exchange delta contact.inside = contact.outside
  <-> delta = forbiddenDelta contact

(or the symmetric equality orientation if it simplifies rewriting).

This theorem should reuse existsUnique_exchange_to or direct additive
cancellation; do not enumerate states.

Also expose uniqueness explicitly if useful:

existsUnique_forbiddenDelta.

## D. Current conflict and zero delta

Prove:

forbiddenDelta contact = 0
  <-> contact.inside = contact.outside.

Equivalently:

the current placement (delta = 0) conflicts at a contact
  <-> zero is its forbidden delta.

This is needed for the later nonzero-rescue theorem.

## E. Finite forbiddenExchangeSet

For contacts : Finset BoundaryContact, define:

forbiddenExchangeSet contacts

as the image of forbiddenDelta.

Provide a simp-friendly membership theorem:

delta in forbiddenExchangeSet contacts
<->
exists contact in contacts, forbiddenDelta contact = delta.

Use Finset.image unless repository evidence suggests a cleaner owner API.

## F. Boundary compatibility

Define:

boundaryCompatible delta contacts

to mean every recorded contact avoids equality after uniform exchange.

Semantic form:

forall contact in contacts,
  exchange delta contact.inside != contact.outside.

Prove the central equivalence:

boundaryCompatible delta contacts
  <-> delta notin forbiddenExchangeSet contacts.

This theorem is the bridge from local contact equations to the finite forbidden
delta set.

## G. Piece-level rescue

Main theorem:

forbiddenExchangeSet contacts != Finset.univ
->
exists delta, boundaryCompatible delta contacts.

Do not assume that the forbidden set is non-full universally. The condition is
part of the theorem.

Prefer reusing the finite four-state rescue machinery if it gives a clean
proof. A direct finite-set complement argument is also acceptable if it avoids
semantic abuse of availableExchanges.

## H. Nonzero piece-level rescue

Define current conflict either as:

not boundaryCompatible 0 contacts

or via an existential conflicting contact.

Prove:

not boundaryCompatible 0 contacts
->
forbiddenExchangeSet contacts != Finset.univ
->
exists delta, delta != 0 and boundaryCompatible delta contacts.

The proof should use that zero is forbidden when the current placement
conflicts.

## I. Exact forbidden/contact observations

Useful corollaries:

- one contact produces a singleton forbiddenExchangeSet;
- no contacts produce the empty forbiddenExchangeSet;
- if forbiddenExchangeSet.card = 3, exactly one delta is compatible;
- if forbiddenExchangeSet = univ, no delta is compatible.

For the cardinality-three theorem, reuse TRM-004 if practical.

Do not claim that four contacts necessarily forbid four different deltas.

## J. Regression cases

Include finite state-only examples:

1. no contacts -> all 4 deltas compatible;
2. one conflicting contact -> zero forbidden, 3 compatible;
3. two contacts with the same forbidden delta -> still only one delta forbidden;
4. three distinct forbidden deltas -> unique compatible delta;
5. all four forbidden deltas represented -> no compatible delta.

These examples may use explicit TrominoState values if needed in the test file,
but production declarations remain color-name-free.

## K. Interpretation boundary

This checkpoint proves:

- uniform exchange preserves internal equality/distinctness;
- each boundary contact forbids exactly one delta;
- finite contacts induce a forbidden delta set;
- non-full forbidden delta set gives a uniform piece rescue.

It does not yet prove:

- the contacts arise from an actual planar Shape boundary;
- the contact set of every Tromino piece is non-full;
- a MacroCell boundary has the same signature under recursion;
- additive rescue alone always solves a coloring instance.

Those remain later questions.

## L. Validation

Run focused builds for every new/changed module, at minimum:

- DkMath.Tromino.Exchange
- DkMath.Tromino.ExchangeRescue
- DkMath.Tromino.PieceExchange
- DkMathTest.Tromino.PieceExchangeAxiomAudit

Run git diff --check.

Audit substantive public theorems with #print axioms.

Scan new/changed files for:

- sorry
- admit
- unsafe
- new axiom declarations

## M. Report

Create:

docs/dev/Tromino-ExchangeCalculus-260924-v0/report-004.md

Record:

- the indexed uniformExchange representation;
- BoundaryContact representation;
- forbiddenDelta formula and iff theorem;
- forbiddenExchangeSet definition;
- boundaryCompatible definition;
- rescue / nonzero-rescue theorem surfaces;
- regression results;
- build / axiom audit;
- any Finset-image or DecidableEq issue.

## Stop condition

Stop after piece-level uniform exchange rescue is kernel-checked.

Do not proceed to planar geometry, MacroCell, BoundaryIR, transition graphs,
residual optimization, or Four Color claims without review.
