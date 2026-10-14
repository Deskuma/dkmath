
# TRM-004 — Forbidden-state rescue / exchange liberty

## Goal

Promote the four-state exchange kernel into the first certified local rescue
layer.

This checkpoint remains state-only:

- no geometry;
- no boundary contacts;
- no colored piece structure;
- no MacroCell;
- no BoundaryIR;
- no graph search;
- no optimization.

The target is the finite theorem:

forbidden ≠ univ
→ some exchange avoids the forbidden set.

If the current state itself is forbidden, the rescuing exchange can be chosen
nonzero.

Also expose the exact number of legal exchanges:

4 - forbidden.card.

## Existing owners

Reuse:

- DkMath.Tromino.State
- DkMath.Tromino.Exchange
- Mathlib Finset / Equiv APIs

Do not import CosmicBridge or Restoration unless a concrete theorem requires
them. The rescue kernel should stay independent.

## Proposed production module

DkMath/Tromino/ExchangeRescue.lean

Test/audit:

DkMathTest/Tromino/ExchangeRescueAxiomAudit.lean

## A. Complete exchange-to-target theorem

The current API has:

x ≠ y
→ exists unique nonzero delta with exchange delta x = y.

Add the zero-inclusive theorem, preferably in Exchange.lean:

for all x y, there exists a unique delta such that exchange delta x = y.

Suggested semantic shape:

existsUnique_exchange_to (x y : TrominoState) :
  ∃! delta, exchange delta x = y

This should reduce to the same characteristic-two algebra already used by
existsUnique_nonzero_exchange_to.

If clean, define an equivalence/permutation:

exchangeEquiv (x : TrominoState) : TrominoState ≃ TrominoState

whose forward map sends delta to exchange delta x.

This is preferred if it simplifies finite-cardinality transport.

Do not add a custom permutation abstraction if Mathlib Equiv is sufficient.

## B. Available exchanges

For a current state x and forbidden target states B : Finset TrominoState,
define the legal deltas.

Preferred meaning:

availableExchanges x B
  = { delta | exchange delta x ∉ B }.

A direct implementation as a filter over Finset.univ is acceptable.

Also expose the complementary forbidden-delta set only if useful:

forbiddenExchanges x B
  = { delta | exchange delta x ∈ B }.

Avoid duplicate APIs if one definition plus complement lemmas is enough.

## C. Membership theorem

Provide a simp-friendly theorem:

delta ∈ availableExchanges x B
↔ exchange delta x ∉ B.

This should be the main rewriting API for later piece/boundary modules.

## D. Rescue theorem

Main theorem:

B ≠ Finset.univ
→ ∃ delta, delta ∈ availableExchanges x B.

Equivalent formulations are acceptable if the public theorem clearly means:

B ≠ univ
→ ∃ delta, exchange delta x ∉ B.

The proof should use the transitivity/bijectivity of exchange, not case
enumeration over four states.

## E. Nonzero rescue theorem

If the current state is itself forbidden, identity exchange cannot be legal.

Prove:

x ∈ B
→ B ≠ Finset.univ
→ ∃ delta, delta ≠ 0 ∧ delta ∈ availableExchanges x B.

Equivalent target-state wording is acceptable.

This is the first exact theorem matching the "current + three waiting states"
rescue intuition.

## F. Exact candidate count

Prove the exact finite cardinality:

(availableExchanges x B).card = 4 - B.card.

Because exchange by a fixed source is a permutation of the four-state carrier,
the legal-delta set is the inverse image of the complement of B.

Prefer an Equiv/Finset transport proof over exhaustive four-state enumeration.

If the direct statement with Nat subtraction is awkward, an equivalent exact
statement such as:

(availableExchanges x B).card + B.card = 4

is acceptable and may be exposed as the primary theorem, with the subtraction
form as a corollary.

## G. Forced move corollary

Derive the useful special case:

B.card = 3
→ (availableExchanges x B).card = 1.

If Mathlib's singleton-card API is clean, also derive existence/uniqueness of
the legal delta.

Do not force a cumbersome singleton theorem merely for presentation; exact
cardinality one is sufficient for this checkpoint.

## H. Deadlock theorem

Expose the all-forbidden boundary:

B = Finset.univ
→ availableExchanges x B = ∅.

And conversely, if clean:

availableExchanges x B = ∅
↔ B = Finset.univ.

This theorem is important later because "no additive rescue" must become an
explicit obstruction marker, not a theorem failure.

## I. Regression cases

Include small examples covering:

1. B = ∅ gives 4 legal exchanges.
2. B = {x} gives 3 legal exchanges and every legal delta is nonzero.
3. B.card = 3 gives exactly one legal exchange.
4. B = univ gives zero legal exchanges.

Keep examples state-only and color-name-free.

## J. Interpretation boundary

This checkpoint proves only:

- translation in V4 is a permutation;
- proper target states survive exactly when not forbidden;
- non-full forbidden sets admit rescue;
- the exact liberty count is 4 - |B|.

It does not yet prove:

- a boundary contact generates a particular forbidden state;
- a colored piece remains internally proper;
- a piece-level forbiddenExchangeSet is not univ;
- every planar local configuration is rescuable.

Those are TRM-005 / later piece-boundary work.

## K. Validation

Run focused builds for:

- DkMath.Tromino.Exchange
- DkMath.Tromino.ExchangeRescue
- DkMathTest.Tromino.ExchangeRescueAxiomAudit

Run git diff --check.

Audit substantive public theorems with #print axioms.

Scan new/changed files for:

- sorry
- admit
- unsafe
- new axiom declarations

## L. Report

Create:

docs/dev/Tromino-ExchangeCalculus-260924-v0/report-003.md

Record:

- whether exchangeEquiv was introduced;
- the exact availableExchanges definition;
- rescue theorem surface;
- nonzero rescue theorem;
- cardinality theorem form chosen;
- deadlock theorem;
- regression examples;
- build / axiom audit.

## Stop condition

Stop once the state-only forbidden-set rescue calculus is complete.

Do not proceed to colored pieces, boundary contacts, MacroCell, BoundaryIR,
graph, or optimization without review.
