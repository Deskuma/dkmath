# Gnomon Inversion / Projection Roadmap 260914 v0

## Campaign question

Can the square-growth law itself be promoted to a neutral DkMath arithmetic layer and then used to restate the Legendre square shell as a gnomon-interior problem, exposing a real preservation/projection theorem rather than another cover-count rewrite?

## GNIP-000 — neutral gnomon algebra recovery

Status: NEXT

Target production:

```text
DkMath/Gnomon/Algebra.lean
DkMath/Gnomon.lean
```

Required content:

```text
oddGnomon n = 2*n+1
squareGnomonBand x u = u*(2*x+u)
petalMul a b = 2*a*b+a+b
```

Required theorem families:

```text
basic oddGnomon laws
petalMul unit/comm/assoc and multiplicative transport
x^2 + oddGnomon x = (x+1)^2
x^2 + squareGnomonBand x u = (x+u)^2
squareGnomonBand x 1 = oddGnomon x
squareGnomonBand composition under u+v
squareGnomonBand as shifted sum of unit odd gnomons
sum of odd gnomons reconstructs a square
```

The layer must be independent of Collatz, Legendre, GN, Pascal, and Polyomino.

## GNIP-001 — Cosmic degree-two bridge

Status: PLANNED

Expected target:

```text
DkMath/Gnomon/CosmicBridge.lean
```

Expected exact identities:

```text
oddGnomon n = GTail 2 1 1 n
squareGnomonBand x u = u * GTail 2 1 u x
```

This phase fixes the production orientation explicitly and prevents the recurring `(x,u)` reversal ambiguity.

## GNIP-002 — Collatz compatibility refactor

Status: PLANNED

`DkMath.Collatz.GnomonEvaluation` keeps all public names.  Its pure square-gnomon definitions/theorems should become aliases or short bridges to `DkMath.Gnomon.Algebra`.

Collatz-specific objects remain application-owned:

```text
RawGnomonStep
RawGnomonHeight
RawGnomonResidualShape
pow2 alignment
accelerated map bridge
```

## GNIP-003 — Legendre open-gnomon bridge

Status: PLANNED

Expected theorem:

```text
SquareOffset n r <-> 1 <= r and r < oddGnomon n
```

and an equivalent restatement of the square cell / Legendre frontier in neutral gnomon vocabulary.

Important boundary:

```text
r = oddGnomon n
```

is not a Legendre interior seat; it is the next square itself.

## GNIP-004 — inversion/projection audit at the 30 -> 31 boundary

Status: CONDITIONAL / AUDIT-FIRST

Use the stabilized generic API to inspect the concrete boundary where the bounded prime basis gains the fresh prime `31`.

Relevant existing facts include:

```text
CosmicSquareScaling at y=30
primeScalesUpTo
SquareOffset / SquareOffsetCovered
MultiGauge successor increment bridge
```

Questions:

```text
1. What part of a covered square-shell pattern transports from n to n+1?
2. Which part is invariant under unit-thickness square growth?
3. What exactly changes when primeScalesUpTo n gains a fresh prime?
4. Can full cover at the new gnomon interior be reduced to support that must enter through the new channel?
5. Does this produce a genuinely stronger theorem than existing tied-pair/local cover rewrites?
```

Outcome policy:

```text
A — NONTRIVIAL PROJECTION LAW FOUND
    Add the smallest production theorem exposing it, then return to Legendre.

B — ONLY REWRITE / NORMALIZATION
    Record the exact normal form and stop; do not manufacture a preservation theorem.

C — COUNTEREXAMPLE TO THE PROPOSED PRESERVATION READING
    Kernel-check the counterexample and return to Legendre with the model corrected.
```

## Scope after this branch

If GNIP-004 closes, this branch should merge to `develop`.  The next work returns to the owning application branch:

```text
Legendre -> use the gnomon-interior/projection result
ABC      -> later consume the resulting structural arithmetic if useful
```

The wider 2026-07-30 Gnomon/Petal/Pascal/Polyomino roadmap remains separate and can continue later.
