# CGE-007 report

## Scope

Implemented the bounded signed CRT pair/triple geometry requested by
`instruction-007.md`.  The attached document was treated as the stage
contract; this implementation remains finite, anchor-local, and combinatorial.
CGE-006 was kept intact.

## Implementation

- Added `DkMath/NumberTheory/Goldbach/BalancedSignedCRTOverlap.lean`.
- Exported it from `DkMath.NumberTheory.Goldbach`.
- Extended `DkMathTest/NumberTheory/GoldbachBalancedReflectionAudit.lean`.

`signedPairResidues` and `signedTripleResidues` are canonical natural
representatives below `p*q` and `p*q*r`, filtered by the existing local
`goldbachForbiddenResidues` predicates.  The membership theorems expose the
requested bounded local-coordinate characterization.  Coprime prime
coordinates give the product-cardinality bounds and hence the nominal limits
`4` and `8`; collapsed signs are deduplicated by the `Finset` representation.
The theorem `signedTripleResidues_center_aligned_eq_singleton` additionally
proves the general center-aligned triple collapse to the existing
`goldbachTripleWitness` residue under explicit prime, distinctness, and
`r ∣ 2*n` hypotheses.

`goldbachProgressionSeats` gives the explicit seats `t₀ + M*k` in a plain
finite interval, with the exact executable count
`if t₀ ≤ w then (w-t₀)/M+1 else 0` for `0 < M`.  The signed pair/triple
counts sum these counts over canonical residues and the corresponding world
sums range over strict unordered pairs and triples.

`goldbach_signed_pair_raw_iff_support` implements the CGE-006 endpoint
firewall: under `w ≤ n`, `P < n-w`, and the finite world bound, raw forbidden
membership is equivalent to proper obstruction support at each coordinate.
The provider-facing theorem keeps the pair and triple comparison hypotheses
explicit and feeds their safe pair-minus-triple budget into the existing
Pascal survivor provider.

## Regressions

The audit kernel-checks the center-aligned target
`n=15`, `w=8`, `S={2,3,5}`:

```text
signed pair residues: {3}, {5}, {0}
signed triple residues: {15} = {goldbachTripleWitness 15 2 3 5}
signed pair sum = 3
signed triple sum = 0
```

It also checks the non-center-aligned mixed-sign world
`n=50`, `w=10`, `S={2,3,5,7}`:

```text
window = 11
pair overlap = 12
triple overlap = 2
pair-minus-triple = 10
signed pair sum = 12
signed triple sum = 2
coarse capacity = 21
21 < 11 + 10 is false
```

The failed strict budget is retained as a firewall; no survivor is asserted
from it.  The target-30 signed budget is separately replayed through the
explicit provider bridge.

## Boundary

The general theorem identifying the signed world sums with the Pascal overlap
counts was not asserted.  The repository contains the exact target-30 and
mixed-sign executable regressions, plus the explicit comparison hypotheses
needed by the provider bridge.  No useful-direction comparison is hidden in
the signed definitions.

No Strong Goldbach theorem, universal survivor/capacity inequality, analytic
density claim, coprime-to-prime shortcut, `sorry`, `admit`, `native_decide`,
`unsafe`, or new axiom was added.

## Verification

Focused build:

```text
lake build DkMath.NumberTheory.Goldbach DkMathTest.NumberTheory.GoldbachBalancedReflectionAudit
```

Result: completed successfully (`8733` jobs).  The audit `#print axioms`
output reports only the repository's existing logical/classical axioms
(`propext`, `Classical.choice`, and `Quot.sound`) for the checked declarations.
