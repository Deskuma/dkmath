# FLT7TC-005R58 — Current common-prime cyclotomic phase transport

## Scope

This report records the implementation of `instruction-064.md`.  The
checkpoint moves to `C > 1` and separates the current common-prime residue
address from the historical `RamifiedSignedRootRoutingPacket` provenance.

The first production target is a neutral degree-six address module.  The
intended exact endpoint is a current residue evaluation with a primitive
seventh-root ratio, followed by a phase-alignment choice among the three
values `1 + tau^k + tau^(-k)` for `k = 1, 2, 3`.

No `C = 1` Thomas work, historical terminal contradiction, `q % 28` claim,
reciprocity theorem, or FLT7 closure is in scope.

## Incremental ledger

| stage | result |
|---|---|
| instruction/source/API inspection | complete |
| report scaffold | complete |
| neutral address and degree-six evaluation | complete |
| current common-prime constructor | pending |
| phase/Galois transport audit | phase index complete; Galois transport remains separate |
| scratch checks and focused build | complete |
| warning/axiom audit | complete for new declarations |

## Implemented production surface

Added `SevenRealCubicCurrentCyclotomicAddress.lean` with the neutral
`CurrentMuSevenResidueAddress q` packet.  It packages the prime field
evaluation, a nontrivial seventh-root ratio, the real trace formula, and the
degree-six carrier evaluation.  The carrier-side map, surjectivity, maximal
kernel, contraction to the real cubic order, and conjugate-address formulas
are kernel-checked without importing the historical signed-root packet.

Added `SevenRealCubicCurrentCyclotomicPhase.lean`.  Its `currentBeta r n`
uses the field value of `r`, and the implementation proves the geometric sum,
the cubic factorization for phases `n = 1, 2, 3`, and
`current_phase_alignment`, which returns an explicit `Fin 3` phase index.
`CurrentMuSevenResidueAddress.phase_alignment` applies that result directly
to the current address.  No normalization to phase `1` is made.

The public `DkMath.FLT.Seven` facade now imports both new modules.

## Verification ledger

The following single-process checks passed:

```text
lake build DkMath.FLT.Seven.SevenRealCubicCurrentCyclotomicAddress
lake build DkMath.FLT.Seven.SevenRealCubicCurrentCyclotomicPhase
lake env lean docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/scratch-064-phase.lean
```

The scratch file checks both the generic phase theorem and the address-level
wrapper.  Its axiom print is `[propext, Classical.choice, Quot.sound]` for
each new phase theorem; no `sorry`, `admit`, `unsafe`, or `native_decide`
occurs in the new production or scratch files.

The existing current common-prime residue theorem was inspected as the
source of the local `f` and quotient-zero equation.  This checkpoint adds the
neutral phase/address layer and does not claim the later current packet
constructor, Galois transport, fourteen-power transport, cyclic product, or
FLT closure.

## Boundary

The tempting product argument for three local fourteenth-power relations is
not used before the prime and coefficient transport maps are made explicit.
The final outcome will distinguish a genuine strengthened congruence from a
collapse to one oriented residue class.
