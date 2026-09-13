# CGE-006 report

## Scope

Implemented the bounded CRT witness layer requested by `instruction-006.md`.
The implementation stays at finite pair/triple accounting and does not add a
universal survivor provider or a Strong Goldbach theorem.

## Files

- Added `DkMath/NumberTheory/Goldbach/BalancedCRTOverlap.lean`.
- Updated `DkMath/NumberTheory/Goldbach.lean` to export the module.
- Extended `DkMathTest/NumberTheory/GoldbachBalancedReflectionAudit.lean`.

## Pair provider

`goldbachLeftPairWitness n p q` is defined as

```text
n % (p * q)
```

`goldbachLeftPairWitness_dvd_left` proves simultaneous divisibility of
`n - witness` by `p` and `q` from prime hypotheses.  The eligible finite set
`goldbachWindowEligibleLeftPairs n w S` filters `S × S` by strict order and
balanced-window membership of the canonical witness.

`goldbachWindowEligibleLeftPair_support` supplies both proper obstruction
members under `KnownPrimeScales S`, an explicit world upper bound, `w ≤ n`, and
the anchor condition `P < n - w`.  The endpoint inequalities are closed
explicitly; no proper-divisor exception is discarded.

`goldbachWindowPairLower` is the cardinality of this eligible set, and
`goldbachWindowPairLower_le_pairOverlap` injects each eligible pair into the
corresponding two-element support subset.  Thus the lower bound is a finite
CRT witness payment, not an equality claim for general worlds.

## Center-aligned triple control

`GoldbachCenterAlignedWorld n S` is exactly

```text
∀ r ∈ S, r ∣ 2 * n
```

`goldbachCenterAlignedWorld_forbiddenResidues` reuses
`goldbachForbiddenResidues`, `goldbach_residue_eq_neg_iff`, and the
one-class collapse.  `goldbach_center_aligned_obstruction_left` converts a
proper raw obstruction back to left divisibility under the required offset
bound.

Strict triples are represented by `goldbachPrimeTriples S`, with
`p < q < r`.  The canonical triple witness is
`goldbachTripleWitness n p q r = n % (p*q*r)`, and
`goldbachTripleWitness_center_aligned_progression` proves the product
divisibility of `n - t` for a center-aligned triple of proper support
obstructions.  The executable progression estimate is
`goldbachTripleCRTUpper`; its finite sum is
`goldbachTripleCRTUpperSum`.

The general signed eight-class CRT hierarchy remains outside this checkpoint.
The triple API is intentionally center-aligned and finite.

## Target-30 replay

For `n=15`, `w=8`, `P=5`, and `S=primeScalesUpTo 5 = {2,3,5}`, the audit
kernel-checks:

```text
t(2,3) = 3,  t(2,5) = 5,  t(3,5) = 0
PairLower = 3
TripleWitness(2,3,5) = 15 > 8
TripleUpper = 0
Window = 9, Capacity = 10
10 < 9 + (PairLower - TripleUpper)
```

It also replays `PairLower ≤ PairOverlap`, the target equality
`PairLower = PairOverlap = 3`, and
`TripleUpper = TripleOverlap = 0`.  The existing CGE-005 provider therefore
continues to close the target-30 conditional `GoldbachPairAt 15` replay.

## Firewalls and non-goals

- Witnesses outside the balanced window are excluded from `PairLower`.
- The pair lower bound is not asserted to equal pair overlap in general.
- Triple collapse is stated only under `GoldbachCenterAlignedWorld`.
- Strict ordering excludes repeated triple coordinates.
- Prime membership is supplied by `KnownPrimeScales`; no coprime-to-prime
  shortcut is introduced.
- No universal `PairLower`/`TripleUpper` theorem, universal survivor provider,
  Strong Goldbach, RH/CFBRC, AKS, `sorry`, `admit`, `native_decide`, `unsafe`,
  or new `axiom` was added.

## Verification

Focused build:

```text
lake build DkMath.NumberTheory.Goldbach DkMathTest.NumberTheory.GoldbachBalancedReflectionAudit
```

The focused build completed successfully.  The audit `#print axioms` output
contains only the existing logical/classical axioms (`propext`,
`Classical.choice`, and `Quot.sound`) and no `sorryAx`.

The forbidden-construct search over the added module and extended audit found
no forbidden implementation construct, and `git diff --check` passed.

## Outcome

**Outcome A — CRT OVERLAP PAYMENT PROVIDER.**

The canonical pair lower bound and center-aligned triple progression payment
are production APIs, and target-30 reproduces the CGE-005 budget without
directly assuming the external pair/triple overlap values.  The result remains
finite and anchor-local as required.
