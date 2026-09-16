# CGE-005 report

## Scope

Implemented the balanced-window Pascal pair/triple overlap layer requested by
`instruction-005.md`.  The new module is a lightweight wrapper over the
CGE-004 generic obstruction support and supplies a safe pair-minus-triple
lower bound for first-overlap excess.

## Files

- Added `DkMath/NumberTheory/Goldbach/BalancedPascalOverlap.lean`.
- Updated `DkMath/NumberTheory/Goldbach.lean` to export the module.
- Extended `DkMathTest/NumberTheory/GoldbachBalancedReflectionAudit.lean` with
  pair/triple arithmetic and target-30 regressions.

## Production theorem list

- `choose_two_le_sub_one_add_choose_three`
- `goldbachWindowLocalPairMultiplicity`
- `goldbachWindowLocalTripleMultiplicity`
- `goldbachWindowPairOverlapCount`
- `goldbachWindowTripleOverlapCount`
- `goldbachWindowLocalPairMultiplicity_le_overlap_add_triple`
- `goldbachWindowPairOverlapCount_le_overlap_add_triple`
- `goldbachWindowPairOverlap_sub_triple_le_overlap`
- `goldbachWindowSurvivor_of_incidence_le_of_pairMinusTriple_budget`
- `goldbachWindowSurvivor_of_residue_capacity_of_pairMinusTriple_budget`
- `goldbachPairAt_of_goldbachWindow_residue_capacity_of_pairMinusTriple_budget`

## Local Pascal kernel

The pure natural-number theorem is

```text
Nat.choose k 2 ≤ (k - 1) + Nat.choose k 3
```

It is proved by the Pascal recurrence after the finite `k=0,1` boundary
cases.  Applying it to the cardinality of
`goldbachObstructionSupportIn n t S` gives the seat-local inequality

```text
localPair ≤ localOverlapExcess + localTriple
```

Summing over the balanced window gives the arbitrary-finite-world theorem

```text
PairOverlap ≤ OverlapExcess + TripleOverlap
```

and the safe truncated corollary

```text
PairOverlap - TripleOverlap ≤ OverlapExcess
```

No positivity of the truncated difference is asserted.

## Provider connection

The pair-minus-triple bound is passed directly to the CGE-004 supplied
incidence/overlap provider.  A residue-capacity corollary uses the width-local
sum, and an anchor-local corollary accepts `w ≤ n`, `P < n-w`, and
`n+w ≤ squareBody P` before returning `GoldbachPairAt n`.

The interface only consumes the finite strict budget

```text
ResidueCapacity < card Window + (PairOverlap - TripleOverlap)
```

It does not prove that this inequality holds universally, and it does not
assume `GoldbachPairAt n`.

## Target-30 audit

For `n=15`, `w=8`, and `S=primeScalesUpTo 5 = {2,3,5}`, the existing CGE-004
values remain `Window=9`, `Covered=6`, `Incidence=9`, `Overlap=3`, and
`Capacity=10`.  The new kernel-checked values are

```text
PairOverlap   = 3
TripleOverlap = 0
Pair-Triple   = 3
```

Thus the pair-minus-triple payment reproduces the exact overlap in this
regression, and `10 < 9 + 3` supplies the conditional survivor and Goldbach
replays.

## Arithmetic firewalls

The audit checks support size three:

```text
choose 3 2 = 3, choose 3 3 = 1, excess = 2
3 ≤ 2 is false, but 3 ≤ 2 + 1 is true.
```

It also checks support size four:

```text
choose 4 2 = 6, choose 4 3 = 4, excess = 3,
6 - 4 = 2 ≤ 3.
```

Therefore pair-minus-triple is recorded as a lower bound, not as an exact
identity and not as a replacement for the overlap ledger.

## Reuse and non-goals

`BalancedCapacity.lean` supplies the window incidence, support, and exact
first-overlap ledger.  Existing full-fiber `PairOverlap.lean` is not modified
or copied into a window hierarchy.  No CRT lower bound, higher inclusion-
exclusion layer, Strong Goldbach theorem, universal survivor theorem, RH,
CFBRC, AKS, or coprimality shortcut is introduced.

## Verification

Focused build command:

```text
lake build DkMath.NumberTheory.Goldbach DkMathTest.NumberTheory.GoldbachBalancedReflectionAudit
```

The focused build completed successfully with 8731 jobs.  The audit
`#print axioms` output contains only `propext`, `Classical.choice`, and
`Quot.sound`; no `sorryAx` or newly introduced axiom is present.

Facade build:

```text
lake build DkMath
```

The facade build completed successfully with 9854 jobs.  A fresh warning
filter found no warnings other than the repository's excluded
`declaration uses \`sorry\`` category.

The forbidden-construct grep over the added implementation and extended audit
found no `sorry`, `admit`, `native_decide`, `unsafe`, or new `axiom`
declaration.  `git diff --check` also passed.

## Outcome

**Outcome A — PASCAL OVERLAP PAYMENT.**

The pair/triple Pascal layer supplies `PairOverlap - TripleOverlap ≤ E` as a
kernel-checked overlap lower bound and is connected to the CGE-004 provider.
The next exact input needed is a nontrivial pair-overlap lower bound together
with a compatible triple-overlap upper bound from CRT or residue geometry.
