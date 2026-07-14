# cp-318 Implementation Report

## Status

**Completed through the first genuine Stage L obstruction.**

The exact positive-block dichotomy, its saturated arithmetic normal form,
open positive excursions, and a relational finite-transition certificate are
now formalized without `sorry`.  A dedicated finite audit also falsified the
simplest saturated-successor rule.  No universal successor claim was inferred
from the remaining finite pattern.

## 1. Integration closure

`UniversalPaymentBlockNormalForm.lean` now uses the existing unique canonical
block coverage theorem to lift two conditional bounds to every orbit time:

```text
uniform queue bound C
+ uniform canonical-block burst bound D
-> bitWidth (iterateT i n) <= bitWidth n + C + D
```

The theorem is conditional only on the two named uniform bounds.  No extra
coverage assumption is needed because `existsUnique_mem_canonicalPaymentBlock`
already partitions all natural orbit indices.

The endpoint audit also has a canonical-block-facing public theorem:

```text
canonicalBlockNextStartState n k = 1
-> canonicalOutstandingClaimQueue n k = 0
```

## 2. Low/high claim-depth split

New module:

```text
DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPositiveBlock
```

For a canonical block, claim depths are split at terminal valuation `v` into
the finite sets:

```text
low  = {d in claims | d <= v}
high = {d in claims | v < d}
```

Lean proves that they are disjoint and partition all claim depths, with exact
cardinality accounting:

```text
claimCount = low.card + high.card
low.card <= v

endpointAccountingTerm
  = high.card - (v - low.card)       -- in Int
endpointAccountingTerm <= high.card
```

Therefore positive block drift forces a nonempty high-depth claim family.

## 3. High claims enter continuation fibers

Every high claim depth has a unique canonical source.  Its exact-depth theorem
places that source in the continuation fiber at terminal depth `v`.

The implementation constructs the explicit finite injection from high claim
depths into that continuation fiber and proves:

```text
high.card <= (continuationFiber at v).card
```

This is block-local and contribution-preserving.  It does not introduce a
global orbit-time/source-depth identification.

## 4. Exact positive-block dichotomy

`CanonicalSaturatedBorderBlock n k` records exactly:

```text
L = v + 1
claimCount = L
endpointAccountingTerm = 1
```

The main theorem is now proved:

```text
0 < endpointAccountingTerm n k
->
  0 < blockPressureContributionInt n k v
  or CanonicalSaturatedBorderBlock n k
```

The exceptional branch is also characterized bidirectionally:

```text
CanonicalSaturatedBorderBlock n k
<->
  0 < endpointAccountingTerm n k
  and blockPressureContributionInt n k v <= 0
```

In a saturated block, all depths in `Finset.Icc 1 L` are claims.  Thus the
exception is not an unspecified failure case; its finite claim structure is
fully determined.

## 5. Saturated arithmetic normal form

For every saturated block, Lean proves:

```text
terminal valuation = L - 1
endpoint height = L
every block source has upper carry two
every strict interior source has height one
every strict interior step raises bit width by one
net block drift = 1
```

The exact arithmetic normal form is:

```text
x + 1 = 2^L * u
v2 (3^L * u - 1) = L - 1
```

The residue boundary is exact as well:

```text
2^(L-1) divides the terminal carrier
2^L does not divide the terminal carrier
```

No logarithmic estimate or asymptotic substitution is used.

## 6. Open positive excursions

`UniversalPaymentPrimitiveExcursion.lean` now defines an open excursion ending
at an observed positive queue position.  It requires a preceding queue zero
and positivity through the observed interval, but makes no future repayment
assumption.

Lean proves:

```text
positive queue at m
-> exists unique q, CanonicalOpenPositiveQueueExcursion n q m
```

The start is the block immediately after the last preceding zero.  Every
positive-drift block inside such an observed excursion is then decomposed by
the pressure-or-saturated theorem.  This avoids assuming the still-unproved
future-zero statement.

## 7. Dynamic pressure witness

`CanonicalPositiveBlockPressureWitness` packages the non-saturated branch with:

- canonical block index;
- that block's terminal valuation as a dynamic depth;
- positive pressure at precisely that depth.

The witness is intentionally not converted into one fixed global pressure
depth.  Existing pressure-separator APIs do not yet provide a proved map that
preserves these block-local contributions across changing depths.

## 8. Relational finite-transition certificate

`FiniteSignedTransition.lean` now defines
`RelationalFiniteSignedTransitionPotentialCertificate` with an explicit
transition relation `Step`.

Only realized edges must satisfy concrete-to-projected soundness.  For every
finite related path, Lean proves:

```text
actual path weight <= projected path weight
projected path weight <= endpoint potential difference
actual path weight <= finite potential bound
equal endpoint signatures -> actual path weight <= 0
```

The former all-pairs certificate remains available and maps to the relational
one by taking `Step := True`.

The cp-317 signature diagnostics now have a precise interpretation:

- drift collision refutes exact deterministic drift recovery;
- nondeterministic successors refute a deterministic automaton but not a
  graph abstraction or sound over-approximation;
- a realized related positive closed-signature path refutes a bounded
  potential certificate for that signature.

## 9. Saturated-chain audit

New executable audit and recorded outputs:

```text
python/Collatz/PetalBridge/saturated_block_audit.py
python/Collatz/PetalBridge/results/saturated_block_audit_318.json
python/Collatz/PetalBridge/results/saturated_block_audit_318.md
```

Range:

- all 65,536 odd roots through `131071`;
- 1,280 deterministic random odd roots of widths 64, 128, 256, 512, and 1024;
- random seed `54039`.

Observed results:

| Observation | Result |
| --- | ---: |
| saturated blocks | 33,435 |
| maximum consecutive saturated length | 1 |
| consecutive saturated pairs | 0 |
| saturated blocks of length 2 | 33,435 |
| immediate successor drift nonpositive | 31,650 |
| immediate successor drift positive | 1,785 |
| runs lacking a later observed nonpositive block | 0 |
| maximum blocks to first later nonpositive drift | 5 |

The 1,785 positive immediate successors are counterexamples to the proposed
rule:

```text
saturated block -> next block has nonpositive drift
```

The observed length-two and no-consecutive-saturation patterns are not Lean
theorems and are not exposed as API claims.

## 10. Exact stopping point

The first genuine Stage L obstruction is saturated successor behavior.

The exact normal form determines the current block, but no existing theorem
currently turns

```text
x + 1 = 2^L * u
v2 (3^L * u - 1) = L - 1
```

into a stable successor grammar.  In particular, the audit disproves the
strongest one-step repayment candidate.  Proving either `L = 2`, exclusion of
consecutive saturation, or a bounded later repayment requires a new arithmetic
argument controlling the next canonical block from this normal form.

This is the safe endpoint of cp-318.  Returning to queue algebra or enlarging
the failed low-bit signatures would not address this obstruction.

## 11. Next implementation direction

The next productive experiment should start from the exact saturated normal
form rather than from another finite signature.  Candidate proof obligations,
in order, are:

1. derive a next-block normal form directly from `(L,u)`;
2. test whether simultaneous carry-two inequalities can prove `L = 2`;
3. if not, seek an exact residue descent that excludes consecutive saturation;
4. separately design a contribution-preserving aggregator for pressure
   witnesses whose terminal depths vary by block.

Any new successor theorem must first survive both the exact recurrence and the
recorded positive-successor counterexamples.

## 12. Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlockNormalForm
lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPositiveBlock
lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPrimitiveExcursion
lake build DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath.Collatz.PetalBridge
lake build DkMath
git diff --check
```

The four modified/new theorem modules contain no `sorry`.  The top-level build
continues to report pre-existing `sorry` declarations in unrelated research
modules; cp-318 introduces none.
