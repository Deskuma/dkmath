# ABC/GN Balance Calibration — Checkpoint 006

## Scope and outcome

This report treats the attached `instruction-006.md` as the bounded
checkpoint contract.  The implementation separates the exact local ruler
law from finite Hensel transport.  In particular, no existence of a lift is
assumed from uniqueness.

Outcome A — EXACT DEPTH TRANSPORT.

The following are kernel-checked:

- an exact valuation successor adds `log q` to local mass and subtracts
  `log q` from local balance;
- a canonical depth-`k+1` residue reduces to a canonical depth-`k` residue;
- existing congruence uniqueness gives injectivity of successor reduction;
- under the existing simple-root hypotheses, the successor residue-cardinality
  is non-increasing.

The result is finite and local.  It does not assert that any depth-`k` root
lifts to depth `k+1`, and it does not assert equality of successive
cardinalities.

## Repository-first audit

The focused production module imports
`DkMath.ABC.GNBalanceDepthLayers` and
`DkMath.ABC.GNLegacyTailCountingBridge`
(`GNBalanceDepthTransport.lean:7-8`).  The relevant existing declarations
were checked and reused as follows:

| Existing declaration | Source and role |
|---|---|
| `GNNonExceptionalLocalMass`, `GNNonExceptionalLocalBalance` | `DkMath/ABC/GNBalanceDepthLayers.lean:29-36`; the local coordinates used by Level A |
| `GN_modEq_left` | `DkMath/ABC/GNLegacyTailCountingBridge.lean:216`; congruence transport for `GN` |
| `GNDeepLiftResidues`, `mem_GNDeepLiftResidues_iff` | `.../GNLegacyTailCountingBridge.lean:233-241`; canonical representatives and their range/divisibility characterization |
| `GNDeepLiftCongruenceUnique` | `.../GNLegacyTailCountingBridge.lean:536-542`; pointwise same-mod-`q` uniqueness at a fixed depth |
| `GNDeepLiftReductionInjective_of_congruenceUnique` | `.../GNLegacyTailCountingBridge.lean:545-556`; existing fixed-depth reduction injectivity |
| `GNDeepLiftCongruenceUnique_of_simpleRoot` | `.../GNLegacyTailCountingBridge.lean:657-664`; finite Hensel uniqueness under simple roots |
| `GNDeepLiftReductionInjective_of_simpleRoot` | `.../GNLegacyTailCountingBridge.lean:749-759`; existing simple-root fixed-depth wrapper |
| `GNDeepLiftResidues_card_le_of_simpleRoot` | `.../GNLegacyTailCountingBridge.lean:840-851`; existing bound by the base-depth cardinality |

The new module is exported through `DkMath/ABC.lean:56`.

## Level A — exact local-coordinate successor law

`GNNonExceptionalLocalMass_eq_add_log_of_factorization_succ`
(`GNBalanceDepthTransport.lean:31-39`) assumes the explicit exact-depth
hypothesis

```text
v_q(GN p a' b) = v_q(GN p a b) + 1
```

and proves

```text
LocalMass(a') = LocalMass(a) + log q.
```

`GNNonExceptionalLocalBalance_eq_sub_log_of_factorization_succ`
(`:42-50`) proves the corresponding exact identity

```text
LocalBalance(a') = LocalBalance(a) - log q.
```

These are algebraic identities under an exact factorization successor.  They
do not construct `a'`, prove a root exists, or imply that a fixed integer
mutates its valuation.

The existing pivot declarations remain distinct: factorization depth two has
zero local balance and depth at least three is negative
(`GNBalanceDepthLayers.lean:152-180`).

## Level B — canonical downward reduction

`GNDeepLiftResidues_succ_reduction_mem`
(`GNBalanceDepthTransport.lean:55-73`) proves, for `Nat.Prime q` and
`0 < k`,

```text
r ∈ GNDeepLiftResidues p q b (k+1)
  -> r % q^k ∈ GNDeepLiftResidues p q b k.
```

The proof uses the canonical range bound, divisibility monotonicity
`q^k ∣ q^(k+1)`, `GN_modEq_left`, and
`mem_GNDeepLiftResidues_iff`.  No polynomial Hensel theorem is reproved.

## Level C — injectivity and cardinality

`GNDeepLiftSuccessorReductionInjective_of_congruenceUnique`
(`GNBalanceDepthTransport.lean:81-101`) takes existing pointwise uniqueness
at depth `k+1` and proves injectivity of

```text
r ↦ r % q^k
```

on canonical depth-`k+1` roots.  Equality of reductions modulo `q^k` is first
reduced to equality modulo `q`; the existing uniqueness theorem then gives
congruence modulo `q^(k+1)`, and canonical range bounds give equality.

The simple-root wrapper
`GNDeepLiftSuccessorReductionInjective_of_simpleRoot`
(`GNBalanceDepthTransport.lean:104-115`) retains exactly these hypotheses:

```text
Nat.Prime p
Nat.Prime q
¬ q ∣ p
¬ q ∣ b
0 < k.
```

It invokes the existing simple-root theorem at depth `k+1`.  The exceptional
channel `q ∣ p` is not routed through this result.

The finite endpoint
`GNDeepLiftResidues_card_succ_le_of_congruenceUnique`
(`GNBalanceDepthTransport.lean:118-142`) combines Level B membership with
Level C injectivity and proves

```text
card (GNDeepLiftResidues p q b (k+1))
  ≤ card (GNDeepLiftResidues p q b k).
```

`GNDeepLiftResidues_card_succ_le_of_simpleRoot`
(`:145-156`) supplies the requested simple-root specialization.

This is a genuine finite branch-count law: deeper canonical branches can
disappear, but cannot split under the stated uniqueness hypothesis.  It is
not a global density monotonicity theorem.

## Existence boundary and BCAL interpretation

No existing declaration used here proves that every depth-`k` root has a
depth-`k+1` lift.  Therefore the implementation does not claim lift
existence, an infinite Hensel branch, or

```text
card R_(k+1) = card R_k.
```

Also, `q^k ∣ GN p a b` is only the threshold statement
`v_q(GN p a b) ≥ k`; it is not an exact valuation equality.  Consequently the
Level B/C residue theorems do not assign the BCAL local value `(2-k) log q`
to a residue.  That value is available only through the Level A exact
factorization-depth hypothesis.

Thus BCAL-006 connects the arithmetic depth tree to the BCAL ruler without
identifying threshold depth with exact valuation.  No ABC estimate, uniform
calibration constant, global balance monotonicity, optimization, or shell
counting statement follows.

## Validation

The following validations passed in the nested Lake project `lean/dk_math`:

- `lake env lean DkMath/ABC/GNBalanceDepthTransport.lean`
- `lake build DkMath.ABC.GNBalanceDepthTransport`
- `lake build DkMath.ABC`
- `#print axioms` for the Level A, B, simple-root Level C, and cardinality
  endpoints: only `[propext, Classical.choice, Quot.sound]`
- forbidden-token scan of the new production module for `sorry`, `admit`,
  `axiom`, and `unsafe`: no matches
- trailing-whitespace scan: no matches
- `git diff --check`: passed

The facade build replayed the pre-existing warning at
`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147` (`sorry`), outside
this checkpoint.

## Later boundary

A later checkpoint may study a separately justified lift-existence theorem or
an iterated finite transport.  Such a checkpoint must retain the present
non-exceptional hypotheses and must not turn the current `≤` law into equality
without new arithmetic input.
