# instruction-006 — Depth-step / finite Hensel transport audit

## 0. Scope

This is a bounded structural checkpoint.

BCAL-003 established the exact local balance law

```text
localMass(q)    = v_q(GN) * log q
localBalance(q) = (2 - v_q(GN)) * log q.
```

BCAL-005 completed the cubic exceptional bookkeeping.  The next question is whether the existing finite Hensel / deep-lift API supports a genuine depth-transport statement, and exactly how much of the heuristic

```text
v -> v + 1
localMass    -> localMass + log q
localBalance -> localBalance - log q
```

can be promoted to kernel-checked production theorems.

Do **not** assume a Hensel lift exists merely because uniqueness is available.

## 1. Required repository-first audit

Before implementing anything, inspect the current production declarations in at least:

```text
DkMath/ABC/GNBalanceDepthLayers.lean
DkMath/ABC/GNLegacyTailCountingBridge.lean
DkMath/ABC/GNDepthPressure.lean
```

Record exact declarations and imports used.

In particular verify the current status of:

```text
GNDeepLiftResidues
mem_GNDeepLiftResidues_iff
GN_modEq_left
GNDeepLiftCongruenceUnique
GNDeepLiftReductionInjective
GNDeepLiftCongruenceUnique_of_simpleRoot
GNDeepLiftReductionInjective_of_simpleRoot
GNDeepLiftResidues_card_le_base
GNDeepLiftResidues_card_le_of_simpleRoot

GNNonExceptionalLocalMass
GNNonExceptionalLocalBalance
```

The existing finite Hensel theorem gives **uniqueness inside a mod-q branch** under the non-exceptional simple-root hypotheses.  It does not by itself state that every root at depth `k` has a root at depth `k+1`.

This distinction is mandatory throughout the checkpoint.

## 2. Three levels of statement — keep them separate

### Level A — algebraic valuation-step law

If two GN states have exact q-adic factorization depths differing by one, then the BCAL local coordinates differ by exactly one `log q` unit.

Preferred theorem shapes, adapted to actual namespaces/types:

```lean
GNNonExceptionalLocalMass_eq_add_log_of_factorization_succ
GNNonExceptionalLocalBalance_eq_sub_log_of_factorization_succ
```

Conceptually, from

```text
v_q(GN p a' b) = v_q(GN p a b) + 1
```

prove exactly

```text
LocalMass(a') = LocalMass(a) + log q
LocalBalance(a') = LocalBalance(a) - log q.
```

These are algebraic transport theorems under an explicit successor-depth hypothesis.  They are **not** Hensel existence theorems.

If a cleaner theorem can be stated directly for natural depths `v` and `v+1` without introducing a redundant public definition, prefer that.

### Level B — actual deep-root reduction transport

Use the existing canonical finite residue sets.

For `0 < k`, a canonical root at depth `k+1` should reduce modulo `q^k` to a canonical root at depth `k`:

```text
r ∈ GNDeepLiftResidues p q b (k+1)
------------------------------------------------
r % q^k ∈ GNDeepLiftResidues p q b k.
```

Prove this exact downward transport if it is not already available.

Suggested theorem shape:

```lean
GNDeepLiftResidues_succ_reduction_mem
```

Use `GN_modEq_left` / divisibility monotonicity and canonical range bounds.  Do not reprove polynomial Hensel theory.

### Level C — uniqueness-induced branch pruning

Under the existing finite Hensel uniqueness hypotheses, reduction from depth `k+1` to depth `k` should be injective on canonical roots.

Target shape:

```lean
GNDeepLiftSuccessorReductionInjective_of_congruenceUnique
```

or, directly specialized to the existing simple-root hypotheses,

```lean
GNDeepLiftSuccessorReductionInjective_of_simpleRoot
```

with map

```text
r ↦ r % q^k.
```

From downward membership plus injectivity, derive the genuine arithmetic branch-count law

```text
card (GNDeepLiftResidues p q b (k+1))
  ≤ card (GNDeepLiftResidues p q b k).
```

Preferred endpoint:

```lean
GNDeepLiftResidues_card_succ_le_of_simpleRoot
```

This is the intended finite Hensel transport statement for this checkpoint:

> deeper canonical root branches can disappear, but cannot split into multiple descendants within the same simple-root branch.

Do **not** strengthen `≤` to `=` without a separately proved lift-existence theorem.

## 3. Important interpretation boundary

The following statements are different and must not be conflated.

```text
q^k ∣ GN p a b
```

means only

```text
v_q(GN p a b) ≥ k.
```

It does **not** mean

```text
v_q(GN p a b) = k.
```

Therefore membership in `GNDeepLiftResidues ... k` does not by itself assign the BCAL local balance value `(2-k) log q` to that root.

The exact BCAL successor law belongs to Level A and requires an exact factorization-depth successor hypothesis.

The Hensel residue transport belongs to Levels B/C and is a threshold/divisibility statement.

If an exact bridge between these two levels requires an additional theorem, state the missing hypothesis explicitly rather than silently identifying threshold depth with exact valuation.

## 4. Non-exceptional hypotheses

For the Hensel/simple-root specialization retain the existing conditions exactly, expected to include:

```text
Nat.Prime p
Nat.Prime q
¬ q ∣ p
¬ q ∣ b
0 < k
```

Do not weaken or remove them unless an existing production theorem already supports the weaker statement.

Do not route the exceptional `q ∣ p` channel through the simple-root theorem.

BCAL-005 already completed the exceptional cubic gauge bookkeeping; this checkpoint is about genuine non-exceptional depth transport.

## 5. Suggested production module

If new reusable endpoints are justified, use a focused module such as:

```text
DkMath/ABC/GNBalanceDepthTransport.lean
```

and export it through `DkMath/ABC.lean`.

However, if the cleanest result is a very small extension of `GNBalanceDepthLayers.lean` or `GNLegacyTailCountingBridge.lean`, prefer the existing module rather than creating a wrapper-only file.

Do not duplicate existing Hensel proofs.

## 6. Desired exact endpoints

Outcome A should ideally contain all of the following classes of result.

### A. Exact local-coordinate successor law

```text
exact valuation +1
  => local mass + log q
  => local balance - log q
```

### B. Canonical depth reduction

```text
depth k+1 canonical root
  -> reduction mod q^k
  -> depth k canonical root.
```

### C. Simple-root successor injectivity

```text
two depth-(k+1) roots
same reduction mod q^k
  -> same canonical root.
```

This may be proved by reducing equality mod `q^k` to equality mod `q` and reusing `GNDeepLiftCongruenceUnique_of_simpleRoot` at depth `k+1`.

### D. Cardinality monotonicity in depth

```text
card R_(k+1) ≤ card R_k.
```

This is a local finite-root-tree statement only.  It is not global density monotonicity and not an ABC estimate.

## 7. Optional exact corollaries

Only if essentially free from the preceding API:

- iterated cardinality monotonicity `j ≤ k -> card R_k ≤ card R_j` for positive depths;
- depth-2 / depth-3 interpretations consistent with the BCAL pivot:
  - exact valuation `2` gives balance `0`;
  - exact valuation `3` gives balance `-log q`;
- a theorem explicitly recording that a one-step exact valuation increase crosses the pivot by one log-unit.

Do not add these if they require bulky infrastructure or obscure the main result.

## 8. Explicitly forbidden claims

Do not prove or claim any of the following unless a genuinely existing theorem already supplies the missing premise and the report documents it:

```text
every depth-k root lifts to depth-(k+1)
card R_(k+1) = card R_k
there is a canonical infinite Hensel branch for every root
a fixed integer a mutates its valuation from k to k+1
GNChannelBalance is globally monotone in a
GNChannelBalance is globally monotone in k
Q = 0 is globally optimal
Hensel transport proves an ABC bound
Hensel transport produces a uniform calibration constant
```

No new ABC contract, no supremum, no new exponent optimization, no shell counting campaign.

## 9. Outcome classes

### Outcome A — EXACT DEPTH TRANSPORT

Kernel checked:

- algebraic local-coordinate successor law;
- canonical downward depth reduction;
- simple-root successor injectivity;
- `card R_(k+1) ≤ card R_k`.

This is enough.  Lift existence is not required.

### Outcome B — PARTIAL TRANSPORT

At least one reusable exact component is obtained, but e.g. successor injectivity cannot be packaged cleanly from the existing API.

Record precisely whether the blocker is:

```text
missing reduction lemma
missing congruence transport
missing positivity/index condition
API engineering only
actual mathematical existence gap
```

### Outcome C — AUDIT ONLY

If existing Hensel/counting APIs do not support a meaningful new exact theorem beyond trivial rewrites, add no production layer.  Record why.

## 10. Validation

Run at minimum:

```text
lake env lean <focused module>
lake build <focused target>
lake build DkMath.ABC
```

and:

```text
#print axioms <new central endpoints>
forbidden-token scan: sorry admit axiom unsafe
git diff --check
```

No new `sorryAx` or stronger axiom surface.

## 11. Report

Write:

```text
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/report-006.md
```

The report must include:

- Outcome A / B / C;
- exact existing Hensel API reused;
- whether lift existence is available or absent;
- theorem list for Level A, B, C;
- exact hypotheses of the simple-root transport;
- whether successor cardinality monotonicity was proved;
- why this is or is not an arithmetic realization of the BCAL local ruler;
- any boundary for a later checkpoint.

## 12. Core rule

BCAL-003 already tells us what **one more exact valuation layer would do to the scale**:

```text
mass    + log q
balance - log q.
```

BCAL-006 asks a different question:

> what does the existing arithmetic actually let us transport between depth layers?

Keep those two facts separate.  The checkpoint succeeds by connecting them without inventing lift existence.
