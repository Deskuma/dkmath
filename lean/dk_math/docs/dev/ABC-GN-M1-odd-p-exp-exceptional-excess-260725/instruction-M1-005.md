# M1-005 Instruction: Odd-prime exceptional excess closure and autonomous M1 completion

Date: 2026-07-26

## 0. Operating doctrine

This is not a stop-bounded subordinate task.

Codex and Wise Wolf are peer reasoning agents operating as two brains over the same Lean-verified research program. Checkpoints are audit markers, not permission gates.

After completing a checkpoint, do not wait for a new instruction. Evaluate the new repository state, choose the mathematically strongest next action consistent with the campaign and dependency boundaries, and continue.

Preserve reviewability:

```text
one coherent theorem layer
focused verification
checkpoint report
explicit statement of what changed mathematically
then continue
```

Implementation, local verification, and reports are in scope. Repository publication operations remain user-controlled unless separately requested.

## 1. Current facts

M1-004 established, for every odd prime `p`:

```lean
theorem padicValNat_GN_prime_eq_one_of_dvd
    {p a b : ℕ}
    (hp : Nat.Prime p)
    (hpOdd : Odd p)
    (hcop : Nat.Coprime a b)
    (hpGN : p ∣ GN p a b) :
    padicValNat p (GN p a b) = 1

 theorem factorization_GN_prime_eq_one_of_dvd
    {p a b : ℕ}
    (hp : Nat.Prime p)
    (hpOdd : Odd p)
    (hcop : Nat.Coprime a b)
    (hpGN : p ∣ GN p a b) :
    (GN p a b).factorization p = 1
```

The proof is positivity-free and uses:

```text
prime-row GN boundary congruence
GN = geometric quotient
emultiplicity_geom_sum₂_eq_one
padicValNat / factorization transfer
```

## 2. Primary M1-005 objective

Close the odd-prime exceptional filtered sum and exact affine zero budget.

Preferred new bridge module:

```text
lean/dk_math/DkMath/ABC/GNExceptionalExcessOddPrime.lean
```

A different placement is acceptable if repository inspection shows a cleaner existing owner. Keep the local arithmetic module and the finite-sum/final-budget bridge conceptually separated.

Expected imports:

```lean
import DkMath.ABC.GNOddPrimeExceptionalExcess
import DkMath.ABC.GNFinalBudgetBridge
```

## 3. Required mathematical endpoints

Target theorem shape:

```lean
theorem Triple.GNExceptionalValuationExcess_eq_zero_of_oddPrime
    (T : Triple) {p : ℕ}
    (hp : Nat.Prime p)
    (hpOdd : Odd p) :
    GNExceptionalValuationExcess p T.a T.b = 0
```

and:

```lean
theorem Triple.GNExceptionalExcessBudgetAffine_zero_of_oddPrime
    (T : Triple) {p : ℕ}
    (hp : Nat.Prime p)
    (hpOdd : Odd p) :
    GNExceptionalExcessBudgetAffine T p 0 0
```

Do not add positivity hypotheses unless actual Lean evidence forces them. Current mathematics indicates they are unnecessary.

Exact names may improve after implementation. Preserve discoverability around:

```text
GNExceptionalValuationExcess
oddPrime
eq_zero
zero budget
```

## 4. Finite-sum proof spine

Unfold only the exceptional sum.

For each summand index `q` in:

```text
(GN p T.a T.b).factorization.support.filter (fun q => q ∣ p)
```

extract:

```text
hqSupport : q ∈ (GN p T.a T.b).factorization.support
hqDvdP    : q ∣ p
```

Then:

```text
hqSupport
  -> q ∈ primeFactors
  -> q.Prime

q.Prime + q ∣ p + p.Prime
  -> q = p
```

After substitution:

```text
hqSupport
  -> (GN p T.a T.b).factorization p ≠ 0
  -> p ∣ GN p T.a T.b
```

Use:

```lean
factorization_GN_prime_eq_one_of_dvd hp hpOdd T.hcop hpGN
```

and reduce the summand:

```text
(((1 - 1 : ℕ) : ℝ) * Real.log (p : ℝ)) = 0
```

The finite sum closes with `Finset.sum_eq_zero`.

## 5. Exact budget and split-budget simplification

The zero-budget theorem should be a thin wrapper around the finite-sum theorem.

Also inspect whether the following caller-facing theorem materially improves the final contract surface:

```lean
theorem Triple.GNValuationExcessBudgetAffine_of_oddPrime_nonExceptional
    (T : Triple) {p : ℕ} {τn Dn : ℝ}
    (hp : Nat.Prime p)
    (hpOdd : Odd p)
    (hn : GNNonExceptionalExcessBudgetAffine T p τn Dn) :
    GNValuationExcessBudgetAffine T p τn Dn
```

It should be a thin application of:

```lean
GNValuationExcessBudgetAffine.of_split
```

using exceptional budget `(0,0)` and the supplied non-exceptional budget. Do not duplicate the final bridge proof.

Treat this wrapper as a judgment call: include it if it gives a natural production-facing simplification; omit it if it creates an awkward theorem surface.

## 6. Verification and report

Verify the new bridge module and immediate dependents.

At minimum:

```text
lake build DkMath.ABC.GNExceptionalExcessOddPrime
lake build DkMath.ABC.GNFinalBudgetBridge
```

If the module name differs, adapt the focused build.

Audit representative endpoints with `#print axioms` and record:

```text
new project axioms
sorry
native_decide
```

The expected result is none.

Create:

```text
report-M1-005.md
```

The report must explain:

```text
support prime q collapses to exponent p
support membership supplies p ∣ GN
M1-004 supplies factorization p = 1
all exceptional summands vanish
τe = 0 and De = 0
positivity status
contract simplification
```

## 7. Autonomous continuation into M1-006

After M1-005 closes, continue directly into M1-006 without waiting for review permission.

M1-006 is an integration and ownership audit, not a new deep arithmetic proof.

Evaluate and act on:

```text
1. public/aggregator import placement
2. focused regression builds
3. theorem statement and naming audit
4. axiom audit
5. dependency-direction audit
6. fixed-five and odd-prime theorem coexistence
7. ownership of neutral API:
     GN_eq_geom_sum₂
     prime_dvd_boundary_of_dvd_GN_prime
8. README / roadmap / final report closure
```

For neutral API ownership, choose based on evidence:

```text
keep in ABC
or
move to NumberTheory / CosmicFormula and leave ABC thin
```

Do not refactor merely for aesthetic purity. Move only if reuse, dependency clarity, and theorem ownership clearly improve enough to justify churn.

Create the final M1 closure report, expected path:

```text
FINAL_REPORT.md
```

The final report should state the exact theorem chain and the resulting contract reduction:

```text
odd-prime exceptional excess = 0
τe = 0
De = 0
remaining final-contract enemies:
  M2 lifted-radical support growth
  M3 non-exceptional valuation excess
```

## 8. After M1 victory

After M1 integration is complete, inspect the remaining repository state and choose the next strongest research action rather than idling at the milestone.

Preserve branch hygiene:

```text
M1 changes remain in the M1 branch
M2/M3 implementation belongs to its own campaign branch
neutral prerequisite lemmas may be factored only when dependency ownership is clear
```

Continue with read-only reconnaissance and a concrete next-campaign design if the next implementation belongs on a new branch. If an immediately necessary neutral lemma is a direct consequence of the completed M1 chain and belongs in the current dependency graph, implementing it is acceptable when the report explains why.

The objective is continuous mathematical progress with auditable boundaries, not permission-driven pauses.

## 9. Hard trust and scope boundaries

The following remain absolute:

```text
no abc_main_axiom modification
no ABC -> FLT.Five production dependency
no FLT7 WIP import
no new axiom
no sorry
no native_decide proof
no finite enumeration as a general proof
no unrelated repository refactor
```

These are trust and dependency boundaries, not master-subordinate stop commands.
