# PCK-009 — Campaign closeout / generic-abstraction audit instructions

Date: 2026-09-04  
Branch: `wip/number-theory-primitive-conservation-kernel-260903-v0`  
Predecessor: `report-010.md` / PCK-008

## 0. Authorization

PCK-009 is the campaign closeout checkpoint.

Its primary task is audit and consolidation, not new mathematics.

The campaign now has the complete finite chain:

```text
half-unit / square-Gnomon algebra
  -> squareBody monotonic nesting
  -> coarse-to-fine prime certification
  -> self-fresh support escape
  -> finite squarePrimeExpansion
  -> finite-basis product coarse anchor
  -> canonical 30-world regression
  -> Primitive Conservation Kernel dichotomy
```

PCK-009 must:

1. audit the theorem graph and dependency direction;
2. decide whether a generic `PrimitiveKernel` abstraction is justified;
3. audit public aggregators and make only minimal public-surface updates if justified;
4. record future extraction candidates separately from this campaign;
5. run closeout builds and produce the final campaign report.

Do not add another substantive theorem unless the audit discovers a genuine missing
bridge required only to make the existing public surface coherent.

## 1. Generic PrimitiveKernel abstraction audit

Repository-wide reconnaissance currently finds the exact interface

```text
PrimeScaleGeneratedBy
FreshPrimeDirection
bounded cofactor
unique fresh direction
squareBody bound
```

in the generic SquareBody owner and downstream square/Legendre consumers.

Legendre is a specialization of the same square-body theorem, not an independent
non-square realization.

Therefore the expected closeout classification is:

```text
GENERIC-PRIMITIVE-KERNEL: NOT-YET-JUSTIFIED
```

Do not create:

```lean
structure PrimitiveKernel ...
class PrimitiveKernel ...
def PrimitiveKernel ...
```

or any equivalent generic abstraction unless the audit finds an already-existing,
independent non-square consumer with the same exact laws and no forced square
semantics.

If no such consumer is found, record explicitly that abstraction is deferred until
at least a second independent domain exists.

## 2. Primitive public aggregator audit

Current public entry point:

```text
DkMath/NumberTheory/Primitive.lean
```

currently exports `SquareBody` but not the new PCK public surfaces.

Audit whether the following should now be exported:

```text
DkMath.NumberTheory.Primitive.SquarePrimeExpansion
DkMath.NumberTheory.Primitive.PrimitiveConservationKernel
```

Expected decision, if there is no import cycle or public-API conflict:

```text
EXPORT-BOTH
```

Rationale:
- `SquarePrimeExpansion` is the canonical finite closure operator;
- `PrimitiveConservationKernel` is the final semantic facade of the Primitive package.

If exported, add only the two import lines and update the module docstring minimally
to mention finite square expansion and the nested old-or-one-fresh dichotomy.

Do not duplicate theorem statements in the aggregator.

After any change run:

```text
lake build DkMath.NumberTheory.Primitive
```

## 3. PrimorialUniverse public aggregator audit

Current public entry point:

```text
DkMath/NumberTheory/PrimorialUniverse.lean
```

Audit:

```text
DkMath.NumberTheory.PrimorialUniverse.SquareBodyBridge
DkMath.NumberTheory.PrimorialUniverse.ThirtySquareWorld
```

Expected decision:

```text
SquareBodyBridge   -> EXPORT
ThirtySquareWorld  -> KEEP CONCRETE / NOT PUBLIC BY DEFAULT
```

Rationale:
- `SquareBodyBridge` is a generic bridge from finite-basis product anchors to
  complete square-world certification;
- `ThirtySquareWorld` is a concrete regression / firewall module.

If project convention strongly exports concrete regression modules, document the
reason before deviating.

After any aggregator change run:

```text
lake build DkMath.NumberTheory.PrimorialUniverse
```

## 4. CosmicFormula public-surface audit

Inspect:

```text
DkMath/CosmicFormula.lean
DkMath/CosmicFormula/SquareGnomon.lean
DkMath/CosmicFormula/HalfUnitZeroConjugate.lean
```

Do not move either module in this checkpoint.

Audit only whether they should be imported by the current CosmicFormula public entry
point.

Recommended default:

```text
SquareGnomon          -> PUBLIC-EXPORT-CANDIDATE
HalfUnitZeroConjugate -> KEEP DIRECT-IMPORT unless a current public consumer needs it
```

Reason:
- `SquareGnomon` is generic degree-two Cosmic Formula algebra and already has an
  independent Collatz vocabulary consumer;
- `HalfUnitZeroConjugate` remains a narrower algebraic coordinate layer with no
  need to force public exposure merely because it appeared in this campaign.

If `SquareGnomon` is exported, add only the import and a minimal docstring mention.

Run:

```text
lake build DkMath.CosmicFormula
```

if this aggregator is changed.

## 5. DkMath.Lib.Gnomon promotion audit

Do NOT perform the promotion in PCK-009.

Record the status:

```text
DKMATH-LIB-GNOMON: CANDIDATE / SEPARATE CAMPAIGN
```

Evidence already present:

1. generic owner:
   `DkMath.CosmicFormula.SquareGnomon`;
2. independent vocabulary consumer:
   `DkMath.Collatz.GnomonEvaluation`;
3. exact generic identities:
   - GN/GTail bridge;
   - core + Gnomon = next square;
   - fixed-Gap Body growth;
   - kernel increment `2*u`;
   - area increment `2*u^2`;
   - degree-two scaling.

Before future promotion, require a dedicated migration audit:
- canonical namespace and names;
- Collatz bridge direction;
- import-cycle analysis;
- whether the object is truly square-specific or belongs in a more generic Gnomon algebra.

Do not rename or move files now.

## 6. Campaign theorem graph audit

The closeout report must inventory at least these load-bearing surfaces.

### PCK-001

```text
HalfUnitZeroConjugate.zeroConjugateUniverse_eq_mul
zeroConjugateUniverse_eq_zero_iff
zeroConjugateUniverse_reflection
```

### PCK-002

```text
squareBody_mono
```

### PCK-002G

```text
squareGnomonKernel_eq_GTail
squareGnomon_eq_mul_two_mul_add
core_add_squareGnomon_eq_next_square
bodyN_two_add_squareGnomon
bigN_two_step_fixedGap
squareGnomonKernel_step
squareGnomon_step
squareGnomon_scale
```

### PCK-003

```text
prime_of_supportDisjointFrom_primeScalesUpTo_coarse_of_le_fine_squareBody
```

### PCK-004

```text
freshPrimeDirection_self_of_supportDisjointFrom_primeScalesUpTo_coarse_of_le_fine_squareBody
```

Use the exact final source name.

### PCK-005

```text
squarePrimeExpansion
mem_squarePrimeExpansion_iff
squarePrimeExpansion_eq_primeScalesUpTo_squareBody
```

### PCK-006

```text
finitePrimeBasis_subset_primeScalesUpTo_product
prime_of_supportDisjointFrom_productClosure_of_le_fine_squareBody
```

### PCK-007

```text
primeBasis235_subset_primeScalesUpTo_thirty
primeScalesUpTo_thirty_eq
squareBody_thirty
squarePrimeExpansion_thirty_eq_primeScalesUpTo_960
prime_of_supportDisjointFrom_thirtyClosure_of_le_fine_squareBody
fortyNine_basis_vs_completeClosure_firewall
```

### PCK-008

```text
primitiveConservationKernel_dichotomy_of_le_fine_squareBody
```

For each layer, record whether it is:
- new mathematics;
- thin adapter;
- semantic facade;
- concrete regression.

## 7. Exact final mathematical summary

The closeout report should state the final finite theorem architecture without
overclaiming.

### Complete-support certification

For

$$
q\le P,
\qquad
1<m\le\operatorname{squareBody}(q),
$$

if `m` escapes every prime in `primeScalesUpTo P`, then `m` is prime and
self-fresh.

### Exact finite closure

$$
\operatorname{squarePrimeExpansion}(P)
=
\operatorname{primeScalesUpTo}(\operatorname{squareBody}(P)).
$$

### Coarse product anchor

For a finite prime basis `S`,

$$
S
\subseteq
\operatorname{primeScalesUpTo}
\bigl(
\operatorname{finitePrimeBasisProduct}(S)
\bigr).
$$

The basis is not generally equal to the complete closure.

### Primitive Conservation Kernel

For

$$
q\le P,
\qquad
0<m\le\operatorname{squareBody}(q),
$$

either:
- `m` is entirely old-generated by `primeScalesUpTo P`; or
- `m = p*k` with one unique fresh prime `p>P`, positive old-generated
  `k≤P`, and `Nat.Coprime p k`.

This is finite and bounded.

## 8. Mandatory firewalls in the closeout report

The report must explicitly preserve all of these.

### Basis is not complete closure

```text
{2,3,5} != primeScalesUpTo 30
```

with 49 as the concrete firewall.

### Survivor is not prime

Wheel/PHZ survival against a generating basis is only candidate-seat information.

### Fresh is not support-disjoint

`FreshPrimeDirection` records one fresh prime divisor.
`SupportDisjointFrom` excludes all old prime directions.

### Primitive is not universally squarefree

The PCK theorem controls only the fresh direction to depth one.
Old-generated cofactors may contain repeated old prime powers.

### Finite closure is not an unbounded prime algorithm

PCK-005 is an exact finite equality, not a computational-efficiency or asymptotic claim.

### PCK is not Legendre

The campaign does not prove that every interval between consecutive squares contains
a prime.

### PCK is not RH

No zeta, Xi, PHZ analytic, CFBRC, zero-derived provider, or RH theorem is supplied.

## 9. Verification matrix

At minimum run focused builds for final owners:

```text
lake build DkMath.CosmicFormula.SquareGnomon
lake build DkMath.NumberTheory.Primitive.SquarePrimeExpansion
lake build DkMath.NumberTheory.Primitive.PrimitiveConservationKernel
lake build DkMath.NumberTheory.PrimorialUniverse.SquareBodyBridge
lake build DkMath.NumberTheory.PrimorialUniverse.ThirtySquareWorld
```

If aggregators are modified, also run their builds.

Run:

```text
git diff --check
```

Axiom-check at least the final three public load-bearing theorems:

```text
squarePrimeExpansion_eq_primeScalesUpTo_squareBody
primitiveConservationKernel_dichotomy_of_le_fine_squareBody
prime_of_supportDisjointFrom_productClosure_of_le_fine_squareBody
```

Also audit the campaign-added Lean files for:
- `sorry`;
- `admit`;
- `native_decide`;
- project `axiom`;
- forbidden analytic imports.

## 10. Final report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveConservationKernel-260903-v0/report-011-closeout.md
```

The report must include:

1. final outcome classification;
2. branch and starting HEAD;
3. all changed files in PCK-009;
4. checkpoint-by-checkpoint theorem inventory;
5. dependency graph;
6. public aggregator decisions;
7. generic PrimitiveKernel audit result;
8. DkMath.Lib.Gnomon future-promotion status;
9. exact mathematical summary;
10. all firewalls;
11. verification matrix;
12. remaining future work;
13. merge/readiness recommendation.

## 11. Expected final classifications

Unless the audit finds contrary evidence, close with:

```text
PCK-CAMPAIGN: COMPLETE
FINITE-SQUARE-PRIME-CLOSURE: COMPLETE
COARSE-TO-FINE-CERTIFICATION: COMPLETE
PRIMITIVE-CONSERVATION-DICHOTOMY: COMPLETE
PRIMORIAL-PRODUCT-BRIDGE: COMPLETE
CANONICAL-30-WORLD-REGRESSION: COMPLETE

GENERIC-PRIMITIVE-KERNEL: NOT-YET-JUSTIFIED
DKMATH-LIB-GNOMON: CANDIDATE / SEPARATE CAMPAIGN

LEGENDRE: NOT PROVED BY PCK
RH: NOT ADDRESSED BY PCK
```

## 12. After PCK-009

Do not automatically begin another implementation campaign.

The closeout report should recommend separate future work items, for example:

```text
A. Gnomon library-promotion / resolution-refinement campaign
B. use PCK as an arithmetic provider inside Legendre work
C. investigate higher-degree analogues only after an exact bounded replacement
   for squareBody is identified
D. RH/CFBRC remains on its independent provider frontier
```

PCK-009 ends the current campaign.
