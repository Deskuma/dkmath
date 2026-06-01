# roadmap: DKMK-011

## 0. Position

DKMK-010 fixed the interface between finite/truncated source envelopes and the
capacity-kernel hitting route.

The endpoint is:

```text
finiteStepTailNatMassSpace
  -> TailWindowSourceMassBound
  -> weightedHitMass <= sum increment
  -> FiniteStepTailAnalyticBound
  -> weightedHitMass <= 1 + error
```

DKMK-011 starts the next layer.  Its job is to decide how to supply
`FiniteStepTailAnalyticBound` from concrete finite-step or truncation data.

## 1. Main Question

The DKMK-010 placeholder is:

```lean
FiniteStepTailAnalyticBound steps increment error
```

which means:

```text
((Finset.sum steps increment : Q) : R) <= 1 + error
```

DKMK-011 must explain what the following data mean:

```text
steps
threshold
increment
error
```

This chapter should not yet prove a Mertens theorem or a final
`1 + O(1 / log x)` statement.  It should design the concrete finite envelope
that an analytic theorem can later estimate.

## 2. Interpretation Targets

### steps

`steps` should index the finite pieces of a truncation envelope.

Possible interpretations:

- dyadic or logarithmic bands;
- finite windows in a truncation parameter;
- finitely many tail regions above thresholds.

The Lean type should remain abstract at first:

```lean
{ι : Type _} [DecidableEq ι]
steps : Finset ι
```

This keeps DKMK-011 independent of the eventual analytic partition.

### threshold

`threshold : ι -> Nat` determines where each finite-step piece becomes active.

In DKMK-010 this feeds:

```lean
finiteStepTailNatMassSpace steps threshold increment hinc
```

For DKMK-011, the design question is how `threshold` relates to a truncation
parameter such as `x`.

At roadmap level, keep this as a contract:

```text
threshold encodes the finite tail window activated by the truncation parameter
```

Do not hard-code a specific analytic choice yet.

### increment

`increment : ι -> Q` is the finite envelope height added by each active step.

It must satisfy:

```lean
hinc : forall i in steps, 0 <= increment i
```

DKMK-010 uses only the total:

```text
sum increment
```

DKMK-011 should specify what analytic quantity this total approximates or
dominates.

### error

`error : R` is the term in the placeholder bound:

```text
sum increment <= 1 + error
```

Eventually `error` should be related to a truncation parameter, for example a
term of size `O(1 / log x)`.  DKMK-011 should not need big-O formalization yet.

## 3. Proposed Contracts

DKMK-011 should introduce one or two lightweight contracts before proving any
heavy estimate.

### DKMK-011A: roadmap and interpretation

This file is DKMK-011A.

It fixes the target:

```text
concrete finite-step/truncation data
  -> FiniteStepTailAnalyticBound steps increment error
```

### DKMK-011B: docs inventory of possible truncation data

Collect possible choices of finite envelope:

- single-window tail envelope;
- finite-step monotone envelope;
- dyadic/logarithmic band envelope;
- externally supplied increment list.

The output can remain docs-only.

### DKMK-011C: Lean contract for supplied finite-step estimate

If Lean is added, start with a thin Prop wrapper around the existing
placeholder.

Possible name:

```lean
FiniteStepTailEstimateData
```

or:

```lean
TruncationEnvelopeEstimate
```

The minimal useful shape is:

```lean
structure TruncationEnvelopeEstimate
    {ι : Type _} [DecidableEq ι]
    (steps : Finset ι) (threshold : ι -> Nat)
    (increment : ι -> Q) (error : R) : Prop where
  nonneg_increment : forall i in steps, 0 <= increment i
  analytic_bound : FiniteStepTailAnalyticBound steps increment error
```

This would package the two inputs needed by
`finiteStepTail_weightedHitMass_le_one_add_error`.

### DKMK-011D: route theorem from estimate data

If 011C is added, the next theorem should be a thin wrapper:

```text
TruncationEnvelopeEstimate
  -> finiteStepTail_weightedHitMass_le_one_add_error
  -> weightedHitMass <= 1 + error
```

Again, this should not be a new proof route.  It should only package the
existing DKMK-010 theorem with the nonnegative increment hypothesis.

### DKMK-011E: analytic handoff

Record what remains outside the current Lean layer:

```text
prove the concrete analytic inequality
sum increment <= 1 + error
```

This is where later work can connect to a Mertens/truncation estimate.

### DKMK-011F: report

Close DKMK-011 with a report explaining:

- which finite envelope data were fixed;
- which Prop contract supplies `FiniteStepTailAnalyticBound`;
- which theorem carries the data to `weightedHitMass <= 1 + error`;
- what analytic proof remains future work.

## 4. Non-goals

DKMK-011 should not:

- prove a Mertens theorem;
- formalize big-O;
- replace `TailWindowSourceMassBound`;
- add another kernel/path bridge;
- change the DKMK-009 quotient-path route.

The chapter is about making the analytic estimate provider explicit, not about
changing the route that consumes it.

## 5. Verification Plan

For DKMK-011A/B docs-only steps:

```text
git diff --check
long-line check on changed docs files
```

For the first Lean step:

```text
lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
lake build DkMath.NumberTheory.PrimitiveSet
```

If a new module is introduced, build that module first and then the
`PrimitiveSet` aggregator.

## 6. Next Step

The next concrete step should be DKMK-011B.

It should decide whether the first concrete provider is:

- an externally supplied finite-step estimate contract; or
- a small built-in truncation envelope data structure.

The conservative choice is to start with the externally supplied contract,
because it preserves the separation between finite route plumbing and analytic
estimates.

## 7. DKMK-011B Envelope Candidate Inventory

DKMK-011B compares the finite envelope data candidates before adding Lean code.

The target remains:

```text
finite envelope data
  -> FiniteStepTailAnalyticBound steps increment error
  -> weightedHitMass <= 1 + error
```

The important design point is that `threshold` and `increment` play different
roles.

```text
threshold:
  activates the source envelope inside finiteStepTailNatMassSpace

increment:
  contributes to the total sum used by FiniteStepTailAnalyticBound
```

`FiniteStepTailAnalyticBound` itself only sees `steps`, `increment`, and
`error`.  It does not mention `threshold`.  Therefore the first Lean contract
can either bundle everything together, or keep envelope data and analytic
total estimate as separate layers.

### Candidate: single-window tail envelope

Shape:

```text
steps      = Unit
threshold  = x
increment  = C
```

Advantages:

- smallest possible finite envelope;
- easiest to connect to `finiteStepTailNatMassSpace`;
- useful as a sanity check for the DKMK-010 route.

Risks:

- too coarse for the final tail estimate;
- hides the structure needed for `1 / log x`-scale errors.

This is a good toy provider, but probably not the main analytic route.

### Candidate: finite-step monotone envelope

Shape:

```text
steps      = arbitrary finite index set
threshold  = piecewise thresholds
increment  = nonnegative envelope increments
```

Advantages:

- exactly matches the current `finiteStepTailNatMassSpace` API;
- keeps `DvdMonotoneMass` available through the existing theorem;
- allows external analytic work to choose the finite partition.

Risks:

- too abstract if used without additional documentation;
- the mathematical meaning of each step must be supplied externally.

This is the best first Lean target.

### Candidate: dyadic band envelope

Shape:

```text
steps      = k = 0, ..., K
threshold  = 2^k * x
increment  = band estimate
```

Advantages:

- common analytic discretization;
- finite by construction after choosing `K`;
- easier to explain than arbitrary external data.

Risks:

- requires committing to powers and truncation parameters;
- may need extra Nat/Real coercion infrastructure;
- still does not by itself prove the final estimate.

This is a likely later specialization, not the first generic contract.

### Candidate: logarithmic band envelope

Shape:

```text
steps      = k = 0, ..., K
threshold  = approximate exp(k) * x
increment  = log-density estimate
```

Advantages:

- closer to `1 / log x` behavior;
- may align better with final asymptotic statements.

Risks:

- natural-number thresholds require rounding choices;
- introduces real exponential/log infrastructure too early;
- can obscure the finite route plumbing.

This should wait until the analytic layer is ready.

### Candidate: externally supplied increment list

Shape:

```text
steps      = arbitrary finite set
threshold  = supplied
increment  = supplied
error      = supplied
```

Advantages:

- Lean contract stays small;
- preserves separation between route plumbing and analytic estimates;
- lets later chapters instantiate the data in different ways.

Risks:

- weak mathematical meaning unless documented;
- too permissive if treated as the final result.

This is the conservative DKMK-011C choice.

## 8. DKMK-011B Decision

The first Lean contract should use externally supplied finite-step data.

Recommended next Lean shape:

```lean
structure TruncationEnvelopeEstimate
    {ι : Type _} [DecidableEq ι]
    (steps : Finset ι)
    (threshold : ι -> Nat)
    (increment : ι -> Q)
    (error : R) : Prop where
  increment_nonneg :
    forall i in steps, 0 <= increment i
  analytic_bound :
    FiniteStepTailAnalyticBound steps increment error
```

This bundles the two hypotheses needed by the DKMK-010E route theorem:

```text
increment_nonneg:
  builds finiteStepTailNatMassSpace and TailWindowSourceMassBound

analytic_bound:
  upgrades sum increment to 1 + error
```

The theorem in DKMK-011C should be only a wrapper:

```text
TruncationEnvelopeEstimate
  -> TailWindowSourceMassBound
       .finiteStepTail_weightedHitMass_le_one_add_error
  -> weightedHitMass <= 1 + error
```

No dyadic/logarithmic specialization should be added yet.

## 9. DKMK-011C Lean Contract

DKMK-011C adds the externally supplied finite-step contract.

```lean
structure TruncationEnvelopeEstimate
    {ι : Type _} [DecidableEq ι]
    (steps : Finset ι) (threshold : ι -> Nat)
    (increment : ι -> Q) (error : R) : Prop where
  increment_nonneg :
    forall i in steps, 0 <= increment i
  analytic_bound :
    FiniteStepTailAnalyticBound steps increment error
```

In Lean this uses `Nat`, `Q`, and `R` as `ℕ`, `ℚ`, and `ℝ`.

This contract deliberately bundles:

```text
increment_nonneg:
  enough to build finiteStepTailNatMassSpace

analytic_bound:
  enough to upgrade sum increment to 1 + error
```

The route theorem is:

```lean
TruncationEnvelopeEstimate
  .finiteStepTail_weightedHitMass_le_one_add_error
```

It is only a packaging wrapper around:

```lean
TailWindowSourceMassBound
  .finiteStepTail_weightedHitMass_le_one_add_error
```

Thus DKMK-011C fixes the first concrete provider shape:

```text
externally supplied finite-step estimate
  -> weightedHitMass <= 1 + error
```

No dyadic/logarithmic band data are introduced in this step.
