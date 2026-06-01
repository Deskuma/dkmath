# roadmap: DKMK-010

## 0. Position

DKMK-009 closed the capacity-kernel-facing hitting route.

```text
PrimePowerWitnessProvider
  -> globalLogCapacityKernel
  -> CapacityKernel generic bridge
  -> primePowerQuotientPathFamily
  -> weightedHitMass bound
```

The remaining input in that route is the source mass estimate.

```lean
LogCapacitySourceMassBound M C
```

DKMK-010 starts the next layer: tail, truncation, and source mass estimates.
This is not yet the final analytic `1 + O(1 / log x)` theorem.  The goal is
to design the theorem-facing interface that can later carry such an estimate
into the DKMK-009 route.

## 1. Problem

The DKMK-009 endpoint has the following shape.

```lean
PrimePowerWitnessProvider
  .globalLogCapacityKernel_primePowerQuotientPathFamily_weightedHitMass_le_of_sourceBound
```

Conceptually, it says:

```text
capacity kernel route
  + quotient path family
  + LogCapacitySourceMassBound M C
  => weightedHitMass A <= C
```

Therefore DKMK-010 should not add another kernel wrapper.  It should explain
how to choose or approximate `M` and `C` so that the source mass side begins to
look like a tail or truncation estimate.

The final target is still analytic in nature.  In older notes this appeared as
the gap between finite channel weights such as

```text
log p / log n
```

and tail weights of the form

```text
1 / (a * log a)
```

That bridge should be staged.  DKMK-010 only sets up the finite/truncated
interface.

## 2. Existing Surface

The current Lean surface already has bounded source mass models.

```lean
LogCapacitySourceMassBound
tailIndicatorNatMassSpace_logCapacitySourceMassBound_one
scaledTailIndicatorNatMassSpace_logCapacitySourceMassBound
twoStepTailNatMassSpace_logCapacitySourceMassBound
boundedMonotoneNatMassSpace_logCapacitySourceMassBound
finiteStepTailNatMassSpace_logCapacitySourceMassBound
```

It also has route theorems that apply those models to one-step, multi-step,
and witness-derived quotient path families.

The useful lesson is that source mass is already a modular input.  DKMK-010
should preserve that modularity and avoid baking a specific analytic estimate
directly into the kernel/path layer.

## 3. Caution

The current reusable route often passes through `DvdMonotoneMass`.
This is well suited to bounded tail indicators and finite-step increasing
height models.

However, a naive analytic weight such as `1 / (n * log n)` may have the wrong
monotonicity direction for this interface.  DKMK-010 should therefore avoid
jumping straight to the infinite analytic weight.

The safer first move is to specify finite or truncated envelopes that can be
used as source mass bounds.  The analytic work can then prove that those
envelopes have the required constants.

## 4. Work Items

### DKMK-010A: roadmap and scope

Create this roadmap and fix the scope of the chapter.

Non-goals:

- no new kernel wrapper;
- no replacement of the DKMK-009 route;
- no final Mertens-style estimate;
- no final `1 + O(1 / log x)` theorem.

### DKMK-010B: source mass inventory

Record the theorem surface that can already consume a source mass bound.

Expected output:

- a short inventory section in the project docs;
- a decision on whether the next Lean surface belongs in
  `LogCapacityHittingBridge.lean` or a separate tail/truncation file.

### DKMK-010C: truncation interface

Introduce a theorem-facing specification for finite truncation windows.

The interface should be phrased in terms of supplying a bounded mass model and
a constant:

```lean
LogCapacitySourceMassBound M C
```

Possible names:

```lean
TruncatedTailSourceMassBound
TailWindowSourceMassBound
```

The interface should not require the final analytic proof.

### DKMK-010D: envelope-to-route bridge

Connect the truncation interface to the DKMK-009 endpoint.

Expected shape:

```text
truncated tail envelope
  -> LogCapacitySourceMassBound M C
  -> globalLogCapacityKernel ... quotientPathFamily weightedHitMass <= C
```

The bridge should remain thin.  The kernel/path theorem should still be the
DKMK-009 theorem.

### DKMK-010E: analytic placeholder

State, as a docs-level or Prop-level interface, the future analytic input:

```text
C(x) <= 1 + error(x)
```

or a finite-window version of it.

This item is a contract for later DKMK chapters, not a proof obligation for
DKMK-010.

### DKMK-010F: report and handoff

Close the chapter with a short report describing:

- what source mass interface DKMK-010 fixed;
- which existing route theorem consumes it;
- what analytic estimates are still outside the Lean core.

## 5. Verification Plan

For docs-only steps:

```text
git diff --check
long-line check on changed docs files
```

For the first Lean interface step:

```text
lake build DkMath.NumberTheory.PrimitiveSet.LogCapacityHittingBridge
lake build DkMath.NumberTheory.PrimitiveSet
```

If a new module is introduced, build that module first and then the
`PrimitiveSet` aggregator.

## 6. Next Decision

The next concrete step should be DKMK-010B.

It should inspect the existing source mass route and decide whether a
tail/truncation interface should be:

- a docs-only contract first;
- a small Prop interface in the existing hitting bridge file; or
- a separate Lean module for tail/truncation estimates.

## 7. Source Mass Inventory

DKMK-010B records the current source-mass surface before adding any Lean
interface.

The key separation is:

```text
source mass model
  -> LogCapacitySourceMassBound M C
  -> existing DKMK-009 / DKMK-008 route theorem
  -> weightedHitMass <= C
```

The source bound itself is usually just a uniform estimate on log-capacity
states.  The path route may additionally require `DvdMonotoneMass M`, because
one-step and quotient-path families are built as divisor-descending families.

Current source-bound providers:

- `unitNatMassSpace_logCapacitySourceMassBound_one`
  - model: unit mass
  - constant: `1`
  - route monotonicity: `unitNatMassSpace_dvdMonotone`
- `nonunitNatMassSpace_logCapacitySourceMassBound_one`
  - model: nonunit indicator
  - constant: `1`
  - route monotonicity: `nonunitNatMassSpace_dvdMonotone`
- `tailIndicatorNatMassSpace_logCapacitySourceMassBound_one`
  - model: tail indicator
  - constant: `1`
  - route monotonicity: `tailIndicatorNatMassSpace_dvdMonotone`
- `scaledTailIndicatorNatMassSpace_logCapacitySourceMassBound`
  - model: scaled tail indicator
  - constant: `c`
  - route monotonicity: `scaledTailIndicatorNatMassSpace_dvdMonotone`
- `twoStepTailNatMassSpace_logCapacitySourceMassBound`
  - model: two-step tail
  - constant: `cHigh`
  - route monotonicity: `twoStepTailNatMassSpace_dvdMonotone`
- `boundedMonotoneNatMassSpace_logCapacitySourceMassBound`
  - model: bounded height envelope
  - constant: `C`
  - route monotonicity: `boundedMonotoneNatMassSpace_dvdMonotone`
- `finiteStepTailNatMassSpace_logCapacitySourceMassBound`
  - model: finite-step tail
  - constant: `sum increment`
  - source bound: via bounded monotone
  - route monotonicity: `finiteStepTailNatMassSpace_dvdMonotone`
- `twoStepAsFiniteStepTailNatMassSpace_logCapacitySourceMassBound`
  - model: two-step as finite-step
  - constant: `cHigh`
  - source bound: via finite-step
  - route monotonicity: `twoStepAsFiniteStepTailNatMassSpace_dvdMonotone`

The main DKMK-010 candidate is the finite-step tail model.  It already packages
a finite family of thresholds and nonnegative increments as a bounded monotone
height:

```lean
finiteStepTailNatMassSpace steps threshold increment hinc
```

and supplies:

```lean
LogCapacitySourceMassBound
  (finiteStepTailNatMassSpace steps threshold increment hinc)
  ((Finset.sum steps increment : ℚ) : ℝ)
```

This is close to a finite window or truncated envelope.  It does not yet encode
an analytic estimate, but it gives the right theorem shape for one.

## 8. Existing Route Consumers

The current consumers of `LogCapacitySourceMassBound M C` include the generic
capacity-kernel endpoint:

```lean
PrimePowerWitnessProvider
  .globalLogCapacityKernel_primePowerQuotientPathFamily_weightedHitMass_le_of_sourceBound
```

and the selected `SubMarkovShadow` endpoints:

```lean
PrimePowerWitnessProvider
  .globalLogCapacitySubMarkovShadow_adjacentDivisorPathFamily_weightedHitMass_le_of_sourceBound
PrimePowerWitnessProvider
  .globalLogCapacitySubMarkovShadow_divisorStep_weightedHitMass_le_of_sourceBound
```

There are also concrete finite-step wrappers for one-step, adjacent family, and
witness-derived quotient path routes.  The corresponding canonical full-shadow
wrappers exist as well.

For DKMK-010, the most important consumer remains the DKMK-009 endpoint:

```text
globalLogCapacityKernel
  + primePowerQuotientPathFamily
  + LogCapacitySourceMassBound M C
  => weightedHitMass <= C
```

The source estimate layer should feed this endpoint, not duplicate it.

## 9. Placement Decision

The tail/truncation interface should live outside `LogCapacityHittingBridge.lean`.

Recommended file:

```text
DkMath/NumberTheory/PrimitiveSet/SourceMassTruncation.lean
```

Reason:

- `LogCapacityHittingBridge.lean` already carries the kernel/path route;
- DKMK-010 is about the source estimate layer;
- keeping truncation contracts separate prevents analytic placeholders from
  spreading into the kernel bridge file.

The first Lean step should be small.  If a wrapper is added, prefer a
theorem-facing name such as:

```lean
TailWindowSourceMassBound
```

over a heavier analytic name.  `TailWindow` emphasizes that the object is still
finite/truncated.  The final infinite tail estimate can be supplied later as a
separate analytic input.

## 10. DKMK-010B Conclusion

DKMK-010B is docs-only inventory.

The current theorem surface is already sufficient to express the route:

```text
finite-step or bounded monotone source envelope
  -> LogCapacitySourceMassBound M C
  -> DKMK-009 quotient-path capacity route
  -> weightedHitMass <= C
```

The next step, DKMK-010C, should introduce the tail-window/truncation contract
in the new `SourceMassTruncation.lean` module, unless review feedback asks for
one more docs-only design pass first.

## 11. DKMK-010C Lean Contract

DKMK-010C adds the first Lean interface for the source estimate layer.

New module:

```text
DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
```

Main contract:

```lean
structure TailWindowSourceMassBound (M : MassSpace ℕ) (C : ℝ) : Prop where
  nonneg_const : 0 ≤ C
  source_bound : LogCapacitySourceMassBound M C
  dvd_mono : DvdMonotoneMass M
```

This is intentionally small.  It packages exactly the hypotheses needed to
feed a finite or truncated source envelope into the existing quotient-path
capacity route.

The first concrete provider is:

```lean
TailWindowSourceMassBound.finiteStepTail
```

which turns `finiteStepTailNatMassSpace` into a tail-window contract with
constant:

```lean
((Finset.sum steps increment : ℚ) : ℝ)
```

The route theorem is:

```lean
TailWindowSourceMassBound
  .globalLogCapacityKernel_primePowerQuotientPathFamily_weightedHitMass_le
```

It is only a thin wrapper around the DKMK-009 theorem:

```lean
PrimePowerWitnessProvider
  .globalLogCapacityKernel_primePowerQuotientPathFamily_weightedHitMass_le_of_sourceBound
```

So the layer separation remains:

```text
tail-window source contract
  -> DKMK-009 quotient-path capacity route
  -> weightedHitMass <= C
```

No analytic estimate is introduced in DKMK-010C.

## 12. DKMK-010D Finite-step Route Convenience

DKMK-010D adds one concrete convenience theorem.

```lean
TailWindowSourceMassBound.finiteStepTail_weightedHitMass_le
```

It composes the two DKMK-010C ingredients:

```text
finiteStepTailNatMassSpace
  -> TailWindowSourceMassBound.finiteStepTail
  -> TailWindowSourceMassBound
       .globalLogCapacityKernel_primePowerQuotientPathFamily_weightedHitMass_le
```

The theorem exposes the common finite-window use case directly:

```text
finite-step tail envelope
  + globalLogCapacityKernel
  + primePowerQuotientPathFamily
  => weightedHitMass <= sum increment
```

This remains a convenience layer.  It does not add a new proof route and does
not introduce an analytic estimate.

DKMK-010D therefore closes the finite/truncated envelope-to-route bridge in
the first concrete case.  The next layer can focus on analytic placeholders,
such as a future contract proving:

```text
sum increment <= 1 + error
```
