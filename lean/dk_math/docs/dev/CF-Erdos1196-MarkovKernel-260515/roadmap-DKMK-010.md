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
