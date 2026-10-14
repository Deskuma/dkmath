# FLT7TC-000 — Exact p=7 TraceOne closure reconnaissance

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

Base: `develop` at `65642ab38e9110609db407913969c86c786ec662`

## 1. Mission

Perform a **read-only theorem-surface audit** before adding new production Lean
code.

The immediate question is not yet “prove FLT7”.  It is:

```text
Given the new unconditional p=7 stripped-residual seventh-power receiver,
what exact additional checked fact is needed to turn the ramified branch
into a contradiction?
```

The audit must separate:

1. facts already present in the generic `DkMath.FLT.Prime` route;
2. facts already present in the specialized `DkMath.FLT.Seven` arithmetic;
3. missing bridge theorems between those two surfaces;
4. genuinely missing mathematics.

Do not modify production Lean files in this checkpoint.

Create only:

```text
lean/dk_math/docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/report-000.md
```

Temporary scratch files may be used locally for `#check`, reduction, or theorem
shape experiments, but do not commit them.

## 2. Read first

Campaign context:

```text
lean/dk_math/docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/README.md
lean/dk_math/docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/ROADMAP.md
lean/dk_math/docs/dev/FLT-Prime-TraceOne-Closure-260916-v0/report-004.md
lean/dk_math/docs/dev/FLT-Prime-TraceOne-Closure-260916-v0/report-010.md
```

Generic prime/TraceOne route:

```text
lean/dk_math/DkMath/FLT/Prime/AdicPowerSplit.lean
lean/dk_math/DkMath/FLT/Prime/CounterexampleRouting.lean
lean/dk_math/DkMath/FLT/Prime/PrimeTraceOneStrippedIdeal.lean
lean/dk_math/DkMath/FLT/Prime/PrimeTraceOneClassGroupClosure.lean
lean/dk_math/DkMath/FLT/Prime/PrimeTraceOneCoordinateReceiver.lean
lean/dk_math/DkMath/Lib/NumberTheory/TraceOnePowerLanding.lean
lean/dk_math/DkMath/NumberTheory/CyclotomicQRTraceOneBridge.lean
lean/dk_math/DkMath/NumberTheory/PrimeQuadraticDiscriminant.lean
lean/dk_math/DkMath/NumberTheory/TraceOneDiscriminantAxis.lean
```

Specialized p=7 arithmetic:

```text
lean/dk_math/DkMath/FLT/Seven/QuadraticBridge.lean
lean/dk_math/DkMath/FLT/Seven/AxisDivisibility.lean
lean/dk_math/DkMath/FLT/Seven/SeventhPowerCoordinates.lean
lean/dk_math/DkMath/FLT/Seven/CounterexampleRouting.lean
lean/dk_math/DkMath/FLT/Seven/SevenAdicPowerSplit.lean
lean/dk_math/DkMath/FLT/Seven/QuadraticCoprimeFactor.lean
lean/dk_math/DkMath/FLT/Seven/PrimitiveCyclotomicDepth.lean
```

Inspect these only if needed to determine whether an existing reusable theorem
already closes a gap:

```text
lean/dk_math/DkMath/FLT/Seven/SevenBaseTerminalRamifiedQuadraticInnerRoot.lean
lean/dk_math/DkMath/FLT/Seven/docs/STATUS.md
```

For the large status file, search for the exact identifiers/frontiers; do not
read unrelated historical sections exhaustively.

## 3. Questions to answer

Every answer in `report-000.md` must give exact theorem/structure identifiers
and file paths.

### Q1. Exact new p=7 endpoint

Record the complete type and dependency chain of:

```text
exists_powCoords_of_primeTraceOneImaginaryStrippedIdealPacket_seven
```

Confirm exactly which p=7 hypotheses are already discharged internally.
In particular, verify that no caller-supplied class-group hypothesis remains.

Also identify the element-level theorem supplying:

```text
Q.residual = delta^7
```

if it is separately exposed.

### Q2. Exact `PrimeTraceOneStrippedIdealPacket` invariant surface

Inventory every field of `PrimeTraceOneStrippedIdealPacket` and mark whether it
is relevant to a final p=7 arithmetic consumer.

At minimum trace:

```text
Q.adicSplit
Q.parent
Q.residual
Q.axis_eq
Q.parent_coordinate_coprime
Q.residual_coordinate_coprime
Q.residual_norm_ne_zero
Q.residual_axis_terminal
Q.residual_norm_pow
Q.residual_conj_ideal_coprime
Q.residual_span_eq
```

For `Q.adicSplit`, record the p=7 specializations of:

```text
gap_eq
residual_eq
distinguished_eq
coprime_a_b
prime_not_dvd_b
```

Do not merely restate field names; identify which data still mention the
original natural-number counterexample coordinates and which live purely in
`TraceOneInt (-2)`.

### Q3. Generic recurrence coordinates versus specialized seventh-power coordinates

Determine whether the following are already theorems, immediate corollaries,
or genuinely missing bridge lemmas:

```text
(traceOnePowCoords (-2) m n 7).1 = seventhPowerFst m n
(traceOnePowCoords (-2) m n 7).2 = seventhPowerSnd m n
```

The preferred proof route, if missing, should compare the two already checked
coordinate descriptions of

```text
(⟨m,n⟩ : TraceOneInt (-2))^7
```

rather than re-expanding the seventh power twice.

Record the minimal import boundary needed for these bridge lemmas.

Also determine whether the generic p=7 receiver can therefore be rewritten as:

```text
∃ m n,
  Q.residual.fst = seventhPowerFst m n ∧
  Q.residual.snd = seventhPowerSnd m n.
```

### Q4. Axis terminality and the seventh-root norm

Audit the exact checked chain connecting:

```text
Q.residual_axis_terminal
Q.residual = delta^7
```

to root-side 7-unit information.

Determine whether current APIs prove, without new mathematics:

```text
¬ (7 : ℤ) ∣ norm Q.residual
¬ (7 : ℤ) ∣ norm delta
```

and identify the exact theorem chain through `discrAxis (-2)`, `sevenAxis`,
norm multiplicativity, and primality.

Do not assume that `discrAxis (-2) = sevenAxis` is definitional; locate or
propose the smallest checked equality/adapter if required.

### Q5. Consequences of the explicit seventh-power factorization

Assuming the Q3/Q4 bridges, classify which of the following follow immediately
from existing p=7 lemmas:

```text
7 | Q.residual.snd
7 ∤ seventhPowerSndCore m n
49 | Q.residual.snd <-> 7 | n
Q.residual.fst mod 7 = m + 4*n
7 ∤ Q.residual.fst
```

For the last item, determine whether it follows from
`Q.residual_coordinate_coprime` together with `7 | Q.residual.snd`, from axis
terminality, or by another existing theorem.

Also answer a separate question:

```text
Does primitive/coprime coordinate data for delta^7 imply primitive/coprime
coordinates for delta itself in the current API?
```

Search for an existing theorem before proposing a new one.  Do not silently
assume root-coordinate primitivity.

### Q6. The critical parent-coordinate provenance boundary

This is the most important audit question.

The generic packet has:

```text
Q.parent = P.coord (g+u) u
Q.parent = discrAxis (-2) * Q.residual
```

The specialized p=7 tower has:

```text
cyclotomicSevenToTraceOne (g+u) u
sevenAxis * delta^7
```

Determine exactly what is currently checked between

```text
P.coord (g+u) u
```

for an arbitrary p=7 `PrimeTraceOneCoordinatePacket` and

```text
cyclotomicSevenToTraceOne (g+u) u.
```

Search for:

- a canonical p=7 `PrimeTraceOneCoordinatePacket` constructor;
- an equality theorem;
- conjugation/sign/orientation equivalence;
- coordinate permutation equivalence;
- a uniqueness theorem for primitive TraceOne representations of the same
  cyclotomic norm;
- an invariant-only bridge sufficient for the planned obstruction.

If only equality of norms is known, state explicitly:

```text
EQUAL NORM IS NOT AN ELEMENT/COORDINATE BRIDGE.
```

Do not infer the stronger relation.

### Q7. Specialized FLT7 reuse inventory

Classify existing `DkMath.FLT.Seven` lemmas into three groups:

```text
A. carrier-local / reusable
B. packet-specific but bridgeable
C. historical-tower dependent / unsafe for the first direct attack
```

At minimum classify the surfaces around:

```text
SeventhPowerCoordinates
AxisDivisibility
QuadraticCoprimeFactor
PrimitiveCyclotomicDepth
SevenBaseTerminalRamifiedQuadraticInnerRoot
```

For every B/C item, name the exact packet dependency that prevents immediate
reuse.

Do not classify a theorem as reusable merely because its statement mentions
`TraceOneInt (-2)`; inspect its assumptions/import chain.

### Q8. Direct ramified contradiction candidates

Using only checked data found in Q1–Q7, list the strongest honest candidate
contradiction routes.

For each candidate give:

```text
input facts
existing lemmas
missing theorem, if any
whether the missing item is API glue or new mathematics
```

Prioritize small routes involving:

```text
residual_coordinate_coprime
residual_axis_terminal
seventhPowerSnd = 7 * n * seventhPowerSndCore
fortyNine_dvd_seventhPowerSnd_iff
PrimeAdicPowerSplit at p=7
parent = axis * residual
```

A candidate is allowed to end with “arithmetically consistent; no
contradiction”.  That is preferable to inventing a false theorem.

### Q9. Historical missing-obligation comparison

Identify the exact current historical FLT7 terminal blocker recorded by the
specialized tower, including the relevant identifier such as
`InternalDepthFourCounterexampleReconstructionObligation` if it remains the
actual frontier.

Then answer:

```text
Does the new generic exact seventh-power receiver provide data that the old
blocker was missing?
```

Classify the answer as:

```text
YES — exact bridge identified
PARTIAL — related data, bridge missing
NO — logically different obligation
```

Do not claim that the old blocker is closed unless a theorem already composes
the surfaces.

### Q10. Away branch status

Record, but do not attack, the exact p=7 away-branch endpoint supplied by the
new generic routing:

```text
7 ∤ (z-y)
-> z-y = a^7
-> GTail 7 1 (z-y) y = b^7.
```

Identify which existing `AwaySeven*` entry packet is nearest to this data and
whether a bridge already exists.

This is reconnaissance only; FLT7TC-000 remains focused on the ramified
TraceOne closure.

### Q11. Dependency and circularity audit

Propose the smallest import set for FLT7TC-001.

Explicitly identify imports/theorems that would be circular because they
already depend on a desired terminal FLT7 contradiction or on a later historical
packet reconstructed from one.

Check whether the candidate reusable p=7 files introduce any project axiom,
`sorryAx`, or known proof hole into the intended new dependency surface.

### Q12. Exact next theorem surface

End by proposing the exact declarations FLT7TC-001 should implement.

Prefer a small surface such as:

```text
traceOnePowCoords_negTwo_seven_fst
traceOnePowCoords_negTwo_seven_snd
exists_seventhPowerCoords_of_primeTraceOneStrippedIdealPacket_seven
<root 7-unit bridge, if genuinely available>
```

Use actual repository naming conventions discovered in the audit rather than
blindly preserving these suggested names.

If Q6 shows that the parent provenance bridge must come first, revise the next
checkpoint accordingly and say so explicitly.

## 4. Required report structure

Write `report-000.md` in this order:

1. Executive conclusion
2. Exact checked p=7 starting endpoint
3. `PrimeTraceOneStrippedIdealPacket` invariant table
4. Generic recurrence -> specialized seventh-power coordinate audit
5. Axis terminality / root 7-unit audit
6. Parent-coordinate provenance audit
7. Specialized FLT7 reuse matrix
8. Direct ramified contradiction candidates
9. Historical blocker comparison
10. Away-branch nearest-entry audit
11. Minimal dependency surface for the next checkpoint
12. Proposed exact FLT7TC-001 theorem surface
13. Risks / stop conditions
14. Outcome

## 5. Outcome classification

Use exactly one primary outcome.

```text
Outcome A — DIRECT P7 COORDINATE CONSUMER SURFACE GREEN
```

Use when the generic seventh-power receiver connects cleanly to the specialized
seventh-power arithmetic and there is a concrete next obstruction theorem that
does not first require parent-coordinate canonicalization.

```text
Outcome B — P7 POWER BRIDGE GREEN; PARENT PROVENANCE BRIDGE IS NEXT
```

Use when the residual seventh-power coordinate bridge is clean but the generic
parent `P.coord` cannot yet be identified strongly enough with
`cyclotomicSevenToTraceOne`.

```text
Outcome C — CURRENT GENERIC PACKET IS TOO WEAK FOR DIRECT P7 CLOSURE
```

Use when even after specializing the recurrence and axis facts, the packet lacks
an invariant required by every noncircular direct obstruction route.

```text
Outcome D — PROPOSED DIRECT ROUTE IS FALSE OR CIRCULAR
```

Use when a proposed key implication has a counterexample, or the only apparent
closure reuses a theorem that already contains the desired FLT7 contradiction.

Outcomes B/C/D are valid research results.  Do not force Outcome A.

## 6. Restrictions

- no production Lean source changes;
- no new committed test/probe module;
- no theorem renaming or refactor;
- no public facade update;
- no `sorry`, `sorryAx`, `admit`, new `axiom`, or `unsafe` shortcut;
- no equality-of-norms -> equality-of-elements inference;
- no assumption that root coordinates are coprime;
- no assumption that `discrAxis (-2)` and `sevenAxis` are interchangeable
  without checking the adapter;
- no import of a specialized final contradiction theorem as evidence that the
  direct route works;
- no claim of FLT7 unconditionality from ramified-branch closure alone;
- no attack on the away branch beyond inventory in this checkpoint.

## 7. Verification

This checkpoint is reconnaissance, so a full rebuild is not required.

Run lightweight source searches and `#check`/temporary scratch compilation as
needed.  If useful, verify only small existing targets such as:

```text
lake build DkMath.FLT.Prime.PrimeTraceOneCoordinateReceiver
lake build DkMath.FLT.Seven.SeventhPowerCoordinates
lake build DkMath.FLT.Seven.AxisDivisibility
```

Do not spend time rebuilding the full historical FLT7 tower unless the audit
finds an inconsistency.

Commit only `report-000.md` with a concise reconnaissance commit message.
