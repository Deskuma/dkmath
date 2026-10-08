# Successor degree / factor support / unit gauge — Findings 002

Date: 2026-10-04. Branch: `research/GapFocusing-ExponentGauge-Ultra-261004-v0`.
Initial HEAD: `9f7c38bf4`; initial working tree clean.
Lean / Mathlib: `v4.34.1`.

This campaign investigates the questions in [instruction-002](instruction-002.md)
under the user's request to read and carry them out. The document's candidate
reset interpretation and possible outcomes are research questions, not
assumptions to encode as hypotheses.

## Current status

- Successor identities built over all commutative semirings.
- Natural/integer factor support and polynomial separation are checked.
- Power subgroup product, intersection, and genuine quotient-group CRT are checked.
- Existing `SameUnitPowerClass` agrees with equality in the actual unit quotient.
- Outcome B is selected. Primitive-prime counterexamples and source audit are checked.
- The 58 new production declarations passed the explicit dependency audit.
- Focused and full facade validation passed; the durable report is complete.

## Checkpoint history

### 2026-10-04 checkpoint 01 — successor identities checked

`lake build DkMath.NumberTheory.GapFocusing.Successor` passed (2787 jobs).

```text
GN_(d+1)(x,u) = (x+u)*GN_d(x,u)+u^d
GN_(d+1)(x,u) = u*GN_d(x,u)+(x+u)^d
```

Both hold at `d=0`, zero gap, and zero divisors. The proof reuses the existing
homogeneous shell recurrence and the Cosmic Formula, without numerical
cancellation.

At anchor `1`, the recurrence gives constant remainder `1`. Over every
commutative ring this is an explicit Bézout identity and proves `IsCoprime`.
For natural numbers the appropriate notion is `Nat.Coprime`; a separate
natural support proof is in progress.

### 2026-10-04 checkpoint 02 — adjacent factor support checked

`lake build DkMath.NumberTheory.GapFocusing.Support` passed (2788 jobs).

- Arbitrary ring common divisors divide `u^d` and `(x+u)^d`.
- Natural common prime divisors divide both `x` and `u`.
- Primitive natural pairs give `Nat.Coprime` adjacent GN at every degree.
- At degree at least two, common prime support is exactly common coordinate
  support, and adjacent natural coprimality is equivalent to primitive coordinates.
- Over any commutative ring, `IsCoprime x u` gives Bézout coprimality of the
  adjacent kernels. The integer gcd theorem permits negative coordinates.
- Nonprimitive `(2,2)` produces adjacent values `6,28`, so the primitive-pair
  hypothesis cannot simply be dropped.

### 2026-10-04 checkpoint 03 — polynomial separation and ring CRT checked

`lake build DkMath.NumberTheory.GapFocusing.PolynomialSuccessor` passed (2814 jobs).

- Adjacent unit-anchor polynomials are Bézout coprime over every coefficient
  ring, including degree zero. Integral `K_d` and `K_(d+1)` have explicit witnesses.
- Nontrivial divisor-index sets are disjoint, and adjacent positive-degree
  root sets share only the trivial phase.
- Adjacent kernel ideals are comaximal and have an actual quotient-ring CRT
  equivalence, with the canonical map on representatives checked.
- This ring CRT is separate from a quotient by power images in a unit group.

### 2026-10-04 checkpoint 04 — power subgroups and quotient-group CRT checked

The neutral `DkMath.Lib.Algebra.PowerSubgroup` implementation passed its
focused build. For any commutative group and coprime `n,m`:

```text
G^n ⊔ G^m = G
G^n ⊓ G^m = G^(nm)
G/G^(nm) ≃* (G/G^n) × (G/G^m).
```

The subgroup is the range of the actual power homomorphism. Explicit integer
Bézout coefficients give the product and simultaneous-power constructions.
The quotient map is surjective and its kernel is the intersection; its
representative formula is checked. No finiteness, torsion-freeness, or
surjectivity of either power map is assumed. Adjacent exponents include `d=0`.

### 2026-10-04 checkpoint 05 — actual quotient and existing class bridge checked

`lake build DkMath.NumberTheory.GapFocusing` passed (2822 jobs).
`SuccessorGauge` identifies `SameUnitPowerClass n u v` with membership of
`u*v⁻¹` in the image of the power map, equivalently equality in the quotient.
Agreement at coprime `n,m` is equivalent to agreement at `nm`; the successor
specialization includes zero. This is a bridge to the existing gauge API,
not a map from GN prime support to the gauge.

The polynomial ring CRT also has an explicit interpolation witness:
`P=A*K_(d+1)-B*(X+1)*K_d`, with residues `A,B` modulo the two kernels.

### 2026-10-04 checkpoint 06 — Outcome B selected

The polynomial kernels generate comaximal ideals. The power images are
subgroups of an arbitrary commutative group. Each has a genuine CRT theorem,
but their carriers, maps, and arithmetic meaning differ. No identification
of those objects, or of GN prime support with a normalized FLT unit class,
was constructed. The shared Bézout reasoning is substantive, but insufficient
for Outcome A. This decision does not assert that a future bridge is impossible.

### 2026-10-04 checkpoint 07 — primitive-prime audit checked

The document-local check proves `GN_5(1,1)=31`, `GN_6(1,1)=63`, adjacent
coprimality, and absence of any primitive prime at base `(2,1)`, degree six.
All primes of 63 already occur at degree two or three. Thus freshness against
the immediate predecessor differs from freshness against all earlier degrees.

The positive primitive-coordinate theorem does supply a prime in every next
GN value that is absent from its immediate predecessor, for `d>0`.
Current production Zsigmondy existence handles odd prime degree with the
additional hypothesis `d∤a-b`; its omitted cases are not an exact exception
classification. General classical Zsigmondy was not imported or assumed.
Existing valuation research endpoints retain their `sorryAx` boundary; new
regressions and the audited safe endpoints do not. Details are in
[primitive-prime-audit-002](primitive-prime-audit-002.md).

### 2026-10-04 checkpoint 08 — production audit and boundary regressions checked

`lake build DkMathTest.NumberTheory.GapFocusingSuccessorCalibration
DkMathTest.NumberTheory.GapFocusingSuccessorAxiomAudit` passed (2824 jobs).
All 58 declarations in the five new production files were printed individually;
their dependency lists contain only `propext`, `Classical.choice`, `Quot.sound`
or are empty. Boundary calibrations cover degree zero, zero divisors in the
coefficient ring, polynomial interpolation, and degree-zero/one unit classes.

### 2026-10-04 checkpoint 09 — final validation and report complete

The combined focused run passed (2828 jobs), including all four new test/audit
modules and both Instruction 001 regression modules. `lake build DkMath.Lib
DkMath` passed (10360 jobs); its five pre-existing `sorry` warnings are recorded
separately. The document-local primitive check passed with the expected two
old research `sorryAx` endpoints, and no new one.

All 58 production and 12 named regression declarations passed the source-to-log
dependency coverage check. Sixteen anonymous regression examples compiled.
The forbidden-token scan of all ten new Lean files had zero matches.
See [validation-002](validation-002.md) and [report-002](report-002.md).

## Next mathematical action

Instruction 002 is complete with Outcome B. A future arithmetic bridge needs
an explicit carrier and a proved map before stronger reset terminology is
justified. The full all-index primitive-prime theorem is also a separate task;
it cannot be inferred from the adjacent-degree result.
