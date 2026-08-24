# GWSS-003E Gram / polarization bridge decision — implementation report

Date: 2026-08-22

Repository: `Deskuma/dkmath`

## 1. Orientation and exact state

The global objective remains

```text
zero configuration
  -> independent source
  -> off-critical detector
  -> arithmetic control
  -> centered-coordinate uniqueness
  -> RiemannHypothesis
```

This audit is GWSS-003E.  It started on branch
`wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`, at HEAD
`e35af50e5c726bff7ca37e4d8a55276817ec8021`, with a clean working tree before
the implementation edit.  The Lean toolchain is 4.32.2
(`leanprover/lean4:v4.32.2`).  The 0033 instructions, 0034 report, provider
decision and quantitative-homogeneity modules, off-critical witness,
quadraticization, whole-surface energy, and `DkMath.Analysis.MellinQuadraticGramKernel`
APIs were read before editing.

The load-bearing boundary is unchanged:

```text
h_off = qIm * h_mass
```

003C showed that first-order linear/norm estimates transport and cancel this
scalar.  003D identified a genuinely source-derived quadratic candidate, but
no bridge to the synthesized GWSS-002 witness.

## 2. Existing vertical and whole-surface polarization

The repository already proves the fixed-`τ = 0` source-side identities in
`PascalCenteredXiPrimeSideQuadraticizationAudit.lean`:

```text
pascalCenteredXiPrimeSideQuadraticization_polarization_pointwise
pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature_polarization_pointwise
pascalCenteredXiPrimeSideQuadraticization_verticalSurface_eq_shiftedEnergyDifference
pascalCenteredXiPrimeSideQuadraticization_shiftedEnergy_order_iff_vertical_nonneg
pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature_polarization_pointwise
pascalCenteredXiPrimeSideQuadraticization_wholeSurface_eq_shiftedEnergyDifference
pascalCenteredXiPrimeSideQuadraticization_wholeShiftedEnergy_order_iff_scalarSurface_nonneg
```

The vertical and whole identities have the exact shape

```text
4 * sourceSurface = shiftedPlusEnergy - shiftedMinusEnergy.
```

Both shifted energies are nonnegative, including the whole finite surface
with its source-derived horizontal symmetrization.  The existing order
equivalences are only equivalences with the sign of the corresponding source
surface; they do not prove either ordering.  In particular, positivity of the
two energies alone is not a provider.

## 3. Fixed-reference scaling audit

The new focused module is
`DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessGramPolarizationBridgeAudit.lean`.

It proves
`normSq_shifted_difference_real_scale`:

```text
F = conj(F) ->
normSq(q * F + 1) - normSq(q * F - 1) = 4 * q * F
```

for real `q`.  Thus a fixed reference can preserve a term linear in `q`, in
contrast with bare quadratic scaling, which carries `|q|²`.  This is an exact
algebraic distinction only; it supplies no independent ordering of the two
shifted energies.

The certificate
`shifted_energy_nonneg_does_not_determine_order` gives opposite orderings for
the real features `1` and `-1` while all four entries are norm squares and
therefore nonnegative.

## 4. Target-witness source-feature compatibility

The GWSS-002 witness is the synthesized weight

```text
h_target = ∑ i, c_i * H_{ε,τ_i}
```

with target-dependent complex inverse-matrix coefficients.  The existing
quadraticization instead uses the fixed `τ = 0` logarithmic-box source feature
and its finite prime/archimedean/elementary/horizontal aggregate.

The current API provides no theorem that:

```text
sourceFeature (h_target)
sourceFeature (q * h_target) = q * sourceFeature h_target
wholeArithmeticSurface (h_target)
  = normalized integral of sourceFeature (h_target)
```

for the synthesized witness.  In particular, no general-`τ` source feature,
coefficient-compatible adjoint, or target-dependent whole-surface bridge was
found.  The existing `τ = 0` identities must not be silently generalized.

Therefore:

```text
general-τ source feature:              GAP
synthesized-witness source feature:    GAP
off-critical source aggregate scaling: GAP
whole-surface target compatibility:    GAP
```

The first missing interface is a source-preserving finite feature for the
actual synthesized witness, with scalar linearity and a whole-surface identity.
It must be proved from existing arithmetic/source APIs; it must not be added as
an assumed provider structure.

## 5. Shifted-energy order / dominance audit

The fixed-`τ = 0` source API supplies:

```text
shifted-energy nonnegativity: FOUND
vertical polarization:        FOUND
whole-surface polarization:    FOUND
order equivalence:             FOUND
independent order/dominance:   NOT FOUND
```

No source-side theorem proves P1, P2, or P3 for the same target witness:

```text
P1: one shifted energy dominates the other
P2: the shifted energies are equal
P3: an independent quantitative gap is controlled
```

The vertical identities alone would also leave the top-horizontal term outside
the current synthesized witness bridge.  The whole-surface fixed-source
identity retains that term, but does not repair the target-witness gap.

## 6. Questions required by GWSS-003E

```text
Q1. Does the existing candidate apply to the same GWSS-002 witness?
    No.  Only the fixed τ = 0 source feature is implemented.

Q2. Does a fixed reference preserve qIm linearly?
    Yes algebraically, by normSq_shifted_difference_real_scale; no target
    source bridge transports that identity to h_off.

Q3. Does source positivity independently order shifted energies?
    No.  Only nonnegativity and sign/order equivalences are available.

Q4. Does the whole finite surface participate?
    Yes for the fixed source-side whole-box feature, including horizontal
    symmetrization; no for the synthesized GWSS-002 witness.

Q5. What is the first missing provider theorem?
    A source-preserving quadraticization bridge for h_target, with scalar
    linearity and an exact whole-surface arithmetic identity.  After that,
    an independent P1/P2/P3 source-side order theorem would still be needed.
```

## 7. Primary classification and next Gap

Exactly one primary classification is selected:

```text
TARGET-WITNESS-QUADRATICIZATION-BRIDGE-GAP
```

Secondary findings:

```text
vertical shifted-energy polarization:       FOUND
whole-surface shifted-energy polarization:   FOUND
shifted-energy nonnegativity:               FOUND
fixed-reference linear cross-term:          FOUND
general-τ source feature:                   GAP
synthesized witness source feature:         GAP
off-critical source aggregate factorization: GAP
independent shifted-energy dominance:       NOT FOUND
horizontal compatibility for h_target:      GAP
```

The polarization candidate has not collapsed algebraically: its fixed
reference genuinely exposes a linear cross-term.  It nevertheless does not
survive as a provider because the exact bridge to the target-dependent witness
is absent, and no independent shifted-energy order is available.

GWSS-004 remains unauthorized.  No classical Guinand--Weil infrastructure,
full Weil positivity, Li, `T -> infinity`, new zero-avoidance theory, DkReal,
or RH deduction was started.

## 8. Verification

Focused verification passed:

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessGramPolarizationBridgeAudit.lean
```

The new load-bearing certificates were axiom-audited.  Their footprint is the
standard:

```text
propext
Classical.choice
Quot.sound
```

No `sorry`, `admit`, `native_decide`, new axiom, unproved positivity order,
unproved limit exchange, RH assumption, Weil criterion, or Li criterion was
introduced.  Commit, push, CI, and GWSS-004 work were not performed.
