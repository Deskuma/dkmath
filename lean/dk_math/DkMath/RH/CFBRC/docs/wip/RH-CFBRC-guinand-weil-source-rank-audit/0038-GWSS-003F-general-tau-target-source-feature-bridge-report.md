# GWSS-003F general-`τ` target source-feature bridge — implementation report

Date: 2026-08-22

Repository: `Deskuma/dkmath`

## 1. Orientation and bounded scope

The implementation was performed on branch
`wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`, at HEAD
`0acdf2b007f6a8d478aa08c11ad6b0f6d75d8ad5`.  The working tree was clean
before the edit.  The Lean toolchain is 4.32.2
(`leanprover/lean4:v4.32.2`).

The global objective remains

```text
zero configuration
  -> independent source
  -> off-critical detector
  -> arithmetic control
  -> centered-coordinate uniqueness
  -> RiemannHypothesis
```

This report closes only GWSS-003F.  The 0035 decision, 0036 report, fixed
polarization audit, quantitative homogeneity audit, off-critical witness,
general arithmetic specialization, finite source quadraticization, and
finite explicit-formula APIs were read before editing.  No GWSS-004,
Guinand--Weil criterion, Li criterion, infinite-height limit, new zero
avoidance theory, DkReal route, or RH deduction was started.

## 2. New module and feature boundary

The focused module is
`DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessGeneralTauSourceBridgeAudit.lean`.

For `τ ≠ 0` it defines

```text
K_τ(z) = (exp(τ z) - 2 + exp(-τ z)) / τ²
Φ_τ(z,u) = K_τ(z) exp(u z).
```

The theorem
`pascalCenteredXiMellinSecondDifferenceWeight_eq_normalized_generalTauBoxFeature_integral`
proves the exact representation

```text
H_{ε,τ}(z) = (2ε)⁻¹ ∫_{-ε}^{ε} Φ_τ(z,u) du
```

from the existing nonzero-`τ` kernel factorization and Mellin logarithmic
average.  The feature is therefore not a renamed `τ = 0` quadratic weight.

## 3. Source bridges proved

The following finite source interfaces compile without `sorry`, `admit`, or
an added axiom.

```text
generalTauVerticalBoxFeature_integral_eq_weight_mul_amplitude
generalTau_weighted_vertical_source_eq_normalized_aggregate
generalTauTopBoxFeature_integral_eq_weight_mul_amplitude
generalTau_top_horizontal_source_eq_normalized_aggregate
```

The right-edge rectangle integrability provider is discharged using the
existing finite vertical-amplitude certificate and compact continuity of the
new general-`τ` kernel.  The top-horizontal rectangle integrability provider
is discharged analogously from the existing top-amplitude interval
certificate.  These are finite source statements; they retain the finite
cutoff and the top edge.

The finite witness layer also contains

```text
pascalCenteredXiMellinWitnessWeight_eq_normalized_generalTauWitnessBoxFeature_integral
pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature_integral_eq_witnessWeight_mul_amplitude
```

Thus the synthesized weight `Σ i, c i H_{ε,τᵢ}` has an exact logarithmic-box
feature representation, and its right-edge source fibre has the corresponding
finite linear lift.  The aggregate synthesized right-edge theorem keeps its
finite rectangle integrability as an explicit hypothesis:

```text
pascalCenteredXiMellinGeneralTauWitness_weighted_vertical_source_eq_normalized_aggregate
```

This explicit hypothesis is intentional.  It is not silently replaced by a
whole-surface theorem or by an unproved exchange of a target-dependent finite
sum with the source integrals.

## 4. Fixed-reference polarization

The module records the requested generic complex reference identities:

```text
normSq_shifted_difference_one_eq_four_mul_re
normSq_shifted_difference_I_eq_four_mul_im
```

They state, for arbitrary `F : ℂ`,

```text
normSq(F + 1) - normSq(F - 1) = 4 F.re
normSq(F + I) - normSq(F - I) = 4 F.im.
```

These are algebraic polarization identities only.  They do not provide an
ordering of shifted energies or a positivity theorem for the synthesized
source.

## 5. Remaining load-bearing gap

The new results do not yet prove one exact whole-source identity for the
actual synthesized witness.  In particular, the following combined bridge
is not asserted:

```text
finite arithmetic approximant of h_target
  = normalized whole source feature of h_target
```

The missing piece is the target-dependent horizontal/whole aggregation and
its exact compatibility with the finite arithmetic ledger and off-critical
scalar transport.  The fixed `τ = 0` whole-surface API remains specialized
and is not reused as though it were general `τ`.

Accordingly, the single primary classification is:

```text
TARGET-WITNESS-SOURCE-BRIDGE-REPRESENTATION-GAP
```

Secondary findings:

```text
nonzero-τ logarithmic-box feature:                 FOUND
single-basis weight averaging:                     FOUND
single-basis finite vertical bridge:               FOUND
single-basis top-horizontal bridge:                FOUND
synthesized weight feature representation:         FOUND
synthesized vertical fibre lift:                   FOUND
synthesized whole finite source bridge:             GAP
independent shifted-energy dominance:               NOT FOUND
```

The result is a genuine source-interface reduction of the earlier gap, not a
positivity provider.  No sign, order, limit exchange, RH-equivalent source,
or exact-zeta identification has been introduced.

## 6. Verification

Focused verification passed:

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessGeneralTauSourceBridgeAudit.lean
```

`git diff --check` passed.  The new module contains no `sorry`, `admit`,
`native_decide`, or `axiom`.  Commit, push, CI, and later GWSS stages were not
performed.
