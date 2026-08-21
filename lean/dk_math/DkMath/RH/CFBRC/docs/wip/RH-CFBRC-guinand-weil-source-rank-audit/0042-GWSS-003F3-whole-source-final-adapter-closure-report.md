# GWSS-003F3 whole-source final adapter closure — implementation report

Date: 2026-08-22

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`

Starting HEAD: `599cd0a251b024ff23fcc0f2c2635577335f8ab4`.

## Scope and files

The supplied 0041 document was treated as the bounded implementation
contract.  The user request was to implement that contract and maintain the
Lean docstrings.  Only the two 0040 adapter gaps were addressed:

* outer-variable integrability of the synthesized vertical/top aggregates;
* the arbitrary differentiable-weight finite vertical source ledger.

The focused Lean module was extended:

```text
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessGeneralTauSourceBridgeAudit.lean
```

This report was added at:

```text
DkMath/RH/CFBRC/docs/wip/RH-CFBRC-guinand-weil-source-rank-audit/
0042-GWSS-003F3-whole-source-final-adapter-closure-report.md
```

No GWSS-004, Guinand--Weil positivity, Li criterion, height limit, new
zero-avoidance, source-rank family, DkReal route, or RH deduction was started.
No commit, push, PR, CI, or merge was performed.

## Aggregate-integrability adapter

The new declarations

```text
pascalCenteredXiMellinGeneralTauWitnessVerticalAggregatedBoxFeature_intervalIntegrable
pascalCenteredXiMellinGeneralTauWitnessTopAggregatedBoxFeature_intervalIntegrable
```

use the existing synthesized `IntegrableOn` rectangle certificates.  Each
certificate is converted to the restricted product measure

```text
(volume.restrict A).prod (volume.restrict B)
```

and `Integrable.swap.integral_prod_left` supplies integrability of the outer
logarithmic-variable integral.  The right-edge interval is converted using
`-T ≤ T`, obtained from `W.rectangle.hT`.  The top interval handles both
orientations by cases on `σ ≤ 1 - σ`; the reversed case is transported by the
negative interval integral.  Thus no totalized interval integral is used as a
surrogate for integrability.

The existing conditional whole-source theorem remains available.  The new
public theorem

```text
pascalCenteredXiMellinGeneralTauWitness_whole_source_eq_normalized_aggregate
```

removes `hV` and `hT` and proves the unconditional normalized whole-source
representation for `ε > 0` and nonzero selected `τ` values.

## Vertical ledger and orientation

The generic theorem

```text
pascalCenteredXiMellinGeneralTau_vertical_source_ledger
```

proves, for every differentiable complex weight `h`,

```text
2 * PrimeCutoff(h) + 2 * Arch(h) + 2 * Elem(h)
  = 2 * I * VerticalSource(h).
```

The pointwise identity is proved first from the definitions:

```text
(h * prime) * I + (h * arch) * I + (h * elem) * I
  = I * (h * (prime + arch + elem)).
```

The interval lift reuses the public archimedean and elementary integrability
theorems.  The finite prime cutoff needed a local adapter because the
existing continuity theorem in `PascalCenteredXiPrimeRightEdgeTransport` is
private.  The adapter proves continuity of the finite von-Mangoldt sum and
then interval-integrability of the oriented cutoff integrand; it does not
rebuild dominated convergence or use a cutoff limit.

The synthesized specialization

```text
pascalCenteredXiMellinGeneralTauWitness_vertical_source_ledger
```

uses `pascalCenteredXiMellinWitnessWeight_differentiable` and discharges the
previous `hvertical` premise.  Consequently the unconditional theorem

```text
pascalCenteredXiMellinFiniteArithmeticApproximant_eq_two_mul_I_mul_wholeSource
```

is available without a vertical-ledger hypothesis.  The composed finite
representation is also exposed as

```text
pascalCenteredXiMellinFiniteArithmeticApproximant_eq_two_mul_I_mul_normalizedWholeFeatureIntegral
```

and does not use `X → ∞` or an exact zero-moment rewrite.

## `q.im` transport and classification

The existing coefficient-scaling results remain unchanged.  The new theorem

```text
pascalCenteredXiMellinGeneralTauWitness_qIm_unconditional_finite_representation
```

applies the unconditional finite and normalized whole-source links to the
coefficient family `fun i => (q.im : ℂ) * c i`.  This certifies linear
transport of the already-isolated off-critical scalar; it does not imply
`q.im = 0`, positivity, or an asymmetric energy inequality.

The representation layer is closed:

```text
TARGET-WITNESS REPRESENTATION LAYER CLOSED
```

The single primary classification is:

```text
TARGET-WITNESS-SHIFTED-ENERGY-DOMINANCE-GAP
```

The next exact missing provider is an independent source-side theorem for
the actual synthesized whole feature, such as one shifted energy dominating
the other, equality of the shifted energies, or a controlled asymmetric gap.
That provider is outside GWSS-003F3 and no attempt was made to prove it.

## Verification and axiom footprint

Focused verification passed:

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessGeneralTauSourceBridgeAudit.lean
git diff --check
```

The load-bearing declarations were axiom-audited.  Each has the expected
footprint only:

```text
propext
Classical.choice
Quot.sound
```

No `sorry`, `admit`, `native_decide`, new `axiom`, RH assumption, Weil or Li
criterion, or unproved limit exchange was introduced.
