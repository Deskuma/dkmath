# IPSM-032 — CS8 closeout and upper-envelope strength audit

Date: 2026-08-14

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v0`

Status: CS8 Green-B / named obstruction / no sign theorem / no RH theorem / no limit exchange

## 0. Review result

`PascalCenteredXiPrimeSideArithmeticUpperEnvelopeAudit.lean` is accepted as the new chained module after the frozen `PascalCenteredXiPrimeSideQuadraticizationAudit.lean`.

The implementation correctly records:

```text
CS7 lower one-sided smoothing wrapper             GREEN
CS7 upper one-sided smoothing wrapper             GREEN
small-box condition eventual on ε → 0+            GREEN
finite four-component source ledger               GREEN
independent vanishing arithmetic upper envelope   OPEN
```

The public import in `DkMath.RH` is also present.

The old 3000+ line quadraticization module remains unchanged after the CS6--CS7 closeout, as intended.

## 1. Important logical upgrade

Before searching further for an arbitrary vanishing envelope, audit the logical strength of the envelope contract itself.

Define a fixed-window contract in the new chained module, for example:

```lean
def PascalCenteredXiPrimeSideVanishingUpperEnvelopeAt
    (W : PascalCenteredXiResidueTransportWindow) : Prop :=
  ∃ r : ℝ → ℝ,
    Tendsto r (𝓝[>] 0) (nhds 0) ∧
      ∀ᶠ ε : ℝ in 𝓝[>] 0,
        pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W ≤ r ε
```

This definition is only an audit surface.  It is not an independent provider.

## 2. CS9-A — envelope implies fixed-defect nonpositivity

This direction is already available through the CS5 adapter:

```lean
pascalCenteredXiFixedDefect_nonpos_of_endpoint_le_vanishingEnvelope
```

Target wrapper:

```lean
theorem pascalCenteredXiPrimeSideVanishingUpperEnvelopeAt_imp_fixedDefect_nonpos
    (W : PascalCenteredXiResidueTransportWindow) :
    PascalCenteredXiPrimeSideVanishingUpperEnvelopeAt W →
      pascalCenteredXiFixedSecondMomentDefectFunctional W.R ≤ 0 := by
  ...
```

Do not reprove the limit argument.

## 3. CS9-B — fixed-defect nonpositivity produces a canonical envelope

The converse should follow from the CS7 upper smoothing estimate.

Assume:

```text
fixedDefect(W.R) ≤ 0.
```

Choose the canonical envelope

```lean
r ε := pascalCenteredXiPrimeSideQuadraticizationCommonSourceSmoothingEnvelope ε W.R
```

Its limit is already Green:

```lean
tendsto_pascalCenteredXiPrimeSideQuadraticizationCommonSourceSmoothingEnvelope_zero
```

The small-box condition is eventually Green:

```lean
eventually_pascalCenteredXiPrimeSideQuadraticization_smallBox
```

On that eventual set, the CS7 upper one-sided estimate gives

```text
endpoint(ε,W)
≤ fixedDefect(W.R) + smoothingEnvelope(ε,W.R)
≤ smoothingEnvelope(ε,W.R).
```

Target:

```lean
theorem pascalCenteredXiPrimeSideVanishingUpperEnvelopeAt_of_fixedDefect_nonpos
    (W : PascalCenteredXiResidueTransportWindow)
    (hD : pascalCenteredXiFixedSecondMomentDefectFunctional W.R ≤ 0) :
    PascalCenteredXiPrimeSideVanishingUpperEnvelopeAt W := by
  ...
```

No zero-side theorem is needed for this converse; it is only CS7 approximation algebra.

## 4. CS9-C — exact fixed-window equivalence

Combine CS9-A and CS9-B:

```lean
theorem pascalCenteredXiPrimeSideVanishingUpperEnvelopeAt_iff_fixedDefect_nonpos
    (W : PascalCenteredXiResidueTransportWindow) :
    PascalCenteredXiPrimeSideVanishingUpperEnvelopeAt W ↔
      pascalCenteredXiFixedSecondMomentDefectFunctional W.R ≤ 0 := by
  ...
```

This theorem is a strength audit.  It must not be presented as a new sign provider.

## 5. CS9-D — combine with the already proved zero-side nonnegativity

For every residue transport window, `W.circle_safe` supplies the safe-radius hypothesis required by:

```lean
pascalCenteredXiFixedSecondMomentDefectFunctional_nonneg
```

Therefore, at a fixed `W`, the upper-envelope contract should be equivalent to defect vanishing:

```lean
theorem pascalCenteredXiPrimeSideVanishingUpperEnvelopeAt_iff_fixedDefect_eq_zero
    (W : PascalCenteredXiResidueTransportWindow) :
    PascalCenteredXiPrimeSideVanishingUpperEnvelopeAt W ↔
      pascalCenteredXiFixedSecondMomentDefectFunctional W.R = 0 := by
  ...
```

Proof idea:

```text
envelope
→ fixed defect ≤ 0
→ fixed defect = 0       using existing fixed defect ≥ 0

fixed defect = 0
→ fixed defect ≤ 0
→ canonical smoothing envelope exists
```

This use of zero-side nonnegativity is allowed only for logical-strength classification.  It is not an arithmetic proof of the envelope.

## 6. CS9-E — finite zero-window interpretation

The existing fixed-defect detector gives:

```lean
pascalCenteredXiFixedSecondMomentDefectFunctional_eq_zero_iff
```

Hence derive the local interpretation:

```lean
theorem pascalCenteredXiPrimeSideVanishingUpperEnvelopeAt_iff_all_window_zeros_critical
    (W : PascalCenteredXiResidueTransportWindow) :
    PascalCenteredXiPrimeSideVanishingUpperEnvelopeAt W ↔
      ∀ ρ ∈ pascalCriticalMirrorZeroWindowFinset W.R,
        ρ.re = (1 : ℝ) / 2 := by
  ...
```

This is the key firewall theorem.

It says that, for a fixed finite transport window, an arbitrary vanishing upper-envelope contract is already exactly as strong as excluding off-critical zeros in that window.

## 7. Do not yet assert a global RH equivalence for transport windows

There is already a global theorem:

```lean
PascalCenteredXiFixedDefectVanishesOnSafeRadii ↔ RiemannHypothesis
```

However, do not immediately claim

```text
(∀ W, VanishingUpperEnvelopeAt W) ↔ RH
```

unless the coverage relation between arbitrary safe radii / arbitrary nontrivial zeros and the available `PascalCenteredXiResidueTransportWindow` structure is explicitly audited.

A transport window carries more data than a radius.  Do not silently assume every required safe radius is realized by an admissible `W`.

## 8. Consequence for the research strategy

If CS9 is Green, then the current CS8 gap is reclassified.

Old reading:

```text
we need a small missing upper-bound lemma
```

Correct reading:

```text
a vanishing upper envelope at fixed W
is itself equivalent to fixed-window criticality.
```

Therefore repeatedly searching for an abstract function `r ε → 0` is not progress by itself.

The next mathematical input must be source-specific and must arise before the target is repackaged as an arbitrary envelope.

## 9. CS10 candidate — finite source cancellation mechanism audit

After CS9 strength classification, inspect the finite source ledger componentwise:

```text
prime-mode sum
archimedean correction
elementary correction
top-horizontal fixed-Xi contribution
```

The purpose is not to assign arbitrary signs to the four pieces.  Instead determine whether an exact source-level cancellation/decomposition exists that produces a quantitatively controlled remainder independently of the zero-side defect.

Priority questions:

```text
1. Can the prime-mode source be paired under t ↔ -t before integration?
2. Which correction terms are exact conjugate/even partners under the same pairing?
3. Can the full finite ledger be rewritten as a real integral of a named arithmetic density?
4. Does that density admit a source-derived square / covariance / monotonicity decomposition?
5. If no such decomposition exists, record the exact arity/sign obstruction rather than inventing a provider.
```

Do not return to the already closed generic Gram route unless a new concrete coefficient-adjoint identity is found.

## 10. Module chain

Keep the split introduced by IPSM-031.

Recommended new module for CS9:

```text
DkMath.RH.CFBRC.PascalCenteredXiPrimeSideUpperEnvelopeStrengthAudit
```

with

```lean
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideArithmeticUpperEnvelopeAudit
```

If CS9 closes, CS10 should go into another new module rather than extending CS9 indefinitely.

Suggested chain:

```text
PascalCenteredXiPrimeSideQuadraticizationAudit
  → PascalCenteredXiPrimeSideArithmeticUpperEnvelopeAudit
  → PascalCenteredXiPrimeSideUpperEnvelopeStrengthAudit
  → PascalCenteredXiPrimeSideFiniteSourceCancellationAudit
```

## 11. Acceptance checklist

```text
[ ] old quadraticization module unchanged
[ ] ArithmeticUpperEnvelopeAudit imported, not copied
[ ] fixed-window envelope contract named explicitly
[ ] envelope → fixed defect ≤ 0 uses existing CS5 adapter
[ ] converse uses canonical CS7 smoothing envelope
[ ] small-box eventuality is used explicitly
[ ] envelope iff fixed-defect nonpositive proved
[ ] zero-side nonnegativity used only for strength classification
[ ] envelope iff fixed-defect zero proved
[ ] local all-window-zeros-critical equivalence proved
[ ] no global RH equivalence through W without coverage audit
[ ] no fixed-ε sign theorem claimed
[ ] no limit exchange
[ ] no synthetic completion square
[ ] no zero-side theorem used as arithmetic provider
```

## 12. Expected closeout

If the above compiles:

```text
CS8 independent arithmetic envelope        OPEN
CS9 envelope-strength classification       GREEN
abstract vanishing-envelope search         CLOSED as target-equivalent repackaging
source-specific finite cancellation        NEXT FRONTIER
RH                                          NOT CLAIMED
```

This is a useful narrowing: the next result must come from the finite arithmetic source itself, not from another abstract envelope wrapper.
