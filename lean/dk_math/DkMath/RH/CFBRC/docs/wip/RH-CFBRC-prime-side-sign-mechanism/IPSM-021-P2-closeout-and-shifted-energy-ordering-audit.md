# IPSM-021 — P2 closeout and shifted-energy ordering audit

Date: 2026-08-14

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v0`

Status: Gate 4B.3 post-P2 / no sign claim / no RH claim

## 0. P2 review result

P2 is Green.

The implementation now supplies, at fixed finite `X`, finite contour height, and fixed `ε`:

- interval integrability of the finite PHZ source;
- non-prime integrability transported from the existing right-edge API;
- separation of a jointly continuous box kernel from the `t`-only source amplitude;
- concrete `IntegrableOn` for `BoxFeature` on the finite `t/u` rectangle;
- unconditional `t/u` interval-integral exchange;
- exact normalized aggregate identity;
- exact identification with the existing genuine complex vertical source.

The final endpoint is:

```lean
pascalCenteredXiMellinQuadraticComplexVerticalSurface_eq_normalized_aggregate
```

No `X → ∞`, `ε → 0`, or `T → ∞` argument is used.

The top-horizontal contribution and radial comparison remain outside the vertical identity.

## 1. Q1 must begin with an equivalence audit

The next question is whether the two polarized square energies can be ordered.

Do not assume that positivity of each square energy supplies that order.

For the real aggregate `F_X(u)`, the already proved pointwise polarization identity is:

```text
4 F_X(u) = |F_X(u) + 1|^2 - |F_X(u) - 1|^2.
```

Therefore the ordering of the two shifted energies is expected to be exactly equivalent to the sign of the vertical linear source.

The first task is to formalize this equivalence before searching for an ordering provider.

## 2. Q1-A — define the two shifted energies

Introduce real-valued normalized finite energies:

```lean
noncomputable def pascalCenteredXiPrimeSideQuadraticizationShiftedPlusEnergy
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℝ :=
  (2 * ε)⁻¹ *
    ∫ u in (-ε)..ε,
      Complex.normSq
        (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u + 1)

noncomputable def pascalCenteredXiPrimeSideQuadraticizationShiftedMinusEnergy
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℝ :=
  (2 * ε)⁻¹ *
    ∫ u in (-ε)..ε,
      Complex.normSq
        (pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u - 1)
```

Names may be shortened if needed, but keep the `Plus` / `Minus` distinction explicit.

## 3. Q1-B — prove both energies nonnegative independently

For `hε : 0 < ε`, prove:

```lean
pascalCenteredXiPrimeSideQuadraticizationShiftedPlusEnergy_nonneg
pascalCenteredXiPrimeSideQuadraticizationShiftedMinusEnergy_nonneg
```

These proofs should use only:

```text
(2ε)⁻¹ ≥ 0
normSq ≥ 0
finite symmetric interval
```

No source sign should enter.

This certifies that both beams are individually PSD quantities.

## 4. Q1-C — integrated polarization identity

Use:

```lean
pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature_polarization_pointwise
```

and the completed P2 bridge:

```lean
pascalCenteredXiMellinQuadraticComplexVerticalSurface_eq_normalized_aggregate
```

The preferred exact endpoint is the complex identity:

```text
4 * ComplexVerticalSurface = (ShiftedPlusEnergy : ℂ) - (ShiftedMinusEnergy : ℂ).
```

Suggested theorem shape:

```lean
theorem pascalCenteredXiPrimeSideQuadraticization_verticalSurface_eq_shiftedEnergyDifference
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    (4 : ℂ) * pascalCenteredXiMellinQuadraticComplexVerticalSurface ε W X =
      (pascalCenteredXiPrimeSideQuadraticizationShiftedPlusEnergy ε W X : ℂ) -
      (pascalCenteredXiPrimeSideQuadraticizationShiftedMinusEnergy ε W X : ℂ) := by
  ...
```

An equivalent real-part statement is acceptable if it avoids unnecessary coercion work.

Do not insert the top-horizontal or radial terms here.

## 5. Q1-D — ordering is equivalent to vertical sign

From the difference identity, prove the exact real equivalence:

```text
ShiftedMinusEnergy ≤ ShiftedPlusEnergy
iff
0 ≤ ComplexVerticalSurface.re.
```

Suggested theorem shape:

```lean
theorem pascalCenteredXiPrimeSideQuadraticization_shiftedEnergy_order_iff_vertical_nonneg
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideQuadraticizationShiftedMinusEnergy ε W X ≤
        pascalCenteredXiPrimeSideQuadraticizationShiftedPlusEnergy ε W X ↔
      0 ≤ (pascalCenteredXiMellinQuadraticComplexVerticalSurface ε W X).re := by
  ...
```

This theorem is load-bearing.

It establishes that an ordering provider for the two shifted PSD energies is not automatically new information. Unless derived independently from source structure, it is merely the vertical sign rewritten.

## 6. Q1-E — optional sum identity

If convenient, also prove the complementary identity:

```text
E_+ + E_- = 2 E_0 + 2,
```

where `E_0` is the existing continuous Gram energy.

For `ε > 0`, the normalized average of the constant function `1` over `[-ε, ε]` is `1`.

Together with the difference identity this gives the exact two-beam decomposition:

```text
E_+ = E_0 + 1 + 2 V
E_- = E_0 + 1 - 2 V
```

where `V` denotes the real vertical linear observable.

This is structurally useful but does not give the sign of `V`.

## 7. Q1 classification

After Q1-D, classify the route as follows:

```text
source-derived adjoint                    GREEN
continuous Gram energy                    GREEN
finite rectangle Fubini                   GREEN
vertical source = normalized aggregate    GREEN
polarization into two PSD beams           GREEN
individual shifted-energy nonnegativity   GREEN
ordering between shifted energies         EQUIVALENT TO VERTICAL SIGN
independent ordering provider              OPEN
```

If no additional source theorem independently orders the two energies, record a named audit boundary such as:

```lean
inductive PascalCenteredXiPrimeSideQuadraticizationShiftedEnergyOrderingGap : Prop
  | noIndependentOrderingProvider :
      PascalCenteredXiPrimeSideQuadraticizationShiftedEnergyOrderingGap
```

This is an audit marker, not an impossibility theorem.

## 8. Do not smuggle the desired sign into the provider

Forbidden provider patterns include fields equivalent to:

```text
E_- ≤ E_+
0 ≤ verticalSurface.re
0 ≤ scalarExcess
finite defect ≤ 0
```

unless the field is itself the conclusion of an independently proved source-level theorem.

A provider that simply assumes the ordering is not a positivity mechanism.

## 9. What Q1 can legitimately discover

A genuine Q1 success would require a source-derived theorem that orders the two shifted beams for a reason independent of the vertical sign statement itself.

Possible sources to audit later include:

```text
- monotonicity or contraction of a source-derived transformation;
- a positive operator comparison;
- a projection inequality with an independently normalized reference vector;
- an exact completion-of-square identity with a nonnegative remainder;
- an arithmetic inequality visible before forming the vertical scalar.
```

Do not manufacture such a theorem from polarization alone.

## 10. Whole-surface firewall

Even a successful vertical ordering theorem would not yet prove the finite scalar excess sign.

The whole finite scalar surface is still:

```text
vertical real contribution
+ top-horizontal imaginary contribution
- radial comparison.
```

Therefore these remain separate gates:

```text
Q1  vertical shifted-energy ordering
Q2  top-horizontal quadraticization / control
Q3  radial comparison compatibility
Q4  whole scalar-excess PSD or inequality bridge
```

No zero-side anti-mirror energy may be used to close these prime-side gates.

No limit order may be exchanged.

No RH consequence is asserted at this checkpoint.
