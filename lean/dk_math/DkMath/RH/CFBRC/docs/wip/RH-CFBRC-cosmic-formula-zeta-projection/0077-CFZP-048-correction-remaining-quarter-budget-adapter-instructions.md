# CFZP-0077 / CFZP-048 correction

## remaining-quarter budget adapter — correction instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

対象 module:

`DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisRemainderAbelSmoothDiscrepancyAudit`

CFZP-048 の Abel / smooth remainder 本体は成立している。

CLOSED と扱ってよい部分:

```text
finite remainder Abel identity
smooth/discrepancy exact split
smooth density integral
log-cell transform
smooth remainder O(exp(beta U)/U^2) envelope
smooth remainder <= explicitSmoothMargin / 4
full remainder debt <= margin/4 + remainder discrepancy debt
039 remainder-cell debt = K * raw prime remainder sum
```

ただし Gate J の remaining-quarter adapter が CFZP-0076 の Green criterion と一致していない。

現在の実装は概略

```text
G_A + RemainderDiscrepancy + HigherPower + CarrierDiscrepancy
  <= 3/4 * Margin + eta
```

を `Cfzp048RemainingQuarterMarginBudgetAt` としている。

これは単独では有効な radial adapter だが、CFZP-047 で CLOSED になった

```text
HigherPower <= Margin / 2
```

を使用しておらず、remaining-quarter という名前の意味にも一致しない。

CFZP-048 の intended decomposition は

```text
HigherPower <= Margin / 2
RemainderDebt <= Margin / 4 + RemainderDiscrepancy

remaining budget:
G_A + CarrierDiscrepancy + RemainderDiscrepancy
  <= Margin / 4 + eta
```

である。

したがって CFZP-049 へ進まず、CFZP-048 内で Gate J を修正する。

---

## 1. `Cfzp048RemainingQuarterMarginBudgetAt` を修正

既存 declaration の body を次の意味へ置換する。

```lean
def Cfzp048RemainingQuarterMarginBudgetAt
    (ε η D : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : Prop :=
  pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W
      (cfzp040CarrierCellNaturalLeft W c n) +
    D + cfzp048PrimeAxisRemainderDiscrepancyCellDebt ε W c n ≤
      cfzp044ExplicitSmoothMargin ε W c n / 4 + η
```

Equivalent reassociation/order is fine.

Important:

- `cfzp034HigherPowerReferenceMass` must **not** occur in this predicate.
- RHS must be `Margin / 4 + η`, not `3/4 * Margin + η`.
- This predicate is only the budget left *after* the already-proved half-margin and quarter-margin payments.

---

## 2. Green-required finite radial adapter

Replace or add a theorem with the following logical interface.

Preferred name:

```lean
theorem cfzp048RemainingQuarterMarginBudget_implies_radialContactDeficit_le
```

It should take the existing 044 analytic/discrepancy inputs plus the three finite budget facts:

```lean
(hHigher :
  cfzp034HigherPowerReferenceMass ε W
      (cfzp040CarrierCellNaturalLeft W c n)
      (cfzp040CarrierCellNaturalRight W c n) ≤
    cfzp044ExplicitSmoothMargin ε W c n / 2)

(hRemainder :
  cfzp039PrimeAxisRemainderCellDebt ε W c n
      (cfzp040CarrierCellNaturalLeft W c n)
      (cfzp040CarrierCellNaturalRight W c n) ≤
    cfzp044ExplicitSmoothMargin ε W c n / 4 +
      cfzp048PrimeAxisRemainderDiscrepancyCellDebt ε W c n)

(hQuarter : Cfzp048RemainingQuarterMarginBudgetAt ε η D W c n)
```

and conclude

```lean
pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W
  (cfzp040CarrierCellNaturalRight W c n) ≤ η
```

### Proof spine

Build the existing 044 budget exactly:

```lean
have hbudget044 : Cfzp044ExplicitSmoothMarginBudgetAt ε η D W c n := by
  unfold Cfzp048RemainingQuarterMarginBudgetAt at hQuarter
  unfold Cfzp044ExplicitSmoothMarginBudgetAt
  linarith
```

The arithmetic is:

```text
G_A + D + RemainderDiscrepancy <= Margin/4 + eta
RemainderDebt <= Margin/4 + RemainderDiscrepancy
HigherPower <= Margin/2
----------------------------------------------------
G_A + RemainderDebt + HigherPower + D <= Margin + eta
```

Then call

```lean
cfzp044ExplicitSmoothMarginBudget_implies_radialContactDeficit_le
```

with the existing `hM`, `hLate`, `hSmoothLog`, finite carrier Abel regularity, and carrier discrepancy bound `hD`.

Do not re-prove the 041 reservoir directly unless necessary. 044 is now the canonical radial adapter.

---

## 3. Structural wrapper using the already-proved 048 remainder theorem

Strongly preferred: add a convenience theorem that does not ask the caller to manufacture `hRemainder` manually.

It may take the current premises of

```lean
cfzp048PrimeAxisRemainderCellDebt_le_quarterMargin_add_discrepancyDebt
```

and derive `hRemainder` internally, then call the corrected remaining-quarter adapter.

Conceptual form:

```lean
theorem cfzp048StructuralRemainderRemainingQuarterBudget_implies_radialContactDeficit_le
    ...
    (hHigher : HigherPower <= Margin / 2)
    (hQuarter : Cfzp048RemainingQuarterMarginBudgetAt ε η D W c n) :
    radialDeficit B <= η := by
  have hRemainder :=
    cfzp048PrimeAxisRemainderCellDebt_le_quarterMargin_add_discrepancyDebt ...
  exact cfzp048RemainingQuarterMarginBudget_implies_radialContactDeficit_le
    ... hHigher hRemainder hQuarter
```

This keeps the decomposition visible in theorem dependencies.

---

## 4. Connect CFZP-047 explicitly

The corrected module must contain at least one theorem-level use or wrapper designed for

```lean
cfzp047HigherPowerReferenceMass_eventually_le_half_explicitSmoothMargin
```

or its cofinal positive-phase wrapper.

A compact eventual synchronization helper is enough:

```lean
 theorem cfzp048_eventually_higherPowerHalf_and_remainderQuarterLate
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (c : ℝ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform ε W c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      cfzp048PrimeAxisRemainderQuarterMarginThreshold ε W c ≤
          cfzp039CarrierCellLeft W c n ∧
      cfzp034HigherPowerReferenceMass ε W
          (cfzp040CarrierCellNaturalLeft W c n)
          (cfzp040CarrierCellNaturalRight W c n) ≤
        cfzp044ExplicitSmoothMargin ε W c n / 2 := by
  ...
```

Proof idea:

- use `cfzp047HigherPowerReferenceMass_eventually_le_half_explicitSmoothMargin` for the higher-power threshold;
- use `cfzp043_carrierCellLeft_eventually_ge` at the 048 quarter-margin threshold;
- synchronize with `max N₁ N₂`.

This theorem does **not** need to prove remainder analytic readiness or discrepancy decay.

---

## 5. Keep the actual arithmetic gaps open

After correction, the remaining arithmetic budget should literally read

```text
starting radial deficit
+ carrier discrepancy debt
+ remainder discrepancy debt
<= explicit smooth margin / 4 + eta
```

The structural residuals have already been paid:

```text
higher-prime-power residual: CLOSED at margin/2 (CFZP-047)
prime-axis smooth remainder: CLOSED at margin/4 (CFZP-048)
late exceptional prime axis: CLOSED exactly (CFZP-044)
```

Open gaps remain:

```text
carrier discrepancy functional decay
remainder discrepancy functional decay
pointwise discrepancy -> combined functional bound
leading SmoothAbel -> SmoothLogCell readiness
cofinal remaining-quarter budget provider
interior-strip provider
```

Do not reintroduce higher-power or structural remainder as GAPs in CFZP-048.

---

## 6. Roadmap correction

The CFZP-048 roadmap entry currently says

```text
remaining quarter-margin budget -> finite radial endpoint: CLOSED with supplied providers
```

Keep that line only after the corrected predicate and adapter above exist.

Add/clarify:

```text
CFZP-047 higher-power half-margin + CFZP-048 remainder quarter-margin composition: CLOSED
remaining-quarter predicate excludes HigherPower and structural smooth remainder: CLOSED
remaining-quarter budget -> 044 explicit-margin radial endpoint: CLOSED
```

The intended frontier after correction is:

```text
Margin
  |- 1/2 : higher powers                 CLOSED
  |- 1/4 : prime-axis smooth remainder   CLOSED
  `- 1/4 : G_A + two discrepancy debts   OPEN provider
```

---

## 7. Do not change the already-correct 048 core

Unless required by Lean refactoring, do not disturb:

```text
cfzp048PrimeAxisRemainderTestFunction
cfzp048PrimeRemainderSumIoc_eq_abel
cfzp048PrimeRemainderSumIoc_eq_smooth_add_discrepancy
cfzp048PrimeRemainderSmoothAbelModel_eq_densityIntegral
cfzp048PrimeRemainderSmoothAbelCell_eq_logCell
cfzp048PrimeRemainderSmoothLogCell_le
cfzp048PrimeAxisSmoothRemainderEnvelope_le_quarter_explicitSmoothMargin
cfzp048PrimeAxisRemainderCellDebt_le_quarterMargin_add_discrepancyDebt
cfzp048PrimeAxisRemainderCellDebt_eq_constant_mul_primeRemainderSum
```

The correction is Gate J composition, not a rewrite of the Abel analysis.

---

## 8. Firewall

Still forbidden in this correction:

- PNT
- Mertens
- Dirichlet
- Bertrand
- prime-log equidistribution
- infinite prime sums
- summability / limit exchange
- automatic `σ < 1`
- unconditional prime-counting discrepancy decay
- CFZP-018 provider
- global RH

---

## 9. Green criterion for corrected CFZP-048

CFZP-048 becomes Green-A when all of the following theorem-level facts coexist:

```text
HigherPower <= Margin/2                       [CFZP-047]
RemainderDebt <= Margin/4 + RemainderDisc    [CFZP-048]
G_A + CarrierDisc + RemainderDisc
  <= Margin/4 + eta                           [supplied budget]
---------------------------------------------------------
radial deficit at right endpoint <= eta       [via CFZP-044]
```

The key requirement is that the public `Cfzp048RemainingQuarterMarginBudgetAt` itself expresses only the **last quarter**. If it still contains `HigherPower` or has RHS `3/4 * Margin`, CFZP-048 Gate J remains incomplete and CFZP-049 must not begin.
