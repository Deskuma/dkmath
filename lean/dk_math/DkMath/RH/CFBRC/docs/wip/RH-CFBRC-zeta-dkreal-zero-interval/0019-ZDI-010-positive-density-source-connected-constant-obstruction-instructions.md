# ZDI-010 — positive-density source-connected constant obstruction instructions

Branch: `wip/RH-CFBRC-zeta-dkreal-zero-interval-260819-v0`

Parent roadmap: `0000-RH-CFBRC-zeta-dkreal-zero-interval-roadmap.md`

Depends on:

- `0018-ZDI-009-positive-density-normalized-constant-obstruction-audit-report.md`
- `EtaCriticalMirrorPositiveDensityNormalizedConstantObstructionAudit.lean`
- `EtaCriticalMirrorPairedFrameNormalizedConstantAudit.lean`
- `EtaCriticalMirrorPairedFrameGrowingBlockTailRemainder.lean`
- `EtaCriticalMirrorPairedFramePositiveDensityRotationLimit.lean`

## Goal

ZDI-009 proved the scalar inequalities

```text
R_right > 16 * M_right
R_left  > 16 * M_left
```

for the explicit constants extracted in ZDI-008.  The algebra is Lean-certified, including the norm bridges

```text
|s.im| <= ‖s‖
|s.im| <= ‖criticalMirror s‖.
```

The margin side is already source-connected in Lean: for every realizable `EtaPairPositiveDensityBlockSchedule S`, the actual normalized finite block power lower bounds converge to the explicit constants used as `M_right` and `M_left`.

The residual side is not yet certified at the same level.  The actual source theorem is the pointwise upper majorant

```lean
etaCriticalMirrorBlockStartResidualTailPowerBound s K N
```

from `EtaCriticalMirrorPairedFrameGrowingBlockTailRemainder.lean`, while the positive-density normalized residual constants used by ZDI-008/ZDI-009 were obtained in the audit report by asymptotic calculation.

ZDI-010 must close only this provenance gap.

> Prove directly from the existing residual-majorant definition and positive-density schedule limits that, on each off-critical side, the actual current residual majorant is eventually strictly larger than sixteen times the actual certified block-margin power lower bound.

Do **not** start an exact Eta-tail cancellation argument yet.  Do **not** implement fixed block-start projection transport.  Do **not** introduce a new provider or a definition that merely stores the target constant.

## Global RH boundary

The final target remains Mathlib `RiemannHypothesis`, and the global RH frontier has not moved.

This task proves only that one particular comparison strategy is too coarse:

```text
actual residual projection
  <= current explicit residual power majorant

current certified block margin lower bound
  <= actual positive block margin
```

If the explicit upper majorant is itself eventually much larger than the certified lower margin, then these two current bounds cannot certify residual domination.

This does **not** imply:

- the exact oscillatory Eta tail is large;
- the exact residual cannot cancel;
- a sharper residual estimate is impossible;
- global no-cancellation;
- `centeredSigma` coercivity;
- RH.

Do not add any RH-equivalent provider, residual-domination assumption, no-cancellation structure field, moving-line `research_goal`, or dependency carrying `sorryAx`.

## Fixed source facts

### Residual majorant

From `EtaCriticalMirrorPairedFrameGrowingBlockTailRemainder.lean`:

```lean
noncomputable def etaCriticalMirrorDefectPairTailPowerBound
    (s : ℂ) (L : ℕ) : ℝ :=
  ‖criticalMirror s‖ *
      (((L : ℝ) ^ (-(criticalMirror s).re)) /
        (criticalMirror s).re) +
    ‖s‖ * (((L : ℝ) ^ (-s.re)) / s.re)

noncomputable def etaCriticalMirrorBlockStartResidualTailPowerBound
    (s : ℂ) (K N : ℕ) : ℝ :=
  |s.im| * etaCriticalMirrorDefectPairTailPowerBound s (K + N)
```

and the actual projected residual satisfies the existing pointwise power bound under the open-strip positivity assumptions.

The source definition contains two nonnegative terms.  For the obstruction it is enough to keep only the dominant term on the relevant side; there is no need to prove the full two-term normalized limit unless that is simpler in Lean.

### Positive-density schedule geometry

For `S : EtaPairPositiveDensityBlockSchedule`:

```lean
S.relativeLength_tendsto_density
S.leftEndpointRatio_tendsto_one_add_two_mul_density
S.endpointRatio_tendsto_one_add_two_mul_density
S.density_pos
```

The new residual proof will also need the asymptotic relation between

```text
(K + S.blockLength K : ℝ)
```

and

```text
etaPairFrameLeftEndpoint K = 2K + 1.
```

Prefer proving a small source-derived ratio lemma, for example an equivalent of

```text
(K + S.blockLength K : ℝ) / etaPairFrameLeftEndpoint K
  -> 1/2 + S.density
```

or

```text
etaPairFrameLeftEndpoint K / (K + S.blockLength K : ℝ)
  -> 2 / (1 + 2 * S.density),
```

with all denominator positivity/eventual nonzero obligations proved from existing endpoint facts and `S.density_pos`.

Do not encode the desired limit as a structure field.

### Margin normalization

From `EtaCriticalMirrorPairedFrameNormalizedConstantAudit.lean`:

```lean
S.rightNormalizedBlockMarginPowerLowerBound_tendsto s
S.leftNormalizedBlockMarginPowerLowerBound_tendsto s
```

These already connect the **actual** block-margin power lower bounds to

```text
M_right = (s.im^2 / 4) * S.density *
  (1 + 2*S.density)^(s.re - 2)

M_left = (s.im^2 / 4) * S.density *
  (1 + 2*S.density)^(-s.re - 1).
```

Reuse them; do not duplicate the margin asymptotics.

### ZDI-009 scalar obstruction

Reuse:

```lean
right_normalizedResidualConstant_gt_sixteen_mul_marginConstant_of_point
left_normalizedResidualConstant_gt_sixteen_mul_marginConstant_of_point
```

Do not re-prove the quotient algebra unless theorem-shape adaptation genuinely requires it.

## Preferred proof architecture

### Step 1 — source-derived dominant residual component

On the right side `1/2 < s.re < 1`, isolate the mirror-side nonnegative summand of the actual residual majorant:

```text
|s.im| * ‖criticalMirror s‖ / (1 - s.re) *
  (K + S.blockLength K)^(-(1 - s.re)).
```

Use `criticalMirror_re` to obtain this expression from the existing definition, not from a new target-valued definition.

On the left side `0 < s.re < 1/2`, isolate the original-side summand:

```text
|s.im| * ‖s‖ / s.re *
  (K + S.blockLength K)^(-s.re).
```

Prove each dominant component is pointwise `<=` the corresponding actual `etaCriticalMirrorBlockStartResidualTailPowerBound`, eventually if positivity at `K = 0` makes a global statement inconvenient.

### Step 2 — normalized dominant-component limit

Prove the source-derived normalized limit on the right:

```text
etaPairFrameLeftEndpoint K^(1 - s.re) * dominantRightResidual(K)
  ->
|s.im| * ‖criticalMirror s‖ / (1 - s.re) *
  (2 / (1 + 2*S.density))^(1 - s.re).
```

Likewise on the left:

```text
etaPairFrameLeftEndpoint K^s.re * dominantLeftResidual(K)
  ->
|s.im| * ‖s‖ / s.re *
  (2 / (1 + 2*S.density))^s.re.
```

These are exactly the `R_right` and `R_left` constants consumed by ZDI-009.

Do not assume these limit formulas.  Derive them from the schedule ratio limit and standard `Real.rpow` continuity/limit lemmas.

### Step 3 — combine with the actual margin limit

Use the already proved normalized margin limits plus the ZDI-009 strict constant inequalities and separation of limits to prove eventually:

Right side:

```text
16 *
  (etaPairFrameLeftEndpoint K^(1 - s.re) *
    etaCriticalMirrorRightBlockMarginPowerLowerBound
      s K (S.blockLength K))
<
  etaPairFrameLeftEndpoint K^(1 - s.re) *
    etaCriticalMirrorBlockStartResidualTailPowerBound
      s K (S.blockLength K).
```

Left side:

```text
16 *
  (etaPairFrameLeftEndpoint K^s.re *
    etaCriticalMirrorLeftBlockMarginPowerLowerBound
      s K (S.blockLength K))
<
  etaPairFrameLeftEndpoint K^s.re *
    etaCriticalMirrorBlockStartResidualTailPowerBound
      s K (S.blockLength K).
```

Since the normalizing powers are strictly positive, if convenient derive the stronger unnormalized eventual statements:

```text
16 * etaCriticalMirrorRightBlockMarginPowerLowerBound
       s K (S.blockLength K)
< etaCriticalMirrorBlockStartResidualTailPowerBound
       s K (S.blockLength K)
```

and the analogous left theorem.

The normalized eventual theorem is sufficient for ZDI-010 certification if cancellation of the common positive normalization is technically noisy.

## Recommended source-facing theorem shapes

Names may be adapted to existing conventions, but the semantic content should be equivalent to:

```lean
theorem eventually_sixteen_mul_rightNormalizedBlockMarginPowerLowerBound_lt_residualPowerBound
    (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ}
    (hre : (1 : ℝ) / 2 < s.re)
    (hre1 : s.re < 1)
    (him : s.im ≠ 0) :
    ∀ᶠ K : ℕ in atTop,
      16 *
        (etaPairFrameLeftEndpoint K ^ (1 - s.re) *
          etaCriticalMirrorRightBlockMarginPowerLowerBound
            s K (S.blockLength K)) <
      etaPairFrameLeftEndpoint K ^ (1 - s.re) *
        etaCriticalMirrorBlockStartResidualTailPowerBound
          s K (S.blockLength K) := ...
```

and

```lean
theorem eventually_sixteen_mul_leftNormalizedBlockMarginPowerLowerBound_lt_residualPowerBound
    (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ}
    (hre0 : 0 < s.re)
    (hre : s.re < (1 : ℝ) / 2)
    (him : s.im ≠ 0) :
    ∀ᶠ K : ℕ in atTop,
      16 *
        (etaPairFrameLeftEndpoint K ^ s.re *
          etaCriticalMirrorLeftBlockMarginPowerLowerBound
            s K (S.blockLength K)) <
      etaPairFrameLeftEndpoint K ^ s.re *
        etaCriticalMirrorBlockStartResidualTailPowerBound
          s K (S.blockLength K) := ...
```

A theorem specialized further to `NontrivialRiemannZetaZero s` may be added only as a thin corollary using already proved strip/nonreal-height facts.  The load-bearing analytic result should remain independent of RH.

## Certification requirement

ZDI-010 is complete only if the final obstruction theorem mentions the **actual existing residual-majorant object** and the **actual existing margin-lower-bound object** in its statement or has a transparent theorem chain to them.

A new definition such as

```lean
myResidualConstant := <the ZDI-009 scalar expression>
```

followed by another inequality about `myResidualConstant` does not close the provenance gap.

Likewise, a report-only asymptotic calculation is insufficient.

For every new load-bearing theorem:

1. prove all denominator positivity/eventual nonzero conditions;
2. use only realizable positive-density schedule fields;
3. do not import the incompatible `EtaPairGrowingBlockSchedule` contract as an assumption for the same block function;
4. run `#print axioms`;
5. reject any dependency containing `sorryAx`;
6. run the focused build and `git diff --check`.

## Decision gate after ZDI-010

### If source-connected eventual obstruction is proved

Classify the present route as **O-CONSTANT / FACT-FIXED**:

```text
positive-density schedule
+ current residual power majorant
+ current certified margin lower bound
```

cannot certify residual domination, even before any projection-loss factor.

Then close this bounded-span/current-majorant branch.  The next audit may move to the exact oscillatory Eta tail and ask whether a genuinely sharper cancellation estimate exists.

### If the source connection fails

Do not retain `O-CONSTANT` as a fixed theorem merely because the scalar algebra is true.  Report the exact missing limit/inequality and classify ZDI-009 as a scalar obstruction only.

Do not compensate by defining the missing limit as data or by assuming eventual residual domination/non-domination.

## Deliverables

1. A narrow Lean module implementing the source-connected residual/margin obstruction.
2. A ZDI-010 report containing:
   - exact source theorem trace;
   - new ratio/limit lemmas;
   - right and left eventual obstruction theorem statements;
   - whether unnormalized corollaries were obtained;
   - axiom output;
   - focused build result;
   - final classification (`O-CONSTANT / FACT-FIXED` or exact remaining gap).
3. No fixed-block projection transport implementation unless the source-connected constant obstruction unexpectedly fails and the report explains why transport becomes relevant again.
