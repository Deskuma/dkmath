# IPSM-051 — CS27 closeout and CS28 top-edge factor-safety / finite zeta-mismatch audit

## 0. Status

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v1`

CS27 verdict: **Green-B**.

CS27 has now proved, entirely at finite cutoff and finite rectangle height:

- a holomorphic complex phase potential `Φ_r`, including the genuine `r = 0` branch,
- `Φ_r'(z) = z * exp(r z)`,
- vanishing imaginary part on the real axis,
- the CS26 real phase primitive as an imaginary endpoint jump of `Φ_r`,
- a one-mode Mellin potential whose derivative is exactly the finite Mellin mode source,
- the finite mode kernel as an imaginary potential jump,
- a finite von-Mangoldt aggregate potential,
- the aggregate interaction as the imaginary aggregate-potential jump,
- a finite arithmetic top-edge companion as the top-corner endpoint difference.

The actual fixed-Xi top-horizontal correction is intentionally not identified with that companion.

## 1. Critical firewall: Xi boundary safety is not decomposition safety

The existing repository already records the relevant principle in `PascalCenteredXiCompletedZetaLogDerivBridge`:

> Xi nonvanishing alone does not license separate ordinary-zeta / Gamma / elementary logarithmic-derivative terms.

The local decomposition theorem requires, at the ordinary coordinate `s`, all of:

```text
s ≠ 0,
s ≠ 1,
riemannZeta s ≠ 0,
Complex.Gammaℝ s ≠ 0.
```

On the right edge, `Re(s) > 1` supplies the required zeta/Gamma safety automatically.

On the top edge, the path crosses the critical strip, so this automatic right-edge argument is unavailable.

Therefore CS28 must **not** derive a top-edge decomposition merely from
`W.rectangle_boundary_safe`.

## 2. CS28-A — top-edge decomposition-safety contract

Introduce a narrow contract for the actual top edge, for example:

```lean
def IsPascalCenteredXiTopLogDerivDecompositionSafe
    (W : PascalCenteredXiResidueTransportWindow) : Prop :=
  ∀ u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ),
    let s := pascalSymmetricRectangleTopEdge u W.rectangle.T
    s ≠ 0 ∧ s ≠ 1 ∧
      riemannZeta s ≠ 0 ∧
      Complex.Gammaℝ s ≠ 0
```

Use the exact set/orientation shape convenient for interval-integral proofs; do not weaken mathematical coverage.

If `s ≠ 0`, `s ≠ 1`, or Gamma safety can be proved automatically from `W.rectangle.hT`, export those facts separately, but do not assume zeta nonvanishing is automatic.

Do not add this field to the general residue-window structure unless there is a compelling reusable reason. A local CS28 predicate is preferred.

## 3. CS28-B — actual fixed-Xi top decomposition

Under the top decomposition-safety contract, prove the pointwise theorem along the top edge:

```text
pascalCenteredXiNegLogDeriv(centered(topEdge(u,T)))
  = pascalXiOrdinaryZetaNegLogDeriv(topEdge(u,T))
    + pascalXiArchimedeanLogDeriv(topEdge(u,T))
    + pascalXiElementaryLogDerivCorrection(topEdge(u,T)).
```

Then multiply by the existing Mellin weight and integrate with the repository's exact top orientation to obtain:

```text
TopXi
  = TopZeta + TopArchimedean + TopElementary.
```

All objects remain finite-height path integrals.

No prime-series expansion of `TopZeta` is allowed.

## 4. CS28-C — turn the CS27 endpoint companion into a path integral

CS27 currently proves that the finite arithmetic top companion is an endpoint difference of the aggregate holomorphic potential.

Close the missing finite fundamental-theorem adapter:

```text
FiniteArithmeticTopEdgeCompanion(ε,W,X)
  = 2 * ∫ u in σ..(1-σ),
      hε(centered(topEdge(u,T))) *
      PHZFiniteUpTo X (topEdge(u,T)).
```

The exact coefficient `2` must be derived from the existing aggregate-potential definition, not inserted by convention.

This theorem is finite and uses only the derivative of the finite aggregate potential.

It does not use `-ζ'/ζ = Σ Λ(n)n^{-s}` on the top edge.

## 5. CS28-D — define the genuine finite horizontal zeta mismatch

Define the source-derived horizontal mismatch

```text
TopZetaCutoffMismatch(ε,W,X)
  := 2 * ∫ u in σ..(1-σ),
      hε(centered(topEdge(u,T))) *
      (pascalXiOrdinaryZetaNegLogDeriv(topEdge(u,T))
       - pascalPrimePowerPHZFiniteUpTo X(topEdge(u,T))).
```

Keep it as a finite integral of an exact pointwise difference.

Do **not** rewrite it as an infinite prime tail inside the critical strip.

Under top decomposition safety, prove an exact ledger of the shape

```text
2 * TopXi
  = FiniteArithmeticTopEdgeCompanion
    + 2 * TopArchimedean
    + 2 * TopElementary
    + TopZetaCutoffMismatch.
```

Check orientation and normalization carefully against the existing definition of
`pascalCenteredXiTopHorizontalContribution`.

If the repository's finite arithmetic source already carries the outer factor `2` elsewhere, adjust the statement to the actual source normalization. The theorem must be source-derived, not cosmetically normalized.

## 6. CS28-E — normalized real top mismatch

The CS23-CS25 radial ledger uses normalized real contributions. Define the normalized real version of the horizontal mismatch using the same normalization as
`pascalCenteredXiMellinQuadraticNormalizedTopContribution`.

Prove the exact relation between:

- actual normalized top correction,
- finite arithmetic top companion,
- normalized top archimedean contribution,
- normalized top elementary contribution,
- normalized top zeta-cutoff mismatch.

This should let the CS25 baseline

```text
G(ε,W,0)
```

be rewritten with an explicit finite top mismatch component, if and only if the existing source ledger genuinely supports the algebra.

## 7. CS28-F — compare the vertical interaction endpoint with the top companion

Do not assert they cancel directly.

Instead, use the same aggregate holomorphic potential to prove the exact corner ledger among:

- right-top potential value,
- right-mid / real-axis potential value,
- left-top potential value,
- top companion.

The aggregate interaction is the imaginary part of the right vertical jump.
The top companion is the full complex top-corner difference.

Record only identities that follow from these shared corner values.

If useful, define a finite `CornerLedger` structure or named quantities, but avoid abstracting before the exact formulas are known.

## 8. CS28-G — determine what remains after the exact top decomposition

The key classification question is whether the old `topHorizontalCorrectionMatchingPending` frontier reduces to the finite object

```text
TopZetaCutoffMismatch.
```

If yes, that is a genuine Green-B improvement: a vague fixed-Xi top mismatch has become a concrete finite zeta-vs-PHZ horizontal residual.

Then test whether existing finite-source cancellation or functional-equation reflection theorems constrain this mismatch.

Do not call a mere restatement a provider.

## 9. Strength audit

A future estimate of

```text
TopZetaCutoffMismatch → 0
```

as `X → ∞` is **not** automatic.

On a top edge crossing `Re(s) ≤ 1`, ordinary Dirichlet-series convergence is unavailable in general.

Therefore any convergence theorem must come from an independent analytic mechanism such as:

- a contour identity,
- finite block cancellation,
- analytic continuation encoded without illegal series exchange,
- a path deformation with justified pole/zero accounting,
- or another source-derived finite estimate.

Do not import the right-edge `Re(s)>1` convergence theorem onto the top edge.

## 10. Named frontier

If the exact ledger closes but no independent estimate is obtained, retain a narrower gap, for example:

```lean
inductive PascalCenteredXiPrimeSideFiniteTopZetaMismatchGap : Prop
  | noIndependentFiniteTopZetaMismatchEstimate
```

If top decomposition safety itself is unavailable from current window hypotheses, retain that as a distinct prerequisite gap rather than folding it into the mismatch estimate.

## 11. Expected verdicts

### Green

The actual top correction is reduced to a finite source mismatch and an independent theorem controls that mismatch strongly enough to improve the CS25 interaction-reach frontier.

### Green-B

Top factor-safety contract, finite companion path identity, actual top decomposition, and exact finite zeta-mismatch ledger are all proved, but no independent mismatch estimate is supplied.

### Yellow

The finite companion path identity is proved, but actual fixed-Xi top decomposition cannot be obtained without a new top factor-safety hypothesis. Record the precise prerequisite.

### Red

Any implementation that:

- infers zeta nonvanishing from Xi nonvanishing without proof,
- replaces top-edge zeta log derivative by an infinite von-Mangoldt series in the critical strip,
- identifies a corner endpoint with the whole top integral without a primitive theorem,
- assumes interaction reach / radial contact,
- uses the zero-side fixed defect as provider,
- or derives RH.

## 12. Validation

Run at least:

```text
lake env lean <new-CS28-file>
lake build DkMath.RH
git diff --check
```

No new `sorry`, `axiom`, or `native_decide`.

## 13. Research interpretation

CS25 reduced the cutoff-dependent radial deficit to interaction only.

CS26 reduced that interaction to finite phase boundary values.

CS27 showed those boundary values are evaluations of a single holomorphic finite-mode potential.

CS28 should now separate two very different facts:

```text
finite arithmetic potential geometry
```

and

```text
actual fixed-Xi top-edge analytic continuation.
```

The finite arithmetic companion is exact algebra/holomorphy. The fixed-Xi top term contains the genuinely continued zeta information. Their difference is therefore a natural place for the remaining analytic difficulty to live.

If the mismatch reduces cleanly to a finite `zeta - PHZ_X` horizontal residual, then the old vague top-boundary gap has acquired a concrete source identity without any illegal infinite-series step. That is the intended CS28 target.
