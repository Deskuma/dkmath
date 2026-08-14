# IPSM-033 — CS9 closeout and CS10 prime-cutoff residual cancellation audit

## Status entering this checkpoint

CS9 is Green.

`PascalCenteredXiPrimeSideUpperEnvelopeStrengthAudit.lean` proves, at one fixed residue-transport window `W`, that the abstract vanishing upper-envelope contract is equivalent to fixed-defect nonpositivity, hence by the already-established zero-side nonnegativity to fixed-defect vanishing, hence to every zero in the finite window lying on the critical line.

This is a strength classification only. It is not an independent arithmetic provider and does not prove RH.

The public import is present in `DkMath.RH`.

The large `PascalCenteredXiPrimeSideQuadraticizationAudit.lean` remains frozen at CS1–CS7. New work continues by module chaining.

## CS10 objective

Do not search for another abstract upper-envelope wrapper. CS9 shows that such a wrapper is already as strong as the fixed-window criticality target.

Instead, return to the finite arithmetic source and identify the exact signed residual that remains after all fixed correction terms cancel.

The current finite source ledger is

```text
finite arithmetic approximant
  = 2 * prime cutoff
  + 2 * archimedean correction
  + 2 * elementary correction
  + 2 * top-horizontal contribution.
```

The exact finite Xi endpoint has the same three correction terms and replaces only the finite prime cutoff by the ordinary-zeta right-edge integral.

Therefore, when finite approximant and exact endpoint are subtracted, the archimedean, elementary, and top-horizontal terms cancel algebraically. The entire `X`-cutoff error should reduce to one prime residual.

This cancellation is the first target of CS10.

## New module

Create:

```text
DkMath/RH/CFBRC/PascalCenteredXiPrimeSideFiniteSourceCancellationAudit.lean
```

Import:

```lean
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideUpperEnvelopeStrengthAudit
```

Do not append new theorems to `PascalCenteredXiPrimeSideQuadraticizationAudit.lean` except genuine bug fixes.

After Green validation, add the new module to `DkMath.RH`.

---

## CS10-A — name the prime cutoff residual

Introduce a source-level residual such as

```lean
noncomputable def pascalCenteredXiPrimeSideFiniteCutoffResidual
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℂ :=
  pascalCenteredXiPrimeSideQuadraticizationPrimeModeSum ε W X -
    pascalXiOrdinaryZetaRightEdgeIntegral
      (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
      W.rectangle.σ W.rectangle.T
```

The exact naming may be adjusted, but the object must be the same source residual throughout CS10.

Also prove the adapter between `PrimeModeSum` and the existing XDP-017 cutoff integral, preferably from

```text
pascalPrimePowerRightEdgeCutoffIntegral_eq_vonMangoldt_sum
```

rather than by re-expanding the source independently.

## CS10-B — exact four-term cancellation

Target an exact theorem of the form

```lean
pascalCenteredXiMellinQuadraticArithmeticApproximant ε W X -
    pascalCenteredXiMellinQuadraticArithmeticEndpoint ε W =
  2 * pascalCenteredXiPrimeSideFiniteCutoffResidual ε W X
```

under the required `0 < ε` hypothesis.

The proof should use the already-Green finite source ledger and the exact finite four-term Xi formula. It must not estimate any of the three correction surfaces.

Acceptance criterion:

```text
prime cutoff                       remains
archimedean correction             cancels exactly
elementary correction              cancels exactly
top-horizontal contribution        cancels exactly
```

If this theorem closes, the four-source `X`-error problem is reduced to one source object.

## CS10-C — residual tends to zero in X

Use XDP-017:

```text
tendsto_pascalPrimePowerRightEdgeCutoffIntegral_of_residueTransportWindow
```

and the `PrimeModeSum` adapter to prove

```lean
Tendsto
  (fun X => pascalCenteredXiPrimeSideFiniteCutoffResidual ε W X)
  atTop
  (nhds 0)
```

for fixed positive `ε`.

This theorem is not a new limit exchange. It is only the already-authorized inner `X → ∞` limit at fixed `ε`.

## CS10-D — expose the exact defect coordinate of the cutoff residual

The normalized arithmetic observable uses `(2 * π * I)⁻¹`. Therefore the finite defect error should depend only on one real coordinate of the prime residual.

Audit and prove the exact normalization theorem. With the current conventions, the expected algebraic shape is

```text
ArithmeticDefectApproximant(ε,W,X)
  - ArithmeticDefectEndpoint(ε,W)
  = -(PrimeCutoffResidual(ε,W,X).im) / π.
```

The sign and normalization must be verified by Lean from the existing definitions; do not hard-code the displayed formula if the actual convention differs.

This is an important compression:

```text
complex four-term finite source
  ↓ exact cancellation
one complex prime residual
  ↓ fixed-contour normalization
one real signed projection of that residual
```

A norm bound on the whole residual is weaker than this signed projection and should not replace it unless needed only as a domination lemma.

## CS10-E — prime tail source audit

After CS10-B–D are Green, inspect whether the same residual can be represented directly as a von Mangoldt tail.

The existing source already gives:

```text
pascalPrimePowerPHZFiniteUpTo_eq_LSeries_partialSum
vonMangoldt_LSeries_term_eq
```

and absolute summability in `Re(s) > 1`.

Desired source question:

```text
PrimeCutoffResidual
  = weighted finite-interval integral of
      (finite von Mangoldt partial sum - full von Mangoldt L-series)
```

and, if justified without an unproved sum/integral exchange,

```text
  = negative weighted von Mangoldt tail.
```

Do not commute an infinite sum with the `t`-integral merely because both are totalized. Any such interchange needs its own absolute/dominated convergence certificate.

## CS10-F — signed projection, not coarse norm

The arithmetic defect only sees the real coordinate identified in CS10-D. Therefore the next source-level sign audit should target the signed projection of the residual directly.

At the right edge, each source integrand contains the differential factor `I`; consequently the imaginary part of the integrated residual is related to the real part of the pre-`I` weighted prime tail.

Audit whether symmetric `t ↦ -t` conjugation can reduce this to a real kernel on `[0,T]` or an equivalent paired form.

Potential target shape:

```text
PrimeCutoffResidual.im
  = signed finite/summable von Mangoldt tail functional.
```

Only after this exact signed representation is available should positivity, negativity, cancellation, or a vanishing upper envelope be investigated.

Do not revert to the previously closed coarse-norm route.

## CS10-G — independent arithmetic mechanism decision

Accept one of two outcomes.

### Green-A — source-derived signed control

A theorem derived from the finite/von-Mangoldt source provides a genuine signed upper control sufficient to imply the CS8 envelope contract, without using:

```text
fixed Xi defect nonnegativity/vanishing,
horizontal zero energy,
anti-mirror zero energy,
RH or an RH-equivalent statement,
reverse/joint limit exchange.
```

Only in this case proceed to a closure module.

### Green-B — named prime residual obstruction

If exact reduction succeeds but no independent signed control of the residual is available, introduce a narrowly named frontier, for example

```lean
inductive PascalCenteredXiPrimeSideFiniteCutoffSignedResidualGap : Prop
  | noIndependentSignedPrimeResidualProvider :
      PascalCenteredXiPrimeSideFiniteCutoffSignedResidualGap
```

This is not an impossibility theorem.

## Critical firewalls

1. CS9 has already proved that an abstract vanishing upper envelope is fixed-window criticality in disguise. Do not introduce another provider record that simply assumes it.
2. CS7 smoothing bounds control approximation error, not the sign of the fixed defect.
3. The three correction terms cancel only in the finite-approximant minus exact-endpoint difference. This does not mean they are individually zero or sign-definite.
4. The `X → ∞` residual convergence is allowed only at fixed positive `ε`.
5. No `ε ↔ X` limit exchange, joint limit, or uniform-in-`ε` convergence is to be inferred.
6. No zero-side energy or RH-equivalent theorem may be used as a prime-side sign provider.
7. No RH consequence is to be stated in CS10.

## Expected CS10 closeout ledger

```text
CS9 strength classification                         GREEN
finite four-term source ledger                       GREEN
exact correction cancellation                        TARGET
prime cutoff residual named                          TARGET
prime residual → 0 as X → ∞                         TARGET
finite defect error = signed prime residual coord    TARGET
von Mangoldt tail representation                     AUDIT
independent signed prime residual control             OPEN
fixed-ε sign theorem                                 NOT CLAIMED
limit exchange                                       NOT CLAIMED
RH                                                   NOT CLAIMED
```

## Validation

At minimum:

```text
lake env lean <new module>
lake build DkMath.RH.CFBRC.PascalCenteredXiPrimeSideFiniteSourceCancellationAudit
./lb DkMath.RH.CFBRC.PascalCenteredXiPrimeSideFiniteSourceCancellationAudit
lake build DkMath.RH
git diff --check
```

Also audit that no `sorry`, `admit`, synthetic RH provider, or forbidden limit-exchange theorem was introduced.
